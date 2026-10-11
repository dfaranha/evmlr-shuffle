#include "evmlr_user_proof.h"
#include "evmlr_utils.h"
#include "flint/nmod.h"
#include <stdlib.h>
#include <string.h>

#ifdef EVMLR_LAZER
#include <pthread.h>
#include "lazer.h"
#include "lazer/user2.h"
#include "lazer/user3.h"
#include "lazer/user4.h"
#endif

#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif

/* The statement holds mod 64 q: rows mod q scaled by 2^ZETA, rounding rows
 * mod 2^ZETA scaled by q. gcd(2^ZETA, q) = 1, so each scaled row is 0 mod
 * 64 q exactly when the original is 0 mod its own modulus. */
#define UP_MOD ((1UL << ZETA) * MOD_Q)
#define UP_HALF (UP_MOD / 2)

/*============================================================================*/
/* Shapes                                                                     */
/*============================================================================*/

#ifdef EVMLR_LAZER
/* Pad positions of layer i < k - 1 that the next layers' ciphertexts depend
 * on: w_c for c < K_LWE, through H'', and w_(K_LWE + y) for the y < L_i - 1
 * that are not the vote's position. */
static slong positions(slong k, slong i) {
    return (i < k - 1) ? K_LWE + evmlr_ballot_layer_len(k, i) - 1 : 0;
}

/* Column offsets: per layer, r (K_LWE), e2 (K_LWE), e3, sbar, then 2 ETA bit
 * planes of d and ZETA - 2 ETA of the rounding error, positions() each. */
typedef struct {
    slong k, rows, cols;
    slong base[8], D[8];
} shape_t;

static void shape(shape_t *sh, slong k) {
    sh->k = k;
    sh->cols = 0;
    sh->rows = k * (K_LWE + 1);
    for (slong i = 0; i < k; i++) {
        sh->base[i] = sh->cols;
        sh->D[i] = positions(k, i);
        sh->cols += 2 * K_LWE + 2 + ZETA * sh->D[i];
        sh->rows += sh->D[i];
    }
}

static slong col_r(const shape_t *sh, slong i, slong c) { return sh->base[i] + c; }
static slong col_e2(const shape_t *sh, slong i, slong x) { return sh->base[i] + K_LWE + x; }
static slong col_e3(const shape_t *sh, slong i) { return sh->base[i] + 2 * K_LWE; }
static slong col_sbar(const shape_t *sh, slong i) { return sh->base[i] + 2 * K_LWE + 1; }
static slong col_d(const shape_t *sh, slong i, slong b, slong p) {
    return sh->base[i] + 2 * K_LWE + 2 + b * sh->D[i] + p;
}
static slong col_rb(const shape_t *sh, slong i, slong b, slong p) {
    return sh->base[i] + 2 * K_LWE + 2 + 2 * ETA * sh->D[i] + b * sh->D[i] + p;
}

#endif

#ifdef EVMLR_LAZER

/*============================================================================*/
/* The statement A w + t = 0 mod 64 q                                         */
/*============================================================================*/

typedef struct {
    shape_t sh;
    nmod_poly_struct *A; /* rows x cols, mod UP_MOD */
    nmod_poly_struct *t; /* rows */
} stmt_t;

static nmod_poly_struct *entry(stmt_t *st, slong r, slong c) {
    return st->A + r * st->sh.cols + c;
}

/* x mod m as a centred integer. */
static slong centred(ulong x, ulong m) {
    return (x > m / 2) ? (slong) x - (slong) m : (slong) x;
}

static ulong up(slong v) {
    slong r = v % (slong) UP_MOD;

    return (ulong) (r < 0 ? r + (slong) UP_MOD : r);
}

/* out += scale * a, for a polynomial a mod m read through centred residues. */
static void add_scaled(nmod_poly_t out, const nmod_poly_t a, ulong m, slong scale) {
    for (slong i = 0; i < nmod_poly_length(a); i++) {
        slong v = centred(nmod_poly_get_coeff_ui(a, i), m) * scale;

        nmod_poly_set_coeff_ui(out, i, nmod_add(nmod_poly_get_coeff_ui(out, i), up(v), out->mod));
    }
}

/* out += scale, as a constant. */
static void add_const(nmod_poly_t out, slong scale) {
    nmod_poly_set_coeff_ui(out, 0, nmod_add(nmod_poly_get_coeff_ui(out, 0), up(scale), out->mod));
}

/* sum of a_i[y]'s witness part into row: a_i[y] = sum_(c < K_LWE) H''[y][c] w_c
 * + w_(K_LWE + y), w_c = d_0 + d_1 - d_2 - d_3 (ETA = 2), scaled by 64. */
static void add_pad(stmt_t *st, slong row, slong i, slong y, const evmlr_otse_ctx_t otse) {
    const shape_t *sh = &st->sh;

    for (slong b = 0; b < 2 * ETA; b++) {
        const slong sign = (b < ETA) ? 1 : -1;

        for (slong c = 0; c < K_LWE; c++) {
            add_scaled(entry(st, row, col_d(sh, i, b, c)),
                       nmod_poly_mat_entry(otse->H_prime, y, c), MOD_Q, sign << ZETA);
        }
        add_const(entry(st, row, col_d(sh, i, b, K_LWE + y)), sign << ZETA);
    }
}

/* The MLPKE rows of layer j, u = A^T r + e2 and v = t^T r + e3 + (q+1)/2 sbar,
 * scaled by 64, from row onwards. */
static void add_mlpke(stmt_t *st, slong row, slong j, const evmlr_mlpke_pk_t pk) {
    const shape_t *sh = &st->sh;

    for (slong x = 0; x <= K_LWE; x++) {
        for (slong c = 0; c < K_LWE; c++) {
            const nmod_poly_struct *a = (x < K_LWE) ? nmod_poly_mat_entry(pk->A, c, x)
                                                    : nmod_poly_mat_entry(pk->t, c, 0);
            add_scaled(entry(st, row + x, col_r(sh, j, c)), a, MOD_Q, 1 << ZETA);
        }
        if (x < K_LWE) {
            add_const(entry(st, row + x, col_e2(sh, j, x)), 1 << ZETA);
        } else {
            add_const(entry(st, row + x, col_e3(sh, j)), 1 << ZETA);
            add_const(entry(st, row + x, col_sbar(sh, j)), (slong) ((MOD_Q + 1) / 2) << ZETA);
        }
    }
}

static void stmt_build(stmt_t *st, slong k, const evmlr_ballot_struct *ballot,
                       const evmlr_mlpke_pk_t *pks, const evmlr_otse_ctx_t otse) {
    shape_t *sh = &st->sh;
    slong row = 0;

    shape(sh, k);
    st->A = flint_malloc(sh->rows * sh->cols * sizeof(nmod_poly_struct));
    st->t = flint_malloc(sh->rows * sizeof(nmod_poly_struct));
    for (slong i = 0; i < sh->rows * sh->cols; i++) nmod_poly_init(st->A + i, UP_MOD);
    for (slong i = 0; i < sh->rows; i++) nmod_poly_init(st->t + i, UP_MOD);

    // Layer 0: its MLPKE ciphertext is public.
    add_mlpke(st, row, 0, pks[0]);
    for (slong x = 0; x < K_LWE; x++) {
        add_scaled(st->t + row + x, nmod_poly_mat_entry(ballot->enc[0]->uT, 0, x), MOD_Q, -(1 << ZETA));
    }
    add_scaled(st->t + row + K_LWE, ballot->enc[0]->v, MOD_Q, -(1 << ZETA));
    row += K_LWE + 1;

    // Layer j + 1's MLPKE ciphertext is m_j[0..K_LWE], m_j = c*_j - a_j, and
    // unrolled, m_j[y] = c*_0[3 j + y] - sum_(i <= j) a_i[3 (j - i) + y].
    for (slong j = 0; j + 1 < k; j++) {
        add_mlpke(st, row, j + 1, pks[j + 1]);
        for (slong x = 0; x <= K_LWE; x++) {
            for (slong i = 0; i <= j; i++) {
                add_pad(st, row + x, i, (K_LWE + 1) * (j - i) + x, otse);
            }
            add_scaled(st->t + row + x, nmod_poly_mat_entry(ballot->cstar, (K_LWE + 1) * j + x, 0),
                       MOD_Q, -(1 << ZETA));
        }
        row += K_LWE + 1;
    }

    // Rounding (3), mod 2^ZETA and scaled by q: H[p] sbar - 4 d_p - (rb_p - 2) = 0,
    // with d_p = sum_b 2^b d_(b,p) and the error rb_p - 2 in [-2, 2).
    for (slong i = 0; i + 1 < k; i++) {
        for (slong p = 0; p < sh->D[i]; p++) {
            add_scaled(entry(st, row, col_sbar(sh, i)), nmod_poly_mat_entry(otse->H, p, 0),
                       1UL << ZETA, MOD_Q);
            for (slong b = 0; b < 2 * ETA; b++) {
                add_const(entry(st, row, col_d(sh, i, b, p)), -(slong) MOD_Q << (ZETA - 2 * ETA + b));
            }
            for (slong b = 0; b < ZETA - 2 * ETA; b++) {
                add_const(entry(st, row, col_rb(sh, i, b, p)), -(slong) MOD_Q << b);
            }
            nmod_poly_fit_length(st->t + row, DEGREE_N);
            for (slong c = 0; c < DEGREE_N; c++) {
                nmod_poly_set_coeff_ui(st->t + row, c, up((slong) MOD_Q * (1 << (ZETA - 2 * ETA - 1))));
            }
            row++;
        }
    }
}

static void stmt_clear(stmt_t *st) {
    for (slong i = 0; i < st->sh.rows * st->sh.cols; i++) nmod_poly_clear(st->A + i);
    for (slong i = 0; i < st->sh.rows; i++) nmod_poly_clear(st->t + i);
    flint_free(st->A);
    flint_free(st->t);
}

/* The witness, from the layers' secrets; 0 if a rounding error is out of
 * range, i.e. d is not the rounding of H sbar. */
static int witness(nmod_poly_struct *w, const stmt_t *st, const evmlr_ballot_layer_struct *layers,
                   const evmlr_otse_ctx_t otse) {
    const shape_t *sh = &st->sh;
    const slong stride = K_LWE + otse->L;
    nmod_poly_t hs, prod, s64;
    int ok = 1;

    nmod_poly_init(hs, 1UL << ZETA);
    nmod_poly_init(prod, 1UL << ZETA);
    nmod_poly_init(s64, 1UL << ZETA);
    for (slong i = 0; i < sh->k; i++) {
        for (slong c = 0; c < K_LWE; c++) {
            add_scaled(w + col_r(sh, i, c), nmod_poly_mat_entry(layers[i].r, 0, c), MOD_Q, 1);
            add_scaled(w + col_e2(sh, i, c), nmod_poly_mat_entry(layers[i].e2, 0, c), MOD_Q, 1);
        }
        add_scaled(w + col_e3(sh, i), layers[i].e3, MOD_Q, 1);
        add_scaled(w + col_sbar(sh, i), nmod_poly_mat_entry(layers[i].sbar, 0, 0), MOD_Q, 1);
        nmod_poly_zero(s64);
        for (slong c = 0; c < nmod_poly_length(nmod_poly_mat_entry(layers[i].sbar, 0, 0)); c++) {
            nmod_poly_set_coeff_ui(s64, c, nmod_poly_get_coeff_ui(nmod_poly_mat_entry(layers[i].sbar, 0, 0), c) % 64);
        }
        for (slong p = 0; p < sh->D[i]; p++) {
            slong d[DEGREE_N] = { 0 };

            for (slong b = 0; b < 2 * ETA; b++) {
                const nmod_poly_struct *bit = nmod_poly_mat_entry(layers[i].d_dagger, b * stride + p, 0);

                nmod_poly_set(w + col_d(sh, i, b, p), bit);
                for (slong c = 0; c < nmod_poly_length(bit); c++) {
                    d[c] += (slong) nmod_poly_get_coeff_ui(bit, c) << b;
                }
            }
            // H[p] sbar in R_(2^ZETA), negacyclic.
            nmod_poly_mul(prod, nmod_poly_mat_entry(otse->H, p, 0), s64);
            nmod_poly_zero(hs);
            for (slong c = 0; c < nmod_poly_length(prod); c++) {
                ulong v = nmod_poly_get_coeff_ui(prod, c);
                slong at = c % DEGREE_N;

                nmod_poly_set_coeff_ui(hs, at, (c < DEGREE_N) ? nmod_add(nmod_poly_get_coeff_ui(hs, at), v, hs->mod)
                                                              : nmod_sub(nmod_poly_get_coeff_ui(hs, at), v, hs->mod));
            }
            for (slong c = 0; c < DEGREE_N; c++) {
                slong err = centred((nmod_poly_get_coeff_ui(hs, c) + 64 * 16 - 4 * (ulong) d[c]) % 64, 64);
                slong rb = err + (1 << (ZETA - 2 * ETA - 1));

                if (rb < 0 || rb >= (1 << (ZETA - 2 * ETA))) {
                    ok = 0;
                    rb = 0;
                }
                for (slong b = 0; b < ZETA - 2 * ETA; b++) {
                    if ((rb >> b) & 1) nmod_poly_set_coeff_ui(w + col_rb(sh, i, b, p), c, 1);
                }
            }
        }
    }
    nmod_poly_clear(hs);
    nmod_poly_clear(prod);
    nmod_poly_clear(s64);
    return ok;
}

/* Whether A w + t = 0 mod 64 q, which LaZer's prover does not check. */
static int holds(const stmt_t *st, const nmod_poly_struct *w) {
    nmod_poly_t acc, prod;
    int ok = 1;

    nmod_poly_init(acc, UP_MOD);
    nmod_poly_init(prod, UP_MOD);
    for (slong r = 0; r < st->sh.rows && ok; r++) {
        nmod_poly_set(acc, st->t + r);
        for (slong c = 0; c < st->sh.cols; c++) {
            const nmod_poly_struct *a = st->A + r * st->sh.cols + c;

            if (nmod_poly_is_zero(a) || nmod_poly_is_zero(w + c)) continue;
            nmod_poly_mul(prod, a, w + c);
            for (slong i = 0; i < nmod_poly_length(prod); i++) {
                ulong v = nmod_poly_get_coeff_ui(prod, i);
                slong at = i % DEGREE_N;

                nmod_poly_set_coeff_ui(acc, at, (i < DEGREE_N) ? nmod_add(nmod_poly_get_coeff_ui(acc, at), v, acc->mod)
                                                               : nmod_sub(nmod_poly_get_coeff_ui(acc, at), v, acc->mod));
            }
        }
        ok = nmod_poly_is_zero(acc);
    }
    nmod_poly_clear(acc);
    nmod_poly_clear(prod);
    return ok;
}

#endif

/*============================================================================*/
/* LaZer                                                                      */
/*============================================================================*/

void evmlr_user_proof_init(evmlr_user_proof_t pi) {
    pi->data = NULL;
    pi->len = 0;
}

void evmlr_user_proof_clear(evmlr_user_proof_t pi) {
    free(pi->data);
    pi->data = NULL;
    pi->len = 0;
}

#ifdef EVMLR_LAZER

static const lin_params_struct *params_for(slong k) {
    switch (k) {
        case 2: return user2;
        case 3: return user3;
        case 4: return user4;
        default: return NULL;
    }
}

int evmlr_user_proof_available(slong k) {
    return params_for(k) != NULL;
}

/* One run of LaZer's prover or verifier, on its own thread: its prover
 * recurses over the binary coefficients and overflows a default 8 MB stack
 * from three servers on. */
typedef struct {
    const lin_params_struct *params;
    int64_t *A, *t, *w; /* centred residues mod 64 q */
    slong rows, cols;
    uint8_t *proof;
    size_t len;
    int verify, ok;
} job_t;

static void *job_run(void *arg) {
    job_t *jb = arg;
    static const uint8_t ppseed[32] = "evmlr user proof, LaZer v1";
    INT_T(q, 1);
    polymat_t A;
    polyvec_t t, w;

    int_set_i64(q, (int64_t) UP_MOD);
    POLYRING_T(Rq, q, DEGREE_N);
    polymat_alloc(A, Rq, jb->rows, jb->cols);
    polyvec_alloc(t, Rq, jb->rows);
    polymat_set_i64(A, jb->A);
    polyvec_set_coeffvec_i64(t, jb->t);
    if (!jb->verify) {
        lin_prover_state_t P;

        polyvec_alloc(w, Rq, jb->cols);
        polyvec_set_coeffvec_i64(w, jb->w);
        lin_prover_init(P, ppseed, jb->params);
        lin_prover_set_statement(P, A, t);
        lin_prover_set_witness(P, w);
        lin_prover_prove(P, jb->proof, &jb->len, NULL);
        lin_prover_clear(P);
        polyvec_free(w);
        jb->ok = 1;
    } else {
        lin_verifier_state_t V;
        size_t len = jb->len;

        lin_verifier_init(V, ppseed, jb->params);
        lin_verifier_set_statement(V, A, t);
        jb->ok = lin_verifier_verify(V, jb->proof, &len) && len == jb->len;
        lin_verifier_clear(V);
    }
    polymat_free(A);
    polyvec_free(t);
    return NULL;
}

static void run(job_t *jb) {
    static int ready = 0;
    pthread_attr_t at;
    pthread_t th;

    if (!ready) {
        lazer_init();
        ready = 1;
    }
    pthread_attr_init(&at);
    pthread_attr_setstacksize(&at, (size_t) 1 << 30);
    if (pthread_create(&th, &at, job_run, jb) != 0) {
        jb->ok = 0;
    } else {
        pthread_join(th, NULL);
    }
    pthread_attr_destroy(&at);
}

/* The statement as LaZer reads it: A row-major with each polynomial's
 * coefficients in turn, t likewise, centred mod 64 q. */
static void export(int64_t *out, const nmod_poly_struct *v, slong len) {
    for (slong i = 0; i < len; i++) {
        for (slong c = 0; c < DEGREE_N; c++) {
            out[i * DEGREE_N + c] = centred(nmod_poly_get_coeff_ui(v + i, c), UP_MOD);
        }
    }
}

static void job_init(job_t *jb, const stmt_t *st, slong k) {
    jb->params = params_for(k);
    jb->rows = st->sh.rows;
    jb->cols = st->sh.cols;
    jb->A = flint_malloc(jb->rows * jb->cols * DEGREE_N * sizeof(int64_t));
    jb->t = flint_malloc(jb->rows * DEGREE_N * sizeof(int64_t));
    jb->w = NULL;
    export(jb->A, st->A, jb->rows * jb->cols);
    export(jb->t, st->t, jb->rows);
}

static void job_clear(job_t *jb) {
    flint_free(jb->A);
    flint_free(jb->t);
    if (jb->w != NULL) flint_free(jb->w);
}

int evmlr_user_proof_prove(evmlr_user_proof_t pi, const evmlr_ballot_struct *ballot,
                           const evmlr_ballot_layer_struct *layers, slong k,
                           const evmlr_mlpke_pk_t *pks, const evmlr_otse_ctx_t otse) {
    stmt_t st;
    nmod_poly_struct *w;
    job_t jb;
    int ok;

    evmlr_user_proof_clear(pi);
    if (!evmlr_user_proof_available(k)) return 0;
    stmt_build(&st, k, ballot, pks, otse);
    w = flint_malloc(st.sh.cols * sizeof(nmod_poly_struct));
    for (slong c = 0; c < st.sh.cols; c++) nmod_poly_init(w + c, UP_MOD);
    ok = witness(w, &st, layers, otse) && holds(&st, w);
    if (ok) {
        job_init(&jb, &st, k);
        jb.w = flint_malloc(st.sh.cols * DEGREE_N * sizeof(int64_t));
        export(jb.w, w, st.sh.cols);
        jb.len = lin_params_get_prooflen(jb.params);
        jb.proof = malloc(jb.len);
        jb.verify = 0;
        run(&jb);
        ok = jb.ok;
        if (ok) {
            pi->data = jb.proof;
            pi->len = jb.len;
        } else {
            free(jb.proof);
        }
        job_clear(&jb);
    }
    for (slong c = 0; c < st.sh.cols; c++) nmod_poly_clear(w + c);
    flint_free(w);
    stmt_clear(&st);
    return ok;
}

int evmlr_user_proof_verify(const evmlr_user_proof_t pi, const evmlr_ballot_struct *ballot,
                            slong k, const evmlr_mlpke_pk_t *pks, const evmlr_otse_ctx_t otse) {
    stmt_t st;
    job_t jb;

    if (!evmlr_user_proof_available(k) || pi->data == NULL) return 0;
    stmt_build(&st, k, ballot, pks, otse);
    job_init(&jb, &st, k);
    jb.proof = pi->data;
    jb.len = pi->len;
    jb.verify = 1;
    run(&jb);
    job_clear(&jb);
    stmt_clear(&st);
    return jb.ok;
}

#else

int evmlr_user_proof_available(slong k) {
    (void) k;
    return 0;
}

int evmlr_user_proof_prove(evmlr_user_proof_t pi, const evmlr_ballot_struct *ballot,
                           const evmlr_ballot_layer_struct *layers, slong k,
                           const evmlr_mlpke_pk_t *pks, const evmlr_otse_ctx_t otse) {
    (void) ballot; (void) layers; (void) k; (void) pks; (void) otse;
    evmlr_user_proof_clear(pi);
    return 0;
}

int evmlr_user_proof_verify(const evmlr_user_proof_t pi, const evmlr_ballot_struct *ballot,
                            slong k, const evmlr_mlpke_pk_t *pks, const evmlr_otse_ctx_t otse) {
    (void) pi; (void) ballot; (void) k; (void) pks; (void) otse;
    return 0;
}

#endif

#ifdef MAIN
#include "evmlr_main.h"

#ifndef USER_K
#define USER_K 2 // LaZer's prover needs about 0.6 GB at 2 servers, 2 GB at 3
#endif

void test(flint_rand_t state) {
    const slong k = USER_K, L_max = evmlr_ballot_layer_len(k, 0);
    evmlr_hpke_ctx_t hpke;
    evmlr_mlpke_keypair_t kp[USER_K];
    evmlr_mlpke_pk_t pks[USER_K];
    evmlr_ballot_layer_struct layers[USER_K];
    evmlr_ballot_struct ballot;
    evmlr_user_proof_t pi;
    nmod_poly_mat_t vote;

    evmlr_hpke_ctx_init(hpke, L_max, state);
    for (slong j = 0; j < k; j++) {
        evmlr_mlpke_keypair_gen(kp[j], state, hpke->enc_ctx);
        *pks[j] = *kp[j]->pk;
    }
    nmod_poly_mat_init(vote, M_LEN, 1, MOD_Q);
    evmlr_utils_uniform_mat(vote);
    evmlr_ballot_layers_init(layers, k, L_max);
    evmlr_ballot_init(&ballot, k);
    evmlr_user_proof_init(pi);
    evmlr_ballot_encrypt(&ballot, layers, vote, k, (const evmlr_mlpke_pk_t *) pks, hpke);

    if (!evmlr_user_proof_available(k)) {
        printf("(LaZer not built in, or no parameters for k = %ld: the proof tests are skipped)\n", (long) k);
        goto end;
    }

    TEST_ONCE("the user's proof of correct encryption verifies") {
        TEST_ASSERT(evmlr_user_proof_prove(pi, &ballot, layers, k, (const evmlr_mlpke_pk_t *) pks,
                                           hpke->otse_ctx) == 1, end);
        TEST_ASSERT(evmlr_user_proof_verify(pi, &ballot, k, (const evmlr_mlpke_pk_t *) pks,
                                            hpke->otse_ctx) == 1, end);
    } TEST_END;

    /* Changing any public part of the ballot changes the statement. */
    TEST_ONCE("the proof does not verify for another ballot") {
        nmod_poly_struct *c = nmod_poly_mat_entry(ballot.cstar, 0, 0);
        ulong old = nmod_poly_get_coeff_ui(c, 5);
        nmod_poly_set_coeff_ui(c, 5, nmod_add(old, 1, c->mod));
        int v1 = evmlr_user_proof_verify(pi, &ballot, k, (const evmlr_mlpke_pk_t *) pks, hpke->otse_ctx);
        nmod_poly_set_coeff_ui(c, 5, old);
        old = nmod_poly_get_coeff_ui(ballot.enc[0]->v, 9);
        nmod_poly_set_coeff_ui(ballot.enc[0]->v, 9, nmod_add(old, 1, ballot.enc[0]->v->mod));
        int v2 = evmlr_user_proof_verify(pi, &ballot, k, (const evmlr_mlpke_pk_t *) pks, hpke->otse_ctx);
        nmod_poly_set_coeff_ui(ballot.enc[0]->v, 9, old);
        TEST_ASSERT(v1 == 0 && v2 == 0, end);
    } TEST_END;

    TEST_ONCE("an altered proof does not verify") {
        pi->data[pi->len / 2] ^= 1;
        int v = evmlr_user_proof_verify(pi, &ballot, k, (const evmlr_mlpke_pk_t *) pks, hpke->otse_ctx);
        pi->data[pi->len / 2] ^= 1;
        TEST_ASSERT(v == 0, end);
    } TEST_END;

    /* A pad that is not the rounding of H sbar: the decryption of the next
     * layer would not be what the user claims, and the prover must refuse. */
    TEST_ONCE("the prover refuses a pad that is not derived from its seed") {
        nmod_poly_struct *bit = nmod_poly_mat_entry(layers[0].d_dagger, 0, 0);
        ulong old = nmod_poly_get_coeff_ui(bit, 3);
        nmod_poly_set_coeff_ui(bit, 3, 1 - old);
        evmlr_user_proof_t bad;
        evmlr_user_proof_init(bad);
        int proved = evmlr_user_proof_prove(bad, &ballot, layers, k, (const evmlr_mlpke_pk_t *) pks,
                                            hpke->otse_ctx);
        evmlr_user_proof_clear(bad);
        nmod_poly_set_coeff_ui(bit, 3, old);
        TEST_ASSERT(proved == 0, end);
    } TEST_END;

end:
    evmlr_user_proof_clear(pi);
    evmlr_ballot_clear(&ballot);
    evmlr_ballot_layers_clear(layers, k);
    nmod_poly_mat_clear(vote);
    for (slong j = 0; j < k; j++) evmlr_mlpke_keypair_clear(kp[j]);
    evmlr_hpke_ctx_clear(hpke);
}

void bench(flint_rand_t state) {
    const slong k = USER_K, L_max = evmlr_ballot_layer_len(k, 0);
    evmlr_hpke_ctx_t hpke;
    evmlr_mlpke_keypair_t kp[USER_K];
    evmlr_mlpke_pk_t pks[USER_K];
    evmlr_ballot_layer_struct layers[USER_K];
    evmlr_ballot_struct ballot;
    evmlr_user_proof_t pi;
    nmod_poly_mat_t vote;

    if (!evmlr_user_proof_available(k)) return;
    evmlr_hpke_ctx_init(hpke, L_max, state);
    for (slong j = 0; j < k; j++) {
        evmlr_mlpke_keypair_gen(kp[j], state, hpke->enc_ctx);
        *pks[j] = *kp[j]->pk;
    }
    nmod_poly_mat_init(vote, M_LEN, 1, MOD_Q);
    evmlr_utils_uniform_mat(vote);
    evmlr_ballot_layers_init(layers, k, L_max);
    evmlr_ballot_init(&ballot, k);
    evmlr_user_proof_init(pi);
    evmlr_ballot_encrypt(&ballot, layers, vote, k, (const evmlr_mlpke_pk_t *) pks, hpke);
    BENCH_ONCE("evmlr_user_proof_prove", evmlr_user_proof_prove(pi, &ballot, layers, k,
               (const evmlr_mlpke_pk_t *) pks, hpke->otse_ctx));
    BENCH_ONCE("evmlr_user_proof_verify", evmlr_user_proof_verify(pi, &ballot, k,
               (const evmlr_mlpke_pk_t *) pks, hpke->otse_ctx));
    printf("SIZE: user proof, k = %ld servers: %zu bytes (%.1f KiB)\n", (long) k, pi->len, pi->len / 1024.0);
    evmlr_user_proof_clear(pi);
    evmlr_ballot_clear(&ballot);
    evmlr_ballot_layers_clear(layers, k);
    nmod_poly_mat_clear(vote);
    for (slong j = 0; j < k; j++) evmlr_mlpke_keypair_clear(kp[j]);
    evmlr_hpke_ctx_clear(hpke);
}

int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);
    flint_rand_t state;

    evmlr_rand_init(state);
    if (evmlr_runs_tests(mode))   test(state);
    if (evmlr_runs_benches(mode)) bench(state);
    flint_rand_clear(state);
    return test_status();
}
#endif
