#include "evmlr_zk_proof.h"
#include "gaussian.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>

#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif

/* Domains of the public matrices and challenges expanded from seeds. */
enum { DOM_A1 = 1, DOM_A2 = 2, DOM_B = 3, DOM_ALPHA = 4, DOM_PROJ = 5, DOM_MU = 6 };

/* Rejection sampling keeps its 2^-100 statistical distance at M = 1.75 once
 * the width is 21.485 times the norm of the shift it masks. */
#define ZK_M 1.75
#define ZK_ALPHA_RS 21.485
/* ||R v|| <= sqrt(337) ||v|| except with probability 2^-128 over R (LNP22),
 * which is the shift the projection mask has to hide. */
#define ZK_PROJ_STRETCH 18.357559
/* A Gaussian vector of dimension d exceeds t sigma sqrt(d) with probability
 * below (t e^((1 - t^2) / 2))^d; t = 1.7 makes that 2^-153 at d = ZK_PROJ. */
#define ZK_TAIL3 1.7
/* Tries at a projection before an honest prover would have succeeded except
 * with negligible probability; a witness that fails them all is too long. */
#define ZK_PROJ_TRIES 64

/*============================================================================*/
/* Vectors of ring elements                                                   */
/*============================================================================*/

static nmod_poly_struct *vec_init(slong len) {
    nmod_poly_struct *v = flint_malloc(len * sizeof(nmod_poly_struct));

    for (slong i = 0; i < len; i++) {
        nmod_poly_init(v + i, ZK_P);
    }
    return v;
}

static void vec_clear(nmod_poly_struct *v, slong len) {
    for (slong i = 0; i < len; i++) {
        nmod_poly_clear(v + i);
    }
    flint_free(v);
}

/* Centred value of a residue mod p. */
static slong centre(ulong v) {
    return (v > ZK_P / 2) ? (slong) v - (slong) ZK_P : (slong) v;
}

static ulong from_signed(slong v) {
    return (v < 0) ? ZK_P - (ulong) (-v) : (ulong) v;
}

/* Squared l2 norm of the centred coefficients of v[0..len). */
static double vec_norm2(const nmod_poly_struct *v, slong len) {
    double n = 0;

    for (slong i = 0; i < len; i++) {
        for (slong j = 0; j < nmod_poly_length(v + i); j++) {
            double c = (double) centre(nmod_poly_get_coeff_ui(v + i, j));
            n += c * c;
        }
    }
    return n;
}

/* Inner product of the centred coefficients of a[0..len) and b[0..len). */
static double vec_dot(const nmod_poly_struct *a, const nmod_poly_struct *b, slong len) {
    double d = 0;

    for (slong i = 0; i < len; i++) {
        for (slong j = 0; j < DEGREE_N; j++) {
            d += (double) centre(nmod_poly_get_coeff_ui(a + i, j))
               * (double) centre(nmod_poly_get_coeff_ui(b + i, j));
        }
    }
    return d;
}

/*============================================================================*/
/* Public parameters and the projection, expanded on demand                   */
/*============================================================================*/

static void expand(nmod_poly_t r, const uint8_t seed[32], uint32_t dom, slong i, slong j) {
    prg_t prg;

    evmlr_zk_prg_for(&prg, seed, dom, (uint64_t) i, (uint64_t) j);
    evmlr_zk_uniform(r, &prg);
}

/* out[0..ZK_KAPPA) = A_1 v1 + A_2 v2, v1 of length m1, v2 of length ZK_M2. */
static void ajtai(nmod_poly_struct *out, const nmod_poly_struct *v1, slong m1,
                  const nmod_poly_struct *v2, const uint8_t pp[32]) {
    nmod_poly_t a, t;

    evmlr_zk_init(a);
    evmlr_zk_init(t);
    for (slong i = 0; i < ZK_KAPPA; i++) {
        nmod_poly_zero(out + i);
        for (slong j = 0; j < m1; j++) {
            expand(a, pp, DOM_A1, i, j);
            evmlr_zk_mul(t, a, v1 + j);
            nmod_poly_add(out + i, out + i, t);
        }
        for (slong j = 0; j < ZK_M2; j++) {
            expand(a, pp, DOM_A2, i, j);
            evmlr_zk_mul(t, a, v2 + j);
            nmod_poly_add(out + i, out + i, t);
        }
    }
    nmod_poly_clear(a);
    nmod_poly_clear(t);
}

/* r = <b_l, v2> for slot l. */
static void bdlop_row(nmod_poly_t r, slong l, const nmod_poly_struct *v2, const uint8_t pp[32]) {
    nmod_poly_t b, t;

    evmlr_zk_init(b);
    evmlr_zk_init(t);
    nmod_poly_zero(r);
    for (slong j = 0; j < ZK_M2; j++) {
        expand(b, pp, DOM_B, l, j);
        evmlr_zk_mul(t, b, v2 + j);
        nmod_poly_add(r, r, t);
    }
    nmod_poly_clear(b);
    nmod_poly_clear(t);
}

/* The ZK_PROJ rows of the projection R restricted to the coefficients of
 * element j of (s, k): r[i * n + k], in {-1, 0, 1} with probabilities 1/4,
 * 1/2, 1/4. One stream per element, so R is never held whole. */
static void proj_column(int8_t *r, const uint8_t seed[32], slong j) {
    prg_t prg;
    uint8_t buf[DEGREE_N / 4];

    evmlr_zk_prg_for(&prg, seed, DOM_PROJ, (uint64_t) j, 0);
    for (slong i = 0; i < ZK_PROJ; i++) {
        prg_bytes(&prg, buf, sizeof(buf));
        for (slong k = 0; k < DEGREE_N; k++) {
            int b = (buf[k / 4] >> (2 * (k % 4))) & 3;

            r[i * DEGREE_N + k] = (int8_t) ((b == 1) - (b == 2));
        }
    }
}

/* out = R v over the integers, for v of length m1 with centred coefficients. */
static void proj_apply(slong out[ZK_PROJ], const nmod_poly_struct *v, slong m1,
                       const uint8_t seed[32]) {
    int8_t *r = flint_malloc(ZK_PROJ * DEGREE_N);
    slong c[DEGREE_N];

    for (slong i = 0; i < ZK_PROJ; i++) out[i] = 0;
    for (slong j = 0; j < m1; j++) {
        proj_column(r, seed, j);
        for (slong k = 0; k < DEGREE_N; k++) {
            c[k] = centre(nmod_poly_get_coeff_ui(v + j, k));
        }
        for (slong i = 0; i < ZK_PROJ; i++) {
            slong acc = 0;

            for (slong k = 0; k < DEGREE_N; k++) acc += r[i * DEGREE_N + k] * c[k];
            out[i] += acc;
        }
    }
    flint_free(r);
}

/*============================================================================*/
/* Fiat-Shamir                                                                */
/*============================================================================*/

/* Absorbs v[0..len) injectively: the count, then each element's length and
 * coefficients in six little-endian bytes, which hold any residue mod p. */
static void absorb(SHA256Context *sha, const nmod_poly_struct *v, slong len) {
    _Static_assert(ZK_P < (1UL << 48), "coefficients are absorbed in six bytes");
    uint8_t buf[6 * DEGREE_N + 8];

    for (int b = 0; b < 8; b++) buf[b] = (uint8_t) ((uint64_t) len >> (8 * b));
    SHA256Input(sha, buf, 8);
    for (slong i = 0; i < len; i++) {
        slong n = nmod_poly_length(v + i);

        for (int b = 0; b < 8; b++) buf[b] = (uint8_t) ((uint64_t) n >> (8 * b));
        for (slong j = 0; j < n; j++) {
            ulong c = (v + i)->coeffs[j];

            for (int b = 0; b < 6; b++) buf[8 + 6 * j + b] = (uint8_t) (c >> (8 * b));
        }
        SHA256Input(sha, buf, 8 + 6 * n);
    }
}

/* h1: the parameters, the statement and the commitment. The projection comes
 * from it, so (s, k) and y_3 are fixed before R. */
static void hash_commitment(uint8_t out[32], const uint8_t pp[32],
                            const evmlr_zk_stmt_struct *st, const evmlr_zk_proof_struct *pi) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-commit", 15);
    SHA256Input(&sha, pp, 32);
    SHA256Input(&sha, st->digest, SHA256HashSize);
    absorb(&sha, pi->tA, ZK_KAPPA);
    absorb(&sha, pi->tB, ZK_SLOTS);
    SHA256Result(&sha, out);
}

/* h2: h1 and the projection. The aggregation scalars come from it, so the
 * masks g_l, committed in h1, are fixed before the scalars applied to them. */
static void hash_projection(uint8_t out[32], const uint8_t h1[32], const slong z3[ZK_PROJ]) {
    SHA256Context sha;
    uint8_t buf[8];

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-proj", 13);
    SHA256Input(&sha, h1, 32);
    for (slong i = 0; i < ZK_PROJ; i++) {
        for (int b = 0; b < 8; b++) buf[b] = (uint8_t) ((uint64_t) z3[i] >> (8 * b));
        SHA256Input(&sha, buf, 8);
    }
    SHA256Result(&sha, out);
}

/* The hash the challenge comes from: everything before it, the published h,
 * and the first messages, which the verifier recomputes rather than receives. */
static void hash_challenge(uint8_t out[32], const uint8_t h2[32], const evmlr_zk_proof_struct *pi,
                           const nmod_poly_struct *w, const nmod_poly_struct *wl) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-challenge", 18);
    SHA256Input(&sha, h2, 32);
    absorb(&sha, pi->h, ZK_LAMBDA);
    absorb(&sha, w, ZK_KAPPA);
    absorb(&sha, wl, ZK_LAMBDA);
    SHA256Result(&sha, out);
}

static void challenge_from(nmod_poly_t c, const uint8_t hash[32]) {
    prg_t prg;

    prg_setseed(&prg, hash);
    evmlr_zk_challenge(c, &prg);
}

/*============================================================================*/
/* The aggregation: everything h_l is made of that the challenge acts on      */
/*============================================================================*/

typedef struct {
    slong m1, rows;
    nmod_poly_struct *alpha; /* ZK_LAMBDA x rows: linear rows */
    nmod_poly_struct *P;     /* ZK_LAMBDA x m1: sigma(sum_i mu_li R_i), per element */
    nmod_poly_struct *M;     /* ZK_LAMBDA: sigma(sum_i mu_li x^i) */
    ulong Z[ZK_LAMBDA];      /* sum_i mu_li z3_i */
} aggr_t;

static void aggr_init(aggr_t *a, const uint8_t h2[32], const slong z3[ZK_PROJ],
                      const uint8_t h1[32], slong m1, slong rows) {
    const nmod_t mod = *evmlr_zk_mod();
    ulong mu[ZK_LAMBDA][ZK_PROJ];
    int8_t *r = flint_malloc(ZK_PROJ * DEGREE_N);
    nmod_poly_t t;

    a->m1 = m1;
    a->rows = rows;
    a->alpha = vec_init(ZK_LAMBDA * rows);
    a->P = vec_init(ZK_LAMBDA * m1);
    a->M = vec_init(ZK_LAMBDA);
    evmlr_zk_init(t);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        for (slong r_ = 0; r_ < rows; r_++) {
            expand(a->alpha + l * rows + r_, h2, DOM_ALPHA, l, r_);
        }
        expand(t, h2, DOM_MU, l, 0);
        a->Z[l] = 0;
        for (slong i = 0; i < ZK_PROJ; i++) {
            mu[l][i] = nmod_poly_get_coeff_ui(t, i);
            nmod_poly_set_coeff_ui(a->M + l, i, mu[l][i]);
            a->Z[l] = nmod_add(a->Z[l], nmod_mul(mu[l][i], from_signed(z3[i]), mod), mod);
        }
        evmlr_zk_sigma(a->M + l, a->M + l);
    }
    _Static_assert(ZK_P < (1UL << 48) && ZK_PROJ <= 256,
                   "ZK_PROJ terms below 2^48 sum inside a signed 64-bit word");
    for (slong j = 0; j < m1; j++) {
        proj_column(r, h1, j);
        for (slong l = 0; l < ZK_LAMBDA; l++) {
            int64_t acc[DEGREE_N] = { 0 };

            for (slong i = 0; i < ZK_PROJ; i++) {
                const int64_t mli = (int64_t) mu[l][i];
                const int8_t *ri = r + i * DEGREE_N;

                for (slong k = 0; k < DEGREE_N; k++) acc[k] += ri[k] * mli;
            }
            nmod_poly_struct *Pl = a->P + l * m1 + j;

            nmod_poly_zero(Pl);
            for (slong k = 0; k < DEGREE_N; k++) {
                int64_t v = acc[k] % (int64_t) ZK_P;

                nmod_poly_set_coeff_ui(Pl, k, (v < 0) ? (ulong) (v + (int64_t) ZK_P) : (ulong) v);
            }
            evmlr_zk_sigma(Pl, Pl);
        }
    }
    nmod_poly_clear(t);
    flint_free(r);
}

static void aggr_clear(aggr_t *a) {
    vec_clear(a->alpha, ZK_LAMBDA * a->rows);
    vec_clear(a->P, ZK_LAMBDA * a->m1);
    vec_clear(a->M, ZK_LAMBDA);
}

/* acc = sum_r sigma(alpha_lr) e_r + sum_j P_lj v_j: the part of h_l (or of
 * its first message) that is linear in (s, k), applied to the residual e and
 * to the vector v that stands for (s, k). */
static void aggr_linear(nmod_poly_t acc, const aggr_t *a, slong l,
                        const nmod_poly_struct *e, const nmod_poly_struct *v) {
    nmod_poly_t t;

    evmlr_zk_init(t);
    nmod_poly_zero(acc);
    for (slong r = 0; r < a->rows; r++) {
        evmlr_zk_sigma(t, a->alpha + l * a->rows + r);
        evmlr_zk_mul(t, t, e + r);
        nmod_poly_add(acc, acc, t);
    }
    for (slong j = 0; j < a->m1; j++) {
        evmlr_zk_mul(t, a->P + l * a->m1 + j, v + j);
        nmod_poly_add(acc, acc, t);
    }
    nmod_poly_clear(t);
}

/*============================================================================*/
/* Widths and bounds                                                          */
/*============================================================================*/

void evmlr_zk_sigmas(double sigma[4], slong m, double k_bound) {
    double t = 2.0 * ZK_NU; // ||c||_1, which bounds ||c v|| / ||v||

    // s is binary, so ||s|| <= sqrt(m n); s_2 is ternary.
    sigma[0] = ZK_ALPHA_RS * t * sqrt((double) m * DEGREE_N);
    sigma[1] = ZK_ALPHA_RS * t * k_bound;
    sigma[2] = ZK_ALPHA_RS * t * sqrt((double) ZK_M2 * DEGREE_N);
    // The projection mask hides R (s, k).
    sigma[3] = ZK_ALPHA_RS * ZK_PROJ_STRETCH
             * sqrt((double) m * DEGREE_N + k_bound * k_bound);
}

/* An honest masked opening of dimension d at width sigma exceeds
 * sigma sqrt(2 d) with probability below (sqrt(2) e^(-1/2))^d, which is
 * 2^-128 from d = 580 on; every block here is at least one element of degree
 * 512 per row, and at least rows * 512 >= 580 in the shuffle. */
static double bound2(double sigma, slong elems) {
    return 2.0 * sigma * sigma * (double) elems * DEGREE_N;
}

static double bound3(double sigma) {
    return ZK_TAIL3 * ZK_TAIL3 * sigma * sigma * ZK_PROJ;
}

double evmlr_zk_certified(slong m, double k_bound) {
    double sigma[4];

    evmlr_zk_sigmas(sigma, m, k_bound);
    return 2.0 * sqrt(bound3(sigma[3]));
}

/*============================================================================*/
/* Prover and verifier                                                        */
/*============================================================================*/

void evmlr_zk_proof_init(evmlr_zk_proof_t pi, slong m, slong rows) {
    pi->m = m;
    pi->rows = rows;
    pi->tA = vec_init(ZK_KAPPA);
    pi->tB = vec_init(ZK_SLOTS);
    pi->h = vec_init(ZK_LAMBDA);
    pi->z1 = vec_init(m + rows);
    pi->z2 = vec_init(ZK_M2);
}

void evmlr_zk_proof_clear(evmlr_zk_proof_t pi) {
    vec_clear(pi->tA, ZK_KAPPA);
    vec_clear(pi->tB, ZK_SLOTS);
    vec_clear(pi->h, ZK_LAMBDA);
    vec_clear(pi->z1, pi->m + pi->rows);
    vec_clear(pi->z2, ZK_M2);
}

#ifdef MAIN
/* Tests only: play a prover that skips every rejection test, as a cheating
 * one would, so that the verifier's own checks are what stop it; and one that
 * adds zk_bump to the first coefficient of its witness, which leaves
 * E s mod q unchanged when zk_bump is a multiple of q but makes s long. */
static int zk_skip_rejection = 0;
static slong zk_bump = 0;
#endif

static void sample_gauss(nmod_poly_struct *v, slong len, discrete_gaussian_ctx_t dg) {
    for (slong i = 0; i < len; i++) {
        nmod_poly_zero(v + i);
        nmod_poly_fit_length(v + i, DEGREE_N);
        for (slong j = 0; j < DEGREE_N; j++) {
            nmod_poly_set_coeff_ui(v + i, j, from_signed(discrete_gaussian(0.0, dg)));
        }
    }
}

static int accept(double e) {
    uint64_t rnd;

#ifdef MAIN
    if (zk_skip_rejection) return 1;
#endif
    fastrandombytes((unsigned char *) &rnd, sizeof(rnd));
    return ((double) (rnd >> 11) / (double) (1ULL << 53)) < exp(e) / ZK_M;
}

/* Accepts the masked opening z = y + v with probability
 * min(1, exp((-2<z, v> + ||v||^2) / (2 sigma^2)) / M). */
static int rejection(const nmod_poly_struct *z, const nmod_poly_struct *v, slong len, double sigma) {
    return accept((-2.0 * vec_dot(z, v, len) + vec_norm2(v, len)) / (2.0 * sigma * sigma));
}

static int rejection3(const slong z[ZK_PROJ], const slong v[ZK_PROJ], double sigma) {
    double dot = 0, n2 = 0;

    for (slong i = 0; i < ZK_PROJ; i++) {
        dot += (double) z[i] * (double) v[i];
        n2 += (double) v[i] * (double) v[i];
    }
    return accept((-2.0 * dot + n2) / (2.0 * sigma * sigma));
}

/* e[r] = E_r v_s - q v_k,r, minus t_r if with_t, for v = (v_s, v_k). */
static void residual(nmod_poly_struct *e, const nmod_poly_struct *v,
                     const evmlr_zk_stmt_struct *st, int with_t) {
    nmod_poly_t tmp;

    evmlr_zk_init(tmp);
    st->apply(e, v, st);
    for (slong r = 0; r < st->rows; r++) {
        nmod_poly_scalar_mul_nmod(tmp, v + st->m + r, MOD_Q);
        nmod_poly_sub(e + r, e + r, tmp);
        if (with_t) {
            evmlr_zk_lift(tmp, st->t + r);
            nmod_poly_sub(e + r, e + r, tmp);
        }
    }
    nmod_poly_clear(tmp);
}

int evmlr_zk_prove(evmlr_zk_proof_t pi, const nmod_poly_struct *s,
                   const evmlr_zk_stmt_struct *st, const uint8_t pp[32]) {
    const slong m = st->m, rows = st->rows, m1 = m + rows;
    nmod_poly_struct *s1 = vec_init(m1), *s2 = vec_init(ZK_M2);
    nmod_poly_struct *y1 = vec_init(m1), *y2 = vec_init(ZK_M2);
    nmod_poly_struct *g = vec_init(ZK_SLOTS), *e = vec_init(rows);
    nmod_poly_struct *w = vec_init(ZK_KAPPA), *wl = vec_init(ZK_LAMBDA);
    nmod_poly_struct *cs1 = vec_init(m1), *cs2 = vec_init(ZK_M2);
    nmod_poly_t c, t, u;
    uint8_t h1[32], h2[32];
    slong y3[ZK_PROJ], rs[ZK_PROJ];
    double sigma[4];
    discrete_gaussian_ctx_t dg[4];
    aggr_t ag;
    int ok = 1, have_aggr = 0;

    evmlr_zk_init(c);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_sigmas(sigma, m, st->k_bound);
    for (int b = 0; b < 4; b++) {
        discrete_gaussian_ctx_init(dg[b], sigma[b]);
    }

    // The witness, lifted, and its carry k = (E s - t) / q over the integers.
    for (slong j = 0; j < m; j++) {
        evmlr_zk_lift(s1 + j, s + j);
    }
#ifdef MAIN
    nmod_poly_set_coeff_ui(s1, 0, nmod_add(nmod_poly_get_coeff_ui(s1, 0),
                                           from_signed(zk_bump), *evmlr_zk_mod()));
#endif
    st->apply(e, s1, st);
    for (slong r = 0; r < rows && ok; r++) {
        evmlr_zk_lift(t, st->t + r);
        nmod_poly_sub(e + r, e + r, t);
        nmod_poly_zero(s1 + m + r);
        for (slong i = 0; i < DEGREE_N; i++) {
            slong v = centre(nmod_poly_get_coeff_ui(e + r, i));

            if (v % MOD_Q != 0) {
                ok = 0; // E s != t (mod q): there is nothing to prove
                break;
            }
            nmod_poly_set_coeff_ui(s1 + m + r, i, from_signed(v / MOD_Q));
        }
    }
    // The widths assume ||k|| <= k_bound; past it the proof would not hide k.
    if (!ok || vec_norm2(s1 + m, rows) > st->k_bound * st->k_bound) {
        ok = 0;
        goto end;
    }

    // Commitment and projection, repeated until the projection's rejection
    // test passes: y_3 is committed, so a rejected one cannot be redrawn alone.
    ok = 0;
    for (int tries = 0; tries < ZK_PROJ_TRIES && !ok; tries++) {
        // s_2 ternary; the masks g_l uniform with ct(g_l) = 0; slot Y holds y_3.
        for (slong j = 0; j < ZK_M2; j++) {
            uint8_t buf[DEGREE_N];

            fastrandombytes(buf, sizeof(buf));
            nmod_poly_zero(s2 + j);
            for (slong i = 0; i < DEGREE_N; i++) {
                nmod_poly_set_coeff_ui(s2 + j, i, from_signed((slong) (buf[i] % 3) - 1));
            }
        }
        for (slong l = 0; l < ZK_LAMBDA; l++) {
            uint8_t seed[32];
            prg_t prg;

            fastrandombytes(seed, sizeof(seed));
            prg_setseed(&prg, seed);
            evmlr_zk_uniform(g + l, &prg);
            nmod_poly_set_coeff_ui(g + l, 0, 0);
        }
        nmod_poly_zero(g + ZK_SLOT_Y);
        for (slong i = 0; i < ZK_PROJ; i++) {
            y3[i] = discrete_gaussian(0.0, dg[3]);
            nmod_poly_set_coeff_ui(g + ZK_SLOT_Y, i, from_signed(y3[i]));
        }
        ajtai(pi->tA, s1, m1, s2, pp);
        for (slong l = 0; l < ZK_SLOTS; l++) {
            bdlop_row(pi->tB + l, l, s2, pp);
            nmod_poly_add(pi->tB + l, pi->tB + l, g + l);
        }
        hash_commitment(h1, pp, st, pi);
        proj_apply(rs, s1, m1, h1);
        for (slong i = 0; i < ZK_PROJ; i++) {
            pi->z3[i] = rs[i] + y3[i];
        }
        ok = rejection3(pi->z3, rs, sigma[3]);
    }
    if (!ok) goto end;

    // h_l = g_l + sum_r sigma(alpha_lr) e_r + sum_j P_lj s1_j + M_l Y - Z_l,
    // whose constant coefficient is zero exactly when e = E s - q k - t is
    // zero and the projection is honest.
    hash_projection(h2, h1, pi->z3);
    aggr_init(&ag, h2, pi->z3, h1, m1, rows);
    have_aggr = 1;
    residual(e, s1, st, 1);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        aggr_linear(t, &ag, l, e, s1);
        nmod_poly_add(pi->h + l, g + l, t);
        evmlr_zk_mul(u, ag.M + l, g + ZK_SLOT_Y);
        nmod_poly_add(pi->h + l, pi->h + l, u);
        nmod_poly_set_coeff_ui(pi->h + l, 0,
                nmod_sub(nmod_poly_get_coeff_ui(pi->h + l, 0), ag.Z[l], *evmlr_zk_mod()));
    }

    for (;;) {
        // Masks, and the first messages: w = A_1 y_1 + A_2 y_2, and
        // w_l = v_gl + M_l v_Y - sum_r sigma(alpha_lr) (E_r y_s - q y_k,r)
        //       - sum_j P_lj y1_j.
        sample_gauss(y1, m, dg[0]);
        sample_gauss(y1 + m, rows, dg[1]);
        sample_gauss(y2, ZK_M2, dg[2]);
        ajtai(w, y1, m1, y2, pp);
        residual(e, y1, st, 0);
        bdlop_row(u, ZK_SLOT_Y, y2, pp);
        for (slong l = 0; l < ZK_LAMBDA; l++) {
            bdlop_row(wl + l, l, y2, pp);
            aggr_linear(t, &ag, l, e, y1);
            nmod_poly_sub(wl + l, wl + l, t);
            evmlr_zk_mul(t, ag.M + l, u);
            nmod_poly_add(wl + l, wl + l, t);
        }
        hash_challenge(pi->hash, h2, pi, w, wl);
        challenge_from(c, pi->hash);

        // z = y + c s, and one rejection test per block.
        for (slong j = 0; j < m1; j++) {
            evmlr_zk_mul(cs1 + j, c, s1 + j);
            nmod_poly_add(pi->z1 + j, y1 + j, cs1 + j);
        }
        for (slong j = 0; j < ZK_M2; j++) {
            evmlr_zk_mul(cs2 + j, c, s2 + j);
            nmod_poly_add(pi->z2 + j, y2 + j, cs2 + j);
        }
        if (rejection(pi->z1, cs1, m, sigma[0])
                && rejection(pi->z1 + m, cs1 + m, rows, sigma[1])
                && rejection(pi->z2, cs2, ZK_M2, sigma[2])) {
            break;
        }
    }

end:
    for (int b = 0; b < 4; b++) {
        discrete_gaussian_ctx_clear(dg[b]);
    }
    if (have_aggr) {
        aggr_clear(&ag);
    }
    vec_clear(s1, m1);
    vec_clear(s2, ZK_M2);
    vec_clear(y1, m1);
    vec_clear(y2, ZK_M2);
    vec_clear(g, ZK_SLOTS);
    vec_clear(e, rows);
    vec_clear(w, ZK_KAPPA);
    vec_clear(wl, ZK_LAMBDA);
    vec_clear(cs1, m1);
    vec_clear(cs2, ZK_M2);
    nmod_poly_clear(c);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
    return ok;
}

int evmlr_zk_verify(const evmlr_zk_proof_t pi, const evmlr_zk_stmt_struct *st,
                    const uint8_t pp[32]) {
    const slong m = st->m, rows = st->rows, m1 = m + rows;
    nmod_poly_struct *w, *wl, *e;
    nmod_poly_t c, t, u, uY;
    uint8_t h1[32], h2[32], h3[32];
    double sigma[4], n3 = 0;
    aggr_t ag;
    int ok;

    if (pi->m != m || pi->rows != rows) {
        return 0;
    }
    w = vec_init(ZK_KAPPA);
    wl = vec_init(ZK_LAMBDA);
    e = vec_init(rows);
    evmlr_zk_init(c);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_init(uY);
    evmlr_zk_sigmas(sigma, m, st->k_bound);

    // Norms of the masked openings, block by block, and of the projection.
    ok = vec_norm2(pi->z1, m) <= bound2(sigma[0], m);
    ok &= vec_norm2(pi->z1 + m, rows) <= bound2(sigma[1], rows);
    ok &= vec_norm2(pi->z2, ZK_M2) <= bound2(sigma[2], ZK_M2);
    for (slong i = 0; i < ZK_PROJ; i++) {
        n3 += (double) pi->z3[i] * (double) pi->z3[i];
    }
    ok &= n3 <= bound3(sigma[3]);

    // The aggregated values have zero constant coefficients.
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        ok &= (evmlr_zk_ct(pi->h + l) == 0);
    }

    // First messages, recomputed from the openings, with
    // u_X = <b_X, z_2> - c t_B,X for each slot X:
    //   w   = A_1 z_1 + A_2 z_2 - c t_A,
    //   w_l = c h_l + u_gl + M_l u_Y + c Z_l
    //         - sum_r sigma(alpha_lr) (E_r z_s - q z_k,r - c t_r)
    //         - sum_j P_lj z1_j.
    challenge_from(c, pi->hash);
    hash_commitment(h1, pp, st, pi);
    hash_projection(h2, h1, pi->z3);
    aggr_init(&ag, h2, pi->z3, h1, m1, rows);
    ajtai(w, pi->z1, m1, pi->z2, pp);
    for (slong i = 0; i < ZK_KAPPA; i++) {
        evmlr_zk_mul(t, c, pi->tA + i);
        nmod_poly_sub(w + i, w + i, t);
    }
    residual(e, pi->z1, st, 0);
    for (slong r = 0; r < rows; r++) {
        evmlr_zk_lift(t, st->t + r);
        evmlr_zk_mul(t, t, c);
        nmod_poly_sub(e + r, e + r, t);
    }
    bdlop_row(uY, ZK_SLOT_Y, pi->z2, pp);
    evmlr_zk_mul(t, c, pi->tB + ZK_SLOT_Y);
    nmod_poly_sub(uY, uY, t);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        bdlop_row(u, l, pi->z2, pp);
        evmlr_zk_mul(t, c, pi->tB + l);
        nmod_poly_sub(u, u, t);
        evmlr_zk_mul(wl + l, c, pi->h + l);
        nmod_poly_add(wl + l, wl + l, u);
        evmlr_zk_mul(t, ag.M + l, uY);
        nmod_poly_add(wl + l, wl + l, t);
        nmod_poly_scalar_mul_nmod(t, c, ag.Z[l]);
        nmod_poly_add(wl + l, wl + l, t);
        aggr_linear(t, &ag, l, e, pi->z1);
        nmod_poly_sub(wl + l, wl + l, t);
    }
    hash_challenge(h3, h2, pi, w, wl);
    ok &= (memcmp(h3, pi->hash, sizeof(h3)) == 0);

    aggr_clear(&ag);
    vec_clear(w, ZK_KAPPA);
    vec_clear(wl, ZK_LAMBDA);
    vec_clear(e, rows);
    nmod_poly_clear(c);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
    nmod_poly_clear(uY);
    return ok;
}

#ifdef MAIN
#include "evmlr_main.h"

/* A dense statement over R_q, for the tests. */
typedef struct {
    nmod_poly_struct *E; // rows x m, mod q
} dense_t;

static void dense_apply(nmod_poly_struct *out, const nmod_poly_struct *v,
                        const evmlr_zk_stmt_struct *st) {
    const dense_t *d = (const dense_t *) st->data;
    nmod_poly_t a, t;

    evmlr_zk_init(a);
    evmlr_zk_init(t);
    for (slong r = 0; r < st->rows; r++) {
        nmod_poly_zero(out + r);
        for (slong j = 0; j < st->m; j++) {
            evmlr_zk_lift(a, d->E + r * st->m + j);
            evmlr_zk_mul(t, a, v + j);
            nmod_poly_add(out + r, out + r, t);
        }
    }
    nmod_poly_clear(a);
    nmod_poly_clear(t);
}

/* A random E over R_q, a binary s, and t = E s mod q. */
static void dense_setup(evmlr_zk_stmt_struct *st, dense_t *d, nmod_poly_struct **s,
                        slong rows, slong m, flint_rand_t state) {
    nmod_poly_t tmp;
    SHA256Context sha;

    d->E = flint_malloc(rows * m * sizeof(nmod_poly_struct));
    *s = flint_malloc(m * sizeof(nmod_poly_struct));
    st->t = flint_malloc(rows * sizeof(nmod_poly_struct));
    nmod_poly_init(tmp, MOD_Q);
    for (slong j = 0; j < m; j++) {
        nmod_poly_init(*s + j, MOD_Q);
        for (slong i = 0; i < DEGREE_N; i++) {
            nmod_poly_set_coeff_ui(*s + j, i, n_randint(state, 2));
        }
    }
    for (slong r = 0; r < rows; r++) {
        nmod_poly_init(st->t + r, MOD_Q);
        for (slong j = 0; j < m; j++) {
            nmod_poly_init(d->E + r * m + j, MOD_Q);
            for (slong i = 0; i < DEGREE_N; i++) {
                nmod_poly_set_coeff_ui(d->E + r * m + j, i, n_randint(state, MOD_Q));
            }
            nmod_poly_mul(tmp, d->E + r * m + j, *s + j);
            for (slong i = nmod_poly_length(tmp) - 1; i >= DEGREE_N; i--) {
                ulong hi = nmod_poly_get_coeff_ui(tmp, i);
                ulong lo = nmod_poly_get_coeff_ui(tmp, i - DEGREE_N);

                nmod_poly_set_coeff_ui(tmp, i - DEGREE_N, nmod_sub(lo, hi, tmp->mod));
                nmod_poly_set_coeff_ui(tmp, i, 0);
            }
            nmod_poly_add(st->t + r, st->t + r, tmp);
        }
    }
    nmod_poly_clear(tmp);

    st->m = m;
    st->rows = rows;
    // E has entries below q/2 in absolute value and s is binary, so each
    // coefficient of E s - t is below (m n + 1) q / 2: k is below (m n + 1) / 2.
    st->k_bound = sqrt((double) rows * DEGREE_N) * ((double) m * DEGREE_N + 1) / 2;
    st->apply = dense_apply;
    st->data = d;
    SHA256Reset(&sha);
    for (slong r = 0; r < rows; r++) {
        SHA256Input(&sha, (const uint8_t *) (st->t + r)->coeffs,
                    nmod_poly_length(st->t + r) * sizeof(ulong));
    }
    SHA256Result(&sha, st->digest);
}

static void dense_clear(evmlr_zk_stmt_struct *st, dense_t *d, nmod_poly_struct *s) {
    for (slong i = 0; i < st->rows * st->m; i++) nmod_poly_clear(d->E + i);
    for (slong j = 0; j < st->m; j++) nmod_poly_clear(s + j);
    for (slong r = 0; r < st->rows; r++) nmod_poly_clear(st->t + r);
    flint_free(d->E);
    flint_free(s);
    flint_free(st->t);
}

void test(flint_rand_t state) {
    evmlr_zk_stmt_struct st;
    dense_t d;
    nmod_poly_struct *s;
    evmlr_zk_proof_t pi;
    uint8_t pp[32] = { 3 };

    dense_setup(&st, &d, &s, 3, 4, state);
    evmlr_zk_proof_init(pi, st.m, st.rows);

    TEST_BEGIN("a proof of a true linear statement mod q verifies") {
        TEST_ASSERT(evmlr_zk_prove(pi, s, &st, pp) == 1, end);
        TEST_ASSERT(evmlr_zk_verify(pi, &st, pp) == 1, end);
    } TEST_END;

    TEST_BEGIN("the prover refuses a false statement") {
        nmod_poly_set_coeff_ui(st.t + 0, 0, nmod_add(nmod_poly_get_coeff_ui(st.t + 0, 0), 1, (st.t + 0)->mod));
        int proved = evmlr_zk_prove(pi, s, &st, pp);
        nmod_poly_set_coeff_ui(st.t + 0, 0, nmod_sub(nmod_poly_get_coeff_ui(st.t + 0, 0), 1, (st.t + 0)->mod));
        TEST_ASSERT(proved == 0, end);
    } TEST_END;

    TEST_BEGIN("a proof does not verify against another right-hand side") {
        TEST_ASSERT(evmlr_zk_prove(pi, s, &st, pp) == 1, end);
        nmod_poly_set_coeff_ui(st.t + 1, 5, nmod_add(nmod_poly_get_coeff_ui(st.t + 1, 5), 1, (st.t + 1)->mod));
        int verified = evmlr_zk_verify(pi, &st, pp);
        nmod_poly_set_coeff_ui(st.t + 1, 5, nmod_sub(nmod_poly_get_coeff_ui(st.t + 1, 5), 1, (st.t + 1)->mod));
        TEST_ASSERT(verified == 0, end);
    } TEST_END;

    TEST_BEGIN("a proof with an altered opening or h does not verify") {
        TEST_ASSERT(evmlr_zk_prove(pi, s, &st, pp) == 1, end);
        ulong v = nmod_poly_get_coeff_ui(pi->z1 + 0, 7);
        nmod_poly_set_coeff_ui(pi->z1 + 0, 7, nmod_add(v, 1, *evmlr_zk_mod()));
        int verified = evmlr_zk_verify(pi, &st, pp);
        nmod_poly_set_coeff_ui(pi->z1 + 0, 7, v);
        TEST_ASSERT(verified == 0, end);
        // h with its constant coefficient intact, changed elsewhere.
        v = nmod_poly_get_coeff_ui(pi->h + 0, 3);
        nmod_poly_set_coeff_ui(pi->h + 0, 3, nmod_add(v, 1, *evmlr_zk_mod()));
        verified = evmlr_zk_verify(pi, &st, pp);
        nmod_poly_set_coeff_ui(pi->h + 0, 3, v);
        TEST_ASSERT(verified == 0, end);
        TEST_ASSERT(evmlr_zk_verify(pi, &st, pp) == 1, end);
    } TEST_END;

    TEST_BEGIN("a proof with an altered projection does not verify") {
        TEST_ASSERT(evmlr_zk_prove(pi, s, &st, pp) == 1, end);
        pi->z3[0] += 1;
        int verified = evmlr_zk_verify(pi, &st, pp);
        pi->z3[0] -= 1;
        TEST_ASSERT(verified == 0, end);
    } TEST_END;

    /* s + q X e_0 satisfies the same statement mod q but is long. An honest
     * prover refuses it, since its carry exceeds the bound the widths assume;
     * one that proves anyway, skipping every rejection test, is caught by the
     * verifier's bounds. */
    TEST_BEGIN("a long witness for a true statement mod q is refused or rejected") {
        zk_bump = (slong) MOD_Q << 20;
        int proved = evmlr_zk_prove(pi, s, &st, pp);
        zk_skip_rejection = 1;
        double kb = st.k_bound;
        st.k_bound = 1e30; // let the prover past its own refusal
        int forced = evmlr_zk_prove(pi, s, &st, pp);
        st.k_bound = kb;
        int verified = evmlr_zk_verify(pi, &st, pp);
        zk_skip_rejection = 0;
        zk_bump = 0;
        TEST_ASSERT(proved == 0 && forced == 1 && verified == 0, end);
    } TEST_END;

    TEST_BEGIN("the certified bound leaves the lifting no room to wrap") {
        // |E_r s - q k_r - t_r| <= (q/2) sqrt(m n) B + q B + q/2 < p/2, with
        // B the certified bound on ||(s, k)||: then E s - q k = t holds over
        // the integers, not just mod p.
        double B = evmlr_zk_certified(st.m, st.k_bound);
        double wrap = (MOD_Q / 2.0) * sqrt((double) st.m * DEGREE_N) * B + MOD_Q * B + MOD_Q;
        TEST_ASSERT(wrap < ZK_P / 2.0, end);
    } TEST_END;

end:
    evmlr_zk_proof_clear(pi);
    dense_clear(&st, &d, s);
}

void bench(flint_rand_t state) {
    evmlr_zk_stmt_struct st;
    dense_t d;
    nmod_poly_struct *s;
    evmlr_zk_proof_t pi;
    uint8_t pp[32] = { 4 };

    dense_setup(&st, &d, &s, 3, 16, state);
    evmlr_zk_proof_init(pi, st.m, st.rows);
    BENCH_ONCE("evmlr_zk_prove (3 x 16)", evmlr_zk_prove(pi, s, &st, pp));
    BENCH_ONCE("evmlr_zk_verify (3 x 16)", evmlr_zk_verify(pi, &st, pp));
    evmlr_zk_proof_clear(pi);
    dense_clear(&st, &d, s);
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
