#include "evmlr_zk_proof.h"
#include "gaussian.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>

#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif

/* Domains of the public matrices expanded from the parameter seed. */
enum { DOM_A1 = 1, DOM_A2 = 2, DOM_B = 3, DOM_ALPHA = 4 };

/* Rejection sampling keeps its 2^-100 statistical distance at M = 1.75 once
 * the width is 21.485 times the norm of the shift it masks. */
#define ZK_M 1.75
#define ZK_ALPHA_RS 21.485

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
/* Public parameters, expanded an element at a time                           */
/*============================================================================*/

static void expand(nmod_poly_t r, const uint8_t pp[32], uint32_t dom, slong i, slong j) {
    prg_t prg;

    evmlr_zk_prg_for(&prg, pp, dom, (uint64_t) i, (uint64_t) j);
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

/* The hash that the aggregation scalars come from: the parameters, the
 * statement and the commitment. */
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

/* The hash the challenge comes from: everything before it, the published h,
 * and the first messages, which the verifier recomputes rather than receives. */
static void hash_challenge(uint8_t out[32], const uint8_t h1[32], const evmlr_zk_proof_struct *pi,
                           const nmod_poly_struct *w, const nmod_poly_struct *wl) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-challenge", 18);
    SHA256Input(&sha, h1, 32);
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

/* alpha[l * rows + r]: the scalars, as ring elements, that aggregate row r of
 * the linear claim into h_l. */
static nmod_poly_struct *aggregation(const uint8_t h1[32], slong rows) {
    nmod_poly_struct *alpha = vec_init(ZK_LAMBDA * rows);

    for (slong l = 0; l < ZK_LAMBDA; l++) {
        for (slong r = 0; r < rows; r++) {
            expand(alpha + l * rows + r, h1, DOM_ALPHA, l, r);
        }
    }
    return alpha;
}

/*============================================================================*/
/* Widths and bounds                                                          */
/*============================================================================*/

void evmlr_zk_sigmas(double sigma[3], slong m, double k_bound) {
    double t = 2.0 * ZK_NU; // ||c||_1, which bounds ||c v|| / ||v||

    // s is binary, so ||s|| <= sqrt(m n); s_2 is ternary.
    sigma[0] = ZK_ALPHA_RS * t * sqrt((double) m * DEGREE_N);
    sigma[1] = ZK_ALPHA_RS * t * k_bound;
    sigma[2] = ZK_ALPHA_RS * t * sqrt((double) ZK_M2 * DEGREE_N);
}

/* An honest masked opening of dimension d at width sigma exceeds
 * sigma sqrt(2 d) with probability below (sqrt(2) e^(-1/2))^d, which is
 * 2^-128 from d = 580 on; every block here is at least n = 512 elements of
 * degree 512. */
static double bound2(double sigma, slong elems) {
    return 2.0 * sigma * sigma * (double) elems * DEGREE_N;
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

static void sample_gauss(nmod_poly_struct *v, slong len, discrete_gaussian_ctx_t dg) {
    for (slong i = 0; i < len; i++) {
        nmod_poly_zero(v + i);
        nmod_poly_fit_length(v + i, DEGREE_N);
        for (slong j = 0; j < DEGREE_N; j++) {
            nmod_poly_set_coeff_ui(v + i, j, from_signed(discrete_gaussian(0.0, dg)));
        }
    }
}

/* Accepts the masked opening z = y + v with probability
 * min(1, exp((-2<z, v> + ||v||^2) / (2 sigma^2)) / M). */
static int rejection(const nmod_poly_struct *z, const nmod_poly_struct *v, slong len, double sigma) {
    double e = (-2.0 * vec_dot(z, v, len) + vec_norm2(v, len)) / (2.0 * sigma * sigma);
    uint64_t rnd;

    fastrandombytes((unsigned char *) &rnd, sizeof(rnd));
    return ((double) (rnd >> 11) / (double) (1ULL << 53)) < exp(e) / ZK_M;
}

/* e[r] = E_r s1 - q k_r - t_r in R_p, for s1 = (s, k). */
static void residual(nmod_poly_struct *e, const nmod_poly_struct *s1,
                     const evmlr_zk_stmt_struct *st, int with_t) {
    nmod_poly_t tmp;

    evmlr_zk_init(tmp);
    st->apply(e, s1, st);
    for (slong r = 0; r < st->rows; r++) {
        nmod_poly_scalar_mul_nmod(tmp, s1 + st->m + r, MOD_Q);
        nmod_poly_sub(e + r, e + r, tmp);
        if (with_t) {
            evmlr_zk_lift(tmp, st->t + r);
            nmod_poly_sub(e + r, e + r, tmp);
        }
    }
    nmod_poly_clear(tmp);
}

/* acc = sum_r sigma(alpha_lr) e_r. */
static void aggregate(nmod_poly_t acc, const nmod_poly_struct *alpha, slong l,
                      const nmod_poly_struct *e, slong rows) {
    nmod_poly_t t;

    evmlr_zk_init(t);
    nmod_poly_zero(acc);
    for (slong r = 0; r < rows; r++) {
        evmlr_zk_sigma(t, alpha + l * rows + r);
        evmlr_zk_mul(t, t, e + r);
        nmod_poly_add(acc, acc, t);
    }
    nmod_poly_clear(t);
}

int evmlr_zk_prove(evmlr_zk_proof_t pi, const nmod_poly_struct *s,
                   const evmlr_zk_stmt_struct *st, const uint8_t pp[32]) {
    const slong m = st->m, rows = st->rows, m1 = m + rows;
    nmod_poly_struct *s1 = vec_init(m1), *s2 = vec_init(ZK_M2);
    nmod_poly_struct *y1 = vec_init(m1), *y2 = vec_init(ZK_M2);
    nmod_poly_struct *g = vec_init(ZK_LAMBDA), *e = vec_init(rows);
    nmod_poly_struct *w = vec_init(ZK_KAPPA), *wl = vec_init(ZK_LAMBDA);
    nmod_poly_struct *cs1 = vec_init(m1), *cs2 = vec_init(ZK_M2);
    nmod_poly_struct *alpha = NULL;
    nmod_poly_t c, t, u;
    uint8_t h1[32];
    double sigma[3];
    discrete_gaussian_ctx_t dg[3];
    int ok = 1;

    evmlr_zk_init(c);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_sigmas(sigma, m, st->k_bound);
    for (int b = 0; b < 3; b++) {
        discrete_gaussian_ctx_init(dg[b], sigma[b]);
    }

    // The witness, lifted, and its carry k = (E s - t) / q over the integers.
    for (slong j = 0; j < m; j++) {
        evmlr_zk_lift(s1 + j, s + j);
    }
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
    if (!ok || vec_norm2(s1 + m, rows) > st->k_bound * st->k_bound) {
        ok = 0;
        goto end;
    }

    // Commitment: s_2 ternary; the masks g_l uniform with ct(g_l) = 0.
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
    ajtai(pi->tA, s1, m1, s2, pp);
    for (slong l = 0; l < ZK_SLOTS; l++) {
        bdlop_row(pi->tB + l, l, s2, pp);
        nmod_poly_add(pi->tB + l, pi->tB + l, g + l);
    }

    // h_l = g_l + sum_r sigma(alpha_lr) e_r, with e = E s - q k - t = 0.
    hash_commitment(h1, pp, st, pi);
    alpha = aggregation(h1, rows);
    residual(e, s1, st, 1);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        aggregate(t, alpha, l, e, rows);
        nmod_poly_add(pi->h + l, g + l, t);
    }

    for (;;) {
        // Masks, and the first messages: w = A_1 y_1 + A_2 y_2, and
        // w_l = v_gl - sum_r sigma(alpha_lr) (E_r y_s - q y_k,r).
        sample_gauss(y1, m, dg[0]);
        sample_gauss(y1 + m, rows, dg[1]);
        sample_gauss(y2, ZK_M2, dg[2]);
        ajtai(w, y1, m1, y2, pp);
        residual(e, y1, st, 0);
        for (slong l = 0; l < ZK_LAMBDA; l++) {
            bdlop_row(wl + l, l, y2, pp);
            aggregate(t, alpha, l, e, rows);
            nmod_poly_sub(wl + l, wl + l, t);
        }
        hash_challenge(pi->hash, h1, pi, w, wl);
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
    for (int b = 0; b < 3; b++) {
        discrete_gaussian_ctx_clear(dg[b]);
    }
    if (alpha != NULL) {
        vec_clear(alpha, ZK_LAMBDA * rows);
    }
    vec_clear(s1, m1);
    vec_clear(s2, ZK_M2);
    vec_clear(y1, m1);
    vec_clear(y2, ZK_M2);
    vec_clear(g, ZK_LAMBDA);
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
    nmod_poly_struct *w = vec_init(ZK_KAPPA), *wl = vec_init(ZK_LAMBDA);
    nmod_poly_struct *e = vec_init(rows), *alpha;
    nmod_poly_t c, t, u;
    uint8_t h1[32], h3[32];
    double sigma[3];
    int ok = (pi->m == m && pi->rows == rows);

    if (!ok) {
        vec_clear(w, ZK_KAPPA);
        vec_clear(wl, ZK_LAMBDA);
        vec_clear(e, rows);
        return 0;
    }
    evmlr_zk_init(c);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_sigmas(sigma, m, st->k_bound);

    // Norms of the masked openings, block by block.
    ok &= vec_norm2(pi->z1, m) <= bound2(sigma[0], m);
    ok &= vec_norm2(pi->z1 + m, rows) <= bound2(sigma[1], rows);
    ok &= vec_norm2(pi->z2, ZK_M2) <= bound2(sigma[2], ZK_M2);

    // The aggregated values have zero constant coefficients.
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        ok &= (evmlr_zk_ct(pi->h + l) == 0);
    }

    // First messages, recomputed from the openings:
    //   w   = A_1 z_1 + A_2 z_2 - c t_A,
    //   w_l = c h_l + u_gl - sum_r sigma(alpha_lr) (E_r z_s - q z_k,r - c t_r),
    // with u_gl = <b_l, z_2> - c t_B,l.
    challenge_from(c, pi->hash);
    hash_commitment(h1, pp, st, pi);
    alpha = aggregation(h1, rows);
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
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        bdlop_row(u, l, pi->z2, pp);
        evmlr_zk_mul(t, c, pi->tB + l);
        nmod_poly_sub(u, u, t);
        evmlr_zk_mul(wl + l, c, pi->h + l);
        nmod_poly_add(wl + l, wl + l, u);
        aggregate(t, alpha, l, e, rows);
        nmod_poly_sub(wl + l, wl + l, t);
    }
    hash_challenge(h3, h1, pi, w, wl);
    ok &= (memcmp(h3, pi->hash, sizeof(h3)) == 0);

    vec_clear(alpha, ZK_LAMBDA * rows);
    vec_clear(w, ZK_KAPPA);
    vec_clear(wl, ZK_LAMBDA);
    vec_clear(e, rows);
    nmod_poly_clear(c);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
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
