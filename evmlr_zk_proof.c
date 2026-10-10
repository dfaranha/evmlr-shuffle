#include "evmlr_zk_proof.h"
#include "gaussian.h"
#include <math.h>
#include <stdio.h>
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
/* The projection mask is 9 times that wide. Rejection sampling then repeats
 * exp(12 / 9 + 1 / 162) = 3.8 times on average, against 1.75 at the openings'
 * ratio of 21.485, but certifies a bound 2.4 times tighter, and the binary
 * claim needs the bound on s below sqrt(p / 2). */
#define ZK_ALPHA_PROJ 9.0
#define ZK_M_PROJ 3.81
/* A Gaussian vector of dimension d exceeds t sigma sqrt(d) with probability
 * below (t e^((1 - t^2) / 2))^d; t = 1.7 makes that 2^-153 at d = ZK_PROJ. */
#define ZK_TAIL3 1.7
/* Tries at the projections before an honest prover would have succeeded
 * except with probability below 2^-128: both are accepted together with
 * probability 1 / ZK_M_PROJ^2 = 1/14.5, and (1 - 1/14.5)^1300 < 2^-128. A
 * witness that fails them all is too long. */
#define ZK_PROJ_TRIES 1300

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

/* out = (R_s v_s, R_k v_k) over the integers, for v = (v_s, v_k) with v_s the
 * first m elements: element j feeds rows 0..ZK_PROJ-1 if j < m, and rows
 * ZK_PROJ..2 ZK_PROJ-1 otherwise. */
static void proj_apply(slong out[2 * ZK_PROJ], const nmod_poly_struct *v, slong m, slong m1,
                       const uint8_t seed[32]) {
    int8_t *r = flint_malloc(ZK_PROJ * DEGREE_N);
    slong c[DEGREE_N];

    for (slong i = 0; i < 2 * ZK_PROJ; i++) out[i] = 0;
    for (slong j = 0; j < m1; j++) {
        slong *o = out + ((j < m) ? 0 : ZK_PROJ);

        proj_column(r, seed, j);
        for (slong k = 0; k < DEGREE_N; k++) {
            c[k] = centre(nmod_poly_get_coeff_ui(v + j, k));
        }
        for (slong i = 0; i < ZK_PROJ; i++) {
            slong acc = 0;

            for (slong k = 0; k < DEGREE_N; k++) acc += r[i * DEGREE_N + k] * c[k];
            o[i] += acc;
        }
    }
    flint_free(r);
}

/*============================================================================*/
/* Fiat-Shamir                                                                */
/*============================================================================*/

/* Absorbs v[0..len) injectively: the count, then each element's length and
 * coefficients in seven little-endian bytes, which hold any residue mod p. */
static void absorb(SHA256Context *sha, const nmod_poly_struct *v, slong len) {
    _Static_assert(ZK_P < (1UL << 56), "coefficients are absorbed in seven bytes");
    uint8_t buf[7 * DEGREE_N + 8];

    for (int b = 0; b < 8; b++) buf[b] = (uint8_t) ((uint64_t) len >> (8 * b));
    SHA256Input(sha, buf, 8);
    for (slong i = 0; i < len; i++) {
        slong n = nmod_poly_length(v + i);

        for (int b = 0; b < 8; b++) buf[b] = (uint8_t) ((uint64_t) n >> (8 * b));
        for (slong j = 0; j < n; j++) {
            ulong c = (v + i)->coeffs[j];

            for (int b = 0; b < 7; b++) buf[8 + 7 * j + b] = (uint8_t) (c >> (8 * b));
        }
        SHA256Input(sha, buf, 8 + 7 * n);
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
static void hash_projection(uint8_t out[32], const uint8_t h1[32], const slong z3[2 * ZK_PROJ]) {
    SHA256Context sha;
    uint8_t buf[8];

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-proj", 13);
    SHA256Input(&sha, h1, 32);
    for (slong i = 0; i < 2 * ZK_PROJ; i++) {
        for (int b = 0; b < 8; b++) buf[b] = (uint8_t) ((uint64_t) z3[i] >> (8 * b));
        SHA256Input(&sha, buf, 8);
    }
    SHA256Result(&sha, out);
}

/* The hash the challenge comes from: everything before it, the published h,
 * and the first messages, which the verifier recomputes rather than receives. */
static void hash_challenge(uint8_t out[32], const uint8_t h2[32], const evmlr_zk_proof_struct *pi,
                           const nmod_poly_struct *w, const nmod_poly_struct *wl,
                           const nmod_poly_t tau) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-challenge", 18);
    SHA256Input(&sha, h2, 32);
    absorb(&sha, pi->h, ZK_LAMBDA);
    absorb(&sha, pi->tG, 1);
    absorb(&sha, w, ZK_KAPPA);
    absorb(&sha, wl, ZK_LAMBDA);
    absorb(&sha, tau, 1);
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
    ulong nu[ZK_LAMBDA];     /* the scalars applied to F */
} aggr_t;

static void aggr_init(aggr_t *a, const uint8_t h2[32], const slong z3[2 * ZK_PROJ],
                      const uint8_t h1[32], slong m, slong m1, slong rows) {
    const nmod_t mod = *evmlr_zk_mod();
    ulong mu[ZK_LAMBDA][2 * ZK_PROJ];
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
        expand(t, h2, DOM_MU, l, 1);
        a->nu[l] = nmod_poly_get_coeff_ui(t, 0);
        expand(t, h2, DOM_MU, l, 0);
        a->Z[l] = 0;
        _Static_assert(2 * ZK_PROJ <= DEGREE_N, "the mu of both projections come from one element");
        for (slong i = 0; i < 2 * ZK_PROJ; i++) {
            mu[l][i] = nmod_poly_get_coeff_ui(t, i);
            nmod_poly_set_coeff_ui(a->M + l, i, mu[l][i]);
            a->Z[l] = nmod_add(a->Z[l], nmod_mul(mu[l][i], from_signed(z3[i]), mod), mod);
        }
        evmlr_zk_sigma(a->M + l, a->M + l);
    }
    _Static_assert(ZK_P < (1UL << 55) && ZK_PROJ <= 256,
                   "ZK_PROJ terms below 2^55 sum inside a signed 64-bit word");
    for (slong j = 0; j < m1; j++) {
        proj_column(r, h1, j);
        for (slong l = 0; l < ZK_LAMBDA; l++) {
            int64_t acc[DEGREE_N] = { 0 };

            const ulong *mul = mu[l] + ((j < m) ? 0 : ZK_PROJ);

            for (slong i = 0; i < ZK_PROJ; i++) {
                const int64_t mli = (int64_t) mul[i];
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

void evmlr_zk_sigmas(double sigma[5], slong m, double k_bound) {
    double t = 2.0 * ZK_NU; // ||c||_1, which bounds ||c v|| / ||v||
    double s_bound = sqrt((double) m * DEGREE_N); // s is binary

    sigma[0] = ZK_ALPHA_RS * t * s_bound;
    sigma[1] = ZK_ALPHA_RS * t * k_bound;
    sigma[2] = ZK_ALPHA_RS * t * sqrt((double) ZK_M2 * DEGREE_N); // s_2 is ternary
    // The projection masks hide R_s s and R_k k.
    sigma[3] = ZK_ALPHA_PROJ * ZK_PROJ_STRETCH * s_bound;
    sigma[4] = ZK_ALPHA_PROJ * ZK_PROJ_STRETCH * k_bound;
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

void evmlr_zk_certified(double bound[2], slong m, double k_bound) {
    double sigma[5];

    evmlr_zk_sigmas(sigma, m, k_bound);
    bound[0] = 2.0 * sqrt(bound3(sigma[3]));
    bound[1] = 2.0 * sqrt(bound3(sigma[4]));
}

double evmlr_zk_msis_bound(slong m, slong rows, double k_bound) {
    double sigma[5];

    evmlr_zk_sigmas(sigma, m, k_bound);
    // Two relaxed openings (z, d) and (z2, d2) of one commitment, with d and
    // d2 differences of challenges, give the MSIS solution d2 z - d z2, of norm
    // at most 2 ||d||_1 ||z|| <= 2 (4 ZK_NU) (2 B_z), with B_z the verifier's
    // bound on the openings it accepts.
    double bz = sqrt(bound2(sigma[0], m) + bound2(sigma[1], rows) + bound2(sigma[2], ZK_M2));
    return 2.0 * (4.0 * ZK_NU) * 2.0 * bz;
}

int evmlr_zk_supported(slong m, slong rows, double k_bound) {
    double B[2], mn = (double) m * DEGREE_N;

    evmlr_zk_certified(B, m, k_bound);
    // Linear: |E_r s - q k_r - t_r| <= (q/2) sqrt(m n) B_s + q B_k + q/2,
    // since every entry of E lifts to at most q/2 in absolute value.
    double lin = (MOD_Q / 2.0) * sqrt(mn) * B[0] + MOD_Q * B[1] + MOD_Q;
    // Binary: |sum_i s_i (s_i - 1)| <= B_s^2 + sqrt(m n) B_s.
    double bin = B[0] * B[0] + sqrt(mn) * B[0];
    return lin < ZK_P / 2.0 && bin < (double) ZK_P
        && evmlr_zk_msis_bound(m, rows, k_bound) <= ZK_BETA_MAX;
}

/*============================================================================*/
/* Prover and verifier                                                        */
/*============================================================================*/

void evmlr_zk_proof_init(evmlr_zk_proof_t pi, slong m, slong rows) {
    pi->m = m;
    pi->rows = rows;
    pi->tA = vec_init(ZK_KAPPA);
    pi->tB = vec_init(ZK_SLOTS);
    evmlr_zk_init(pi->tG);
    pi->h = vec_init(ZK_LAMBDA);
    pi->z1 = vec_init(m + rows);
    pi->z2 = vec_init(ZK_M2);
}

void evmlr_zk_proof_clear(evmlr_zk_proof_t pi) {
    vec_clear(pi->tA, ZK_KAPPA);
    vec_clear(pi->tB, ZK_SLOTS);
    nmod_poly_clear(pi->tG);
    vec_clear(pi->h, ZK_LAMBDA);
    vec_clear(pi->z1, pi->m + pi->rows);
    vec_clear(pi->z2, ZK_M2);
}

#ifdef MAIN
/* Tests only. zk_skip_rejection plays a prover that skips every rejection
 * test, as a cheating one would, so that the verifier's own checks are what
 * stop it. zk_bump adds to the first coefficient of the witness, which leaves
 * E s mod q unchanged when it is a multiple of q but makes s long, or makes
 * it non-binary. zk_fake_f commits F with its constant coefficient zeroed, as
 * a prover hiding a non-binary witness would. zk_failure records which check
 * the verifier failed first. */
static int zk_skip_rejection = 0;
static slong zk_bump = 0;
static int zk_fake_f = 0;
enum { FAIL_NONE, FAIL_NORM, FAIL_CT, FAIL_HASH };
static int zk_failure = FAIL_NONE;
#endif

/*
 * Gaussian sampling at the widths ZK⋆ needs.
 *
 * gaussian.cpp's sampler compares its acceptance probability with a random
 * value in comp(), which shifts by a negative amount once that probability is
 * below 2^-20. With center 0 the probability is about 1 / (sigma sqrt(2 pi)),
 * so past sigma = 2^20 / sqrt(2 pi) = 418000 the comparison goes wrong, and
 * the sample comes out 0 most of the time: 84 per cent of the time at
 * sigma = 10^6. A mask that is 0 makes z = c s, which reveals s.
 *
 * Below ZK_GAUSS_BASE it is used as it is. Above, a continuous Gaussian is
 * rounded to the nearest integer: the probability of each integer then
 * differs from the discrete Gaussian's by a factor 1 + O(1 / (24 sigma^2)),
 * below 10^-11 at these widths, which the rejection sampling's analysis
 * absorbs. The normal deviates come from the Box-Muller transform on 53-bit
 * uniforms from the operating-system-seeded stream.
 */
#define ZK_GAUSS_BASE 262144.0

typedef struct {
    double sigma;
    int rounded;              // 1 if above ZK_GAUSS_BASE
    discrete_gaussian_ctx_t dg;
    double spare;             // Box-Muller makes two deviates at a time
    int have_spare;
} zk_gauss_t;

static void zk_gauss_init(zk_gauss_t *g, double sigma) {
    // Samples reach about 40 sigma at most; keep them inside a signed word.
    if (!(sigma > 0 && sigma < 0x1p56)) {
        fprintf(stderr, "evmlr_zk: Gaussian width %g out of range\n", sigma);
        abort();
    }
    g->sigma = sigma;
    g->rounded = (sigma > ZK_GAUSS_BASE);
    g->have_spare = 0;
    discrete_gaussian_ctx_init(g->dg, g->rounded ? 1.0 : sigma);
}

static void zk_gauss_clear(zk_gauss_t *g) {
    discrete_gaussian_ctx_clear(g->dg);
}

/* A uniform double in (0, 1], with 53 bits. */
static double uniform53(void) {
    uint64_t r;

    fastrandombytes((unsigned char *) &r, sizeof(r));
    return ((double) (r >> 11) + 1.0) / 9007199254740992.0;
}

static slong zk_gauss(zk_gauss_t *g) {
    double x;

    if (!g->rounded) {
        return discrete_gaussian(0.0, g->dg);
    }
    if (g->have_spare) {
        g->have_spare = 0;
        x = g->spare;
    } else {
        double r = sqrt(-2.0 * log(uniform53())), th = 2.0 * M_PI * uniform53();

        x = r * cos(th);
        g->spare = r * sin(th);
        g->have_spare = 1;
    }
    return (slong) llround(x * g->sigma);
}

static void sample_gauss(nmod_poly_struct *v, slong len, zk_gauss_t *g) {
    for (slong i = 0; i < len; i++) {
        nmod_poly_zero(v + i);
        nmod_poly_fit_length(v + i, DEGREE_N);
        for (slong j = 0; j < DEGREE_N; j++) {
            nmod_poly_set_coeff_ui(v + i, j, from_signed(zk_gauss(g)));
        }
    }
}

static int accept(double e, double M) {
    uint64_t rnd;

#ifdef MAIN
    if (zk_skip_rejection) return 1;
#endif
    fastrandombytes((unsigned char *) &rnd, sizeof(rnd));
    return ((double) (rnd >> 11) / (double) (1ULL << 53)) < exp(e) / M;
}

/* Accepts the masked opening z = y + v with probability
 * min(1, exp((-2<z, v> + ||v||^2) / (2 sigma^2)) / M). */
static int rejection(const nmod_poly_struct *z, const nmod_poly_struct *v, slong len, double sigma) {
    return accept((-2.0 * vec_dot(z, v, len) + vec_norm2(v, len)) / (2.0 * sigma * sigma), ZK_M);
}

static int rejection3(const slong *z, const slong *v, double sigma) {
    double dot = 0, n2 = 0;

    for (slong i = 0; i < ZK_PROJ; i++) {
        dot += (double) z[i] * (double) v[i];
        n2 += (double) v[i] * (double) v[i];
    }
    return accept((-2.0 * dot + n2) / (2.0 * sigma * sigma), ZK_M_PROJ);
}

static double norm3(const slong *z) {
    double n = 0;

    for (slong i = 0; i < ZK_PROJ; i++) n += (double) z[i] * (double) z[i];
    return n;
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

/* The binary claim's quadratic form, sum_j sigma(a_j)(b_j - x 1) over the
 * first m elements, with 1 the all-ones polynomial: F for (a, b, x) = (s, s, 1),
 * and what the verifier evaluates for (z, z, c). */
static void quad(nmod_poly_t r, const nmod_poly_struct *a, const nmod_poly_struct *b,
                 const nmod_poly_t x, slong m) {
    nmod_poly_t ones, t, u;

    evmlr_zk_init(ones);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_ones(ones);
    evmlr_zk_mul(ones, ones, x);
    nmod_poly_zero(r);
    for (slong j = 0; j < m; j++) {
        evmlr_zk_sigma(t, a + j);
        nmod_poly_sub(u, b + j, ones);
        evmlr_zk_mul(t, t, u);
        nmod_poly_add(r, r, t);
    }
    nmod_poly_clear(ones);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
}

/* G0 = sum_j sigma(y_j)(s_j - 1) + sigma(s_j) y_j and G1 = sum_j sigma(y_j) y_j,
 * the coefficients of c and 1 in sum_j sigma(z_j)(z_j - c 1) for z = y + c s,
 * whose coefficient of c^2 is F (sigma(c) = c). */
static void garbage(nmod_poly_t G0, nmod_poly_t G1, const nmod_poly_struct *y,
                    const nmod_poly_struct *s, slong m) {
    nmod_poly_t one, zero, t;

    evmlr_zk_init(one);
    evmlr_zk_init(zero);
    evmlr_zk_init(t);
    nmod_poly_one(one);
    quad(G0, y, s, one, m);
    nmod_poly_zero(G1);
    for (slong j = 0; j < m; j++) {
        evmlr_zk_sigma(t, s + j);
        evmlr_zk_mul(t, t, y + j);
        nmod_poly_add(G0, G0, t);
    }
    quad(G1, y, y, zero, m);
    nmod_poly_clear(one);
    nmod_poly_clear(zero);
    nmod_poly_clear(t);
}

/* s1 = (s, k): the witness lifted to R_p, and its carry k = (E s - t) / q
 * over the integers. Returns 0 if E s != t (mod q). */
static int lift_witness(nmod_poly_struct *s1, const nmod_poly_struct *s,
                        const evmlr_zk_stmt_struct *st) {
    const slong m = st->m, rows = st->rows;
    nmod_poly_struct *e = vec_init(rows);
    nmod_poly_t t;
    int ok = 1;

    evmlr_zk_init(t);
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
    vec_clear(e, rows);
    nmod_poly_clear(t);
    return ok;
}

double evmlr_zk_carry_norm(const nmod_poly_struct *s, const evmlr_zk_stmt_struct *st) {
    nmod_poly_struct *s1 = vec_init(st->m + st->rows);
    double n = lift_witness(s1, s, st) ? sqrt(vec_norm2(s1 + st->m, st->rows)) : -1.0;

    vec_clear(s1, st->m + st->rows);
    return n;
}

int evmlr_zk_prove(evmlr_zk_proof_t pi, const nmod_poly_struct *s,
                   const evmlr_zk_stmt_struct *st, const uint8_t pp[32]) {
    const slong m = st->m, rows = st->rows, m1 = m + rows;
    nmod_poly_struct *s1 = vec_init(m1), *s2 = vec_init(ZK_M2);
    nmod_poly_struct *y1 = vec_init(m1), *y2 = vec_init(ZK_M2);
    nmod_poly_struct *msg = vec_init(ZK_SLOTS), *e = vec_init(rows);
    nmod_poly_struct *w = vec_init(ZK_KAPPA), *wl = vec_init(ZK_LAMBDA);
    nmod_poly_struct *cs1 = vec_init(m1), *cs2 = vec_init(ZK_M2);
    nmod_poly_t c, t, u, vF, G0, G1, tau;
    uint8_t h1[32], h2[32];
    slong y3[2 * ZK_PROJ], rs[2 * ZK_PROJ];
    double sigma[5];
    zk_gauss_t dg[5];
    aggr_t ag;
    int ok = 1, have_aggr = 0;

    evmlr_zk_init(c);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_init(vF);
    evmlr_zk_init(G0);
    evmlr_zk_init(G1);
    evmlr_zk_init(tau);
    evmlr_zk_sigmas(sigma, m, st->k_bound);
    for (int b = 0; b < 5; b++) {
        zk_gauss_init(&dg[b], sigma[b]);
    }

    // The witness, lifted, and its carry k = (E s - t) / q over the integers.
    ok = evmlr_zk_supported(m, rows, st->k_bound);
#ifdef MAIN
    ok |= zk_skip_rejection; // a cheating prover does not check either
#endif
    ok = ok && lift_witness(s1, s, st);
    // The widths assume ||k|| <= k_bound; past it the proof would not hide k.
    if (!ok || vec_norm2(s1 + m, rows) > st->k_bound * st->k_bound) {
        ok = 0;
        goto end;
    }

    // F = sum_j sigma(s_j)(s_j - 1), whose constant coefficient is
    // sum_i s_i (s_i - 1), zero exactly when s is binary.
    nmod_poly_one(t);
    quad(msg + ZK_SLOT_F, s1, s1, t, m);
#ifdef MAIN
    if (zk_fake_f) nmod_poly_set_coeff_ui(msg + ZK_SLOT_F, 0, 0);
#endif

    // Commitment: s_2 ternary; the masks g_l uniform with ct(g_l) = 0; F.
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
        evmlr_zk_uniform(msg + l, &prg);
        nmod_poly_set_coeff_ui(msg + l, 0, 0);
    }
    ajtai(pi->tA, s1, m1, s2, pp);
    for (slong l = 0; l < ZK_SLOTS; l++) {
        bdlop_row(pi->tB + l, l, s2, pp);
        if (l != ZK_SLOT_Y) {
            nmod_poly_add(pi->tB + l, pi->tB + l, msg + l);
        }
    }
    nmod_poly_set(u, pi->tB + ZK_SLOT_Y); // <b_Y, s_2>

    // The projections, redrawn with slot Y until both pass their rejection
    // tests. Only slot Y changes between tries: rejected tries are never
    // published, so reusing s_2 across them reveals nothing.
    ok = 0;
    for (int tries = 0; tries < ZK_PROJ_TRIES && !ok; tries++) {
        nmod_poly_zero(msg + ZK_SLOT_Y);
        for (slong i = 0; i < 2 * ZK_PROJ; i++) {
            y3[i] = zk_gauss(&dg[(i < ZK_PROJ) ? 3 : 4]);
            nmod_poly_set_coeff_ui(msg + ZK_SLOT_Y, i, from_signed(y3[i]));
        }
        nmod_poly_add(pi->tB + ZK_SLOT_Y, u, msg + ZK_SLOT_Y);
        hash_commitment(h1, pp, st, pi);
        proj_apply(rs, s1, m, m1, h1);
        for (slong i = 0; i < 2 * ZK_PROJ; i++) {
            pi->z3[i] = rs[i] + y3[i];
        }
        ok = rejection3(pi->z3, rs, sigma[3])
          && rejection3(pi->z3 + ZK_PROJ, rs + ZK_PROJ, sigma[4]);
    }
    if (!ok) goto end;

    // h_l = g_l + nu_l F + sum_r sigma(alpha_lr) e_r + sum_j P_lj s1_j
    //       + M_l Y - Z_l,
    // whose constant coefficient is zero exactly when s is binary,
    // e = E s - q k - t is zero, and both projections are honest.
    hash_projection(h2, h1, pi->z3);
    aggr_init(&ag, h2, pi->z3, h1, m, m1, rows);
    have_aggr = 1;
    residual(e, s1, st, 1);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        aggr_linear(t, &ag, l, e, s1);
        nmod_poly_add(pi->h + l, msg + l, t);
        nmod_poly_scalar_mul_nmod(t, msg + ZK_SLOT_F, ag.nu[l]);
        nmod_poly_add(pi->h + l, pi->h + l, t);
        evmlr_zk_mul(u, ag.M + l, msg + ZK_SLOT_Y);
        nmod_poly_add(pi->h + l, pi->h + l, u);
        nmod_poly_set_coeff_ui(pi->h + l, 0,
                nmod_sub(nmod_poly_get_coeff_ui(pi->h + l, 0), ag.Z[l], *evmlr_zk_mod()));
    }

    for (;;) {
        // Masks; the garbage term G = G0 + v_F, committed in row ZK_SLOT_G;
        // and the first messages:
        //   w   = A_1 y_1 + A_2 y_2,
        //   w_l = v_gl + nu_l v_F + M_l v_Y - sum_r sigma(alpha_lr)(E_r y_s - q y_k,r)
        //         - sum_j P_lj y1_j,
        //   tau = v_G + G1,
        // with v_X = <b_X, y_2> the mask of slot X.
        sample_gauss(y1, m, &dg[0]);
        sample_gauss(y1 + m, rows, &dg[1]);
        sample_gauss(y2, ZK_M2, &dg[2]);
        garbage(G0, G1, y1, s1, m);
        bdlop_row(vF, ZK_SLOT_F, y2, pp);
        bdlop_row(pi->tG, ZK_SLOT_G, s2, pp);
        nmod_poly_add(pi->tG, pi->tG, G0);
        nmod_poly_add(pi->tG, pi->tG, vF);
        bdlop_row(tau, ZK_SLOT_G, y2, pp);
        nmod_poly_add(tau, tau, G1);
        ajtai(w, y1, m1, y2, pp);
        residual(e, y1, st, 0);
        bdlop_row(u, ZK_SLOT_Y, y2, pp);
        for (slong l = 0; l < ZK_LAMBDA; l++) {
            bdlop_row(wl + l, l, y2, pp);
            aggr_linear(t, &ag, l, e, y1);
            nmod_poly_sub(wl + l, wl + l, t);
            evmlr_zk_mul(t, ag.M + l, u);
            nmod_poly_add(wl + l, wl + l, t);
            nmod_poly_scalar_mul_nmod(t, vF, ag.nu[l]);
            nmod_poly_add(wl + l, wl + l, t);
        }
        hash_challenge(pi->hash, h2, pi, w, wl, tau);
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
    for (int b = 0; b < 5; b++) {
        zk_gauss_clear(&dg[b]);
    }
    if (have_aggr) {
        aggr_clear(&ag);
    }
    vec_clear(s1, m1);
    vec_clear(s2, ZK_M2);
    vec_clear(y1, m1);
    vec_clear(y2, ZK_M2);
    vec_clear(msg, ZK_SLOTS);
    vec_clear(e, rows);
    vec_clear(w, ZK_KAPPA);
    vec_clear(wl, ZK_LAMBDA);
    vec_clear(cs1, m1);
    vec_clear(cs2, ZK_M2);
    nmod_poly_clear(c);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
    nmod_poly_clear(vF);
    nmod_poly_clear(G0);
    nmod_poly_clear(G1);
    nmod_poly_clear(tau);
    return ok;
}

/* u = <b_X, z_2> - c t_X, the opening of the BDLOP row X. */
static void bdlop_open(nmod_poly_t u, slong X, const nmod_poly_t tX, const nmod_poly_t c,
                       const nmod_poly_struct *z2, const uint8_t pp[32]) {
    nmod_poly_t t;

    evmlr_zk_init(t);
    bdlop_row(u, X, z2, pp);
    evmlr_zk_mul(t, c, tX);
    nmod_poly_sub(u, u, t);
    nmod_poly_clear(t);
}

int evmlr_zk_verify(const evmlr_zk_proof_t pi, const evmlr_zk_stmt_struct *st,
                    const uint8_t pp[32]) {
    const slong m = st->m, rows = st->rows, m1 = m + rows;
    nmod_poly_struct *w, *wl, *e;
    nmod_poly_t c, t, u, uY, uF, tau;
    uint8_t h1[32], h2[32], h3[32];
    double sigma[5];
    aggr_t ag;
    int ok, norms, cts;

    if (pi->m != m || pi->rows != rows || !evmlr_zk_supported(m, rows, st->k_bound)) {
        return 0;
    }
    w = vec_init(ZK_KAPPA);
    wl = vec_init(ZK_LAMBDA);
    e = vec_init(rows);
    evmlr_zk_init(c);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_init(uY);
    evmlr_zk_init(uF);
    evmlr_zk_init(tau);
    evmlr_zk_sigmas(sigma, m, st->k_bound);

    // Norms of the masked openings, block by block, and of the projections.
    norms = vec_norm2(pi->z1, m) <= bound2(sigma[0], m);
    norms &= vec_norm2(pi->z1 + m, rows) <= bound2(sigma[1], rows);
    norms &= vec_norm2(pi->z2, ZK_M2) <= bound2(sigma[2], ZK_M2);
    norms &= norm3(pi->z3) <= bound3(sigma[3]);
    norms &= norm3(pi->z3 + ZK_PROJ) <= bound3(sigma[4]);

    // The aggregated values have zero constant coefficients.
    cts = 1;
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        cts &= (evmlr_zk_ct(pi->h + l) == 0);
    }

    // First messages, recomputed from the openings, with u_X the opening of
    // BDLOP row X:
    //   w   = A_1 z_1 + A_2 z_2 - c t_A,
    //   w_l = c h_l + u_gl + nu_l u_F + M_l u_Y + c Z_l
    //         - sum_r sigma(alpha_lr)(E_r z_s - q z_k,r - c t_r) - sum_j P_lj z1_j,
    //   tau = sum_j sigma(z_j)(z_j - c 1) + c u_F + u_G.
    challenge_from(c, pi->hash);
    hash_commitment(h1, pp, st, pi);
    hash_projection(h2, h1, pi->z3);
    aggr_init(&ag, h2, pi->z3, h1, m, m1, rows);
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
    bdlop_open(uY, ZK_SLOT_Y, pi->tB + ZK_SLOT_Y, c, pi->z2, pp);
    bdlop_open(uF, ZK_SLOT_F, pi->tB + ZK_SLOT_F, c, pi->z2, pp);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        bdlop_open(u, l, pi->tB + l, c, pi->z2, pp);
        evmlr_zk_mul(wl + l, c, pi->h + l);
        nmod_poly_add(wl + l, wl + l, u);
        nmod_poly_scalar_mul_nmod(t, uF, ag.nu[l]);
        nmod_poly_add(wl + l, wl + l, t);
        evmlr_zk_mul(t, ag.M + l, uY);
        nmod_poly_add(wl + l, wl + l, t);
        nmod_poly_scalar_mul_nmod(t, c, ag.Z[l]);
        nmod_poly_add(wl + l, wl + l, t);
        aggr_linear(t, &ag, l, e, pi->z1);
        nmod_poly_sub(wl + l, wl + l, t);
    }
    quad(tau, pi->z1, pi->z1, c, m);
    evmlr_zk_mul(t, c, uF);
    nmod_poly_add(tau, tau, t);
    bdlop_open(u, ZK_SLOT_G, pi->tG, c, pi->z2, pp);
    nmod_poly_add(tau, tau, u);
    hash_challenge(h3, h2, pi, w, wl, tau);
    ok = norms && cts && (memcmp(h3, pi->hash, sizeof(h3)) == 0);
#ifdef MAIN
    zk_failure = !norms ? FAIL_NORM : !cts ? FAIL_CT : !ok ? FAIL_HASH : FAIL_NONE;
#endif

    aggr_clear(&ag);
    vec_clear(w, ZK_KAPPA);
    vec_clear(wl, ZK_LAMBDA);
    vec_clear(e, rows);
    nmod_poly_clear(c);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
    nmod_poly_clear(uY);
    nmod_poly_clear(uF);
    nmod_poly_clear(tau);
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

    /* gaussian.cpp's sampler returns 0 most of the time past sigma = 418000,
     * which would leave masks at 0 and reveal the witness; check both paths
     * of zk_gauss give the width asked for and no excess of zeros. */
    TEST_BEGIN("masks have the width asked for, on both sides of the base") {
        double widths[] = { 3.0e4, 2.0e5, 1.0e6, 1.0e9 };
        int ok = 1;
        for (int w = 0; w < 4; w++) {
            zk_gauss_t g;
            double s2 = 0;
            long zeros = 0, n = 20000;
            zk_gauss_init(&g, widths[w]);
            for (long i = 0; i < n; i++) {
                slong v = zk_gauss(&g);
                s2 += (double) v * (double) v;
                zeros += (v == 0);
            }
            zk_gauss_clear(&g);
            double ratio = sqrt(s2 / n) / widths[w];
            ok &= (ratio > 0.97 && ratio < 1.03 && zeros < 10);
        }
        TEST_ASSERT(ok, end);
    } TEST_END;

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
        st.k_bound = 1e13; // let the prover past its own refusal
        int forced = evmlr_zk_prove(pi, s, &st, pp);
        st.k_bound = kb;
        int verified = evmlr_zk_verify(pi, &st, pp);
        zk_skip_rejection = 0;
        zk_bump = 0;
        TEST_ASSERT(proved == 0 && forced == 1 && verified == 0, end);
    } TEST_END;

    TEST_BEGIN("the certified bounds leave neither claim room to wrap") {
        // Linear: |E_r s - q k_r - t_r| <= (q/2) sqrt(m n) B_s + q B_k + q/2,
        // which below p/2 makes E s - q k = t hold over the integers.
        // Binary: |sum_i s_i (s_i - 1)| <= B_s^2 + sqrt(m n) B_s, which below
        // p makes ct(F) = 0 mean the sum is zero over the integers.
        double B[2];
        evmlr_zk_certified(B, st.m, st.k_bound);
        double lin = (MOD_Q / 2.0) * sqrt((double) st.m * DEGREE_N) * B[0] + MOD_Q * B[1] + MOD_Q;
        double bin = B[0] * B[0] + sqrt((double) st.m * DEGREE_N) * B[0];
        TEST_ASSERT(lin < ZK_P / 2.0 && bin < ZK_P, end);
    } TEST_END;

    /* The shuffle's statement at N messages has m = 25 N + 48 and 7 rows, and
     * a carry bound near 1.25 sqrt(n^2 q^2 / 12 * (25 N + 2 (12 N + 16) * 2
     * + 2 (N + 16))) / q (evmlr_shuffle.c, shuffle_k_bound). The parameters
     * are meant to cover N = 1000, and must refuse what they do not cover. */
    TEST_BEGIN("the parameters cover the shuffle up to N = 1000 and refuse beyond") {
        slong Ns[2] = { 1000, 5000 };
        int ok[2];
        for (int i = 0; i < 2; i++) {
            double N = (double) Ns[i];
            double cols = 25 * N + 4 * (12 * N + 16) + 2 * (N + 16);
            double kb = 1.25 * sqrt((double) DEGREE_N * DEGREE_N * cols * MOD_Q * MOD_Q / 12.0) / MOD_Q;
            ok[i] = evmlr_zk_supported(25 * Ns[i] + 48, 7, kb);
        }
        TEST_ASSERT(ok[0] == 1 && ok[1] == 0, end);
    } TEST_END;

    /* s + 2 e_0 changes E s, so it gets a statement of its own: t' = E s'. */
    TEST_BEGIN("a non-binary witness is rejected by the binary claim") {
        nmod_poly_struct *t0 = flint_malloc(st.rows * sizeof(nmod_poly_struct));
        for (slong r = 0; r < st.rows; r++) {
            nmod_poly_init(t0 + r, MOD_Q);
            nmod_poly_set(t0 + r, st.t + r);
        }
        // Coefficient 0 of s_0 becomes s + 2 (2 or 3), i.e. t gains 2 E_r,0.
        ulong old = nmod_poly_get_coeff_ui(s + 0, 0);
        nmod_poly_set_coeff_ui(s + 0, 0, old + 2);
        for (slong r = 0; r < st.rows; r++) {
            nmod_poly_t col;
            nmod_poly_init(col, MOD_Q);
            nmod_poly_scalar_mul_nmod(col, d.E + r * st.m, 2);
            nmod_poly_add(st.t + r, st.t + r, col);
            nmod_poly_clear(col);
        }
        int proved = evmlr_zk_prove(pi, s, &st, pp);
        int verified = evmlr_zk_verify(pi, &st, pp);
        int reason = zk_failure;
        // A prover that zeroes ct(F) to hide it is caught by the quadratic check.
        zk_fake_f = 1;
        int proved2 = evmlr_zk_prove(pi, s, &st, pp);
        int verified2 = evmlr_zk_verify(pi, &st, pp);
        int reason2 = zk_failure;
        zk_fake_f = 0;
        nmod_poly_set_coeff_ui(s + 0, 0, old);
        for (slong r = 0; r < st.rows; r++) {
            nmod_poly_set(st.t + r, t0 + r);
            nmod_poly_clear(t0 + r);
        }
        flint_free(t0);
        TEST_ASSERT(proved == 1 && verified == 0 && reason == FAIL_CT, end);
        TEST_ASSERT(proved2 == 1 && verified2 == 0 && reason2 == FAIL_HASH, end);
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
