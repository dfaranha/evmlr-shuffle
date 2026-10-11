#include "evmlr_zk_proof.h"
#include "gaussian.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef MAIN
/* A proof takes a fraction of a second, so the default 100 repetitions per
 * test would take minutes; a few still exercise fresh randomness. */
#ifndef TESTS
#define TESTS 5
#endif
#include "test.h"
#include "bench.h"
#endif

/* Domains of the public matrices and challenges expanded from seeds. */
enum { DOM_A1 = 1, DOM_A2 = 2, DOM_B = 3, DOM_ALPHA = 4, DOM_PROJ = 5, DOM_MU = 6 };

/* Rejection sampling keeps its 2^-100 statistical distance at M = 1.75 once
 * the width is 21.485 times the norm of the shift it masks. The openings of
 * s, of k and of s_2 pass one joint test, with block b scaled by its own
 * ratio alpha_b; that is one test of ratio (sum_b alpha_b^-2)^-1/2, which
 * the ratios below keep at 21.485. Three tests at 21.485 each would repeat
 * 1.75^3 = 5.4 times. k and s_2 are a few elements against thousands, so
 * widening them costs little in size; the 2.5 for k is what keeps the MSIS
 * bound at N = 1000 messages lowest (2^42.9), as k still weighs on it. */
#define ZK_M 1.75
#define ZK_ALPHA_RS 21.485
#define ZK_ALPHA_K (2.5 * ZK_ALPHA_RS)
#define ZK_ALPHA_2 (10.0 * ZK_ALPHA_RS)
#define ZK_ALPHA_S 23.583
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
/* Tries at each projection before an honest prover would have succeeded
 * except with probability below 2^-128: each try is accepted with probability
 * 1 / ZK_M_PROJ, and (1 - 1/3.81)^1300 = 2^-570. (1300 dates from when both
 * projections were redrawn together, at 1/14.5.) A witness that fails them all
 * is too long. */
#define ZK_PROJ_TRIES 1300
/* Mask candidates the prover tries per pass over the witness. One is
 * accepted with probability 1 / ZK_M, and a pass costs mostly the columns it
 * generates, which the candidates of a pass share: two take 1.23 passes on
 * average, against 1.75 for one at a time. Rejected candidates are never
 * published, and the first accepted is the one used, so the proof is
 * distributed as with one at a time. */
#ifndef ZK_BATCH
#define ZK_BATCH 2
#endif

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
 * element j of (s, k), with entries in {-1, 0, 1} with probabilities 1/4,
 * 1/2, 1/4. One stream per element, so R is never held whole. Each byte of
 * the stream gives four rows at one coefficient: byte g n + k holds, in bits
 * 2t and 2t + 1, the code of row 4g + t at coefficient k, with 1 for 1, 2 for
 * -1 and 0 or 3 for 0. Keeping the rows of a coefficient together is what
 * lets aggr_P_column look sums of rows up in tables. */
#define ZK_PROJ_BYTES (ZK_PROJ / 4 * DEGREE_N)

static int8_t proj_trit(int code) {
    return (int8_t) ((code == 1) - (code == 2));
}

static void proj_codes(uint8_t codes[ZK_PROJ_BYTES], const uint8_t seed[32], slong j) {
    prg_t prg;

    evmlr_zk_prg_for(&prg, seed, DOM_PROJ, (uint64_t) j, 0);
    prg_bytes(&prg, codes, ZK_PROJ_BYTES);
}

/* The entries themselves, r[i n + k] for row i and coefficient k. */
static void proj_expand(int8_t *r, const uint8_t codes[ZK_PROJ_BYTES]) {
    for (slong g = 0; g < ZK_PROJ / 4; g++) {
        for (slong k = 0; k < DEGREE_N; k++) {
            int b = codes[g * DEGREE_N + k];

            for (int t = 0; t < 4; t++) {
                r[(4 * g + t) * DEGREE_N + k] = proj_trit((b >> (2 * t)) & 3);
            }
        }
    }
}

/* out = R v over the integers for the elements j0..j1-1 of a vector, whose
 * projection comes from seed. */
static void proj_apply(slong out[ZK_PROJ], const nmod_poly_struct *v, slong j0, slong j1,
                       const uint8_t seed[32]) {
    int8_t *r = flint_malloc(ZK_PROJ * DEGREE_N);
    uint8_t *codes = flint_malloc(ZK_PROJ_BYTES);
    slong c[DEGREE_N];
    int32_t c32[DEGREE_N];

    for (slong i = 0; i < ZK_PROJ; i++) out[i] = 0;
    for (slong j = j0; j < j1; j++) {
        slong cmax = 0;

        proj_codes(codes, seed, j);
        proj_expand(r, codes);
        for (slong k = 0; k < DEGREE_N; k++) {
            c[k] = centre(nmod_poly_get_coeff_ui(v + j, k));
            cmax = FLINT_MAX(cmax, FLINT_ABS(c[k]));
        }
        if (cmax < (1 << 21)) {
            // n terms below 2^21 sum inside 32 bits, which vectorises better.
            for (slong k = 0; k < DEGREE_N; k++) c32[k] = (int32_t) c[k];
            for (slong i = 0; i < ZK_PROJ; i++) {
                const int8_t *ri = r + i * DEGREE_N;
                int32_t acc = 0;

                for (slong k = 0; k < DEGREE_N; k++) acc += ri[k] * c32[k];
                out[i] += acc;
            }
        } else {
            for (slong i = 0; i < ZK_PROJ; i++) {
                slong acc = 0;

                for (slong k = 0; k < DEGREE_N; k++) acc += r[i * DEGREE_N + k] * c[k];
                out[i] += acc;
            }
        }
    }
    flint_free(r);
    flint_free(codes);
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

/* h0: the parameters, the statement and the commitment, all but the two
 * projection masks, which are committed after it, each in its own loop. */
static void hash_commitment(uint8_t out[32], const uint8_t pp[32],
                            const evmlr_zk_stmt_struct *st, const evmlr_zk_proof_struct *pi) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-commit", 15);
    SHA256Input(&sha, pp, 32);
    SHA256Input(&sha, st->digest, SHA256HashSize);
    absorb(&sha, pi->tA, ZK_KAPPA);
    absorb(&sha, pi->tB, ZK_SLOT_YS);
    absorb(&sha, pi->tB + ZK_SLOT_F, 1);
    SHA256Result(&sha, out);
}

static void absorb_ints(SHA256Context *sha, const slong *z, slong len) {
    uint8_t buf[8];

    for (slong i = 0; i < len; i++) {
        for (int b = 0; b < 8; b++) buf[b] = (uint8_t) ((uint64_t) z[i] >> (8 * b));
        SHA256Input(sha, buf, 8);
    }
}

/* The seeds of the two projections: R_s from h0 and the commitment to its
 * mask y_s; R_k from that seed, the projection z_s it produced, and the
 * commitment to y_k. Each projection is drawn after the vector it bounds and
 * its mask are committed, which is what the projection lemma needs. */
static void hash_seed_s(uint8_t out[32], const uint8_t h0[32], const evmlr_zk_proof_struct *pi) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-proj-s", 15);
    SHA256Input(&sha, h0, 32);
    absorb(&sha, pi->tB + ZK_SLOT_YS, 1);
    SHA256Result(&sha, out);
}

static void hash_seed_k(uint8_t out[32], const uint8_t seed_s[32], const evmlr_zk_proof_struct *pi) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-proj-k", 15);
    SHA256Input(&sha, seed_s, 32);
    absorb_ints(&sha, pi->z3, ZK_PROJ);
    absorb(&sha, pi->tB + ZK_SLOT_YK, 1);
    SHA256Result(&sha, out);
}

/* h2: the seed of the last projection and both projections. The aggregation
 * scalars come from it, so the masks g_l, committed in h0, are fixed before
 * the scalars applied to them. */
static void hash_projection(uint8_t out[32], const uint8_t seed_k[32], const slong z3[2 * ZK_PROJ]) {
    SHA256Context sha;

    SHA256Reset(&sha);
    SHA256Input(&sha, (const uint8_t *) "evmlr-zk-proj", 13);
    SHA256Input(&sha, seed_k, 32);
    absorb_ints(&sha, z3, 2 * ZK_PROJ);
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

/* The scalars of the aggregation. The projection's part, P_lj =
 * sigma(sum_i mu_li R_i,j) for each element j of (s, k), is never stored:
 * linear_pass rebuilds each column from the projection's stream as it goes,
 * which is what keeps memory linear in the witness. */
typedef struct {
    slong rows;
    nmod_poly_struct *alpha; /* ZK_LAMBDA x rows: sigma(alpha_lr), the linear rows */
    ulong mu[ZK_LAMBDA][2 * ZK_PROJ];
    nmod_poly_struct *M;     /* 2 ZK_LAMBDA: sigma(sum_i mu_li x^i), for Y_s then Y_k */
    ulong Z[ZK_LAMBDA];      /* sum_i mu_li z3_i */
    ulong nu[ZK_LAMBDA];     /* the scalars applied to F */
    uint8_t seed[2][32];     /* the projections' seeds, of s and of k */
    /* For each pair of rows of a projection, of s (pairs 0..ZK_PROJ/2-1)
     * then of k, and each of the 16 codes the pair can have at a coefficient:
     * the sum of mu_li times the pair's entries, for every l. */
    int64_t (*tab)[16][ZK_LAMBDA];
} aggr_t;

static void aggr_init(aggr_t *a, const uint8_t h2[32], const slong z3[2 * ZK_PROJ],
                      const uint8_t seed_s[32], const uint8_t seed_k[32], slong rows) {
    const nmod_t mod = *evmlr_zk_mod();
    nmod_poly_t t;

    a->rows = rows;
    a->alpha = vec_init(ZK_LAMBDA * rows);
    a->M = vec_init(2 * ZK_LAMBDA);
    memcpy(a->seed[0], seed_s, 32);
    memcpy(a->seed[1], seed_k, 32);
    evmlr_zk_init(t);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        for (slong r_ = 0; r_ < rows; r_++) {
            expand(t, h2, DOM_ALPHA, l, r_);
            evmlr_zk_sigma(a->alpha + l * rows + r_, t);
        }
        expand(t, h2, DOM_MU, l, 1);
        a->nu[l] = nmod_poly_get_coeff_ui(t, 0);
        expand(t, h2, DOM_MU, l, 0);
        a->Z[l] = 0;
        _Static_assert(2 * ZK_PROJ <= DEGREE_N, "the mu of both projections come from one element");
        for (slong i = 0; i < 2 * ZK_PROJ; i++) {
            a->mu[l][i] = nmod_poly_get_coeff_ui(t, i);
            // y_s and y_k sit in the first ZK_PROJ coefficients of their slots.
            nmod_poly_set_coeff_ui(a->M + l + ((i < ZK_PROJ) ? 0 : ZK_LAMBDA), i % ZK_PROJ, a->mu[l][i]);
            a->Z[l] = nmod_add(a->Z[l], nmod_mul(a->mu[l][i], from_signed(z3[i]), mod), mod);
        }
        evmlr_zk_sigma(a->M + l, a->M + l);
        evmlr_zk_sigma(a->M + ZK_LAMBDA + l, a->M + ZK_LAMBDA + l);
    }
    a->tab = flint_malloc(ZK_PROJ * sizeof(*a->tab));
    for (slong pr = 0; pr < ZK_PROJ; pr++) { // pair pr: rows 2 pr and 2 pr + 1 of mu
        for (int code = 0; code < 16; code++) {
            for (slong l = 0; l < ZK_LAMBDA; l++) {
                a->tab[pr][code][l] = proj_trit(code & 3) * (int64_t) a->mu[l][2 * pr]
                                    + proj_trit(code >> 2) * (int64_t) a->mu[l][2 * pr + 1];
            }
        }
    }
    nmod_poly_clear(t);
}

static void aggr_clear(aggr_t *a) {
    vec_clear(a->alpha, ZK_LAMBDA * a->rows);
    vec_clear(a->M, 2 * ZK_LAMBDA);
    flint_free(a->tab);
}

/* P[l] = P_lj for l < ZK_LAMBDA, from the projection's codes (proj_codes)
 * of element j: of R_s if j < m, of R_k otherwise. Each byte gives two pairs
 * of rows, whose part of every P_l[k] is one table entry. */
static void aggr_P_column(nmod_poly_struct *P, const aggr_t *a, const uint8_t *codes, int is_s) {
    _Static_assert(ZK_P < (1UL << 52) && ZK_PROJ <= 1024,
                   "ZK_PROJ / 2 entries below 2^53 sum inside a signed 64-bit word");
    const int64_t (*T)[16][ZK_LAMBDA] = (const int64_t (*)[16][ZK_LAMBDA]) a->tab + (is_s ? 0 : ZK_PROJ / 2);
    int64_t acc[DEGREE_N][ZK_LAMBDA] = { { 0 } };

    for (slong g = 0; g < ZK_PROJ / 4; g++) {
        const uint8_t *cg = codes + g * DEGREE_N;
        const int64_t (*T0)[ZK_LAMBDA] = T[2 * g], (*T1)[ZK_LAMBDA] = T[2 * g + 1];

        for (slong k = 0; k < DEGREE_N; k++) {
            const int64_t *x = T0[cg[k] & 15], *y = T1[cg[k] >> 4];

            for (slong l = 0; l < ZK_LAMBDA; l++) acc[k][l] += x[l] + y[l];
        }
    }
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        nmod_poly_zero(P + l);
        nmod_poly_fit_length(P + l, DEGREE_N);
        for (slong k = 0; k < DEGREE_N; k++) {
            int64_t v = acc[k][l] % (int64_t) ZK_P;

            (P + l)->coeffs[k] = (v < 0) ? (ulong) (v + (int64_t) ZK_P) : (ulong) v;
        }
        (P + l)->length = DEGREE_N;
        _nmod_poly_normalise(P + l);
        evmlr_zk_sigma(P + l, P + l);
    }
}

/* The part of h_l (or of its first message) that is linear in (s, k), from a
 * pass over v: sum_r sigma(alpha_lr) e_r + Pv_l, for e = E v_s - q v_k (with
 * whatever multiple of t the caller has subtracted) and Pv_l =
 * sum_j P_lj v_j. */
static void aggr_value(nmod_poly_t out, const aggr_t *a, slong l,
                       const nmod_poly_struct *e, const nmod_poly_t Pv) {
    evmlr_zk_acc_t acc;
    evmlr_zk_ntt_t x, y;

    evmlr_zk_acc_init(&acc);
    for (slong r = 0; r < a->rows; r++) {
        evmlr_zk_ntt(&x, a->alpha + l * a->rows + r);
        evmlr_zk_ntt(&y, e + r);
        evmlr_zk_acc_addmul(&acc, &x, &y);
    }
    evmlr_zk_acc_get(out, &acc);
    nmod_poly_add(out, out, Pv);
    evmlr_zk_acc_clear(&acc);
}

/*============================================================================*/
/* One pass over a vector standing for (s, k)                                 */
/*============================================================================*/

enum { LIN_A = 1, LIN_E = 2, LIN_P = 4 };

/* One vector's part of a pass: which of the functions below to compute on
 * v1 (and v2), and where to put them. */
typedef struct {
    const nmod_poly_struct *v1, *v2;
    nmod_poly_struct *outA, *outE, *outP;
    int what;
} lin_job_t;

/*
 * The linear functions of v1 = (v_s, v_k), of length m1 = m + rows, that the
 * proof needs, for each of nj vectors in one pass that transforms each v1_j
 * once:
 *
 *   LIN_A:  outA = A_1 v1 + A_2 v2      (ZK_KAPPA elements; v2 may be NULL)
 *   LIN_E:  outE = E v_s - q v_k        (rows elements)
 *   LIN_P:  outP_l = sum_j P_lj v1_j    (ZK_LAMBDA elements; needs ag)
 *
 * A_1's column, E's column and P's column j are generated as the pass reaches
 * them, used for every vector and dropped after, so memory is independent of
 * m, and generating the columns, which costs more than using them, is shared
 * by the vectors of one pass.
 */
static void linear_passes(const lin_job_t *jobs, slong nj, const evmlr_zk_stmt_struct *st,
                          const uint8_t pp[32], const aggr_t *ag) {
    const slong m = st->m, rows = st->rows, m1 = m + rows;
    const slong per = ZK_KAPPA + ZK_LAMBDA + rows; // accumulators per job: A, P, E
    evmlr_zk_acc_t *acc = flint_malloc(nj * per * sizeof(evmlr_zk_acc_t));
    evmlr_zk_ntt_t *vj = flint_malloc(nj * sizeof(evmlr_zk_ntt_t)), x;
    nmod_poly_struct *col = vec_init(rows), *P = vec_init(ZK_LAMBDA);
    uint8_t *r = NULL;
    nmod_poly_t a;
    int what = 0;

    for (slong b = 0; b < nj; b++) what |= jobs[b].what;
    if (what & LIN_P) r = flint_malloc(ZK_PROJ_BYTES);
    evmlr_zk_init(a);
    for (slong i = 0; i < nj * per; i++) evmlr_zk_acc_init(&acc[i]);
#define ACC_A(b, i) (&acc[(b) * per + (i)])
#define ACC_P(b, l) (&acc[(b) * per + ZK_KAPPA + (l)])
#define ACC_E(b, i) (&acc[(b) * per + ZK_KAPPA + ZK_LAMBDA + (i)])

    for (slong j = 0; j < m1; j++) {
        for (slong b = 0; b < nj; b++) evmlr_zk_ntt(&vj[b], jobs[b].v1 + j);
        if (what & LIN_A) {
            for (slong i = 0; i < ZK_KAPPA; i++) {
                expand(a, pp, DOM_A1, i, j);
                evmlr_zk_ntt(&x, a);
                for (slong b = 0; b < nj; b++) {
                    if (jobs[b].what & LIN_A) evmlr_zk_acc_addmul(ACC_A(b, i), &x, &vj[b]);
                }
            }
        }
        if ((what & LIN_E) && j < m) {
            uint32_t mask = st->column(col, j, st);

            for (slong i = 0; i < rows; i++) {
                if (mask & (1u << i)) {
                    evmlr_zk_ntt(&x, col + i);
                    for (slong b = 0; b < nj; b++) {
                        if (jobs[b].what & LIN_E) evmlr_zk_acc_addmul(ACC_E(b, i), &x, &vj[b]);
                    }
                }
            }
        }
        if (what & LIN_P) {
            proj_codes(r, ag->seed[j < m ? 0 : 1], j);
            aggr_P_column(P, ag, r, j < m);
            for (slong l = 0; l < ZK_LAMBDA; l++) {
                evmlr_zk_ntt(&x, P + l);
                for (slong b = 0; b < nj; b++) {
                    if (jobs[b].what & LIN_P) evmlr_zk_acc_addmul(ACC_P(b, l), &x, &vj[b]);
                }
            }
        }
    }
    for (slong b = 0; b < nj; b++) {
        const lin_job_t *jb = &jobs[b];

        if (jb->what & LIN_A) {
            for (slong i = 0; i < ZK_KAPPA; i++) {
                if (jb->v2 != NULL) {
                    for (slong j = 0; j < ZK_M2; j++) {
                        expand(a, pp, DOM_A2, i, j);
                        evmlr_zk_ntt(&x, a);
                        evmlr_zk_ntt(&vj[0], jb->v2 + j);
                        evmlr_zk_acc_addmul(ACC_A(b, i), &x, &vj[0]);
                    }
                }
                evmlr_zk_acc_get(jb->outA + i, ACC_A(b, i));
            }
        }
        if (jb->what & LIN_E) {
            for (slong i = 0; i < rows; i++) {
                evmlr_zk_acc_get(jb->outE + i, ACC_E(b, i));
                nmod_poly_scalar_mul_nmod(a, jb->v1 + m + i, MOD_Q);
                nmod_poly_sub(jb->outE + i, jb->outE + i, a);
            }
        }
        if (jb->what & LIN_P) {
            for (slong l = 0; l < ZK_LAMBDA; l++) evmlr_zk_acc_get(jb->outP + l, ACC_P(b, l));
        }
    }
#undef ACC_A
#undef ACC_P
#undef ACC_E

    for (slong i = 0; i < nj * per; i++) evmlr_zk_acc_clear(&acc[i]);
    flint_free(acc);
    flint_free(vj);
    vec_clear(col, rows);
    vec_clear(P, ZK_LAMBDA);
    if (r != NULL) flint_free(r);
    nmod_poly_clear(a);
}

/* linear_passes for one vector. */
static void linear_pass(nmod_poly_struct *outA, nmod_poly_struct *outE, nmod_poly_struct *outP,
                        const nmod_poly_struct *v1, const nmod_poly_struct *v2,
                        const evmlr_zk_stmt_struct *st, const uint8_t pp[32],
                        const aggr_t *ag, int what) {
    lin_job_t job = { v1, v2, outA, outE, outP, what };

    linear_passes(&job, 1, st, pp, ag);
}

/*============================================================================*/
/* Widths and bounds                                                          */
/*============================================================================*/

void evmlr_zk_sigmas(double sigma[5], slong m, double k_bound) {
    double t = 2.0 * ZK_NU; // ||c||_1, which bounds ||c v|| / ||v||
    double s_bound = sqrt((double) m * DEGREE_N); // s is binary

    sigma[0] = ZK_ALPHA_S * t * s_bound;
    sigma[1] = ZK_ALPHA_K * t * k_bound;
    sigma[2] = ZK_ALPHA_2 * t * sqrt((double) ZK_M2 * DEGREE_N); // s_2 is ternary
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

/* LNP22, Lemma 2.9: for R with entries from Bin_1 (0 with probability 1/2,
 * +-1 with 1/4 each), any v of dimension d over [+-P/2] with ||v|| >= b, where
 * b <= P / (41 d), and any y: ||R v + y mod P|| >= b sqrt(26) / 2 except with
 * probability 2^-128. (It rests on Lemma 2.8, which substitutes the normal
 * distribution for Bin_1 heuristically.) So a verified ||z_3|| certifies
 * ||v|| < 2 ||z_3|| / sqrt(26), provided P = p is at least 41 d times that. */
void evmlr_zk_certified(double bound[2], slong m, double k_bound) {
    double sigma[5];

    evmlr_zk_sigmas(sigma, m, k_bound);
    bound[0] = 2.0 * sqrt(bound3(sigma[3])) / sqrt(26.0);
    bound[1] = 2.0 * sqrt(bound3(sigma[4])) / sqrt(26.0);
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
    // The projection lemma's condition b <= p / (41 d), for s of dimension
    // m n and k of dimension rows n.
    int jl = 41.0 * mn * B[0] <= (double) ZK_P && 41.0 * rows * DEGREE_N * B[1] <= (double) ZK_P;
    return lin < ZK_P / 2.0 && bin < (double) ZK_P && jl
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

/*============================================================================*/
/* Encoding                                                                   */
/*============================================================================*/

/* Bits, least significant first within each byte. With buf NULL a writer
 * only counts. */
typedef struct {
    uint8_t *buf;
    size_t bits;
} bit_writer_t;

typedef struct {
    const uint8_t *buf;
    size_t len, bits; /* len in bytes, bits read so far */
    int ok;
} bit_reader_t;

static void put_bits(bit_writer_t *w, uint64_t v, int nbits) {
    for (int i = 0; i < nbits; i++, w->bits++) {
        if (w->buf != NULL && ((v >> i) & 1)) {
            w->buf[w->bits / 8] |= (uint8_t) (1u << (w->bits % 8));
        }
    }
}

static uint64_t get_bits(bit_reader_t *r, int nbits) {
    uint64_t v = 0;

    if (r->bits + (size_t) nbits > 8 * r->len) {
        r->ok = 0;
        return 0;
    }
    for (int i = 0; i < nbits; i++, r->bits++) {
        v |= (uint64_t) ((r->buf[r->bits / 8] >> (r->bits % 8)) & 1) << i;
    }
    return v;
}

/* Residues mod p, uniform for all the encoder knows: ZK_P_BITS bits each. */
static void put_uniform(bit_writer_t *w, const nmod_poly_t a, slong from) {
    for (slong i = from; i < DEGREE_N; i++) put_bits(w, nmod_poly_get_coeff_ui(a, i), ZK_P_BITS);
}

static void get_uniform(bit_reader_t *r, nmod_poly_t a, slong from) {
    nmod_poly_zero(a);
    for (slong i = from; i < DEGREE_N; i++) {
        uint64_t v = get_bits(r, ZK_P_BITS);

        if (v >= ZK_P) r->ok = 0;
        nmod_poly_set_coeff_ui(a, i, v % ZK_P);
    }
}

/* Gaussian values of width sigma, Rice-coded: the low k bits of |x|, then
 * |x| >> k in unary (that many ones, then a zero), then a sign bit when x is
 * not zero. A quotient of ZK_RICE_ESC or more is written as ZK_RICE_ESC ones
 * and |x| in ZK_P_BITS bits, so that every value below p/2 has exactly one
 * encoding, however unlikely. */
#define ZK_RICE_ESC 64

static int rice_k(double sigma) {
    // Minimises k + E|x| / 2^k for |x| half-normal of scale sigma, at
    // 2^k = sigma sqrt(2 / pi) ln 2.
    double k = floor(log2(sigma * sqrt(2.0 / M_PI) * M_LN2) + 0.5);

    return (k < 0) ? 0 : (int) k;
}

static void put_rice(bit_writer_t *w, slong x, int k) {
    uint64_t a = (uint64_t) FLINT_ABS(x), hi = a >> k;

    put_bits(w, a, k);
    if (hi < ZK_RICE_ESC) {
        put_bits(w, (1ULL << hi) - 1, (int) hi + 1);
    } else {
        put_bits(w, ~0ULL, ZK_RICE_ESC);
        put_bits(w, a, ZK_P_BITS);
    }
    if (x != 0) put_bits(w, x < 0, 1);
}

static slong get_rice(bit_reader_t *r, int k) {
    uint64_t a = get_bits(r, k), hi = 0;

    while (r->ok && hi < ZK_RICE_ESC && get_bits(r, 1)) hi++;
    if (hi < ZK_RICE_ESC) {
        a |= hi << k;
    } else {
        uint64_t low = a;

        a = get_bits(r, ZK_P_BITS);
        // The escape is only for quotients that unary does not take, and its
        // low bits must agree with the ones already read.
        if ((a >> k) < ZK_RICE_ESC || (a & ((1ULL << k) - 1)) != low) r->ok = 0;
    }
    if (a > ZK_P / 2) {
        r->ok = 0;
        return 0;
    }
    if (a != 0 && get_bits(r, 1)) return -(slong) a;
    return (slong) a;
}

static void put_gauss(bit_writer_t *w, const nmod_poly_struct *v, slong len, double sigma) {
    int k = rice_k(sigma);

    for (slong j = 0; j < len; j++) {
        for (slong i = 0; i < DEGREE_N; i++) put_rice(w, centre(nmod_poly_get_coeff_ui(v + j, i)), k);
    }
}

static void get_gauss(bit_reader_t *r, nmod_poly_struct *v, slong len, double sigma) {
    int k = rice_k(sigma);

    for (slong j = 0; j < len; j++) {
        nmod_poly_zero(v + j);
        for (slong i = 0; i < DEGREE_N; i++) nmod_poly_set_coeff_ui(v + j, i, from_signed(get_rice(r, k)));
    }
}

/*
 * The proof in a fixed order: t_A, t_B and t_G, h without its constant
 * coefficients (the verifier needs them zero, so they are not sent), the
 * hash, then z_3, z_1 and z_2 Rice-coded with the widths of their blocks,
 * which the statement's shape fixes. The last byte is padded with zeros.
 */
static size_t encode(uint8_t *buf, const evmlr_zk_proof_t pi, double k_bound) {
    bit_writer_t w = { buf, 0 };
    double sigma[5];
    const slong m = pi->m;

    evmlr_zk_sigmas(sigma, m, k_bound);
    for (slong i = 0; i < ZK_KAPPA; i++) put_uniform(&w, pi->tA + i, 0);
    for (slong i = 0; i < ZK_SLOTS; i++) put_uniform(&w, pi->tB + i, 0);
    put_uniform(&w, pi->tG, 0);
    for (slong l = 0; l < ZK_LAMBDA; l++) put_uniform(&w, pi->h + l, 1);
    for (slong i = 0; i < SHA256HashSize; i++) put_bits(&w, pi->hash[i], 8);
    for (slong i = 0; i < 2 * ZK_PROJ; i++) put_rice(&w, pi->z3[i], rice_k(sigma[3 + (i >= ZK_PROJ)]));
    put_gauss(&w, pi->z1, m, sigma[0]);
    put_gauss(&w, pi->z1 + m, pi->rows, sigma[1]);
    put_gauss(&w, pi->z2, ZK_M2, sigma[2]);
    return (w.bits + 7) / 8;
}

size_t evmlr_zk_proof_size(const evmlr_zk_proof_t pi, const evmlr_zk_stmt_struct *st) {
    return encode(NULL, pi, st->k_bound);
}

size_t evmlr_zk_proof_encode(uint8_t *buf, const evmlr_zk_proof_t pi,
                             const evmlr_zk_stmt_struct *st) {
    size_t len = encode(NULL, pi, st->k_bound);

    memset(buf, 0, len);
    return encode(buf, pi, st->k_bound);
}

int evmlr_zk_proof_decode(evmlr_zk_proof_t pi, const uint8_t *buf, size_t len,
                          const evmlr_zk_stmt_struct *st) {
    bit_reader_t r = { buf, len, 0, 1 };
    double sigma[5];
    const slong m = st->m;

    if (pi->m != st->m || pi->rows != st->rows) return 0;
    evmlr_zk_sigmas(sigma, m, st->k_bound);
    for (slong i = 0; i < ZK_KAPPA; i++) get_uniform(&r, pi->tA + i, 0);
    for (slong i = 0; i < ZK_SLOTS; i++) get_uniform(&r, pi->tB + i, 0);
    get_uniform(&r, pi->tG, 0);
    for (slong l = 0; l < ZK_LAMBDA; l++) get_uniform(&r, pi->h + l, 1);
    for (slong i = 0; i < SHA256HashSize; i++) pi->hash[i] = (uint8_t) get_bits(&r, 8);
    for (slong i = 0; i < 2 * ZK_PROJ; i++) pi->z3[i] = get_rice(&r, rice_k(sigma[3 + (i >= ZK_PROJ)]));
    get_gauss(&r, pi->z1, m, sigma[0]);
    get_gauss(&r, pi->z1 + m, pi->rows, sigma[1]);
    get_gauss(&r, pi->z2, ZK_M2, sigma[2]);
    // Canonical: every byte used, and the padding of the last one zero.
    if (r.ok && (r.bits + 7) / 8 != len) r.ok = 0;
    if (r.ok && r.bits % 8 != 0 && (buf[len - 1] >> (r.bits % 8)) != 0) r.ok = 0;
    return r.ok;
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

/* The exponent of one block's part of the rejection test,
 * (-2<z, v> + ||v||^2) / (2 sigma^2), for the masked opening z = y + v. */
static double rejection_exp(const nmod_poly_struct *z, const nmod_poly_struct *v, slong len,
                            double sigma) {
    return (-2.0 * vec_dot(z, v, len) + vec_norm2(v, len)) / (2.0 * sigma * sigma);
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

/* The binary claim's quadratic form, sum_j sigma(a_j)(b_j - x 1) over the
 * first m elements, with 1 the all-ones polynomial: F for (a, b, x) = (s, s, 1),
 * and what the verifier evaluates for (z, z, c). */
static void quad(nmod_poly_t r, const nmod_poly_struct *a, const nmod_poly_struct *b,
                 const nmod_poly_t x, slong m) {
    nmod_poly_t xones, t;
    evmlr_zk_acc_t acc;
    evmlr_zk_ntt_t X, Y;

    evmlr_zk_init(xones);
    evmlr_zk_init(t);
    evmlr_zk_acc_init(&acc);
    evmlr_zk_ones(xones);
    evmlr_zk_mul(xones, xones, x);
    for (slong j = 0; j < m; j++) {
        evmlr_zk_sigma(t, a + j);
        evmlr_zk_ntt(&X, t);
        nmod_poly_sub(t, b + j, xones);
        evmlr_zk_ntt(&Y, t);
        evmlr_zk_acc_addmul(&acc, &X, &Y);
    }
    evmlr_zk_acc_get(r, &acc);
    evmlr_zk_acc_clear(&acc);
    nmod_poly_clear(xones);
    nmod_poly_clear(t);
}

/* G0 = sum_j sigma(y_j)(s_j - 1) + sigma(s_j) y_j and G1 = sum_j sigma(y_j) y_j,
 * the coefficients of c and 1 in sum_j sigma(z_j)(z_j - c 1) for z = y + c s,
 * whose coefficient of c^2 is F (sigma(c) = c). One pass, four transforms per
 * element. */
static void garbage(nmod_poly_t G0, nmod_poly_t G1, const nmod_poly_struct *y,
                    const nmod_poly_struct *s, slong m) {
    nmod_poly_t ones, t;
    evmlr_zk_acc_t acc0, acc1;
    evmlr_zk_ntt_t Tsy, Ty, Tsm, Tss;

    evmlr_zk_init(ones);
    evmlr_zk_init(t);
    evmlr_zk_ones(ones);
    evmlr_zk_acc_init(&acc0);
    evmlr_zk_acc_init(&acc1);
    for (slong j = 0; j < m; j++) {
        evmlr_zk_sigma(t, y + j);
        evmlr_zk_ntt(&Tsy, t);
        evmlr_zk_ntt(&Ty, y + j);
        nmod_poly_sub(t, s + j, ones);
        evmlr_zk_ntt(&Tsm, t);
        evmlr_zk_sigma(t, s + j);
        evmlr_zk_ntt(&Tss, t);
        evmlr_zk_acc_addmul(&acc0, &Tsy, &Tsm);
        evmlr_zk_acc_addmul(&acc0, &Tss, &Ty);
        evmlr_zk_acc_addmul(&acc1, &Tsy, &Ty);
    }
    evmlr_zk_acc_get(G0, &acc0);
    evmlr_zk_acc_get(G1, &acc1);
    evmlr_zk_acc_clear(&acc0);
    evmlr_zk_acc_clear(&acc1);
    nmod_poly_clear(ones);
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
    linear_pass(NULL, e, NULL, s1, NULL, st, NULL, NULL, LIN_E); // k is still 0
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
    nmod_poly_struct *y1 = vec_init(ZK_BATCH * m1), *y2 = vec_init(ZK_BATCH * ZK_M2);
    nmod_poly_struct *msg = vec_init(ZK_SLOTS), *e = vec_init(rows);
    nmod_poly_struct *w = vec_init(ZK_BATCH * ZK_KAPPA), *wl = vec_init(ZK_LAMBDA);
    nmod_poly_struct *Pv = vec_init(ZK_LAMBDA);
    nmod_poly_struct *ey = vec_init(ZK_BATCH * rows), *Py = vec_init(ZK_BATCH * ZK_LAMBDA);
    nmod_poly_struct *cs1 = vec_init(m1), *cs2 = vec_init(ZK_M2);
    nmod_poly_t c, t, u, vF, G0, G1, G1y, tau;
    uint8_t h0[32], seed_s[32], seed_k[32], h2[32];
    slong y3[ZK_PROJ], rs[ZK_PROJ];
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
    evmlr_zk_init(G1y);
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
    linear_pass(pi->tA, NULL, NULL, s1, s2, st, pp, NULL, LIN_A);
    for (slong l = 0; l < ZK_SLOTS; l++) {
        bdlop_row(pi->tB + l, l, s2, pp);
        if (l != ZK_SLOT_YS && l != ZK_SLOT_YK) {
            nmod_poly_add(pi->tB + l, pi->tB + l, msg + l);
        }
    }
    hash_commitment(h0, pp, st, pi);

    // The projections, each redrawn with its own slot until it passes its
    // rejection test: first s's, over every element of the witness, then k's,
    // over the rows of the carry. Only the slot changes between tries;
    // rejected tries are never published, so reusing s_2 reveals nothing.
    for (int which = 0; which < 2; which++) {
        const slong X = which ? ZK_SLOT_YK : ZK_SLOT_YS;
        slong *z = pi->z3 + which * ZK_PROJ;
        uint8_t *seed = which ? seed_k : seed_s;

        nmod_poly_set(u, pi->tB + X); // <b_X, s_2>
        ok = 0;
        for (int tries = 0; tries < ZK_PROJ_TRIES && !ok; tries++) {
            nmod_poly_zero(msg + X);
            for (slong i = 0; i < ZK_PROJ; i++) {
                y3[i] = zk_gauss(&dg[3 + which]);
                nmod_poly_set_coeff_ui(msg + X, i, from_signed(y3[i]));
            }
            nmod_poly_add(pi->tB + X, u, msg + X);
            if (which == 0) {
                hash_seed_s(seed, h0, pi);
                proj_apply(rs, s1, 0, m, seed);
            } else {
                hash_seed_k(seed, seed_s, pi);
                proj_apply(rs, s1, m, m1, seed);
            }
            for (slong i = 0; i < ZK_PROJ; i++) {
                z[i] = rs[i] + y3[i];
            }
            ok = rejection3(z, rs, sigma[3 + which]);
        }
        if (!ok) goto end;
    }

    // h_l = g_l + nu_l F + sum_r sigma(alpha_lr) e_r + sum_j P_lj s1_j
    //       + M_s,l Y_s + M_k,l Y_k - Z_l,
    // whose constant coefficient is zero exactly when s is binary,
    // e = E s - q k - t is zero, and both projections are honest.
    hash_projection(h2, seed_k, pi->z3);
    aggr_init(&ag, h2, pi->z3, seed_s, seed_k, rows);
    have_aggr = 1;
    for (int first = 1, done = 0; !done; first = 0) {
        // Masks for ZK_BATCH candidates, and their linear first messages in
        // one pass, which the first time also gives s's part of h.
        lin_job_t jobs[ZK_BATCH + 1];
        slong nj = 0;

        if (first) {
            jobs[nj++] = (lin_job_t) { s1, NULL, NULL, e, Pv, LIN_E | LIN_P };
        }
        for (slong b = 0; b < ZK_BATCH; b++) {
            nmod_poly_struct *yb1 = y1 + b * m1, *yb2 = y2 + b * ZK_M2;

            sample_gauss(yb1, m, &dg[0]);
            sample_gauss(yb1 + m, rows, &dg[1]);
            sample_gauss(yb2, ZK_M2, &dg[2]);
            jobs[nj++] = (lin_job_t) { yb1, yb2, w + b * ZK_KAPPA, ey + b * rows,
                                       Py + b * ZK_LAMBDA, LIN_A | LIN_E | LIN_P };
        }
        linear_passes(jobs, nj, st, pp, &ag);

        if (first) {
            for (slong r = 0; r < rows; r++) {
                evmlr_zk_lift(t, st->t + r);
                nmod_poly_sub(e + r, e + r, t);
            }
            for (slong l = 0; l < ZK_LAMBDA; l++) {
                aggr_value(t, &ag, l, e, Pv + l);
                nmod_poly_add(pi->h + l, msg + l, t);
                nmod_poly_scalar_mul_nmod(t, msg + ZK_SLOT_F, ag.nu[l]);
                nmod_poly_add(pi->h + l, pi->h + l, t);
                evmlr_zk_mul(u, ag.M + l, msg + ZK_SLOT_YS);
                nmod_poly_add(pi->h + l, pi->h + l, u);
                evmlr_zk_mul(u, ag.M + ZK_LAMBDA + l, msg + ZK_SLOT_YK);
                nmod_poly_add(pi->h + l, pi->h + l, u);
                nmod_poly_set_coeff_ui(pi->h + l, 0,
                        nmod_sub(nmod_poly_get_coeff_ui(pi->h + l, 0), ag.Z[l], *evmlr_zk_mod()));
            }
        }

        for (slong b = 0; b < ZK_BATCH && !done; b++) {
            const nmod_poly_struct *yb1 = y1 + b * m1, *yb2 = y2 + b * ZK_M2;

            // The garbage term G = G0 + v_F, committed in row ZK_SLOT_G, and
            // the first messages:
            //   w   = A_1 y_1 + A_2 y_2,
            //   w_l = v_gl + nu_l v_F + M_l v_Y - sum_r sigma(alpha_lr)(E_r y_s - q y_k,r)
            //         - sum_j P_lj y1_j,
            //   tau = v_G + G1,
            // with v_X = <b_X, y_2> the mask of slot X.
            garbage(G0, G1, yb1, s1, m);
            bdlop_row(vF, ZK_SLOT_F, yb2, pp);
            bdlop_row(pi->tG, ZK_SLOT_G, s2, pp);
            nmod_poly_add(pi->tG, pi->tG, G0);
            nmod_poly_add(pi->tG, pi->tG, vF);
            bdlop_row(tau, ZK_SLOT_G, yb2, pp);
            nmod_poly_add(tau, tau, G1);
            bdlop_row(u, ZK_SLOT_YS, yb2, pp);
            bdlop_row(G1y, ZK_SLOT_YK, yb2, pp);
            for (slong l = 0; l < ZK_LAMBDA; l++) {
                bdlop_row(wl + l, l, yb2, pp);
                aggr_value(t, &ag, l, ey + b * rows, Py + b * ZK_LAMBDA + l);
                nmod_poly_sub(wl + l, wl + l, t);
                evmlr_zk_mul(t, ag.M + l, u);
                nmod_poly_add(wl + l, wl + l, t);
                evmlr_zk_mul(t, ag.M + ZK_LAMBDA + l, G1y);
                nmod_poly_add(wl + l, wl + l, t);
                nmod_poly_scalar_mul_nmod(t, vF, ag.nu[l]);
                nmod_poly_add(wl + l, wl + l, t);
            }
            hash_challenge(pi->hash, h2, pi, w + b * ZK_KAPPA, wl, tau);
            challenge_from(c, pi->hash);

            // z = y + c s, and one rejection test for all of it.
            for (slong j = 0; j < m1; j++) {
                evmlr_zk_mul(cs1 + j, c, s1 + j);
                nmod_poly_add(pi->z1 + j, yb1 + j, cs1 + j);
            }
            for (slong j = 0; j < ZK_M2; j++) {
                evmlr_zk_mul(cs2 + j, c, s2 + j);
                nmod_poly_add(pi->z2 + j, yb2 + j, cs2 + j);
            }
            done = accept(rejection_exp(pi->z1, cs1, m, sigma[0])
                          + rejection_exp(pi->z1 + m, cs1 + m, rows, sigma[1])
                          + rejection_exp(pi->z2, cs2, ZK_M2, sigma[2]), ZK_M);
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
    vec_clear(y1, ZK_BATCH * m1);
    vec_clear(y2, ZK_BATCH * ZK_M2);
    vec_clear(msg, ZK_SLOTS);
    vec_clear(e, rows);
    vec_clear(w, ZK_BATCH * ZK_KAPPA);
    vec_clear(wl, ZK_LAMBDA);
    vec_clear(Pv, ZK_LAMBDA);
    vec_clear(ey, ZK_BATCH * rows);
    vec_clear(Py, ZK_BATCH * ZK_LAMBDA);
    vec_clear(cs1, m1);
    vec_clear(cs2, ZK_M2);
    nmod_poly_clear(c);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
    nmod_poly_clear(vF);
    nmod_poly_clear(G0);
    nmod_poly_clear(G1);
    nmod_poly_clear(G1y);
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
    const slong m = st->m, rows = st->rows;
    nmod_poly_struct *w, *wl, *e, *Pv;
    nmod_poly_t c, t, u, uY, uYk, uF, tau;
    uint8_t h0[32], seed_s[32], seed_k[32], h2[32], h3[32];
    double sigma[5];
    aggr_t ag;
    int ok, norms, cts;

    if (pi->m != m || pi->rows != rows || !evmlr_zk_supported(m, rows, st->k_bound)) {
        return 0;
    }
    w = vec_init(ZK_KAPPA);
    Pv = vec_init(ZK_LAMBDA);
    wl = vec_init(ZK_LAMBDA);
    e = vec_init(rows);
    evmlr_zk_init(c);
    evmlr_zk_init(t);
    evmlr_zk_init(u);
    evmlr_zk_init(uY);
    evmlr_zk_init(uYk);
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
    hash_commitment(h0, pp, st, pi);
    hash_seed_s(seed_s, h0, pi);
    hash_seed_k(seed_k, seed_s, pi);
    hash_projection(h2, seed_k, pi->z3);
    aggr_init(&ag, h2, pi->z3, seed_s, seed_k, rows);
    linear_pass(w, e, Pv, pi->z1, pi->z2, st, pp, &ag, LIN_A | LIN_E | LIN_P);
    for (slong i = 0; i < ZK_KAPPA; i++) {
        evmlr_zk_mul(t, c, pi->tA + i);
        nmod_poly_sub(w + i, w + i, t);
    }
    for (slong r = 0; r < rows; r++) {
        evmlr_zk_lift(t, st->t + r);
        evmlr_zk_mul(t, t, c);
        nmod_poly_sub(e + r, e + r, t);
    }
    bdlop_open(uY, ZK_SLOT_YS, pi->tB + ZK_SLOT_YS, c, pi->z2, pp);
    bdlop_open(uYk, ZK_SLOT_YK, pi->tB + ZK_SLOT_YK, c, pi->z2, pp);
    bdlop_open(uF, ZK_SLOT_F, pi->tB + ZK_SLOT_F, c, pi->z2, pp);
    for (slong l = 0; l < ZK_LAMBDA; l++) {
        bdlop_open(u, l, pi->tB + l, c, pi->z2, pp);
        evmlr_zk_mul(wl + l, c, pi->h + l);
        nmod_poly_add(wl + l, wl + l, u);
        nmod_poly_scalar_mul_nmod(t, uF, ag.nu[l]);
        nmod_poly_add(wl + l, wl + l, t);
        evmlr_zk_mul(t, ag.M + l, uY);
        nmod_poly_add(wl + l, wl + l, t);
        evmlr_zk_mul(t, ag.M + ZK_LAMBDA + l, uYk);
        nmod_poly_add(wl + l, wl + l, t);
        nmod_poly_scalar_mul_nmod(t, c, ag.Z[l]);
        nmod_poly_add(wl + l, wl + l, t);
        aggr_value(t, &ag, l, e, Pv + l);
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
    vec_clear(Pv, ZK_LAMBDA);
    vec_clear(e, rows);
    nmod_poly_clear(c);
    nmod_poly_clear(t);
    nmod_poly_clear(u);
    nmod_poly_clear(uY);
    nmod_poly_clear(uYk);
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

static uint32_t dense_column(nmod_poly_struct *out, slong j, const evmlr_zk_stmt_struct *st) {
    const dense_t *d = (const dense_t *) st->data;

    for (slong r = 0; r < st->rows; r++) {
        evmlr_zk_lift(out + r, d->E + r * st->m + j);
    }
    return (1u << st->rows) - 1;
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
    st->column = dense_column;
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

    TEST_ONCE("the joint rejection test keeps the ratio M = 1.75 is set for") {
        double inv = 1.0 / (ZK_ALPHA_S * ZK_ALPHA_S) + 1.0 / (ZK_ALPHA_K * ZK_ALPHA_K)
                   + 1.0 / (ZK_ALPHA_2 * ZK_ALPHA_2);
        TEST_ASSERT(inv <= 1.0 / (ZK_ALPHA_RS * ZK_ALPHA_RS), end);
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

    TEST_BEGIN("a proof decodes from its encoding and verifies after") {
        TEST_ASSERT(evmlr_zk_prove(pi, s, &st, pp) == 1, end);
        size_t len = evmlr_zk_proof_size(pi, &st);
        uint8_t *buf = flint_malloc(len), *buf2 = flint_malloc(len);
        evmlr_zk_proof_t pi2;
        evmlr_zk_proof_init(pi2, st.m, st.rows);
        int ok = evmlr_zk_proof_encode(buf, pi, &st) == len;
        ok &= evmlr_zk_proof_decode(pi2, buf, len, &st);
        ok &= evmlr_zk_proof_encode(buf2, pi2, &st) == len && memcmp(buf, buf2, len) == 0;
        ok &= evmlr_zk_verify(pi2, &st, pp);
        evmlr_zk_proof_clear(pi2);
        flint_free(buf);
        flint_free(buf2);
        TEST_ASSERT(ok, end);
    } TEST_END;

    /* Truncated, extended, a residue past p, padding set; and any single bit
     * flipped either fails to decode or decodes to what encodes back to the
     * same bytes, so no proof has two encodings. */
    TEST_ONCE("only canonical encodings decode") {
        TEST_ASSERT(evmlr_zk_prove(pi, s, &st, pp) == 1, end);
        size_t len = evmlr_zk_proof_size(pi, &st);
        uint8_t *buf = flint_malloc(len + 1), *buf2 = flint_malloc(len + 1);
        evmlr_zk_proof_t pi2;
        evmlr_zk_proof_init(pi2, st.m, st.rows);
        evmlr_zk_proof_encode(buf, pi, &st);
        buf[len] = 0;
        int ok = evmlr_zk_proof_decode(pi2, buf, len, &st);
        ok &= !evmlr_zk_proof_decode(pi2, buf, len - 1, &st);
        ok &= !evmlr_zk_proof_decode(pi2, buf, len + 1, &st);
        memcpy(buf2, buf, len);
        for (int i = 0; i < ZK_P_BITS; i++) buf2[i / 8] |= (uint8_t) (1u << (i % 8));
        ok &= !evmlr_zk_proof_decode(pi2, buf2, len, &st);
        if (buf[len - 1] < 0x80) {
            memcpy(buf2, buf, len);
            buf2[len - 1] |= 0x80; // the padding, when there is any
            ok &= !evmlr_zk_proof_decode(pi2, buf2, len, &st);
        }
        int accepted = 0;
        for (int t = 0; t < 4000; t++) {
            size_t bit = n_randint(state, 8 * len);
            memcpy(buf2, buf, len);
            buf2[bit / 8] ^= (uint8_t) (1u << (bit % 8));
            if (evmlr_zk_proof_decode(pi2, buf2, len, &st)) {
                uint8_t *buf3 = flint_malloc(len + 64);
                memset(buf3, 0, len + 64);
                accepted++;
                ok &= evmlr_zk_proof_size(pi2, &st) == len;
                ok &= evmlr_zk_proof_encode(buf3, pi2, &st) == len && memcmp(buf2, buf3, len) == 0;
                flint_free(buf3);
            }
        }
        evmlr_zk_proof_clear(pi2);
        flint_free(buf);
        flint_free(buf2);
        TEST_ASSERT(ok && accepted > 0, end);
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

    TEST_ONCE("the certified bounds are LNP22's, and N = 1000 meets its condition") {
        // Lemma 2.9: ||v|| < 2 ||z|| / sqrt(26) for ||z|| at the verifier's
        // limit 1.7 sigma sqrt(256), where 41 d B <= p; at N = 1000 the
        // projection of s, d = (25 N + 48) n, needs p >= 2^51.6.
        double B[2], sigma[5];
        evmlr_zk_certified(B, st.m, st.k_bound);
        evmlr_zk_sigmas(sigma, st.m, st.k_bound);
        int ok = fabs(B[0] - 2.0 * 1.7 * 16.0 * sigma[3] / sqrt(26.0)) < 1e-6 * B[0];
        slong m = 25 * 1000 + 48;
        evmlr_zk_certified(B, m, 1.0);
        ok &= 41.0 * m * DEGREE_N * B[0] <= (double) ZK_P;
        ok &= log2(41.0 * m * DEGREE_N * B[0]) > 51.5;
        TEST_ASSERT(ok, end);
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
