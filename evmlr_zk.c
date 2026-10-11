#include "evmlr_zk.h"
#include "evmlr_crt.h"
#include "sha.h"
#include <string.h>
#include <immintrin.h>

#ifdef MAIN
#include "test.h"
#include "bench.h"
#include "flint/fmpz.h"
#include "flint/fmpz_poly.h"
#endif

static nmod_t zk_mod;
static nmod_poly_t zk_cyclo; // x^n + 1 mod p
static int zk_ready = 0;

static void zk_setup(void) {
    if (zk_ready) return;
    nmod_init(&zk_mod, ZK_P);
    nmod_poly_init(zk_cyclo, ZK_P);
    nmod_poly_set_coeff_ui(zk_cyclo, DEGREE_N, 1);
    nmod_poly_set_coeff_ui(zk_cyclo, 0, 1);
    zk_ready = 1;
}

const nmod_t *evmlr_zk_mod(void) {
    zk_setup();
    return &zk_mod;
}

void evmlr_zk_init(nmod_poly_t a) {
    nmod_poly_init(a, ZK_P);
}

/*============================================================================*/
/* The negacyclic NTT over four 31-bit primes, in AVX2                        */
/*============================================================================*/

/* Four primes 1 mod 2n = 1024 below 2^31, each with psi, a primitive 1024th
 * root of unity: psi^512 = -1, which is what makes the transform negacyclic.
 * Their product Q is 2^123.9998, above 2 ZK_NTT_ACC n (p/2)^2 = 2^123, so a
 * sum of ZK_NTT_ACC products of centred residues is determined by its
 * residues. Below 2^31, values in [0, 2q) fit 32-bit lanes, 8 to a vector. */
#define NP 4
static const uint32_t ntt_q[NP] = { 2147473409u, 2147415041u, 2147396609u, 2147389441u };
static const uint32_t ntt_psi[NP] = { 2094155704u, 101307741u, 1962207230u, 1133102181u };

static struct {
    uint32_t w[NP][DEGREE_N], wpre[NP][DEGREE_N];   /* psi^brv(k), and Shoup's floor(w 2^32 / q) */
    uint32_t wi[NP][DEGREE_N], wipre[NP][DEGREE_N]; /* psi^-brv(k), and Shoup's */
    /* The twiddles of the last three forward stages, t = 4, 2, 1, in the lane
     * order the shuffles leave each pair of vectors in. */
    uint32_t tw[3][NP][DEGREE_N / 16][8], twp[3][NP][DEGREE_N / 16][8];
    uint32_t twi[3][NP][DEGREE_N / 16][8], twip[3][NP][DEGREE_N / 16][8];
    uint32_t qinv[NP];          /* -q^-1 mod 2^32, for Montgomery's reduction */
    uint32_t fin[NP], finpre[NP]; /* 2^32 / n mod q: undoes the reduction's 2^-32, and scales by 1/n */
    uint32_t pmod[NP];          /* p mod q */
    uint32_t r26pre[NP];        /* Shoup's precomputation for 2^26 */
    uint32_t g[NP][NP], gpre[NP][NP]; /* q_j^-1 mod q_i, j < i, for Garner */
    ulong qqp[NP];              /* q_0 ... q_(i-1) mod p */
    unsigned __int128 qq[NP], Q, Qhalf;
    ulong Qp;                   /* Q mod p */
    slong sigma_perm[DEGREE_N]; /* slot of zeta^-1 for the slot of zeta */
    evmlr_zk_ntt_t ones;        /* the transform of 1 + x + ... + x^(n-1) */
    int ready;
} ntt;

static ulong bitrev9(ulong k) {
    ulong r = 0;

    for (int i = 0; i < 9; i++) r |= ((k >> i) & 1) << (8 - i);
    return r;
}

static uint32_t mulmod32(uint32_t a, uint32_t b, uint32_t q) {
    return (uint32_t) (((uint64_t) a * b) % q);
}

static uint32_t powmod32(uint32_t a, ulong e, uint32_t q) {
    uint32_t r = 1;

    for (; e; e >>= 1, a = mulmod32(a, a, q)) {
        if (e & 1) r = mulmod32(r, a, q);
    }
    return r;
}

static uint32_t shoup_pre(uint32_t w, uint32_t q) {
    return (uint32_t) (((uint64_t) w << 32) / q);
}

/* Shoup's w x mod q, in [0, q). */
static inline uint32_t shoup1(uint32_t w, uint32_t wp, uint32_t x, uint32_t q) {
    uint32_t r = w * x - (uint32_t) (((uint64_t) wp * x) >> 32) * q;

    return (r >= q) ? r - q : r;
}

/* x - q if x >= q, for x < 2^32: the subtraction wraps when x < q. */
static inline __m256i csub(__m256i x, __m256i q) {
    return _mm256_min_epu32(x, _mm256_sub_epi32(x, q));
}

/* The high 32 bits of a b in each lane. */
static inline __m256i mulhi32(__m256i a, __m256i b) {
    __m256i e = _mm256_srli_epi64(_mm256_mul_epu32(a, b), 32);
    __m256i o = _mm256_mul_epu32(_mm256_srli_epi64(a, 32), _mm256_srli_epi64(b, 32));

    return _mm256_blend_epi32(e, o, 0xAA);
}

/* Shoup's w x mod q, in [0, 2q), for any 32-bit x. */
static inline __m256i shoup(__m256i w, __m256i wp, __m256i x, __m256i q) {
    return _mm256_sub_epi32(_mm256_mullo_epi32(w, x), _mm256_mullo_epi32(mulhi32(wp, x), q));
}

/* Montgomery's x y 2^-32 mod q, in [0, 2q), for x, y < q. */
static inline __m256i redc(__m256i x, __m256i y, __m256i q, __m256i qinv) {
    __m256i pe = _mm256_mul_epu32(x, y);
    __m256i po = _mm256_mul_epu32(_mm256_srli_epi64(x, 32), _mm256_srli_epi64(y, 32));
    __m256i te = _mm256_add_epi64(pe, _mm256_mul_epu32(_mm256_mul_epu32(pe, qinv), q));
    __m256i to = _mm256_add_epi64(po, _mm256_mul_epu32(_mm256_mul_epu32(po, qinv), q));

    return _mm256_blend_epi32(_mm256_srli_epi64(te, 32), to, 0xAA);
}

/* A Cooley-Tukey butterfly on values in [0, 2q), which it keeps there. */
static inline void bf(__m256i *a, __m256i *b, __m256i w, __m256i wp, __m256i q) {
    __m256i t = csub(shoup(w, wp, *b, q), q);
    __m256i u = csub(*a, q);

    *a = _mm256_add_epi32(u, t);
    *b = _mm256_add_epi32(_mm256_sub_epi32(u, t), q);
}

/* Cooley-Tukey, natural order in, bit-reversed order out, values in [0, 2q)
 * in and [0, q) out. The stages with t >= 8 butterfly whole vectors; the last
 * three shuffle each pair of vectors so that the elements a butterfly joins
 * sit in the same lane of two vectors. */
static void ntt_forward(uint32_t *a, int p_) {
    const __m256i q = _mm256_set1_epi32((int) ntt_q[p_]);
    slong m, t;

    for (m = 1, t = DEGREE_N / 2; t >= 8; m <<= 1, t >>= 1) {
        for (slong i = 0; i < m; i++) {
            const __m256i w = _mm256_set1_epi32((int) ntt.w[p_][m + i]);
            const __m256i wp = _mm256_set1_epi32((int) ntt.wpre[p_][m + i]);
            uint32_t *x = a + 2 * i * t;

            for (slong j = 0; j < t; j += 8) {
                __m256i A = _mm256_loadu_si256((const __m256i *) (x + j));
                __m256i B = _mm256_loadu_si256((const __m256i *) (x + j + t));

                bf(&A, &B, w, wp, q);
                _mm256_storeu_si256((__m256i *) (x + j), A);
                _mm256_storeu_si256((__m256i *) (x + j + t), B);
            }
        }
    }
    for (slong k = 0; k < DEGREE_N / 16; k++) {
        __m256i A = _mm256_loadu_si256((const __m256i *) (a + 16 * k));
        __m256i B = _mm256_loadu_si256((const __m256i *) (a + 16 * k + 8));
        __m256i U, V, w, wp;

        // t = 4: (a0..a3 | b0..b3) against (a4..a7 | b4..b7).
        U = _mm256_permute2x128_si256(A, B, 0x20);
        V = _mm256_permute2x128_si256(A, B, 0x31);
        w = _mm256_loadu_si256((const __m256i *) ntt.tw[0][p_][k]);
        wp = _mm256_loadu_si256((const __m256i *) ntt.twp[0][p_][k]);
        bf(&U, &V, w, wp, q);
        A = _mm256_permute2x128_si256(U, V, 0x20);
        B = _mm256_permute2x128_si256(U, V, 0x31);
        // t = 2: (a0 a1 b0 b1 | a4 a5 b4 b5) against (a2 a3 b2 b3 | a6 a7 b6 b7).
        U = _mm256_unpacklo_epi64(A, B);
        V = _mm256_unpackhi_epi64(A, B);
        w = _mm256_loadu_si256((const __m256i *) ntt.tw[1][p_][k]);
        wp = _mm256_loadu_si256((const __m256i *) ntt.twp[1][p_][k]);
        bf(&U, &V, w, wp, q);
        A = _mm256_unpacklo_epi64(U, V);
        B = _mm256_unpackhi_epi64(U, V);
        // t = 1: (a0 a2 b0 b2 | a4 a6 b4 b6) against (a1 a3 b1 b3 | a5 a7 b5 b7).
        U = _mm256_castps_si256(_mm256_shuffle_ps(_mm256_castsi256_ps(A), _mm256_castsi256_ps(B), 0x88));
        V = _mm256_castps_si256(_mm256_shuffle_ps(_mm256_castsi256_ps(A), _mm256_castsi256_ps(B), 0xDD));
        w = _mm256_loadu_si256((const __m256i *) ntt.tw[2][p_][k]);
        wp = _mm256_loadu_si256((const __m256i *) ntt.twp[2][p_][k]);
        bf(&U, &V, w, wp, q);
        A = _mm256_unpacklo_epi32(U, V);
        B = _mm256_unpackhi_epi32(U, V);
        _mm256_storeu_si256((__m256i *) (a + 16 * k), csub(A, q));
        _mm256_storeu_si256((__m256i *) (a + 16 * k + 8), csub(B, q));
    }
}

/* A Gentleman-Sande butterfly on values in [0, q), which it keeps there. */
static inline void ibf(__m256i *a, __m256i *b, __m256i w, __m256i wp, __m256i q) {
    __m256i s = csub(_mm256_add_epi32(*a, *b), q);
    __m256i d = _mm256_add_epi32(_mm256_sub_epi32(*a, *b), q);

    *a = s;
    *b = csub(shoup(w, wp, d, q), q);
}

/* Gentleman-Sande, bit-reversed order in, natural order out, for values
 * below q, scaled by 2^32 / n: what a sum of Montgomery products needs. The
 * first three stages undo the forward transform's last three shuffles. */
static void ntt_inverse(uint32_t *a, int p_) {
    const __m256i q = _mm256_set1_epi32((int) ntt_q[p_]);
    slong m, t;

    for (slong k = 0; k < DEGREE_N / 16; k++) {
        __m256i A = _mm256_loadu_si256((const __m256i *) (a + 16 * k));
        __m256i B = _mm256_loadu_si256((const __m256i *) (a + 16 * k + 8));
        __m256i U, V, w, wp;

        U = _mm256_castps_si256(_mm256_shuffle_ps(_mm256_castsi256_ps(A), _mm256_castsi256_ps(B), 0x88));
        V = _mm256_castps_si256(_mm256_shuffle_ps(_mm256_castsi256_ps(A), _mm256_castsi256_ps(B), 0xDD));
        w = _mm256_loadu_si256((const __m256i *) ntt.twi[2][p_][k]);
        wp = _mm256_loadu_si256((const __m256i *) ntt.twip[2][p_][k]);
        ibf(&U, &V, w, wp, q);
        A = _mm256_unpacklo_epi32(U, V);
        B = _mm256_unpackhi_epi32(U, V);
        U = _mm256_unpacklo_epi64(A, B);
        V = _mm256_unpackhi_epi64(A, B);
        w = _mm256_loadu_si256((const __m256i *) ntt.twi[1][p_][k]);
        wp = _mm256_loadu_si256((const __m256i *) ntt.twip[1][p_][k]);
        ibf(&U, &V, w, wp, q);
        A = _mm256_unpacklo_epi64(U, V);
        B = _mm256_unpackhi_epi64(U, V);
        U = _mm256_permute2x128_si256(A, B, 0x20);
        V = _mm256_permute2x128_si256(A, B, 0x31);
        w = _mm256_loadu_si256((const __m256i *) ntt.twi[0][p_][k]);
        wp = _mm256_loadu_si256((const __m256i *) ntt.twip[0][p_][k]);
        ibf(&U, &V, w, wp, q);
        _mm256_storeu_si256((__m256i *) (a + 16 * k), _mm256_permute2x128_si256(U, V, 0x20));
        _mm256_storeu_si256((__m256i *) (a + 16 * k + 8), _mm256_permute2x128_si256(U, V, 0x31));
    }
    for (m = DEGREE_N / 16, t = 8; m >= 1; m >>= 1, t <<= 1) {
        for (slong i = 0; i < m; i++) {
            const __m256i w = _mm256_set1_epi32((int) ntt.wi[p_][m + i]);
            const __m256i wp = _mm256_set1_epi32((int) ntt.wipre[p_][m + i]);
            uint32_t *x = a + 2 * i * t;

            for (slong j = 0; j < t; j += 8) {
                __m256i A = _mm256_loadu_si256((const __m256i *) (x + j));
                __m256i B = _mm256_loadu_si256((const __m256i *) (x + j + t));

                ibf(&A, &B, w, wp, q);
                _mm256_storeu_si256((__m256i *) (x + j), A);
                _mm256_storeu_si256((__m256i *) (x + j + t), B);
            }
        }
    }
    {
        const __m256i f = _mm256_set1_epi32((int) ntt.fin[p_]);
        const __m256i fp = _mm256_set1_epi32((int) ntt.finpre[p_]);

        for (slong j = 0; j < DEGREE_N; j += 8) {
            __m256i *x = (__m256i *) (a + j);

            _mm256_storeu_si256(x, csub(shoup(f, fp, _mm256_loadu_si256(x), q), q));
        }
    }
}

/* The twiddle lanes of the last three stages, for the pair of vectors k:
 * which group of stage t's each lane joins. */
static slong last_group(int s, slong k, int lane) {
    static const int g4[8] = { 0, 0, 0, 0, 1, 1, 1, 1 };
    static const int g2[8] = { 0, 0, 2, 2, 1, 1, 3, 3 };
    static const int g1[8] = { 0, 1, 4, 5, 2, 3, 6, 7 };

    if (s == 0) return 64 + 2 * k + g4[lane];
    if (s == 1) return 128 + 4 * k + g2[lane];
    return 256 + 8 * k + g1[lane];
}

static void ntt_setup(void) {
    _Static_assert(DEGREE_N == 512, "the NTT is written for n = 512");
    if (ntt.ready) return;
    zk_setup();
    for (int p_ = 0; p_ < NP; p_++) {
        const uint32_t q = ntt_q[p_], psi = ntt_psi[p_], psii = (uint32_t) n_invmod(psi, q);
        uint32_t inv = q;

        for (ulong k = 0; k < DEGREE_N; k++) {
            const ulong e = bitrev9(k);

            ntt.w[p_][k] = powmod32(psi, e, q);
            ntt.wpre[p_][k] = shoup_pre(ntt.w[p_][k], q);
            ntt.wi[p_][k] = powmod32(psii, e, q);
            ntt.wipre[p_][k] = shoup_pre(ntt.wi[p_][k], q);
        }
        for (int s = 0; s < 3; s++) {
            for (slong k = 0; k < DEGREE_N / 16; k++) {
                for (int l = 0; l < 8; l++) {
                    ntt.tw[s][p_][k][l] = ntt.w[p_][last_group(s, k, l)];
                    ntt.twp[s][p_][k][l] = ntt.wpre[p_][last_group(s, k, l)];
                    ntt.twi[s][p_][k][l] = ntt.wi[p_][last_group(s, k, l)];
                    ntt.twip[s][p_][k][l] = ntt.wipre[p_][last_group(s, k, l)];
                }
            }
        }
        for (int i = 0; i < 5; i++) inv *= 2 - q * inv; // Newton's iteration for q^-1 mod 2^32
        ntt.qinv[p_] = (uint32_t) -inv;
        ntt.fin[p_] = mulmod32((uint32_t) ((1ULL << 32) % q), (uint32_t) n_invmod(DEGREE_N, q), q);
        ntt.finpre[p_] = shoup_pre(ntt.fin[p_], q);
        ntt.pmod[p_] = (uint32_t) (ZK_P % q);
        ntt.r26pre[p_] = shoup_pre(1u << 26, q);
        for (int j = 0; j < p_; j++) {
            ntt.g[p_][j] = (uint32_t) n_invmod(ntt_q[j] % q, q);
            ntt.gpre[p_][j] = shoup_pre(ntt.g[p_][j], q);
        }
    }
    ntt.Q = 1;
    for (int p_ = 0; p_ < NP; p_++) {
        ntt.qq[p_] = ntt.Q;
        ntt.qqp[p_] = (ulong) (ntt.Q % ZK_P);
        ntt.Q *= ntt_q[p_];
    }
    ntt.Qhalf = ntt.Q / 2;
    ntt.Qp = (ulong) (ntt.Q % ZK_P);
    ntt.ready = 1;
    // Slot j of a transform holds the evaluation at some root zeta_j, which
    // the transform of x lists. sigma(a)(x) = a(x^-1) evaluates at zeta_j as a
    // does at zeta_j^-1, another root: so sigma permutes the slots, the same
    // way for every prime.
    {
        uint32_t zeta[DEGREE_N];

        for (slong j = 0; j < DEGREE_N; j++) zeta[j] = (j == 1);
        ntt_forward(zeta, 0);
        for (slong j = 0; j < DEGREE_N; j++) {
            ntt.sigma_perm[j] = -1;
            for (slong k = 0; k < DEGREE_N; k++) {
                if (mulmod32(zeta[j], zeta[k], ntt_q[0]) == 1) ntt.sigma_perm[j] = k;
            }
        }
        for (int p_ = 0; p_ < NP; p_++) {
            for (slong j = 0; j < DEGREE_N; j++) ntt.ones.v[p_][j] = 1;
            ntt_forward(ntt.ones.v[p_], p_);
        }
    }
}

/* Eight coefficients' low 32 bits, from two vectors of four 64-bit lanes. */
static inline __m256i pack32(__m256i lo, __m256i hi) {
    const __m256i idx = _mm256_setr_epi32(0, 2, 4, 6, 0, 2, 4, 6);

    return _mm256_permute2x128_si256(_mm256_permutevar8x32_epi32(lo, idx),
                                     _mm256_permutevar8x32_epi32(hi, idx), 0x20);
}

void evmlr_zk_ntt(evmlr_zk_ntt_t *r, const nmod_poly_t a) {
    ntt_setup();
    ulong v[DEGREE_N];
    const slong len = FLINT_MIN(nmod_poly_length(a), DEGREE_N);
    const __m256i half = _mm256_set1_epi64x((long long) (ZK_P / 2));
    const __m256i low26 = _mm256_set1_epi64x((1LL << 26) - 1);

    if (len > 0) memcpy(v, a->coeffs, len * sizeof(ulong));
    memset(v + len, 0, (DEGREE_N - len) * sizeof(ulong));
    // v mod q = 2^26 (v >> 26) + (v mod 2^26), and the centred residue of a
    // v > p/2 is v - p: subtract p mod q there.
    for (slong j = 0; j < DEGREE_N; j += 8) {
        const __m256i v0 = _mm256_loadu_si256((const __m256i *) (v + j));
        const __m256i v1 = _mm256_loadu_si256((const __m256i *) (v + j + 4));
        const __m256i hi = pack32(_mm256_srli_epi64(v0, 26), _mm256_srli_epi64(v1, 26));
        const __m256i lo = pack32(_mm256_and_si256(v0, low26), _mm256_and_si256(v1, low26));
        const __m256i neg = pack32(_mm256_cmpgt_epi64(v0, half), _mm256_cmpgt_epi64(v1, half));

        for (int p_ = 0; p_ < NP; p_++) {
            const __m256i q = _mm256_set1_epi32((int) ntt_q[p_]);
            __m256i x = csub(shoup(_mm256_set1_epi32(1 << 26), _mm256_set1_epi32((int) ntt.r26pre[p_]), hi, q), q);
            __m256i y;

            x = csub(_mm256_add_epi32(x, lo), q);
            y = csub(_mm256_add_epi32(x, _mm256_set1_epi32((int) (ntt_q[p_] - ntt.pmod[p_]))), q);
            _mm256_storeu_si256((__m256i *) (r->v[p_] + j), _mm256_blendv_epi8(x, y, neg));
        }
    }
    for (int p_ = 0; p_ < NP; p_++) ntt_forward(r->v[p_], p_);
}

void evmlr_zk_ntt_sigma(evmlr_zk_ntt_t *r, const evmlr_zk_ntt_t *a) {
    ntt_setup();
    for (int p_ = 0; p_ < NP; p_++) {
        for (slong j = 0; j < DEGREE_N; j++) r->v[p_][j] = a->v[p_][ntt.sigma_perm[j]];
    }
}

const evmlr_zk_ntt_t *evmlr_zk_ntt_ones(void) {
    ntt_setup();
    return &ntt.ones;
}

void evmlr_zk_ntt_sub(evmlr_zk_ntt_t *r, const evmlr_zk_ntt_t *a, const evmlr_zk_ntt_t *b) {
    for (int p_ = 0; p_ < NP; p_++) {
        const uint32_t q = ntt_q[p_];

        for (slong j = 0; j < DEGREE_N; j++) {
            uint32_t d = a->v[p_][j] + q - b->v[p_][j];

            r->v[p_][j] = (d >= q) ? d - q : d;
        }
    }
}

void evmlr_zk_ntt_const(evmlr_zk_ntt_t *r, ulong c) {
    ntt_setup();
    // A constant's transform is the constant in every slot, as a centred residue.
    for (int p_ = 0; p_ < NP; p_++) {
        const uint32_t q = ntt_q[p_];
        const uint32_t v = (c > ZK_P / 2) ? (q - (uint32_t) ((ZK_P - c) % q)) % q : (uint32_t) (c % q);

        for (slong j = 0; j < DEGREE_N; j++) r->v[p_][j] = v;
    }
}

void evmlr_zk_ntt_mul(evmlr_zk_ntt_t *r, const evmlr_zk_ntt_t *a, const evmlr_zk_ntt_t *b) {
    ntt_setup();
    for (int p_ = 0; p_ < NP; p_++) {
        const __m256i q = _mm256_set1_epi32((int) ntt_q[p_]);
        const __m256i qinv = _mm256_set1_epi32((int) ntt.qinv[p_]);

        for (slong j = 0; j < DEGREE_N; j += 8) {
            __m256i x = _mm256_loadu_si256((const __m256i *) (a->v[p_] + j));
            __m256i y = _mm256_loadu_si256((const __m256i *) (b->v[p_] + j));

            _mm256_storeu_si256((__m256i *) (r->v[p_] + j), csub(redc(x, y, q, qinv), q));
        }
    }
}

void evmlr_zk_intt(nmod_poly_t r, const evmlr_zk_ntt_t *a) {
    ntt_setup();
    uint32_t x[NP][DEGREE_N];
    const nmod_t pm = zk_mod;

    memcpy(x, a->v, sizeof(x));
    for (int p_ = 0; p_ < NP; p_++) ntt_inverse(x[p_], p_);
    nmod_poly_zero(r);
    nmod_poly_fit_length(r, DEGREE_N);
    for (slong j = 0; j < DEGREE_N; j++) {
        // Garner: y = t_0 + q_0 t_1 + q_0 q_1 t_2 + q_0 q_1 q_2 t_3 in [0, Q),
        // then the centred representative, reduced mod p.
        uint32_t tt[NP];
        unsigned __int128 y = 0;
        ulong v = 0;

        for (int i = 0; i < NP; i++) {
            const uint32_t q = ntt_q[i];
            uint32_t u = x[i][j];

            for (int k = 0; k < i; k++) {
                // t_k < q_k < 2 q, so one subtraction of q leaves t_k mod q.
                uint32_t tk = (tt[k] >= q) ? tt[k] - q : tt[k];
                uint32_t d = (u >= tk) ? u - tk : u + q - tk;

                u = shoup1(ntt.g[i][k], ntt.gpre[i][k], d, q);
            }
            tt[i] = u;
            y += ntt.qq[i] * u;
            v = nmod_add(v, nmod_mul(ntt.qqp[i], u, pm), pm);
        }
        if (y > ntt.Qhalf) v = nmod_sub(v, ntt.Qp, pm);
        r->coeffs[j] = v;
    }
    r->length = DEGREE_N;
    _nmod_poly_normalise(r);
}

void evmlr_zk_acc_init(evmlr_zk_acc_t *a) {
    nmod_poly_init(a->sum, ZK_P);
    evmlr_zk_acc_zero(a);
}

void evmlr_zk_acc_clear(evmlr_zk_acc_t *a) {
    nmod_poly_clear(a->sum);
}

void evmlr_zk_acc_zero(evmlr_zk_acc_t *a) {
    memset(a->acc, 0, sizeof(a->acc));
    a->count = 0;
    nmod_poly_zero(a->sum);
}

static void acc_flush(evmlr_zk_acc_t *a) {
    evmlr_zk_ntt_t x;
    nmod_poly_t t;

    if (a->count == 0) return;
    for (int p_ = 0; p_ < NP; p_++) {
        // 2^32 = c mod q for a small c = 2^32 - 2 q, so folding the high half
        // twice leaves less than q + 2 c, without a division.
        const uint64_t q = ntt_q[p_], c = (1ULL << 32) - 2 * q;

        for (slong j = 0; j < DEGREE_N; j++) {
            uint64_t r = a->acc[p_][j];

            r = (r >> 32) * c + (uint32_t) r;
            r = (r >> 32) * c + (uint32_t) r;
            while (r >= q) r -= q;
            x.v[p_][j] = (uint32_t) r;
        }
    }
    nmod_poly_init(t, ZK_P);
    evmlr_zk_intt(t, &x);
    nmod_poly_add(a->sum, a->sum, t);
    nmod_poly_clear(t);
    memset(a->acc, 0, sizeof(a->acc));
    a->count = 0;
}

void evmlr_zk_acc_addmul(evmlr_zk_acc_t *a, const evmlr_zk_ntt_t *x, const evmlr_zk_ntt_t *y) {
    // Each Montgomery product is below 2q < 2^32, so ZK_NTT_ACC of them sum in
    // 64 bits without reduction.
    _Static_assert(ZK_NTT_ACC <= (1L << 31), "the sums would overflow 64 bits");
    ntt_setup();
    if (a->count == ZK_NTT_ACC) {
        acc_flush(a);
    }
    for (int p_ = 0; p_ < NP; p_++) {
        const __m256i q = _mm256_set1_epi32((int) ntt_q[p_]);
        const __m256i qinv = _mm256_set1_epi32((int) ntt.qinv[p_]);

        for (slong j = 0; j < DEGREE_N; j += 8) {
            const __m256i u = _mm256_loadu_si256((const __m256i *) (x->v[p_] + j));
            const __m256i w = _mm256_loadu_si256((const __m256i *) (y->v[p_] + j));
            const __m256i pr = redc(u, w, q, qinv);
            __m256i *s = (__m256i *) (a->acc[p_] + j);

            _mm256_storeu_si256(s, _mm256_add_epi64(_mm256_loadu_si256(s),
                                _mm256_cvtepu32_epi64(_mm256_castsi256_si128(pr))));
            _mm256_storeu_si256(s + 1, _mm256_add_epi64(_mm256_loadu_si256(s + 1),
                                _mm256_cvtepu32_epi64(_mm256_extracti128_si256(pr, 1))));
        }
    }
    a->count++;
}

void evmlr_zk_acc_get(nmod_poly_t r, evmlr_zk_acc_t *a) {
    acc_flush(a);
    nmod_poly_set(r, a->sum);
}

/* r = c v for a challenge c, which has 2 ZK_NU coefficients of +-1: a signed
 * sum of rotations, far cheaper than a general product. */
static int mul_sparse(nmod_poly_t r, const nmod_poly_t c, const nmod_poly_t v) {
    slong idx[2 * ZK_NU + 1];
    int sgn[2 * ZK_NU + 1], nz = 0;
    ulong out[DEGREE_N] = { 0 };
    slong vl = nmod_poly_length(v);

    for (slong i = 0; i < nmod_poly_length(c); i++) {
        ulong x = c->coeffs[i];

        if (x == 0) continue;
        if (nz == 2 * ZK_NU + 1 || (x != 1 && x != ZK_P - 1)) return 0;
        idx[nz] = i;
        sgn[nz++] = (x == 1) ? 1 : -1;
    }
    // Over the integers, on centred residues: at most 2 ZK_NU + 1 terms of
    // at most p/2 each, reduced once at the end.
    _Static_assert((2 * ZK_NU + 1) * (ZK_P / 2) < (1UL << 62), "the sums fit a signed word");
    int64_t vc[DEGREE_N], acc[DEGREE_N] = { 0 };

    for (slong j = 0; j < vl; j++) {
        const ulong x = v->coeffs[j];

        vc[j] = (x > ZK_P / 2) ? (int64_t) x - (int64_t) ZK_P : (int64_t) x;
    }
    for (int k = 0; k < nz; k++) {
        // x^i v_j lands at i + j, or, past x^n, at i + j - n with its sign
        // flipped (x^n = -1).
        const slong i = idx[k], split = FLINT_MIN(vl, DEGREE_N - i);
        int64_t *lo = acc + i;

        if (sgn[k] > 0) {
            for (slong j = 0; j < split; j++) lo[j] += vc[j];
            for (slong j = split; j < vl; j++) acc[i + j - DEGREE_N] -= vc[j];
        } else {
            for (slong j = 0; j < split; j++) lo[j] -= vc[j];
            for (slong j = split; j < vl; j++) acc[i + j - DEGREE_N] += vc[j];
        }
    }
    for (slong j = 0; j < DEGREE_N; j++) {
        int64_t t = acc[j] % (int64_t) ZK_P;

        out[j] = (t < 0) ? (ulong) (t + (int64_t) ZK_P) : (ulong) t;
    }
    nmod_poly_fit_length(r, DEGREE_N);
    memcpy(r->coeffs, out, sizeof(out));
    r->length = DEGREE_N;
    _nmod_poly_normalise(r);
    return 1;
}

void evmlr_zk_mul(nmod_poly_t r, const nmod_poly_t a, const nmod_poly_t b) {
    zk_setup();
    // A challenge is the commonest operand, and a sparse one.
    if (mul_sparse(r, a, b) || mul_sparse(r, b, a)) {
        return;
    }
    evmlr_zk_ntt_t x, y;

    evmlr_zk_ntt(&x, a);
    evmlr_zk_ntt(&y, b);
    evmlr_zk_ntt_mul(&x, &x, &y);
    evmlr_zk_intt(r, &x);
}

#ifdef MAIN
/* The product by FLINT and a fold, the reference the transform is tested
 * against. */
static void mul_reference(nmod_poly_t r, const nmod_poly_t a, const nmod_poly_t b) {
    nmod_poly_t t;

    zk_setup();
    nmod_poly_init(t, ZK_P);
    nmod_poly_mul(t, a, b);
    evmlr_crt_negacyclic_rem(r, t, zk_cyclo);
    nmod_poly_clear(t);
}
#endif

void evmlr_zk_sigma(nmod_poly_t r, const nmod_poly_t a) {
    zk_setup();
    nmod_poly_t t;

    nmod_poly_init(t, ZK_P);
    nmod_poly_fit_length(t, DEGREE_N);
    nmod_poly_set_coeff_ui(t, 0, nmod_poly_get_coeff_ui(a, 0));
    for (slong i = 1; i < DEGREE_N; i++) {
        // x^-i = -x^(n-i) in R_p.
        nmod_poly_set_coeff_ui(t, DEGREE_N - i, nmod_neg(nmod_poly_get_coeff_ui(a, i), zk_mod));
    }
    nmod_poly_swap(r, t);
    nmod_poly_clear(t);
}

ulong evmlr_zk_ct(const nmod_poly_t a) {
    return nmod_poly_get_coeff_ui(a, 0);
}

void evmlr_zk_ones(nmod_poly_t r) {
    nmod_poly_zero(r);
    nmod_poly_fit_length(r, DEGREE_N);
    for (slong i = 0; i < DEGREE_N; i++) {
        nmod_poly_set_coeff_ui(r, i, 1);
    }
}

void evmlr_zk_lift(nmod_poly_t r, const nmod_poly_t a) {
    nmod_poly_t t;

    const slong len = nmod_poly_length(a);

    nmod_poly_init2(t, ZK_P, len);
    for (slong i = 0; i < len; i++) {
        const ulong v = a->coeffs[i];

        t->coeffs[i] = (v > a->mod.n / 2) ? ZK_P - (a->mod.n - v) : v;
    }
    t->length = len; // nonzero leading coefficients stay nonzero
    nmod_poly_swap(r, t);
    nmod_poly_clear(t);
}

/* A value uniform in [0, bound), bound <= 2^16, by rejecting the incomplete top
 * copy of the 16-bit range. */
static ulong uniform_u16(prg_t *prg, ulong bound) {
    ulong limit = 65536 - (65536 % bound);
    uint16_t u;

    do {
        prg_bytes(prg, (unsigned char *) &u, sizeof(u));
    } while (u >= limit);
    return u % bound;
}

void evmlr_zk_challenge(nmod_poly_t r, prg_t *prg) {
    zk_setup();
    int used[DEGREE_N / 2] = { 0 };

    nmod_poly_zero(r);
    for (int k = 0; k < ZK_NU; k++) {
        ulong i;
        uint8_t sign;

        do {
            i = 1 + uniform_u16(prg, DEGREE_N / 2 - 1);
        } while (used[i]);
        used[i] = 1;
        prg_bytes(prg, &sign, 1);
        // c_i = +-1 and c_(n-i) = -c_i, so that sigma(c) = c.
        nmod_poly_set_coeff_ui(r, i, (sign & 1) ? 1 : ZK_P - 1);
        nmod_poly_set_coeff_ui(r, DEGREE_N - i, (sign & 1) ? ZK_P - 1 : 1);
    }
}

void evmlr_zk_uniform(nmod_poly_t r, prg_t *prg) {
    _Static_assert(ZK_P < (1UL << ZK_P_BITS), "uniform sampling draws ZK_P_BITS bits");
    uint64_t buf[DEGREE_N];

    prg_bytes(prg, (unsigned char *) buf, sizeof(buf));
    nmod_poly_fit_length(r, DEGREE_N);
    for (slong i = 0; i < DEGREE_N; i++) {
        uint64_t v = buf[i] & ((1UL << ZK_P_BITS) - 1);

        while (v >= ZK_P) {
            prg_bytes(prg, (unsigned char *) &v, sizeof(v));
            v &= (1UL << ZK_P_BITS) - 1;
        }
        r->coeffs[i] = v;
    }
    r->length = DEGREE_N;
    _nmod_poly_normalise(r);
}

void evmlr_zk_prg_for(prg_t *prg, const uint8_t seed[32], uint32_t domain,
                      uint64_t row, uint64_t col) {
    SHA256Context sha;
    uint8_t key[SHA256HashSize], buf[20];

    for (int b = 0; b < 4; b++) buf[b] = (uint8_t) (domain >> (8 * b));
    for (int b = 0; b < 8; b++) buf[4 + b] = (uint8_t) (row >> (8 * b));
    for (int b = 0; b < 8; b++) buf[12 + b] = (uint8_t) (col >> (8 * b));
    SHA256Reset(&sha);
    SHA256Input(&sha, seed, 32);
    SHA256Input(&sha, buf, sizeof(buf));
    SHA256Result(&sha, key);
    prg_setseed(prg, key);
}

#ifdef MAIN
#include "evmlr_main.h"

/* Centred value of a residue mod p. */
static slong centre(ulong v) {
    return (v > ZK_P / 2) ? (slong) v - (slong) ZK_P : (slong) v;
}

static void random_poly(nmod_poly_t a, flint_rand_t state) {
    nmod_poly_zero(a);
    for (slong i = 0; i < DEGREE_N; i++) {
        nmod_poly_set_coeff_ui(a, i, n_randint(state, ZK_P));
    }
}

void test(flint_rand_t state) {
    nmod_poly_t a, b, c, d, e;
    fmpz_poly_t fa, fb, fc;
    prg_t prg;
    uint8_t seed[32] = { 1 };

    evmlr_zk_init(a);
    evmlr_zk_init(b);
    evmlr_zk_init(c);
    evmlr_zk_init(d);
    evmlr_zk_init(e);
    fmpz_poly_init(fa);
    fmpz_poly_init(fb);
    fmpz_poly_init(fc);
    prg_setseed(&prg, seed);

    TEST_BEGIN("multiplication in R_p matches a negacyclic schoolbook product") {
        random_poly(a, state);
        random_poly(b, state);
        mul_reference(c, a, b);
        // Reference: the product over the integers, folded and reduced.
        fmpz_poly_set_nmod_poly_unsigned(fa, a);
        fmpz_poly_set_nmod_poly_unsigned(fb, b);
        fmpz_poly_mul(fc, fa, fb);
        fmpz_t x, y;
        fmpz_init(x);
        fmpz_init(y);
        int ok = 1;
        for (slong i = 0; i < DEGREE_N && ok; i++) {
            fmpz_poly_get_coeff_fmpz(x, fc, i);
            fmpz_poly_get_coeff_fmpz(y, fc, i + DEGREE_N);
            fmpz_sub(x, x, y);
            fmpz_mod_ui(x, x, ZK_P);
            ok = (fmpz_get_ui(x) == nmod_poly_get_coeff_ui(c, i));
        }
        fmpz_clear(x);
        fmpz_clear(y);
        TEST_ASSERT(ok, end);
    } TEST_END;

    TEST_BEGIN("the NTT product agrees with FLINT's, dense and sparse") {
        random_poly(a, state);
        random_poly(b, state);
        evmlr_zk_mul(c, a, b);
        mul_reference(d, a, b);
        TEST_ASSERT(nmod_poly_equal(c, d), end);
        evmlr_zk_challenge(e, &prg);
        evmlr_zk_mul(c, e, a);
        mul_reference(d, e, a);
        TEST_ASSERT(nmod_poly_equal(c, d), end);
    } TEST_END;

    TEST_BEGIN("sigma permutes a transform's slots, and the ones' transform is right") {
        evmlr_zk_ntt_t x, y, z;
        nmod_poly_zero(a);
        for (slong i = 0; i < DEGREE_N; i++) nmod_poly_set_coeff_ui(a, i, n_randint(state, ZK_P));
        evmlr_zk_ntt(&x, a);
        evmlr_zk_ntt_sigma(&y, &x);
        evmlr_zk_sigma(b, a);
        evmlr_zk_ntt(&z, b);
        int ok = memcmp(&y, &z, sizeof(y)) == 0;
        evmlr_zk_ones(b);
        evmlr_zk_ntt(&z, b);
        ok &= memcmp(&z, evmlr_zk_ntt_ones(), sizeof(z)) == 0;
        TEST_ASSERT(ok, end);
    } TEST_END;

    TEST_BEGIN("a constant's transform is the constant in every slot") {
        evmlr_zk_ntt_t x, y;
        ulong c = n_randint(state, ZK_P);
        if (_i == 0) c = ZK_P - 1;
        nmod_poly_zero(a);
        nmod_poly_set_coeff_ui(a, 0, c);
        evmlr_zk_ntt(&x, a);
        evmlr_zk_ntt_const(&y, c);
        TEST_ASSERT(memcmp(&x, &y, sizeof(x)) == 0, end);
    } TEST_END;

    TEST_BEGIN("an NTT accumulator sums past its flush threshold exactly") {
        // Worst case for the integer range: every coefficient at p/2.
        evmlr_zk_acc_t acc;
        evmlr_zk_ntt_t x, y;
        evmlr_zk_acc_init(&acc);
        nmod_poly_zero(a);
        nmod_poly_zero(b);
        for (slong i = 0; i < DEGREE_N; i++) {
            nmod_poly_set_coeff_ui(a, i, ZK_P / 2);
            nmod_poly_set_coeff_ui(b, i, ZK_P / 2);
        }
        evmlr_zk_ntt(&x, a);
        evmlr_zk_ntt(&y, b);
        slong reps = 2 * ZK_NTT_ACC + 3;
        for (slong k = 0; k < reps; k++) evmlr_zk_acc_addmul(&acc, &x, &y);
        evmlr_zk_acc_get(c, &acc);
        mul_reference(d, a, b);
        nmod_poly_scalar_mul_nmod(d, d, reps);
        int ok = nmod_poly_equal(c, d);
        // Worst case for the 64-bit sums: every slot at q - 1, the transform
        // of -1, so the sum of ZK_NTT_ACC + 40 squares is ZK_NTT_ACC + 40.
        evmlr_zk_acc_zero(&acc);
        for (int t = 0; t < NP; t++) {
            for (slong j = 0; j < DEGREE_N; j++) x.v[t][j] = ntt_q[t] - 1;
        }
        for (slong k = 0; k < ZK_NTT_ACC + 40; k++) evmlr_zk_acc_addmul(&acc, &x, &x);
        evmlr_zk_acc_get(c, &acc);
        nmod_poly_zero(d);
        nmod_poly_set_coeff_ui(d, 0, ZK_NTT_ACC + 40);
        ok &= nmod_poly_equal(c, d);
        evmlr_zk_acc_clear(&acc);
        TEST_ASSERT(ok, end);
    } TEST_END;

    TEST_BEGIN("ct(sigma(a) b) is the inner product of a and b") {
        random_poly(a, state);
        random_poly(b, state);
        evmlr_zk_sigma(c, a);
        evmlr_zk_mul(c, c, b);
        ulong ip = 0;
        for (slong i = 0; i < DEGREE_N; i++) {
            ip = nmod_add(ip, nmod_mul(nmod_poly_get_coeff_ui(a, i),
                                       nmod_poly_get_coeff_ui(b, i), *evmlr_zk_mod()),
                          *evmlr_zk_mod());
        }
        TEST_ASSERT(evmlr_zk_ct(c) == ip, end);
    } TEST_END;

    TEST_BEGIN("sigma is an involutive ring automorphism") {
        random_poly(a, state);
        random_poly(b, state);
        evmlr_zk_sigma(c, a);
        evmlr_zk_sigma(c, c);
        TEST_ASSERT(nmod_poly_equal(c, a), end);
        evmlr_zk_mul(c, a, b);
        evmlr_zk_sigma(c, c);
        evmlr_zk_sigma(d, a);
        evmlr_zk_sigma(e, b);
        evmlr_zk_mul(d, d, e);
        TEST_ASSERT(nmod_poly_equal(c, d), end);
    } TEST_END;

    TEST_BEGIN("challenges are fixed by sigma, ternary, with 2 ZK_NU nonzeros") {
        evmlr_zk_challenge(c, &prg);
        evmlr_zk_sigma(d, c);
        TEST_ASSERT(nmod_poly_equal(c, d), end);
        int ones = 0, ternary = 1;
        for (slong i = 0; i < DEGREE_N; i++) {
            slong v = centre(nmod_poly_get_coeff_ui(c, i));
            ternary &= (v >= -1 && v <= 1);
            ones += (v != 0);
        }
        TEST_ASSERT(ternary && ones == 2 * ZK_NU, end);
    } TEST_END;

    TEST_BEGIN("differences of distinct challenges are invertible in R_p") {
        nmod_poly_t cyclo;
        nmod_poly_init(cyclo, ZK_P);
        nmod_poly_set_coeff_ui(cyclo, DEGREE_N, 1);
        nmod_poly_set_coeff_ui(cyclo, 0, 1);
        evmlr_zk_challenge(c, &prg);
        do {
            evmlr_zk_challenge(d, &prg);
        } while (nmod_poly_equal(c, d));
        nmod_poly_sub(e, c, d);
        nmod_poly_gcd(e, e, cyclo);
        int unit = (nmod_poly_degree(e) == 0);
        nmod_poly_clear(cyclo);
        TEST_ASSERT(unit, end);
    } TEST_END;

    TEST_BEGIN("lifting from R_q keeps the centred representative") {
        nmod_poly_t q_poly;
        nmod_poly_init(q_poly, MOD_Q);
        nmod_poly_set_coeff_ui(q_poly, 0, 5);
        nmod_poly_set_coeff_ui(q_poly, 1, MOD_Q - 5);
        nmod_poly_set_coeff_ui(q_poly, 2, MOD_Q / 2);
        nmod_poly_set_coeff_ui(q_poly, 3, MOD_Q / 2 + 1);
        evmlr_zk_lift(a, q_poly);
        int ok = centre(nmod_poly_get_coeff_ui(a, 0)) == 5
              && centre(nmod_poly_get_coeff_ui(a, 1)) == -5
              && centre(nmod_poly_get_coeff_ui(a, 2)) == MOD_Q / 2
              && centre(nmod_poly_get_coeff_ui(a, 3)) == -(slong) (MOD_Q / 2);
        nmod_poly_clear(q_poly);
        TEST_ASSERT(ok, end);
    } TEST_END;

    TEST_BEGIN("public matrices expand deterministically, element by element") {
        prg_t p1, p2;
        evmlr_zk_prg_for(&p1, seed, 7, 3, 4);
        evmlr_zk_uniform(a, &p1);
        evmlr_zk_prg_for(&p2, seed, 7, 3, 4);
        evmlr_zk_uniform(b, &p2);
        TEST_ASSERT(nmod_poly_equal(a, b), end);
        evmlr_zk_prg_for(&p2, seed, 7, 4, 3);
        evmlr_zk_uniform(b, &p2);
        TEST_ASSERT(!nmod_poly_equal(a, b), end);
    } TEST_END;

end:
    nmod_poly_clear(a);
    nmod_poly_clear(b);
    nmod_poly_clear(c);
    nmod_poly_clear(d);
    nmod_poly_clear(e);
    fmpz_poly_clear(fa);
    fmpz_poly_clear(fb);
    fmpz_poly_clear(fc);
}

void bench(flint_rand_t state) {
    nmod_poly_t a, b, c;
    prg_t prg;
    uint8_t seed[32] = { 2 };

    evmlr_zk_init(a);
    evmlr_zk_init(b);
    evmlr_zk_init(c);
    random_poly(a, state);
    random_poly(b, state);
    prg_setseed(&prg, seed);

    BENCH_BEGIN("evmlr_zk_mul (NTT)") {
        BENCH_ADD(evmlr_zk_mul(c, a, b));
    } BENCH_END;
    BENCH_BEGIN("FLINT nmod_poly_mul and fold") {
        BENCH_ADD(mul_reference(c, a, b));
    } BENCH_END;
    {
        evmlr_zk_challenge(c, &prg);
        BENCH_BEGIN("evmlr_zk_mul by a challenge") {
            BENCH_ADD(evmlr_zk_mul(b, c, a));
        } BENCH_END;
        evmlr_zk_ntt_t x;
        BENCH_BEGIN("evmlr_zk_ntt") {
            BENCH_ADD(evmlr_zk_ntt(&x, a));
        } BENCH_END;
    }
    BENCH_BEGIN("evmlr_zk_sigma") {
        BENCH_ADD(evmlr_zk_sigma(c, a));
    } BENCH_END;
    BENCH_BEGIN("evmlr_zk_uniform") {
        BENCH_ADD(evmlr_zk_uniform(c, &prg));
    } BENCH_END;

    nmod_poly_clear(a);
    nmod_poly_clear(b);
    nmod_poly_clear(c);
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
