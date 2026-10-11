#include "evmlr_zk.h"
#include "evmlr_crt.h"
#include "sha.h"
#include <string.h>

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
/* The negacyclic NTT over two 62-bit primes                                  */
/*============================================================================*/

/* Two primes 1 mod 2n = 1024 below 2^62, each with psi, a primitive 1024th
 * root of unity: psi^512 = -1, which is what makes the transform negacyclic. */
static const ulong ntt_q[2] = { 4611686018427366401UL, 4611686018427365377UL };
static const ulong ntt_psi[2] = { 86170868861168147UL, 623460423351514340UL };

static struct {
    ulong w[2][DEGREE_N], wpre[2][DEGREE_N];     /* psi^brv(k), and Shoup's precomputation */
    ulong wi[2][DEGREE_N], wipre[2][DEGREE_N];   /* psi^-brv(k) */
    ulong ninv[2], ninvpre[2];
    ulong qinv[2];                               /* for n_mulmod2_preinv */
    ulong q1inv;                                 /* q_1^-1 mod q_2 */
    ulong q1p;                                   /* q_1 mod p */
    ulong Qp;                                    /* q_1 q_2 mod p */
    unsigned __int128 Q, Qhalf;
    slong sigma_perm[DEGREE_N];                  /* slot of zeta^-1 for the slot of zeta */
    evmlr_zk_ntt_t ones;                         /* the transform of 1 + x + ... + x^(n-1) */
    int ready;
} ntt;

static void ntt_forward(ulong *a, int t_);

static ulong bitrev9(ulong k) {
    ulong r = 0;

    for (int i = 0; i < 9; i++) r |= ((k >> i) & 1) << (8 - i);
    return r;
}

static void ntt_setup(void) {
    _Static_assert(DEGREE_N == 512, "the NTT is written for n = 512");
    if (ntt.ready) return;
    zk_setup();
    for (int t = 0; t < 2; t++) {
        ulong q = ntt_q[t], psi = ntt_psi[t], psii = n_invmod(psi, q);

        ntt.qinv[t] = n_preinvert_limb(q);
        for (ulong k = 0; k < DEGREE_N; k++) {
            ulong e = bitrev9(k);

            ntt.w[t][k] = n_powmod2_ui_preinv(psi, e, q, ntt.qinv[t]);
            ntt.wpre[t][k] = n_mulmod_precomp_shoup(ntt.w[t][k], q);
            ntt.wi[t][k] = n_powmod2_ui_preinv(psii, e, q, ntt.qinv[t]);
            ntt.wipre[t][k] = n_mulmod_precomp_shoup(ntt.wi[t][k], q);
        }
        ntt.ninv[t] = n_invmod(DEGREE_N, q);
        ntt.ninvpre[t] = n_mulmod_precomp_shoup(ntt.ninv[t], q);
    }
    ntt.q1inv = n_invmod(ntt_q[0] % ntt_q[1], ntt_q[1]);
    ntt.q1p = ntt_q[0] % ZK_P;
    ntt.Q = (unsigned __int128) ntt_q[0] * ntt_q[1];
    ntt.Qhalf = ntt.Q / 2;
    ntt.Qp = (ulong) (ntt.Q % ZK_P);
    ntt.ready = 1;
    // Slot j of a transform holds the evaluation at some root zeta_j, which
    // the transform of x lists. sigma(a)(x) = a(x^-1) evaluates at zeta_j as a
    // does at zeta_j^-1, another root: so sigma permutes the slots.
    {
        ulong zeta[DEGREE_N];

        for (slong j = 0; j < DEGREE_N; j++) zeta[j] = (j == 1);
        ntt_forward(zeta, 0);
        for (slong j = 0; j < DEGREE_N; j++) {
            ntt.sigma_perm[j] = -1;
            for (slong k = 0; k < DEGREE_N; k++) {
                if (n_mulmod2_preinv(zeta[j], zeta[k], ntt_q[0], ntt.qinv[0]) == 1) ntt.sigma_perm[j] = k;
            }
        }
        for (int t = 0; t < 2; t++) {
            for (slong j = 0; j < DEGREE_N; j++) ntt.ones.v[t][j] = 1;
            ntt_forward(ntt.ones.v[t], t);
        }
    }
}

/* Cooley-Tukey, natural order in, bit-reversed order out, with Harvey's lazy
 * butterflies: values stay in [0, 4q), below 2^64 as q < 2^62, and are only
 * reduced to [0, q) at the end. Shoup's product S x - floor(S' x / 2^64) q
 * lies in [0, 2q) for any 64-bit x. */
static void ntt_forward(ulong *a, int t_) {
    const ulong q = ntt_q[t_], q2 = 2 * q;
    slong t = DEGREE_N;

    for (slong m = 1; m < DEGREE_N; m <<= 1) {
        t >>= 1;
        for (slong i = 0; i < m; i++) {
            const ulong S = ntt.w[t_][m + i], Sp = ntt.wpre[t_][m + i];
            ulong *x = a + 2 * i * t;

            for (slong j = 0; j < t; j++) {
                ulong U = x[j], X = x[j + t];
                ulong V = S * X - (ulong) (((unsigned __int128) Sp * X) >> 64) * q;

                U -= (U >= q2) ? q2 : 0;
                x[j] = U + V;
                x[j + t] = U - V + q2;
            }
        }
    }
    for (slong j = 0; j < DEGREE_N; j++) {
        ulong v = a[j];

        v -= (v >= q2) ? q2 : 0;
        v -= (v >= q) ? q : 0;
        a[j] = v;
    }
}

/* Gentleman-Sande, bit-reversed order in, natural order out, scaled by 1/n. */
static void ntt_inverse(ulong *a, int t_) {
    const ulong q = ntt_q[t_];
    slong t = 1;

    for (slong m = DEGREE_N; m > 1; m >>= 1) {
        slong h = m >> 1;

        for (slong i = 0; i < h; i++) {
            const ulong S = ntt.wi[t_][h + i], Sp = ntt.wipre[t_][h + i];
            ulong *x = a + 2 * i * t;

            for (slong j = 0; j < t; j++) {
                ulong U = x[j], V = x[j + t];

                x[j] = n_addmod(U, V, q);
                x[j + t] = n_mulmod_shoup(S, n_submod(U, V, q), Sp, q);
            }
        }
        t <<= 1;
    }
    for (slong j = 0; j < DEGREE_N; j++) {
        a[j] = n_mulmod_shoup(ntt.ninv[t_], a[j], ntt.ninvpre[t_], q);
    }
}

void evmlr_zk_ntt(evmlr_zk_ntt_t *r, const nmod_poly_t a) {
    ntt_setup();
    slong len = nmod_poly_length(a);

    for (slong j = 0; j < DEGREE_N; j++) {
        ulong v = (j < len) ? a->coeffs[j] : 0;

        // The centred residue, so that products stay below n (p/2)^2.
        if (v > ZK_P / 2) {
            ulong neg = ZK_P - v;
            r->v[0][j] = ntt_q[0] - neg;
            r->v[1][j] = ntt_q[1] - neg;
        } else {
            r->v[0][j] = v;
            r->v[1][j] = v;
        }
    }
    ntt_forward(r->v[0], 0);
    ntt_forward(r->v[1], 1);
}

void evmlr_zk_ntt_sigma(evmlr_zk_ntt_t *r, const evmlr_zk_ntt_t *a) {
    ntt_setup();
    for (int t = 0; t < 2; t++) {
        for (slong j = 0; j < DEGREE_N; j++) r->v[t][j] = a->v[t][ntt.sigma_perm[j]];
    }
}

const evmlr_zk_ntt_t *evmlr_zk_ntt_ones(void) {
    ntt_setup();
    return &ntt.ones;
}

void evmlr_zk_ntt_sub(evmlr_zk_ntt_t *r, const evmlr_zk_ntt_t *a, const evmlr_zk_ntt_t *b) {
    for (int t = 0; t < 2; t++) {
        for (slong j = 0; j < DEGREE_N; j++) r->v[t][j] = n_submod(a->v[t][j], b->v[t][j], ntt_q[t]);
    }
}

void evmlr_zk_ntt_const(evmlr_zk_ntt_t *r, ulong c) {
    ntt_setup();
    // A constant's transform is the constant in every slot, as a centred residue.
    for (int t = 0; t < 2; t++) {
        const ulong v = (c > ZK_P / 2) ? ntt_q[t] - (ZK_P - c) : c;

        for (slong j = 0; j < DEGREE_N; j++) r->v[t][j] = v;
    }
}

void evmlr_zk_ntt_mul(evmlr_zk_ntt_t *r, const evmlr_zk_ntt_t *a, const evmlr_zk_ntt_t *b) {
    ntt_setup();
    for (int t = 0; t < 2; t++) {
        for (slong j = 0; j < DEGREE_N; j++) {
            r->v[t][j] = n_mulmod2_preinv(a->v[t][j], b->v[t][j], ntt_q[t], ntt.qinv[t]);
        }
    }
}

void evmlr_zk_intt(nmod_poly_t r, const evmlr_zk_ntt_t *a) {
    ntt_setup();
    ulong x[2][DEGREE_N];
    const nmod_t pm = zk_mod;

    memcpy(x, a->v, sizeof(x));
    ntt_inverse(x[0], 0);
    ntt_inverse(x[1], 1);
    nmod_poly_zero(r);
    nmod_poly_fit_length(r, DEGREE_N);
    for (slong j = 0; j < DEGREE_N; j++) {
        // The integer y with y = x_0 (mod q_1) and y = x_1 (mod q_2), in
        // (-Q/2, Q/2], reduced mod p: y = x_0 + q_1 t.
        ulong d = n_submod(x[1][j], x[0][j] % ntt_q[1], ntt_q[1]);
        ulong t = n_mulmod2_preinv(d, ntt.q1inv, ntt_q[1], ntt.qinv[1]);
        unsigned __int128 y = (unsigned __int128) x[0][j] + (unsigned __int128) ntt_q[0] * t;
        ulong v = nmod_add(x[0][j] % ZK_P, nmod_mul(ntt.q1p, t % ZK_P, pm), pm);

        if (y > ntt.Qhalf) {
            v = nmod_sub(v, ntt.Qp, pm);
        }
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
    a->lazy = 0;
    a->count = 0;
    nmod_poly_zero(a->sum);
}

/* Brings each 128-bit sum back below q. */
static void acc_reduce(evmlr_zk_acc_t *a) {
    for (int t = 0; t < 2; t++) {
        for (slong j = 0; j < DEGREE_N; j++) {
            unsigned __int128 v = a->acc[t][j];

            a->acc[t][j] = n_ll_mod_preinv((ulong) (v >> 64), (ulong) v, ntt_q[t], ntt.qinv[t]);
        }
    }
    a->lazy = 0;
}

static void acc_flush(evmlr_zk_acc_t *a) {
    evmlr_zk_ntt_t x;
    nmod_poly_t t;

    if (a->count == 0) return;
    acc_reduce(a);
    for (int t_ = 0; t_ < 2; t_++) {
        for (slong j = 0; j < DEGREE_N; j++) x.v[t_][j] = (ulong) a->acc[t_][j];
    }
    nmod_poly_init(t, ZK_P);
    evmlr_zk_intt(t, &x);
    nmod_poly_add(a->sum, a->sum, t);
    nmod_poly_clear(t);
    memset(a->acc, 0, sizeof(a->acc));
    a->count = 0;
}

void evmlr_zk_acc_addmul(evmlr_zk_acc_t *a, const evmlr_zk_ntt_t *x, const evmlr_zk_ntt_t *y) {
    // At most ZK_NTT_LAZY - 1 products below q^2 < 2^124 on top of a reduced
    // value below q stay below 2^128.
    _Static_assert(ZK_NTT_LAZY <= 16, "the lazy sums would overflow 128 bits");
    ntt_setup();
    if (a->count == ZK_NTT_ACC) {
        acc_flush(a);
    } else if (a->lazy == ZK_NTT_LAZY - 1) {
        acc_reduce(a);
    }
    for (int t = 0; t < 2; t++) {
        for (slong j = 0; j < DEGREE_N; j++) {
            a->acc[t][j] += (unsigned __int128) x->v[t][j] * y->v[t][j];
        }
    }
    a->lazy++;
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
    for (int k = 0; k < nz; k++) {
        for (slong j = 0; j < vl; j++) {
            slong e = idx[k] + j;
            // x^(n + e) = -x^e
            int s = (e >= DEGREE_N) ? -sgn[k] : sgn[k];
            slong pos = (e >= DEGREE_N) ? e - DEGREE_N : e;
            out[pos] = (s > 0) ? nmod_add(out[pos], v->coeffs[j], zk_mod)
                               : nmod_sub(out[pos], v->coeffs[j], zk_mod);
        }
    }
    nmod_poly_zero(r);
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

    nmod_poly_init(t, ZK_P);
    nmod_poly_fit_length(t, nmod_poly_length(a));
    for (slong i = 0; i < nmod_poly_length(a); i++) {
        ulong v = nmod_poly_get_coeff_ui(a, i);

        nmod_poly_set_coeff_ui(t, i, (v > a->mod.n / 2) ? ZK_P - (a->mod.n - v) : v);
    }
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
    nmod_poly_zero(r);
    nmod_poly_fit_length(r, DEGREE_N);
    for (slong i = 0; i < DEGREE_N; i++) {
        uint64_t v = buf[i] & ((1UL << ZK_P_BITS) - 1);

        while (v >= ZK_P) {
            prg_bytes(prg, (unsigned char *) &v, sizeof(v));
            v &= (1UL << ZK_P_BITS) - 1;
        }
        nmod_poly_set_coeff_ui(r, i, v);
    }
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
        // Worst case for the lazy 128-bit sums: every slot at q - 1, the
        // transform of -1, so the sum of 40 squares is 40.
        evmlr_zk_acc_zero(&acc);
        for (int t = 0; t < 2; t++) {
            for (slong j = 0; j < DEGREE_N; j++) x.v[t][j] = ntt_q[t] - 1;
        }
        for (slong k = 0; k < 40; k++) evmlr_zk_acc_addmul(&acc, &x, &x);
        evmlr_zk_acc_get(c, &acc);
        nmod_poly_zero(d);
        nmod_poly_set_coeff_ui(d, 0, 40);
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
