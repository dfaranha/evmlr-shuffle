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

void evmlr_zk_mul(nmod_poly_t r, const nmod_poly_t a, const nmod_poly_t b) {
    zk_setup();
    nmod_poly_t t;

    nmod_poly_init(t, ZK_P);
    nmod_poly_mul(t, a, b);
    evmlr_crt_negacyclic_rem(r, t, zk_cyclo);
    nmod_poly_clear(t);
}

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

        nmod_poly_set_coeff_ui(t, i, (v > MOD_Q / 2) ? ZK_P - (MOD_Q - v) : v);
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
        evmlr_zk_mul(c, a, b);
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

    BENCH_BEGIN("evmlr_zk_mul") {
        BENCH_ADD(evmlr_zk_mul(c, a, b));
    } BENCH_END;
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
