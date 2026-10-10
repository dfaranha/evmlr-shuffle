#include "evmlr_otse.h"
#include "evmlr_utils.h"
#include "flint/fmpz.h"
#include "flint/fmpz_poly.h"
#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif

void calc_a(nmod_poly_mat_t a, nmod_poly_mat_t d_dagger, const evmlr_otse_key_t key, const evmlr_otse_ctx_t ctx);

void evmlr_otse_ctx_init(evmlr_otse_ctx_t ctx, slong L, flint_rand_t state) {
    ctx->L = L;
    // H \sample R_{2^ZETA}^{(K_LWE + L) x K_LWR}
    nmod_poly_mat_init(ctx->H, K_LWE + L, K_LWR, 2*ZETA);
    evmlr_utils_uniform_mat(ctx->H);

    // H' = (H'' | I_{L}) \in R_q^{L x (K_LWE + L)}
    nmod_poly_mat_init(ctx->H_prime, L, K_LWE + L, MOD_Q);
    for (int i = 0; i < L; i++) {
        for (int j = 0; j < K_LWE + L; j++) {
            nmod_poly_struct* poly = nmod_poly_mat_entry(ctx->H_prime, i, j);
            if (j < K_LWE) { // H'' \sample R_q^{L x K_LWE}
                evmlr_utils_uniform_poly(poly, DEGREE_N);
            } else if (j == K_LWE + i) { // Identity matrix where row=col
                nmod_poly_one(poly);
            } else { // Identity matrix where row!=col
                nmod_poly_zero(poly);
            }
        }
    }

    nmod_poly_init(ctx->cyclo_poly, MOD_Q);
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, DEGREE_N, 1);
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, 0, 1);
}

void evmlr_otse_ctx_clear(evmlr_otse_ctx_t ctx) {
    nmod_poly_mat_clear(ctx->H);
    nmod_poly_mat_clear(ctx->H_prime);
    nmod_poly_clear(ctx->cyclo_poly);
}

void evmlr_otse_keygen(evmlr_otse_key_t key, flint_rand_t state) {
    nmod_poly_mat_init(key->s, K_LWR, 1, MOD_Q);
    evmlr_utils_sample_binary_poly_mat(key->s, DEGREE_N); // s \sample {0,1}^{K_LWR}
}

void evmlr_otse_keyclear(evmlr_otse_key_t key) {
    nmod_poly_mat_clear(key->s);
}

void evmlr_otse_ciphertext_init(evmlr_otse_ciphertext_t ct, slong L) {
    nmod_poly_mat_init(ct->c, L, 1, MOD_Q);
}

void evmlr_otse_encrypt(evmlr_otse_ciphertext_t ct, nmod_poly_mat_t d_dagger, const nmod_poly_mat_t m,
                        const evmlr_otse_key_t key, const evmlr_otse_ctx_t ctx) {
    // c = m + a (ct is owned by the caller)
    calc_a(ct->c, d_dagger, key, ctx);
    nmod_poly_mat_add(ct->c, m, ct->c);
}

void evmlr_otse_decrypt(nmod_poly_mat_t m, const evmlr_otse_ciphertext_t ct, const evmlr_otse_key_t key, const evmlr_otse_ctx_t ctx) {
    nmod_poly_mat_t a;
    nmod_poly_mat_init(a, ctx->L, 1, MOD_Q);
    calc_a(a, NULL, key, ctx);
    // m = c - a (m is owned by the caller)
    nmod_poly_mat_sub(m, ct->c, a);

    nmod_poly_mat_clear(a);
}

void evmlr_otse_ciphertext_clear(evmlr_otse_ciphertext_t ct) {
    nmod_poly_mat_clear(ct->c);
}

void round_poly(nmod_poly_t poly, const nmod_poly_t hs, const fmpz_t q1, const fmpz_t q2) {
    fmpz_t coeff, half_q1;
    fmpz_init(coeff);
    // coeff for rounding equivalent to adding 0.5 before flooring so we round to nearest integer with ties rounding up
    fmpz_init(half_q1);
    fmpz_fdiv_q_2exp(half_q1, q1, 1); // half_q1 = q1 / 2

    slong deg = nmod_poly_degree(hs);
    nmod_poly_fit_length(poly, deg + 1);
    for (slong i = 0; i <= deg; i++) {
        ulong coeff_hs = nmod_poly_get_coeff_ui(hs, i);
        fmpz_set_ui(coeff, coeff_hs);
        // round(coeff * q2 / q1)
        fmpz_mul(coeff, coeff, q2);
        fmpz_add(coeff, coeff, half_q1);
        fmpz_fdiv_q(coeff, coeff, q1);

        fmpz_mod(coeff, coeff, q2); // coeff mod q2
        nmod_poly_set_coeff_ui(poly, i, fmpz_get_ui(coeff));
    }

    fmpz_clear(coeff);
    fmpz_clear(half_q1);
}

void calc_d(nmod_poly_mat_t d, const nmod_poly_mat_t H, const nmod_poly_mat_t s, const nmod_poly_t cyclo_poly, slong L) {
    // ⌈Hs⌋_{2^ζ →2^{2η}} := ⌈(Hs * 2^{2η})/2^ζ⌋ mod 2^{2η} := Hs * q2/q1 mod q2
    fmpz_t q1, q2;
    fmpz_init(q1);
    fmpz_init(q2);
    fmpz_set_ui(q1, 1UL << ZETA);      // q1 = 2^ζ
    fmpz_set_ui(q2, 1UL << (2 * ETA)); // q2 = 2^{2η}

    nmod_poly_mat_t Hs;
    nmod_poly_mat_init(Hs, K_LWE + L, 1, MOD_Q);
    nmod_poly_mat_mulmod(Hs, H, s, cyclo_poly);

    // d = Hs * q2/q1 mod q2 (d is owned by the caller)
    for (int i = 0; i < K_LWE + L; i++) {
        nmod_poly_struct* d_i = nmod_poly_mat_entry(d, i, 0);
        nmod_poly_struct* Hs_i = nmod_poly_mat_entry(Hs, i, 0);
        round_poly(d_i, Hs_i, q1, q2);
    }

    fmpz_clear(q1);
    fmpz_clear(q2);
    nmod_poly_mat_clear(Hs);
}

void multiply_by_B_eta(nmod_poly_mat_t w, const nmod_poly_mat_t d, slong L) {
    nmod_poly_mat_zero(w); // w is owned by the caller
    // Accumulate the first eta vectors
    for (int i = 0; i < K_LWE + L; i++) {
        nmod_poly_struct* w_i = nmod_poly_mat_entry(w, i, 0);
        for (int b = 0; b < ETA; b++) {
            nmod_poly_struct* d_bi = nmod_poly_mat_entry(d, b * (K_LWE + L) + i, 0);
            nmod_poly_add(w_i, w_i, d_bi);
        }
    }
    // Subtract the last eta vectors
    for (int i = 0; i < K_LWE + L; i++) {
        nmod_poly_struct* w_i = nmod_poly_mat_entry(w, i, 0);
        for (int b = ETA; b < 2 * ETA; b++) {
            nmod_poly_struct* d_bi = nmod_poly_mat_entry(d, b * (K_LWE + L) + i, 0);
            nmod_poly_sub(w_i, w_i, d_bi);
        }
    }
}

void calc_a(nmod_poly_mat_t a, nmod_poly_mat_t d_dagger, const evmlr_otse_key_t key, const evmlr_otse_ctx_t ctx) {
    nmod_poly_mat_t d, d_bin;
    nmod_poly_mat_init(d, K_LWE + ctx->L, 1, MOD_Q);
    calc_d(d, ctx->H, key->s, ctx->cyclo_poly, ctx->L); // d = ⌈Hs⌋_{2^ZETA →2^{2η}}
    int bits = 2 * ETA;
    nmod_poly_mat_init(d_bin, bits, nmod_poly_mat_nrows(d), 2);
    evmlr_utils_ring_to_bin(d_bin, d, bits);

    // a = H' B^n stack(d); d_dagger, when given, is owned by the caller.
    if (d_dagger != NULL) {
        evmlr_utils_stack(d_dagger, d_bin); // d_dagger = stack(d_bin)
        evmlr_calc_a(a, d_dagger, ctx);
    } else {
        nmod_poly_mat_t tmp_dagger;
        nmod_poly_mat_init(tmp_dagger, d_bin->r * d_bin->c, 1, MOD_Q);
        evmlr_utils_stack(tmp_dagger, d_bin); // d_dagger = stack(d_bin)
        evmlr_calc_a(a, tmp_dagger, ctx);
        nmod_poly_mat_clear(tmp_dagger);
    }
    nmod_poly_mat_clear(d);
    nmod_poly_mat_clear(d_bin);
}

void evmlr_calc_a(nmod_poly_mat_t a, const nmod_poly_mat_t d_stack, const evmlr_otse_ctx_t ctx) {
    // w = B_eta stack(d)
    nmod_poly_mat_t w;
    nmod_poly_mat_init(w, K_LWE + ctx->L, 1, MOD_Q);
    multiply_by_B_eta(w, d_stack, ctx->L);
    // a = H' w
    nmod_poly_mat_mulmod(a, ctx->H_prime, w, ctx->cyclo_poly);
    nmod_poly_mat_clear(w);
}

#ifdef MAIN
#include "evmlr_main.h"
void test(flint_rand_t rand, evmlr_otse_ctx_t ctx) {
    evmlr_otse_key_t key;
    evmlr_otse_keygen(key, rand);

    nmod_poly_mat_t msg, decrypted_msg;
    nmod_poly_mat_init(msg, ctx->L, 1, MOD_Q);
    nmod_poly_mat_init(decrypted_msg, ctx->L, 1, MOD_Q);
    nmod_poly_mat_randtest(msg, rand, DEGREE_N);

    evmlr_otse_ciphertext_t ct;
    evmlr_otse_ciphertext_init(ct, ctx->L);
    TEST_BEGIN("encryption and decryption are consistent") {
        evmlr_otse_encrypt(ct, NULL, msg, key, ctx);
        evmlr_otse_decrypt(decrypted_msg, ct, key, ctx);
        TEST_ASSERT(nmod_poly_mat_equal(msg, decrypted_msg) == 1, end)
    } TEST_END;

    end:
        evmlr_otse_ciphertext_clear(ct);
        evmlr_otse_keyclear(key);
        nmod_poly_mat_clear(msg);
        nmod_poly_mat_clear(decrypted_msg);
}

void bench(flint_rand_t rand, evmlr_otse_ctx_t ctx) {
    evmlr_otse_key_t key;
    BENCH_BEGIN("evmlr_otse_keygen") {
        BENCH_ADD(evmlr_otse_keygen(key, rand))
    } BENCH_END;

    nmod_poly_mat_t msg;
    nmod_poly_mat_init(msg, ctx->L, 1, MOD_Q);
    nmod_poly_mat_randtest(msg, rand, DEGREE_N);

    evmlr_otse_ciphertext_t ct;
    evmlr_otse_ciphertext_init(ct, ctx->L);
    BENCH_BEGIN("evmlr_otse_encrypt") {
        BENCH_ADD(evmlr_otse_encrypt(ct, NULL, msg, key, ctx))
    } BENCH_END;

    nmod_poly_mat_t decrypted_msg;
    nmod_poly_mat_init(decrypted_msg, ctx->L, 1, MOD_Q);
    BENCH_BEGIN("evmlr_otse_decrypt") {
        BENCH_ADD(evmlr_otse_decrypt(decrypted_msg, ct, key, ctx))
    } BENCH_END;

    evmlr_otse_keyclear(key);
    evmlr_otse_ciphertext_clear(ct);
    nmod_poly_mat_clear(msg);
    nmod_poly_mat_clear(decrypted_msg);
}

int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);

    flint_rand_t state;
    evmlr_rand_init(state);

    evmlr_otse_ctx_t ctx;
    evmlr_otse_ctx_init(ctx, M_LEN, state);

    if (evmlr_runs_tests(mode))   test(state, ctx);
    if (evmlr_runs_benches(mode)) bench(state, ctx);

    evmlr_otse_ctx_clear(ctx);
    flint_rand_clear(state);
    return test_status();
}
#endif


