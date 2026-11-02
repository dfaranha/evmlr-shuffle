#include "evmlr_otse.h"
#include "evmlr_utils.h"
#include "flint/fmpz.h"
#include "flint/fmpz_poly.h"
#include "flint/nmod.h"
#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif

void calc_a(nmod_poly_mat_t a, nmod_poly_mat_t d_dagger, const evmlr_otse_key_t key, const evmlr_otse_ctx_t ctx);

void evmlr_otse_ctx_init(evmlr_otse_ctx_t ctx, slong L, flint_rand_t state) {
    ctx->L = L;
    // H \sample R_{2^ZETA}^{(K_LWE + L) x K_LWR}. The modulus used to be
    // 2*ZETA = 12 rather than 2^ZETA = 64.
    nmod_poly_mat_init(ctx->H, K_LWE + L, K_LWR, 1UL << ZETA);
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
    nmod_poly_zero(poly);
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

/* out = a * b in Z_m[x]/(x^DEGREE_N + 1), for a and b already mod m. */
static void mul_negacyclic(nmod_poly_t out, const nmod_poly_t a, const nmod_poly_t b) {
    nmod_t mod = a->mod;
    nmod_poly_t t;

    nmod_poly_init_mod(t, mod);
    nmod_poly_mul(t, a, b);
    nmod_poly_zero(out);
    nmod_poly_fit_length(out, DEGREE_N);
    for (slong k = 0; k < nmod_poly_length(t); k++) {
        ulong c = nmod_poly_get_coeff_ui(t, k);
        slong i = k % DEGREE_N;
        ulong o = nmod_poly_get_coeff_ui(out, i);

        // x^DEGREE_N = -1, so the upper half folds back with a sign flip.
        nmod_poly_set_coeff_ui(out, i, (k < DEGREE_N) ? nmod_add(o, c, mod) : nmod_sub(o, c, mod));
    }
    nmod_poly_clear(t);
}

/*
 * d = ⌈Hs⌋_{2^ζ → 2^{2η}}, with Hs computed in R_{2^ζ} as in Figure 2 of the
 * paper. It used to be computed by nmod_poly_mat_mulmod into a matrix mod q,
 * with H mod 12: the products wrapped mod 3109, which is not a multiple of
 * 2^ζ, before the rounding that assumes them mod 2^ζ. Encryption and
 * decryption agreed, so messages still decrypted, but the pad was not the
 * MLWR output the security argument is about, and the rounding relation (3)
 * that the proofs of correct encryption and decryption must show would not
 * have held.
 */
void calc_d(nmod_poly_mat_t d, const nmod_poly_mat_t H, const nmod_poly_mat_t s, slong L) {
    // ⌈Hs⌋_{2^ζ →2^{2η}} := ⌈(Hs * 2^{2η})/2^ζ⌋ mod 2^{2η} := Hs * q2/q1 mod q2
    fmpz_t q1, q2;
    fmpz_init(q1);
    fmpz_init(q2);
    fmpz_set_ui(q1, 1UL << ZETA);      // q1 = 2^ζ
    fmpz_set_ui(q2, 1UL << (2 * ETA)); // q2 = 2^{2η}

    nmod_poly_mat_t Hs;
    nmod_poly_t s_i, prod;
    nmod_poly_mat_init(Hs, K_LWE + L, 1, 1UL << ZETA);
    nmod_poly_init(s_i, 1UL << ZETA);
    nmod_poly_init(prod, 1UL << ZETA);
    for (int i = 0; i < K_LWE + L; i++) {
        nmod_poly_struct* Hs_i = nmod_poly_mat_entry(Hs, i, 0);

        nmod_poly_zero(Hs_i);
        for (int j = 0; j < K_LWR; j++) {
            // s is binary, so its residues mod q are its residues mod 2^ζ.
            const nmod_poly_struct* s_j = nmod_poly_mat_entry(s, j, 0);

            nmod_poly_zero(s_i);
            for (slong k = 0; k < nmod_poly_length(s_j); k++) {
                nmod_poly_set_coeff_ui(s_i, k, nmod_poly_get_coeff_ui(s_j, k));
            }
            mul_negacyclic(prod, nmod_poly_mat_entry(H, i, j), s_i);
            nmod_poly_add(Hs_i, Hs_i, prod);
        }
    }
    nmod_poly_clear(s_i);
    nmod_poly_clear(prod);

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
    calc_d(d, ctx->H, key->s, ctx->L); // d = ⌈Hs⌋_{2^ZETA →2^{2η}}
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

    /* The rounding relation (3) of the paper, which the proofs of correct
     * encryption and decryption are to show: 2^(ζ-2η) d + r = Hs mod 2^ζ with
     * r in [-2^(ζ-2η)/2, 2^(ζ-2η)/2), against Hs computed over the integers. */
    TEST_BEGIN("the OTSE pad is the rounding of Hs mod 2^zeta") {
        nmod_poly_mat_t d;
        fmpz_poly_t h, s, t;
        int ok = 1;
        slong shift = 1L << (ZETA - 2 * ETA);

        nmod_poly_mat_init(d, K_LWE + ctx->L, 1, MOD_Q);
        calc_d(d, ctx->H, key->s, ctx->L);
        fmpz_poly_init(h);
        fmpz_poly_init(s);
        fmpz_poly_init(t);
        for (slong i = 0; i < K_LWE + ctx->L && ok; i++) {
            slong hs[DEGREE_N] = { 0 };

            for (slong j = 0; j < K_LWR; j++) {
                fmpz_poly_set_nmod_poly_unsigned(h, nmod_poly_mat_entry(ctx->H, i, j));
                fmpz_poly_set_nmod_poly_unsigned(s, nmod_poly_mat_entry(key->s, j, 0));
                fmpz_poly_mul(t, h, s);
                for (slong k = 0; k < fmpz_poly_length(t); k++) {
                    slong c = fmpz_get_si(fmpz_poly_get_coeff_ptr(t, k));
                    hs[k % DEGREE_N] += (k < DEGREE_N) ? c : -c;
                }
            }
            for (slong k = 0; k < DEGREE_N; k++) {
                slong x = ((hs[k] % (1L << ZETA)) + (1L << ZETA)) % (1L << ZETA);
                slong dk = (slong) nmod_poly_get_coeff_ui(nmod_poly_mat_entry(d, i, 0), k);
                slong r = ((x - shift * dk) % (1L << ZETA) + (1L << ZETA)) % (1L << ZETA);

                if (r >= (1L << ZETA) / 2) {
                    r -= 1L << ZETA;
                }
                if (dk >= (1L << (2 * ETA)) || r < -shift / 2 || r >= shift / 2) {
                    ok = 0;
                }
            }
        }
        fmpz_poly_clear(h);
        fmpz_poly_clear(s);
        fmpz_poly_clear(t);
        nmod_poly_mat_clear(d);
        TEST_ASSERT(ok, end)
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


