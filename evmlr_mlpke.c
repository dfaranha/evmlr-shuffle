#include "evmlr_mlpke.h"
#include "evmlr_utils.h"
#ifdef MAIN
#include "test.h"
#include "bench.h"
#endif


void evmlr_mlpke_ctx_init(evmlr_mlpke_ctx_t ctx) {
    nmod_poly_init(ctx->cyclo_poly, MOD_Q);
    // Initialize cyclotomic polynomial x^N + 1
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, DEGREE_N, 1);
    nmod_poly_set_coeff_ui(ctx->cyclo_poly, 0, 1);
}

void evmlr_mlpke_ctx_clear(evmlr_mlpke_ctx_t ctx) {
    nmod_poly_clear(ctx->cyclo_poly);
}

void evmlr_mlpke_keypair_gen(evmlr_mlpke_keypair_t keypair, flint_rand_t state, const evmlr_mlpke_ctx_t ctx) {
    // Generate secret key s and error e with coefficients from B_eta
    nmod_poly_mat_t e;
    nmod_poly_mat_init(keypair->sk->s, K_LWE, 1, MOD_Q);
    nmod_poly_mat_init(e, K_LWE, 1, MOD_Q);
    evmlr_utils_binom_sample_mat_ring(keypair->sk->s, ETA);
    evmlr_utils_binom_sample_mat_ring(e, ETA);

    // Generate public matrix A with uniform random coefficients
    nmod_poly_mat_init(keypair->pk->A, K_LWE, K_LWE, MOD_Q);
    nmod_poly_mat_randtest(keypair->pk->A, state, DEGREE_N);

    nmod_poly_mat_init(keypair->pk->t, K_LWE, 1, MOD_Q);
    nmod_poly_mat_zero(keypair->pk->t);

    // Compute t = A * s + e
    nmod_poly_mat_mulmod(keypair->pk->t, keypair->pk->A, keypair->sk->s, ctx->cyclo_poly);
    nmod_poly_mat_add(keypair->pk->t, keypair->pk->t, e);

    nmod_poly_mat_clear(e);
}

void evmlr_mlpke_keypair_clear(evmlr_mlpke_keypair_t keypair) {
    // Clear secret key
    nmod_poly_mat_clear(keypair->sk->s);
    // Clear public key
    nmod_poly_mat_clear(keypair->pk->A);
    nmod_poly_mat_clear(keypair->pk->t);
}

void evmlr_mlpke_cipher_init(evmlr_mlpke_cipher_t cipher) {
    nmod_poly_mat_init(cipher->uT, 1, K_LWE, MOD_Q);
    nmod_poly_init(cipher->v, MOD_Q);
}

void evmlr_mlpke_enc_with_secrets(evmlr_mlpke_cipher_t cipher, nmod_poly_mat_t r, nmod_poly_mat_t e2, nmod_poly_t e3, const nmod_poly_t msg, const evmlr_mlpke_pk_t pk, const evmlr_mlpke_ctx_t ctx) {
    nmod_poly_mat_t tmp;
    nmod_poly_mat_init(tmp, 1, 1, MOD_Q);

    // Compute u^T = r^T A + e_2^T (cipher is owned by the caller)
    nmod_poly_mat_mulmod(cipher->uT, r, pk->A, ctx->cyclo_poly);
    nmod_poly_mat_add(cipher->uT, cipher->uT, e2);

    // c = q/2 getting the closest integer with ties rounded up
    ulong c = (MOD_Q + 1) / 2;
    // Compute v = r^T t + e_3 + c * msg

    nmod_poly_mat_mulmod(tmp, r, pk->t, ctx->cyclo_poly); // r^T t
    nmod_poly_struct* poly = nmod_poly_mat_entry(tmp, 0, 0);

    nmod_poly_add(cipher->v, poly, e3); // + e_3
    nmod_poly_scalar_mul_nmod(poly, msg, c); // c * msg
    nmod_poly_add(cipher->v, cipher->v, poly); // + c * msg

    nmod_poly_mat_clear(tmp);
}

void evmlr_mlpke_enc(evmlr_mlpke_cipher_t cipher, const nmod_poly_t msg, const evmlr_mlpke_pk_t pk, const evmlr_mlpke_ctx_t ctx) {
    nmod_poly_mat_t r, e2;
    nmod_poly_t e3;

    nmod_poly_mat_init(r, 1, K_LWE, MOD_Q);
    nmod_poly_mat_init(e2, 1, K_LWE, MOD_Q);
    // Sample r and e2 from B^{k_lwe}_{eta}, we already make them transpose
    evmlr_utils_binom_sample_mat_ring(r, ETA);
    evmlr_utils_binom_sample_mat_ring(e2, ETA);

    // Sample e3 from B_{eta}
    nmod_poly_init(e3, MOD_Q);
    evmlr_utils_binom_sample_ring(e3, ETA);

    evmlr_mlpke_enc_with_secrets(cipher, r, e2, e3, msg, pk, ctx);

    nmod_poly_mat_clear(r);
    nmod_poly_mat_clear(e2);
    nmod_poly_clear(e3);
}

void evmlr_mlpke_dec(nmod_poly_t msg, const evmlr_mlpke_cipher_t cipher, const evmlr_mlpke_sk_t sk, const evmlr_mlpke_ctx_t ctx) {
    // \tilde{m} = v - u^T s
    nmod_poly_t m_tilde;
    nmod_poly_mat_t tmp;
    nmod_poly_init(m_tilde, MOD_Q);
    nmod_poly_mat_init(tmp, 1, 1, MOD_Q);
    nmod_poly_set(m_tilde, cipher->v);

    nmod_poly_mat_mul(tmp, cipher->uT, sk->s);
    nmod_poly_struct* poly = nmod_poly_mat_entry(tmp, 0, 0);
    nmod_poly_rem(poly, poly, ctx->cyclo_poly);

    nmod_poly_sub(m_tilde, m_tilde, poly);

    nmod_poly_zero(msg); // msg is owned by the caller
    // msg = 0 if \tilde{m} is closer to 0 than to q/2, and 1 otherwise
    ulong threshold = (MOD_Q) / 4;
    for (slong i = 0; i < DEGREE_N; i++) {
        ulong coeff = nmod_poly_get_coeff_ui(m_tilde, i);
        if (coeff > threshold && coeff < (MOD_Q - threshold)) {
            nmod_poly_set_coeff_ui(msg, i, 1); // closer to q/2
        } else {
            nmod_poly_set_coeff_ui(msg, i, 0); // closer to 0
        }
    }

    nmod_poly_clear(m_tilde);
    nmod_poly_mat_clear(tmp);
}

void evmlr_mlpke_cipher_clear(evmlr_mlpke_cipher_t cipher) {
    nmod_poly_mat_clear(cipher->uT);
    nmod_poly_clear(cipher->v);
}

#ifdef MAIN
#include "evmlr_main.h"
static void test(flint_rand_t rand, evmlr_mlpke_ctx_t ctx) {
    evmlr_mlpke_keypair_t keypair;
    evmlr_mlpke_cipher_t cipher;
    evmlr_mlpke_cipher_init(cipher);
    evmlr_mlpke_keypair_gen(keypair, rand, ctx);

    nmod_poly_t msg, decrypted_msg;
    nmod_poly_init(msg, MOD_Q);
    nmod_poly_init(decrypted_msg, MOD_Q);

    ulong msg_val[1];
    evmlr_utils_random(msg_val, sizeof(ulong));
    evmlr_utils_int_to_bin(msg, msg_val[0]);

    TEST_BEGIN("encryption and decryption are consistent") {
        evmlr_mlpke_enc(cipher, msg, keypair->pk, ctx);
        evmlr_mlpke_dec(decrypted_msg, cipher, keypair->sk, ctx);
        TEST_ASSERT(nmod_poly_equal(msg, decrypted_msg) == 1, end)
    } TEST_END;

    // clear memory
    end:
        evmlr_mlpke_cipher_clear(cipher);
        evmlr_mlpke_keypair_clear(keypair);
        nmod_poly_clear(msg);
        nmod_poly_clear(decrypted_msg);
}

static void bench(flint_rand_t rand, evmlr_mlpke_ctx_t ctx) {
    evmlr_mlpke_keypair_t keypair;
    evmlr_mlpke_keypair_gen(keypair, rand, ctx);

    nmod_poly_t msg, decrypted_msg;
    nmod_poly_init(msg, MOD_Q);
    nmod_poly_init(decrypted_msg, MOD_Q);

    evmlr_mlpke_cipher_t cipher;
    evmlr_mlpke_cipher_init(cipher);

    BENCH_BEGIN("evmlr_mlpke_keypair_gen") {
        BENCH_ADD(evmlr_mlpke_keypair_gen(keypair, rand, ctx))
    } BENCH_END;

    ulong msg_val[1];
    evmlr_utils_random(msg_val, sizeof(ulong));
    evmlr_utils_int_to_bin(msg, msg_val[0]);

    BENCH_BEGIN("evmlr_mlpke_enc") {
        BENCH_ADD(evmlr_mlpke_enc(cipher, msg, keypair->pk, ctx))
    } BENCH_END;

    BENCH_BEGIN("evmlr_mlpke_dec") {
        BENCH_ADD(evmlr_mlpke_dec(decrypted_msg, cipher, keypair->sk, ctx))
    } BENCH_END;

    // clear memory
    evmlr_mlpke_cipher_clear(cipher);
    evmlr_mlpke_keypair_clear(keypair);
    nmod_poly_clear(msg);
    nmod_poly_clear(decrypted_msg);
}


int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);

    flint_rand_t state;
    evmlr_rand_init(state);

    evmlr_mlpke_ctx_t ctx;
    evmlr_mlpke_ctx_init(ctx);

    if (evmlr_runs_tests(mode))   test(state, ctx);
    if (evmlr_runs_benches(mode)) bench(state, ctx);

    evmlr_mlpke_ctx_clear(ctx);
    flint_rand_clear(state);

    return test_status();
}
#endif