#include "evmlr_enc_proof.h"
#include "evmlr_utils.h"
#include <stdlib.h>

static void build_A_hpke(nmod_poly_mat_t A_hpke, const evmlr_mlpke_pk_t pk) {
    nmod_poly_mat_zero(A_hpke);
    ulong shift = (MOD_Q + 1) / 2;
    for (int i = 0; i < K_LWR; i++) {
        slong offset = i * (K_LWE + 1);
        // Copy A^T
        for (int r = 0; r < K_LWE; r++) {
            for (int c = 0; c < K_LWE; c++) {
                nmod_poly_set(nmod_poly_mat_entry(A_hpke, offset + r, offset + c),
                              nmod_poly_mat_entry(pk->A, c, r));
            }
        }
        // Copy t^T
        for (int c = 0; c < K_LWE; c++) {
            nmod_poly_set(nmod_poly_mat_entry(A_hpke, offset + K_LWE, offset + c),
                          nmod_poly_mat_entry(pk->t, c, 0));
        }
        // Set shift in the bottom-right of the block
        nmod_poly_set_coeff_ui(nmod_poly_mat_entry(A_hpke, offset + K_LWE, offset + K_LWE), 0, shift);
    }
}

static void build_A_otse(nmod_poly_mat_t A_otse, const nmod_poly_mat_t H_prime, slong L_in) {
    slong cols = 2 * ETA * (K_LWE + L_in);
    nmod_poly_mat_zero(A_otse);
    for (slong r = 0; r < L_in; r++) {
        for (slong c = 0; c < cols; c++) {
            slong b = c / (K_LWE + L_in);
            slong idx = c % (K_LWE + L_in);
            nmod_poly_struct* entry = nmod_poly_mat_entry(A_otse, r, c);
            nmod_poly_struct* h_prime_entry = nmod_poly_mat_entry(H_prime, r, idx);
            if (b < ETA) {
                nmod_poly_set(entry, h_prime_entry);
            } else {
                nmod_poly_neg(entry, h_prime_entry);
            }
        }
    }
}

static void truncate_d_dagger(nmod_poly_mat_t d_dagger_trunc, const nmod_poly_mat_t d_dagger, slong L_in, slong L_max) {
    nmod_poly_mat_zero(d_dagger_trunc);
    for (int b = 0; b < 2 * ETA; b++) {
        slong src_offset = b * (K_LWE + L_max);
        slong dst_offset = b * (K_LWE + L_in);
        for (int i = 0; i < K_LWE + L_in; i++) {
            nmod_poly_set(nmod_poly_mat_entry(d_dagger_trunc, dst_offset + i, 0),
                          nmod_poly_mat_entry(d_dagger, src_offset + i, 0));
        }
    }
}

/*
 * The contexts of the two linear proofs, shared by init, prove and verify.
 * Both use Gaussian masks with rejection sampling and a norm bound. prove and
 * verify used to build bare contexts, which default to binomial masks whose
 * rejection test and norm check both accept everything: z = y + c s was
 * published without rejection, so it was not independent of the witness, and
 * the verifier bounded nothing.
 */
static void ctx_hpke_init(evmlr_lin_proof_ctx_t ctx) {
    evmlr_lin_proof_ctx_init(ctx, K_LWR * (K_LWE + 1), K_LWR * (K_LWE + 1));
    evmlr_lin_proof_ctx_set_gaussian(ctx, ETA); // r, e2, e3 are CBD(ETA), s is binary
}

static void ctx_otse_init(evmlr_lin_proof_ctx_t ctx, slong L) {
    evmlr_lin_proof_ctx_init(ctx, L, 2 * ETA * (K_LWE + L));
    evmlr_lin_proof_ctx_set_gaussian(ctx, 1); // d_dagger is binary
}

void evmlr_enc_proof_init(evmlr_enc_proof_t proof, slong L_curr) {
    evmlr_lin_proof_ctx_t ctx_hpke;
    ctx_hpke_init(ctx_hpke);
    evmlr_lin_proof_init(&proof->proof_hpke, ctx_hpke);
    evmlr_lin_proof_ctx_clear(ctx_hpke);

    evmlr_lin_proof_ctx_t ctx_otse;
    ctx_otse_init(ctx_otse, L_curr);
    evmlr_lin_proof_init(&proof->proof_otse, ctx_otse);
    evmlr_lin_proof_ctx_clear(ctx_otse);
}

void evmlr_enc_proof_clear(evmlr_enc_proof_t proof) {
    evmlr_lin_proof_clear(&proof->proof_hpke);
    evmlr_lin_proof_clear(&proof->proof_otse);
}

void evmlr_enc_proof_copy(evmlr_enc_proof_t dest, const evmlr_enc_proof_t src) {
    nmod_poly_mat_set(dest->proof_hpke.w, src->proof_hpke.w);
    nmod_poly_mat_set(dest->proof_hpke.z_1, src->proof_hpke.z_1);
    nmod_poly_mat_set(dest->proof_hpke.z_2, src->proof_hpke.z_2);

    nmod_poly_mat_set(dest->proof_otse.w, src->proof_otse.w);
    nmod_poly_mat_set(dest->proof_otse.z_1, src->proof_otse.z_1);
    nmod_poly_mat_set(dest->proof_otse.z_2, src->proof_otse.z_2);
}

void evmlr_enc_proof_prove(evmlr_enc_proof_t proof,
                           const evmlr_mlpke_pk_t pk,
                           const evmlr_otse_ctx_t otse_ctx,
                           const nmod_poly_mat_t* r_mats,
                           const nmod_poly_mat_t* e2_mats,
                           const nmod_poly_t* e3_polys,
                           const evmlr_otse_key_t key,
                           const evmlr_hpke_cipher_t cipher,
                           const nmod_poly_mat_t d_dagger,
                           const nmod_poly_mat_t plaintext,
                           slong L_in,
                           slong L_max) {
    // 1. HPKE proof of correct encryption
    slong hpke_dim = K_LWR * (K_LWE + 1);
    nmod_poly_mat_t A_hpke, s1_hpke, s2_hpke, t_hpke;
    nmod_poly_mat_init(A_hpke, hpke_dim, hpke_dim, MOD_Q);
    nmod_poly_mat_init(s1_hpke, hpke_dim, 1, MOD_Q);
    nmod_poly_mat_init(s2_hpke, hpke_dim, 1, MOD_Q);
    nmod_poly_mat_init(t_hpke, hpke_dim, 1, MOD_Q);

    build_A_hpke(A_hpke, pk);

    for (int i = 0; i < K_LWR; i++) {
        slong offset = i * (K_LWE + 1);
        for (int r = 0; r < K_LWE; r++) {
            nmod_poly_set(nmod_poly_mat_entry(s1_hpke, offset + r, 0),
                          nmod_poly_mat_entry(r_mats[i], 0, r)); // r_mats is 1 x K_LWE
            nmod_poly_set(nmod_poly_mat_entry(s2_hpke, offset + r, 0),
                          nmod_poly_mat_entry(e2_mats[i], 0, r)); // e2_mats is 1 x K_LWE
            nmod_poly_set(nmod_poly_mat_entry(t_hpke, offset + r, 0),
                          nmod_poly_mat_entry(cipher->enc_cipher[i]->uT, 0, r)); // uT is 1 x K_LWE
        }
        nmod_poly_set(nmod_poly_mat_entry(s1_hpke, offset + K_LWE, 0),
                      nmod_poly_mat_entry(key->s, i, 0));
        nmod_poly_set(nmod_poly_mat_entry(s2_hpke, offset + K_LWE, 0),
                      e3_polys[i]);
        nmod_poly_set(nmod_poly_mat_entry(t_hpke, offset + K_LWE, 0),
                      cipher->enc_cipher[i]->v);
    }

    evmlr_lin_proof_ctx_t ctx_hpke;
    ctx_hpke_init(ctx_hpke);
    evmlr_lin_prove(&proof->proof_hpke, A_hpke, s1_hpke, s2_hpke, t_hpke, ctx_hpke);
    evmlr_lin_proof_ctx_clear(ctx_hpke);

    nmod_poly_mat_clear(A_hpke);
    nmod_poly_mat_clear(s1_hpke);
    nmod_poly_mat_clear(s2_hpke);
    nmod_poly_mat_clear(t_hpke);

    // 2. OTSE proof of correct encryption
    slong otse_m = 2 * ETA * (K_LWE + L_in);
    nmod_poly_mat_t A_otse, s1_otse, s2_otse, t_otse;
    nmod_poly_mat_init(A_otse, L_in, otse_m, MOD_Q);
    nmod_poly_mat_init(s1_otse, otse_m, 1, MOD_Q);
    nmod_poly_mat_init(s2_otse, L_in, 1, MOD_Q);
    nmod_poly_mat_init(t_otse, L_in, 1, MOD_Q);

    build_A_otse(A_otse, otse_ctx->H_prime, L_in);
    truncate_d_dagger(s1_otse, d_dagger, L_in, L_max);
    nmod_poly_mat_zero(s2_otse);

    for (slong i = 0; i < L_in; i++) {
        nmod_poly_sub(nmod_poly_mat_entry(t_otse, i, 0),
                      nmod_poly_mat_entry(cipher->otse_cipher->c, i, 0),
                      nmod_poly_mat_entry(plaintext, i, 0));
    }

    evmlr_lin_proof_ctx_t ctx_otse;
    ctx_otse_init(ctx_otse, L_in);
    evmlr_lin_prove(&proof->proof_otse, A_otse, s1_otse, s2_otse, t_otse, ctx_otse);
    evmlr_lin_proof_ctx_clear(ctx_otse);

    nmod_poly_mat_clear(A_otse);
    nmod_poly_mat_clear(s1_otse);
    nmod_poly_mat_clear(s2_otse);
    nmod_poly_mat_clear(t_otse);
}

int evmlr_enc_proof_verify(const evmlr_enc_proof_t proof,
                           const evmlr_mlpke_pk_t pk,
                           const evmlr_otse_ctx_t otse_ctx,
                           const evmlr_hpke_cipher_t cipher,
                           const nmod_poly_mat_t decrypted_plaintext,
                           slong L_max) {
    slong L_in = decrypted_plaintext->r;

    // 1. Verify HPKE proof
    slong hpke_dim = K_LWR * (K_LWE + 1);
    nmod_poly_mat_t A_hpke, t_hpke;
    nmod_poly_mat_init(A_hpke, hpke_dim, hpke_dim, MOD_Q);
    nmod_poly_mat_init(t_hpke, hpke_dim, 1, MOD_Q);

    build_A_hpke(A_hpke, pk);

    for (int i = 0; i < K_LWR; i++) {
        slong offset = i * (K_LWE + 1);
        for (int r = 0; r < K_LWE; r++) {
            nmod_poly_set(nmod_poly_mat_entry(t_hpke, offset + r, 0),
                          nmod_poly_mat_entry(cipher->enc_cipher[i]->uT, 0, r));
        }
        nmod_poly_set(nmod_poly_mat_entry(t_hpke, offset + K_LWE, 0),
                      cipher->enc_cipher[i]->v);
    }

    evmlr_lin_proof_ctx_t ctx_hpke;
    ctx_hpke_init(ctx_hpke);
    int hpke_ok = evmlr_lin_verify(&proof->proof_hpke, A_hpke, t_hpke, ctx_hpke);
    evmlr_lin_proof_ctx_clear(ctx_hpke);

    nmod_poly_mat_clear(A_hpke);
    nmod_poly_mat_clear(t_hpke);

    if (!hpke_ok) return 0;

    // 2. Verify OTSE proof
    slong otse_m = 2 * ETA * (K_LWE + L_in);
    nmod_poly_mat_t A_otse, t_otse;
    nmod_poly_mat_init(A_otse, L_in, otse_m, MOD_Q);
    nmod_poly_mat_init(t_otse, L_in, 1, MOD_Q);

    build_A_otse(A_otse, otse_ctx->H_prime, L_in);

    for (slong i = 0; i < L_in; i++) {
        nmod_poly_sub(nmod_poly_mat_entry(t_otse, i, 0),
                      nmod_poly_mat_entry(cipher->otse_cipher->c, i, 0),
                      nmod_poly_mat_entry(decrypted_plaintext, i, 0));
    }

    evmlr_lin_proof_ctx_t ctx_otse;
    ctx_otse_init(ctx_otse, L_in);
    int otse_ok = evmlr_lin_verify(&proof->proof_otse, A_otse, t_otse, ctx_otse);
    evmlr_lin_proof_ctx_clear(ctx_otse);

    nmod_poly_mat_clear(A_otse);
    nmod_poly_mat_clear(t_otse);

    return otse_ok;
}

#ifdef MAIN
#include "evmlr_main.h"

#include "test.h"
#include "bench.h"
#include "cpucycles.h"

void test_enc_proof(flint_rand_t state) {
    slong L_max = M_LEN;
    slong L_in = M_LEN;

    evmlr_hpke_ctx_t hpke_ctx;
    evmlr_hpke_ctx_init(hpke_ctx, L_max, state);

    evmlr_hpke_keypair_t keypair;
    evmlr_hpke_keypair_gen(keypair, state, hpke_ctx);

    nmod_poly_mat_t msg, msg_padded;
    nmod_poly_mat_init(msg, L_in, 1, MOD_Q);
    nmod_poly_mat_init(msg_padded, L_max, 1, MOD_Q);
    nmod_poly_mat_randtest(msg, state, DEGREE_N);
    nmod_poly_mat_zero(msg_padded);
    for (slong i = 0; i < L_in; i++) {
        nmod_poly_set(nmod_poly_mat_entry(msg_padded, i, 0), nmod_poly_mat_entry(msg, i, 0));
    }

    evmlr_otse_key_t key;
    evmlr_otse_keygen(key, state);

    nmod_poly_mat_t r_mats[K_LWR];
    nmod_poly_mat_t e2_mats[K_LWR];
    nmod_poly_t e3_polys[K_LWR];

    evmlr_hpke_cipher_t cipher;
    evmlr_hpke_cipher_init(cipher, hpke_ctx->otse_ctx->L);
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_init(r_mats[i], 1, K_LWE, MOD_Q);
        nmod_poly_mat_init(e2_mats[i], 1, K_LWE, MOD_Q);
        evmlr_utils_binom_sample_mat_ring(r_mats[i], ETA);
        evmlr_utils_binom_sample_mat_ring(e2_mats[i], ETA);

        nmod_poly_init(e3_polys[i], MOD_Q);
        evmlr_utils_binom_sample_ring(e3_polys[i], ETA);

        evmlr_mlpke_enc_with_secrets(cipher->enc_cipher[i], r_mats[i], e2_mats[i], e3_polys[i],
                                     nmod_poly_mat_entry(key->s, i, 0), keypair->enc_keypair->pk, hpke_ctx->enc_ctx);
    }

    nmod_poly_mat_t d_dagger;
    nmod_poly_mat_init(d_dagger, 2 * ETA * (K_LWE + L_max), 1, MOD_Q);
    evmlr_otse_encrypt(cipher->otse_cipher, d_dagger, msg_padded, key, hpke_ctx->otse_ctx);

    evmlr_enc_proof_t proof;
    evmlr_enc_proof_init(proof, L_max);

    TEST_BEGIN("encryption proof can be created and verified") {
        evmlr_enc_proof_prove(proof, keypair->enc_keypair->pk, hpke_ctx->otse_ctx,
                              r_mats, e2_mats, e3_polys, key, cipher, d_dagger,
                              msg, L_in, L_max);
        int valid = evmlr_enc_proof_verify(proof, keypair->enc_keypair->pk, hpke_ctx->otse_ctx,
                                           cipher, msg, L_max);
        TEST_ASSERT(valid == 1, end);
    } TEST_END;

end:
    evmlr_enc_proof_clear(proof);
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_clear(r_mats[i]);
        nmod_poly_mat_clear(e2_mats[i]);
        nmod_poly_clear(e3_polys[i]);
    }
    evmlr_otse_keyclear(key);
    nmod_poly_mat_clear(d_dagger);
    nmod_poly_mat_clear(msg);
    nmod_poly_mat_clear(msg_padded);
    evmlr_hpke_cipher_clear(cipher);
    evmlr_hpke_keypair_clear(keypair);
    evmlr_hpke_ctx_clear(hpke_ctx);
}

void bench_enc_proof(flint_rand_t state) {
    slong L_max = M_LEN;
    slong L_in = M_LEN;

    evmlr_hpke_ctx_t hpke_ctx;
    evmlr_hpke_ctx_init(hpke_ctx, L_max, state);

    evmlr_hpke_keypair_t keypair;
    evmlr_hpke_keypair_gen(keypair, state, hpke_ctx);

    nmod_poly_mat_t msg, msg_padded;
    nmod_poly_mat_init(msg, L_in, 1, MOD_Q);
    nmod_poly_mat_init(msg_padded, L_max, 1, MOD_Q);
    nmod_poly_mat_randtest(msg, state, DEGREE_N);
    nmod_poly_mat_zero(msg_padded);
    for (slong i = 0; i < L_in; i++) {
        nmod_poly_set(nmod_poly_mat_entry(msg_padded, i, 0), nmod_poly_mat_entry(msg, i, 0));
    }

    evmlr_otse_key_t key;
    evmlr_otse_keygen(key, state);

    nmod_poly_mat_t r_mats[K_LWR];
    nmod_poly_mat_t e2_mats[K_LWR];
    nmod_poly_t e3_polys[K_LWR];

    evmlr_hpke_cipher_t cipher;
    evmlr_hpke_cipher_init(cipher, hpke_ctx->otse_ctx->L);
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_init(r_mats[i], 1, K_LWE, MOD_Q);
        nmod_poly_mat_init(e2_mats[i], 1, K_LWE, MOD_Q);
        evmlr_utils_binom_sample_mat_ring(r_mats[i], ETA);
        evmlr_utils_binom_sample_mat_ring(e2_mats[i], ETA);

        nmod_poly_init(e3_polys[i], MOD_Q);
        evmlr_utils_binom_sample_ring(e3_polys[i], ETA);

        evmlr_mlpke_enc_with_secrets(cipher->enc_cipher[i], r_mats[i], e2_mats[i], e3_polys[i],
                                     nmod_poly_mat_entry(key->s, i, 0), keypair->enc_keypair->pk, hpke_ctx->enc_ctx);
    }

    nmod_poly_mat_t d_dagger;
    nmod_poly_mat_init(d_dagger, 2 * ETA * (K_LWE + L_max), 1, MOD_Q);
    evmlr_otse_encrypt(cipher->otse_cipher, d_dagger, msg_padded, key, hpke_ctx->otse_ctx);

    evmlr_enc_proof_t proof;
    evmlr_enc_proof_init(proof, L_max);

    BENCH_BEGIN("Encryption ZK proof generation") {
        BENCH_ADD(evmlr_enc_proof_prove(proof, keypair->enc_keypair->pk, hpke_ctx->otse_ctx,
                                        r_mats, e2_mats, e3_polys, key, cipher, d_dagger,
                                        msg, L_in, L_max));
    } BENCH_END;

    BENCH_BEGIN("Encryption ZK proof verification") {
        BENCH_ADD(evmlr_enc_proof_verify(proof, keypair->enc_keypair->pk, hpke_ctx->otse_ctx,
                                         cipher, msg, L_max));
    } BENCH_END;

    evmlr_enc_proof_clear(proof);
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_clear(r_mats[i]);
        nmod_poly_mat_clear(e2_mats[i]);
        nmod_poly_clear(e3_polys[i]);
    }
    evmlr_otse_keyclear(key);
    nmod_poly_mat_clear(d_dagger);
    nmod_poly_mat_clear(msg);
    nmod_poly_mat_clear(msg_padded);
    evmlr_hpke_cipher_clear(cipher);
    evmlr_hpke_keypair_clear(keypair);
    evmlr_hpke_ctx_clear(hpke_ctx);
}

void bench_layered_enc_proof(flint_rand_t state) {
    slong k_layers = 5;
    slong L_max = (k_layers - 1) * K_LWR * (K_LWE + 1) + 1;

    evmlr_hpke_ctx_t hpke_ctx;
    evmlr_hpke_ctx_init(hpke_ctx, L_max, state);

    // Generate keys for each layer
    evmlr_hpke_keypair_t keypairs[5];
    for (slong j = 0; j < k_layers; j++) {
        evmlr_hpke_keypair_gen(keypairs[j], state, hpke_ctx);
    }

    printf("\n=== Layered Cipher ZK Proof Benchmark (k = %ld layers, L_max = %ld) ===\n", k_layers, L_max);

    // We start with a plain vote of size 1
    nmod_poly_mat_t current_msg;
    nmod_poly_mat_init(current_msg, 1, 1, MOD_Q);
    nmod_poly_mat_randtest(current_msg, state, DEGREE_N);

    // Layered encryption and proof generation
    for (slong j = k_layers - 1; j >= 0; j--) {
        slong L_in = current_msg->r;

        // Pad msg to L_max
        nmod_poly_mat_t msg_padded;
        nmod_poly_mat_init(msg_padded, L_max, 1, MOD_Q);
        nmod_poly_mat_zero(msg_padded);
        for (slong i = 0; i < L_in; i++) {
            nmod_poly_set(nmod_poly_mat_entry(msg_padded, i, 0), nmod_poly_mat_entry(current_msg, i, 0));
        }

        evmlr_otse_key_t key;
        evmlr_otse_keygen(key, state);

        nmod_poly_mat_t r_mats[K_LWR];
        nmod_poly_mat_t e2_mats[K_LWR];
        nmod_poly_t e3_polys[K_LWR];

        evmlr_hpke_cipher_t cipher;
        evmlr_hpke_cipher_init(cipher, hpke_ctx->otse_ctx->L);
        for (int i = 0; i < K_LWR; i++) {
            nmod_poly_mat_init(r_mats[i], 1, K_LWE, MOD_Q);
            nmod_poly_mat_init(e2_mats[i], 1, K_LWE, MOD_Q);
            evmlr_utils_binom_sample_mat_ring(r_mats[i], ETA);
            evmlr_utils_binom_sample_mat_ring(e2_mats[i], ETA);

            nmod_poly_init(e3_polys[i], MOD_Q);
            evmlr_utils_binom_sample_ring(e3_polys[i], ETA);

            evmlr_mlpke_enc_with_secrets(cipher->enc_cipher[i], r_mats[i], e2_mats[i], e3_polys[i],
                                         nmod_poly_mat_entry(key->s, i, 0), keypairs[j]->enc_keypair->pk, hpke_ctx->enc_ctx);
        }

        nmod_poly_mat_t d_dagger;
        nmod_poly_mat_init(d_dagger, 2 * ETA * (K_LWE + L_max), 1, MOD_Q);
        evmlr_otse_encrypt(cipher->otse_cipher, d_dagger, msg_padded, key, hpke_ctx->otse_ctx);

        evmlr_enc_proof_t proof;
        evmlr_enc_proof_init(proof, L_in);

        // Benchmark prove
        uint64_t start_prove = cpucycles();
        evmlr_enc_proof_prove(proof, keypairs[j]->enc_keypair->pk, hpke_ctx->otse_ctx,
                              r_mats, e2_mats, e3_polys, key, cipher, d_dagger,
                              current_msg, L_in, L_max);
        uint64_t end_prove = cpucycles();

        // Benchmark verify
        uint64_t start_verify = cpucycles();
        int valid = evmlr_enc_proof_verify(proof, keypairs[j]->enc_keypair->pk, hpke_ctx->otse_ctx,
                                           cipher, current_msg, L_max);
        uint64_t end_verify = cpucycles();

        printf("Layer %ld (L_in = %ld): prove = %lu cycles, verify = %lu cycles, status = %s\n",
               k_layers - j, L_in, (unsigned long)(end_prove - start_prove), (unsigned long)(end_verify - start_verify),
               valid ? "VALID" : "INVALID");

        // Serialize layer to prepare input for next level (if not the last one)
        if (j > 0) {
            nmod_poly_mat_clear(current_msg);
            slong L_next = (k_layers - j) * K_LWR * (K_LWE + 1) + 1;
            nmod_poly_mat_init(current_msg, L_next, 1, MOD_Q);
            
            // We serialize it manually using the serialized format:
            slong idx = 0;
            for (int i = 0; i < K_LWR; i++) {
                for (int j_lwe = 0; j_lwe < K_LWE; j_lwe++) {
                    nmod_poly_set(nmod_poly_mat_entry(current_msg, idx++, 0), nmod_poly_mat_entry(cipher->enc_cipher[i]->uT, 0, j_lwe));
                }
                nmod_poly_set(nmod_poly_mat_entry(current_msg, idx++, 0), cipher->enc_cipher[i]->v);
            }
            for (int i = 0; i < L_in; i++) {
                nmod_poly_set(nmod_poly_mat_entry(current_msg, idx++, 0), nmod_poly_mat_entry(cipher->otse_cipher->c, i, 0));
            }
        }

        // Cleanup this layer's temporary allocations
        evmlr_enc_proof_clear(proof);
        for (int i = 0; i < K_LWR; i++) {
            nmod_poly_mat_clear(r_mats[i]);
            nmod_poly_mat_clear(e2_mats[i]);
            nmod_poly_clear(e3_polys[i]);
        }
        evmlr_otse_keyclear(key);
        nmod_poly_mat_clear(d_dagger);
        nmod_poly_mat_clear(msg_padded);
        evmlr_hpke_cipher_clear(cipher);
    }

    // Cleanup global keys and contexts
    nmod_poly_mat_clear(current_msg);
    for (slong j = 0; j < k_layers; j++) {
        evmlr_hpke_keypair_clear(keypairs[j]);
    }
    evmlr_hpke_ctx_clear(hpke_ctx);
    printf("=======================================================================\n\n");
}

int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);

    flint_rand_t state;
    evmlr_rand_init(state);

    if (evmlr_runs_tests(mode)) test_enc_proof(state);
    if (evmlr_runs_benches(mode)) {
        bench_enc_proof(state);
        bench_layered_enc_proof(state);
    }

    flint_rand_clear(state);
    return test_status();
}

#endif
