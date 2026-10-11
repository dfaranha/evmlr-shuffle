#include "evmlr_ballot.h"
#include "evmlr_utils.h"
#include <stdlib.h>

#ifdef MAIN
#include "test.h"
#endif

slong evmlr_ballot_layer_len(slong k, slong i) {
    return (k - i - 1) * K_LWR * (K_LWE + 1) + 1;
}

/*============================================================================*/
/* Layered encryption, keeping the secrets                                    */
/*============================================================================*/

void evmlr_ballot_layers_init(evmlr_ballot_layer_struct *layers, slong k, slong L_max) {
    for (slong i = 0; i < k; i++) {
        nmod_poly_mat_init(layers[i].r, 1, K_LWE, MOD_Q);
        nmod_poly_mat_init(layers[i].e2, 1, K_LWE, MOD_Q);
        nmod_poly_init(layers[i].e3, MOD_Q);
        nmod_poly_mat_init(layers[i].sbar, K_LWR, 1, MOD_Q);
        nmod_poly_mat_init(layers[i].d_dagger, 2 * ETA * (K_LWE + L_max), 1, MOD_Q);
    }
}

void evmlr_ballot_layers_clear(evmlr_ballot_layer_struct *layers, slong k) {
    for (slong i = 0; i < k; i++) {
        nmod_poly_mat_clear(layers[i].r);
        nmod_poly_mat_clear(layers[i].e2);
        nmod_poly_clear(layers[i].e3);
        nmod_poly_mat_clear(layers[i].sbar);
        nmod_poly_mat_clear(layers[i].d_dagger);
    }
}

void evmlr_ballot_init(evmlr_ballot_struct *ballot, slong k) {
    for (int i = 0; i < K_LWR; i++) evmlr_mlpke_cipher_init(ballot->enc[i]);
    nmod_poly_mat_init(ballot->cstar, evmlr_ballot_layer_len(k, 0), 1, MOD_Q);
}

void evmlr_ballot_clear(evmlr_ballot_struct *ballot) {
    for (int i = 0; i < K_LWR; i++) evmlr_mlpke_cipher_clear(ballot->enc[i]);
    nmod_poly_mat_clear(ballot->cstar);
}

void evmlr_ballot_encrypt(evmlr_ballot_struct *ballot, evmlr_ballot_layer_struct *layers,
                        const nmod_poly_mat_t vote, slong k, const evmlr_mlpke_pk_t *pks,
                        const evmlr_hpke_ctx_t hpke) {
    const slong L_max = hpke->otse_ctx->L;
    nmod_poly_mat_t msg, padded;
    evmlr_otse_ciphertext_t ct;
    evmlr_mlpke_cipher_t enc[K_LWR];

    nmod_poly_mat_init(msg, vote->r, 1, MOD_Q);
    nmod_poly_mat_set(msg, vote);
    nmod_poly_mat_init(padded, L_max, 1, MOD_Q);
    evmlr_otse_ciphertext_init(ct, L_max);
    for (int r = 0; r < K_LWR; r++) evmlr_mlpke_cipher_init(enc[r]);
    for (slong j = k - 1; j >= 0; j--) {
        const slong L_j = evmlr_ballot_layer_len(k, j);
        evmlr_otse_key_t key;

        // The seed, encrypted under server j's key with secrets kept.
        evmlr_otse_keygen(key, NULL);
        nmod_poly_mat_set(layers[j].sbar, key->s);
        evmlr_utils_binom_sample_mat_ring(layers[j].r, ETA);
        evmlr_utils_binom_sample_mat_ring(layers[j].e2, ETA);
        evmlr_utils_binom_sample_ring(layers[j].e3, ETA);
        for (int r = 0; r < K_LWR; r++) {
            evmlr_mlpke_enc_with_secrets(enc[r], layers[j].r, layers[j].e2, layers[j].e3,
                                         nmod_poly_mat_entry(key->s, r, 0), pks[j], hpke->enc_ctx);
        }
        // The message, padded to L_max and masked; the ciphertext keeps L_j.
        nmod_poly_mat_zero(padded);
        for (slong y = 0; y < L_j; y++) {
            nmod_poly_set(nmod_poly_mat_entry(padded, y, 0), nmod_poly_mat_entry(msg, y, 0));
        }
        evmlr_otse_encrypt(ct, layers[j].d_dagger, padded, key, hpke->otse_ctx);
        evmlr_otse_keyclear(key);

        // Serialise (u, v, c*) as the next layer's message, as evmlr_voting does.
        nmod_poly_mat_clear(msg);
        nmod_poly_mat_init(msg, K_LWR * (K_LWE + 1) + L_j, 1, MOD_Q);
        slong idx = 0;
        for (int r = 0; r < K_LWR; r++) {
            for (int x = 0; x < K_LWE; x++) {
                nmod_poly_set(nmod_poly_mat_entry(msg, idx++, 0), nmod_poly_mat_entry(enc[r]->uT, 0, x));
            }
            nmod_poly_set(nmod_poly_mat_entry(msg, idx++, 0), enc[r]->v);
        }
        for (slong y = 0; y < L_j; y++) {
            nmod_poly_set(nmod_poly_mat_entry(msg, idx++, 0), nmod_poly_mat_entry(ct->c, y, 0));
        }
        if (j == 0) {
            for (int r = 0; r < K_LWR; r++) {
                nmod_poly_mat_set(ballot->enc[r]->uT, enc[r]->uT);
                nmod_poly_set(ballot->enc[r]->v, enc[r]->v);
            }
            for (slong y = 0; y < L_j; y++) {
                nmod_poly_set(nmod_poly_mat_entry(ballot->cstar, y, 0), nmod_poly_mat_entry(ct->c, y, 0));
            }
        }
    }
    for (int r = 0; r < K_LWR; r++) evmlr_mlpke_cipher_clear(enc[r]);
    evmlr_otse_ciphertext_clear(ct);
    nmod_poly_mat_clear(padded);
    nmod_poly_mat_clear(msg);
}

#ifdef MAIN
#include "evmlr_main.h"

#define BALLOT_K 3

/* Peels the k layers of ballot with the servers' keys, as the mixnet does. */
static void peel(nmod_poly_mat_t vote, const evmlr_ballot_struct *ballot, slong k,
                 const evmlr_mlpke_sk_t *sks, const evmlr_hpke_ctx_t hpke) {
    const slong L_max = hpke->otse_ctx->L;
    evmlr_mlpke_cipher_t enc;
    evmlr_otse_key_t key;
    evmlr_otse_ciphertext_t ct;
    nmod_poly_mat_t m;

    evmlr_mlpke_cipher_init(enc);
    nmod_poly_mat_init(key->s, K_LWR, 1, MOD_Q);
    evmlr_otse_ciphertext_init(ct, L_max);
    nmod_poly_mat_init(m, L_max, 1, MOD_Q);
    nmod_poly_mat_set(enc->uT, ballot->enc[0]->uT);
    nmod_poly_set(enc->v, ballot->enc[0]->v);
    nmod_poly_mat_zero(ct->c);
    for (slong y = 0; y < evmlr_ballot_layer_len(k, 0); y++) {
        nmod_poly_set(nmod_poly_mat_entry(ct->c, y, 0), nmod_poly_mat_entry(ballot->cstar, y, 0));
    }
    for (slong j = 0; j < k; j++) {
        const slong L_j = evmlr_ballot_layer_len(k, j);

        evmlr_mlpke_dec(nmod_poly_mat_entry(key->s, 0, 0), enc, sks[j], hpke->enc_ctx);
        evmlr_otse_decrypt(m, ct, key, hpke->otse_ctx);
        if (j == k - 1) break;
        // m[0..L_j) is the next layer: (u, v, c*).
        for (slong x = 0; x < K_LWE; x++) {
            nmod_poly_set(nmod_poly_mat_entry(enc->uT, 0, x), nmod_poly_mat_entry(m, x, 0));
        }
        nmod_poly_set(enc->v, nmod_poly_mat_entry(m, K_LWE, 0));
        nmod_poly_mat_zero(ct->c);
        for (slong y = 0; y + K_LWE + 1 < L_j; y++) {
            nmod_poly_set(nmod_poly_mat_entry(ct->c, y, 0), nmod_poly_mat_entry(m, K_LWE + 1 + y, 0));
        }
    }
    for (slong y = 0; y < vote->r; y++) {
        nmod_poly_set(nmod_poly_mat_entry(vote, y, 0), nmod_poly_mat_entry(m, y, 0));
    }
    evmlr_mlpke_cipher_clear(enc);
    nmod_poly_mat_clear(key->s);
    evmlr_otse_ciphertext_clear(ct);
    nmod_poly_mat_clear(m);
}

void test(flint_rand_t state) {
    const slong k = BALLOT_K, L_max = evmlr_ballot_layer_len(k, 0);
    evmlr_hpke_ctx_t hpke;
    evmlr_mlpke_keypair_t kp[BALLOT_K];
    evmlr_mlpke_pk_t pks[BALLOT_K];
    evmlr_mlpke_sk_t sks[BALLOT_K];
    evmlr_ballot_layer_struct layers[BALLOT_K];
    evmlr_ballot_struct ballot;
    nmod_poly_mat_t vote, out;

    evmlr_hpke_ctx_init(hpke, L_max, state);
    for (slong j = 0; j < k; j++) {
        evmlr_mlpke_keypair_gen(kp[j], state, hpke->enc_ctx);
        *pks[j] = *kp[j]->pk;
        *sks[j] = *kp[j]->sk;
    }
    nmod_poly_mat_init(vote, M_LEN, 1, MOD_Q);
    nmod_poly_mat_init(out, M_LEN, 1, MOD_Q);
    evmlr_utils_uniform_mat(vote);
    evmlr_ballot_layers_init(layers, k, L_max);
    evmlr_ballot_init(&ballot, k);
    evmlr_ballot_encrypt(&ballot, layers, vote, k, (const evmlr_mlpke_pk_t *) pks, hpke);

    TEST_ONCE("a layered ballot decrypts to the vote through every layer") {
        peel(out, &ballot, k, (const evmlr_mlpke_sk_t *) sks, hpke);
        TEST_ASSERT(nmod_poly_mat_equal(out, vote), end);
    } TEST_END;

end:
    evmlr_ballot_clear(&ballot);
    evmlr_ballot_layers_clear(layers, k);
    nmod_poly_mat_clear(vote);
    nmod_poly_mat_clear(out);
    for (slong j = 0; j < k; j++) evmlr_mlpke_keypair_clear(kp[j]);
    evmlr_hpke_ctx_clear(hpke);
}

int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);
    flint_rand_t state;

    evmlr_rand_init(state);
    if (evmlr_runs_tests(mode)) test(state);
    flint_rand_clear(state);
    return test_status();
}
#endif
