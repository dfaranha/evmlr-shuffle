#include "evmlr_voting.h"
#include "evmlr_utils.h"
#include <string.h>

#ifdef MAIN
#include "test.h"
#include "bench.h"
#include "cpucycles.h"
#include <sys/random.h>
#endif

// The inverse of the serialisation in evmlr_ballot_encrypt: an inner layer
// (u, v, c*) from the message that the outer layer decrypts to.
static void deserialize_layer(evmlr_voting_layer_t ct, const nmod_poly_mat_t msg, slong next_layer_len) {
    slong idx = 0;
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_init(ct->enc_cipher[i]->uT, 1, K_LWE, MOD_Q);
        nmod_poly_init(ct->enc_cipher[i]->v, MOD_Q);
        for (int j = 0; j < K_LWE; j++) {
            nmod_poly_set(nmod_poly_mat_entry(ct->enc_cipher[i]->uT, 0, j), nmod_poly_mat_entry(msg, idx++, 0));
        }
        nmod_poly_set(ct->enc_cipher[i]->v, nmod_poly_mat_entry(msg, idx++, 0));
    }
    nmod_poly_mat_init(ct->otse_cipher->c, next_layer_len, 1, MOD_Q);
    for (int i = 0; i < next_layer_len; i++) {
        nmod_poly_set(nmod_poly_mat_entry(ct->otse_cipher->c, i, 0), nmod_poly_mat_entry(msg, idx++, 0));
    }
}

extern void calc_a(nmod_poly_mat_t a, nmod_poly_mat_t d_dagger, const evmlr_otse_key_t key, const evmlr_otse_ctx_t ctx);

static void voting_decrypt_layer(nmod_poly_mat_t msg, nmod_poly_mat_t d_dagger, nmod_poly_mat_t a, const evmlr_voting_layer_t ct, const evmlr_mlpke_sk_t sk, const evmlr_voting_pp_t pp) {
    slong L_in = ct->otse_cipher->c->r;

    // Reconstruct key s
    evmlr_otse_key_t key;
    nmod_poly_t key_poly;
    nmod_poly_init(key_poly, MOD_Q);
    nmod_poly_mat_init(key->s, K_LWR, 1, MOD_Q);

    for (int i = 0; i < K_LWR; i++) {
        evmlr_mlpke_dec(key_poly, ct->enc_cipher[i], sk, pp->hpke_ctx->enc_ctx);
        nmod_poly_set(nmod_poly_mat_entry(key->s, i, 0), key_poly);
    }
    nmod_poly_clear(key_poly);

    // Call calc_a to get a and extract d_dagger
    nmod_poly_mat_init(a, pp->hpke_ctx->otse_ctx->L, 1, MOD_Q);
    calc_a(a, d_dagger, key, pp->hpke_ctx->otse_ctx);

    // m = c - a (truncated to L_in)
    nmod_poly_mat_init(msg, L_in, 1, MOD_Q);
    for (slong i = 0; i < L_in; i++) {
        nmod_poly_struct* msg_val = nmod_poly_mat_entry(msg, i, 0);
        nmod_poly_sub(msg_val, nmod_poly_mat_entry(ct->otse_cipher->c, i, 0), nmod_poly_mat_entry(a, i, 0));
    }

    evmlr_otse_keyclear(key);
}

static void sync_hpke_ctx(evmlr_hpke_ctx_t dst, const evmlr_hpke_ctx_t src) {
    nmod_poly_mat_set(dst->otse_ctx->H, src->otse_ctx->H);
    nmod_poly_mat_set(dst->otse_ctx->H_prime, src->otse_ctx->H_prime);
}

// setup(k, state) -> (pp, sk)
void evmlr_voting_setup(evmlr_voting_pp_t pp, evmlr_voting_sk_t sk, slong k, flint_rand_t state) {
    pp->k = k;
    sk->k = k;

    // Outer message input has length k * K_LWR * (K_LWE + 1) + 1.
    // Decrypting layer 1 yields length (k - 1) * K_LWR * (K_LWE + 1) + 1.
    // This is the maximum length of the messages being shuffled.
    pp->L_max = (k - 1) * K_LWR * (K_LWE + 1) + 1;

    // Initialize HPKE and Shuffle contexts.
    evmlr_hpke_ctx_init(pp->hpke_ctx, pp->L_max, state);
    evmlr_shuffle_ctx_init(pp->shuf_ctx, SHUFFLE_N_MSGS, pp->L_max, state);
    sync_hpke_ctx(pp->shuf_ctx->hpke_ctx, pp->hpke_ctx);

    // Allocate keys
    pp->pks = (evmlr_mlpke_pk_t*) malloc(k * sizeof(evmlr_mlpke_pk_t));
    sk->sks = (evmlr_mlpke_sk_t*) malloc(k * sizeof(evmlr_mlpke_sk_t));

    for (slong j = 0; j < k; j++) {
        nmod_poly_mat_init(pp->pks[j]->A, K_LWE, K_LWE, MOD_Q);
        nmod_poly_mat_init(pp->pks[j]->t, K_LWE, 1, MOD_Q);
        nmod_poly_mat_init(sk->sks[j]->s, K_LWE, 1, MOD_Q);

        evmlr_mlpke_keypair_t kp;
        evmlr_mlpke_keypair_gen(kp, state, pp->hpke_ctx->enc_ctx);
        
        nmod_poly_mat_set(pp->pks[j]->A, kp->pk->A);
        nmod_poly_mat_set(pp->pks[j]->t, kp->pk->t);
        nmod_poly_mat_set(sk->sks[j]->s, kp->sk->s);

        evmlr_mlpke_keypair_clear(kp);
    }
}

// casting(submission, voter_id, vote, pp, state)
void evmlr_voting_casting(evmlr_voting_submission_t submission, slong voter_id, const nmod_poly_mat_t vote, const evmlr_voting_pp_t pp, flint_rand_t state) {
    const slong k = pp->k;
    evmlr_ballot_layer_struct *layers = malloc(k * sizeof(evmlr_ballot_layer_struct));
    evmlr_ballot_struct ballot;
    (void) state;

    submission->voter_id = voter_id;
    evmlr_ballot_layers_init(layers, k, pp->L_max);
    evmlr_ballot_init(&ballot, k);
    evmlr_ballot_encrypt(&ballot, layers, vote, k, (const evmlr_mlpke_pk_t *) pp->pks, pp->hpke_ctx);
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_set(submission->ballot->layer->enc_cipher[i]->uT, ballot.enc[i]->uT);
        nmod_poly_set(submission->ballot->layer->enc_cipher[i]->v, ballot.enc[i]->v);
    }
    nmod_poly_mat_set(submission->ballot->layer->otse_cipher->c, ballot.cstar);
    // The proof of correct encryption, when LaZer is built in.
    if (evmlr_user_proof_available(k)) {
        evmlr_user_proof_prove(submission->proof, &ballot, layers, k,
                               (const evmlr_mlpke_pk_t *) pp->pks, pp->hpke_ctx->otse_ctx);
    }
    evmlr_ballot_clear(&ballot);
    evmlr_ballot_layers_clear(layers, k);
    free(layers);
}

int evmlr_voting_verify_submission(const evmlr_voting_pp_t pp, const evmlr_voting_submission_t sub) {
    const slong k = pp->k;
    evmlr_ballot_struct ballot;
    int ok;

    evmlr_ballot_init(&ballot, k);
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_set(ballot.enc[i]->uT, sub->ballot->layer->enc_cipher[i]->uT);
        nmod_poly_set(ballot.enc[i]->v, sub->ballot->layer->enc_cipher[i]->v);
    }
    nmod_poly_mat_set(ballot.cstar, sub->ballot->layer->otse_cipher->c);
    ok = evmlr_user_proof_verify(sub->proof, &ballot, k, (const evmlr_mlpke_pk_t *) pp->pks,
                                 pp->hpke_ctx->otse_ctx);
    evmlr_ballot_clear(&ballot);
    return ok;
}

/* Cycle counts of the phases of counting, for the benchmark. */
typedef struct {
    uint64_t verify_user, decrypt, shuffle_prove, shuffle_verify;
} counting_stats_t;

static uint64_t now_cycles(void) {
    uint64_t lo, hi;

    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return (hi << 32) | lo;
}

static slong counting_impl(nmod_poly_mat_t* results, evmlr_shuffle_proof_t* shuffle_proofs,
                           const evmlr_voting_submission_t* submissions, slong num_submissions,
                           const evmlr_voting_pp_t pp, const evmlr_voting_sk_t sk, flint_rand_t state,
                           counting_stats_t *stats) {
    slong k = pp->k;
    counting_stats_t dummy;
    uint64_t t0;

    if (stats == NULL) stats = &dummy;
    memset(stats, 0, sizeof(*stats));

    // 1. Drop the submissions whose proof of correct encryption fails: the
    // servers must not decrypt malformed ciphertexts (Section 3.3). Without
    // LaZer there are no proofs to check.
    int *valid = (int *) malloc(num_submissions * sizeof(int));
    t0 = now_cycles();
    for (slong i = 0; i < num_submissions; i++) {
        valid[i] = !evmlr_user_proof_available(k) || evmlr_voting_verify_submission(pp, submissions[i]);
        if (!valid[i]) {
            printf("Warning: proof of encryption failed for voter %ld; the ballot is dropped\n",
                   submissions[i]->voter_id);
        }
    }
    stats->verify_user = now_cycles() - t0;

    // 2. Apply the revote policy (the last valid submission counts) to get the
    // list of unique voter submissions.
    evmlr_voting_submission_struct** active_subs = (evmlr_voting_submission_struct**) malloc(num_submissions * sizeof(evmlr_voting_submission_struct*));
    slong N = 0;
    for (slong i = num_submissions - 1; i >= 0; i--) {
        if (!valid[i]) continue;
        slong voter_id = submissions[i]->voter_id;
        int found = 0;
        for (slong j = 0; j < N; j++) {
            if (active_subs[j]->voter_id == voter_id) {
                found = 1;
                break;
            }
        }
        if (!found) {
            active_subs[N++] = (evmlr_voting_submission_struct*) submissions[i];
        }
    }
    free(valid);
    // Reverse active_subs to maintain chronological order
    for (slong i = 0; i < N / 2; i++) {
        evmlr_voting_submission_struct* tmp = active_subs[i];
        active_subs[i] = active_subs[N - 1 - i];
        active_subs[N - 1 - i] = tmp;
    }

    if (N == 0) {
        free(active_subs);
        return 0;
    }

    // Re-initialize shuffle context for N unique submissions
    evmlr_shuffle_ctx_clear((evmlr_shuffle_ctx_struct *)pp->shuf_ctx);
    evmlr_shuffle_ctx_init((evmlr_shuffle_ctx_struct *)pp->shuf_ctx, N, pp->L_max, state);
    sync_hpke_ctx(((evmlr_shuffle_ctx_struct *)pp->shuf_ctx)->hpke_ctx, pp->hpke_ctx);

    // 3. The current ciphertexts, starting from the ballots.
    evmlr_voting_layer_struct* curr_cts = (evmlr_voting_layer_struct*) malloc(N * sizeof(evmlr_voting_layer_struct));
    for (slong i = 0; i < N; i++) {
        evmlr_voting_layer_init(&curr_cts[i], pp->L_max);
        for (int r = 0; r < K_LWR; r++) {
            nmod_poly_mat_set(curr_cts[i].enc_cipher[r]->uT, active_subs[i]->ballot->layer->enc_cipher[r]->uT);
            nmod_poly_set(curr_cts[i].enc_cipher[r]->v, active_subs[i]->ballot->layer->enc_cipher[r]->v);
        }
        nmod_poly_mat_set(curr_cts[i].otse_cipher->c, active_subs[i]->ballot->layer->otse_cipher->c);
    }

    nmod_poly_mat_t* decrypted_msgs = (nmod_poly_mat_t*) malloc(N * sizeof(nmod_poly_mat_t));
    nmod_poly_mat_t* shuffled_msgs = (nmod_poly_mat_t*) malloc(N * sizeof(nmod_poly_mat_t));

    // 4. Each server in turn removes a layer, shuffles, and proves both.
    int failed = 0;
    for (slong j = 0; j < k; j++) {
        slong L_next = (k - j - 1) * K_LWR * (K_LWE + 1) + 1;

        nmod_poly_mat_t* d_dagger = (nmod_poly_mat_t*) malloc(N * sizeof(nmod_poly_mat_t));
        nmod_poly_mat_t* a_mats = (nmod_poly_mat_t*) malloc(N * sizeof(nmod_poly_mat_t));

        t0 = now_cycles();
        for (slong i = 0; i < N; i++) {
            // d_dagger is owned by the caller; decryption only fills it in.
            nmod_poly_mat_init(d_dagger[i], 2 * ETA * (K_LWE + pp->hpke_ctx->otse_ctx->L), 1, MOD_Q);
            voting_decrypt_layer(decrypted_msgs[i], d_dagger[i], a_mats[i], &curr_cts[i], sk->sks[j], pp);
        }
        stats->decrypt += now_cycles() - t0;

        // Shuffle
        size_t* pi = (size_t *) malloc(N * sizeof(size_t));
        evmlr_utils_new_perm(pi, N);

        for (slong i = 0; i < N; i++) {
            nmod_poly_mat_init(shuffled_msgs[i], L_next, 1, MOD_Q);
            nmod_poly_mat_set(shuffled_msgs[i], decrypted_msgs[pi[i]]);
        }

        // Generate Proof of Shuffle
        t0 = now_cycles();
        evmlr_shuffle_sp_t shuf_sp;
        evmlr_shuffle_pp_t shuf_pp;

        shuf_sp->pi = pi;
        shuf_sp->d_dagger = d_dagger;
        // The proof of correct decryption: the server's key, and the seed
        // ciphertexts of the layer it removes.
        shuf_sp->sk = sk->sks[j];
        shuf_pp->pk = pp->pks[j];
        evmlr_mlpke_cipher_struct *c_prime = flint_malloc(N * sizeof(evmlr_mlpke_cipher_struct));
        for (slong i = 0; i < N; i++) c_prime[i] = *curr_cts[i].enc_cipher[0];
        shuf_pp->c_prime = c_prime;
        nmod_poly_mat_init(shuf_sp->r_D, 2 * K_SIS, 1, MOD_Q);
        evmlr_commit_sample_r(shuf_sp->r_D);

        nmod_poly_mat_t d_flat;
        nmod_poly_mat_init(d_flat, pp->shuf_ctx->com_ctx->N, 1, MOD_Q);
        nmod_poly_mat_zero(d_flat);
        slong row_len = (2*ETA) * (K_LWE + pp->L_max);
        for (slong i = 0; i < N; i++) {
            for (slong r = 0; r < row_len; r++) {
                nmod_poly_struct* d_dag_ir = nmod_poly_mat_entry(shuf_sp->d_dagger[i], r, 0);
                nmod_poly_struct* poly = nmod_poly_mat_entry(d_flat, i * row_len + r, 0);
                nmod_poly_set(poly, d_dag_ir);
            }
        }
        evmlr_commit_init(shuf_pp->D);
        evmlr_commit(shuf_pp->D, d_flat, shuf_sp->r_D, pp->shuf_ctx->com_ctx);
        nmod_poly_mat_clear(d_flat);

        shuf_pp->c_hat = (nmod_poly_mat_t *) malloc(N * sizeof(nmod_poly_mat_t));
        for (slong i = 0; i < N; i++) {
            nmod_poly_mat_init(shuf_pp->c_hat[i], pp->L_max, 1, MOD_Q);
            nmod_poly_mat_zero(shuf_pp->c_hat[i]);
            for (slong r = 0; r < L_next; r++) {
                nmod_poly_set(nmod_poly_mat_entry(shuf_pp->c_hat[i], r, 0), nmod_poly_mat_entry(shuffled_msgs[i], r, 0));
            }
        }
        for (slong i = 0; i < N; i++) {
            for (slong r = L_next; r < pp->L_max; r++) {
                nmod_poly_struct* hat_val = nmod_poly_mat_entry(shuf_pp->c_hat[i], r, 0);
                nmod_poly_struct* a_val = nmod_poly_mat_entry(a_mats[pi[i]], r, 0);
                nmod_poly_neg(hat_val, a_val);
            }
        }

        shuf_pp->c_star = (evmlr_otse_ciphertext_t *) malloc(N * sizeof(evmlr_otse_ciphertext_t));
        for (slong i = 0; i < N; i++) {
            nmod_poly_mat_init(shuf_pp->c_star[i]->c, pp->L_max, 1, MOD_Q);
            nmod_poly_mat_zero(shuf_pp->c_star[i]->c);
            for (slong r = 0; r < curr_cts[i].otse_cipher->c->r; r++) {
                nmod_poly_set(nmod_poly_mat_entry(shuf_pp->c_star[i]->c, r, 0), nmod_poly_mat_entry(curr_cts[i].otse_cipher->c, r, 0));
            }
        }

        evmlr_proof_init(shuffle_proofs[j], pp->shuf_ctx);
        evmlr_shuffle_prove(shuffle_proofs[j], shuf_sp, shuf_pp, pp->shuf_ctx, state);
        stats->shuffle_prove += now_cycles() - t0;

        t0 = now_cycles();
        int shuffle_ok = evmlr_shuffle_verify(shuffle_proofs[j], pp->shuf_ctx, shuf_pp);
        stats->shuffle_verify += now_cycles() - t0;
        if (!shuffle_ok) {
            printf("Warning: Shuffle verification failed at server %ld!\n", j);
            failed = 1;
        }

        // Clean up pp/sp
        for (slong i = 0; i < N; i++) {
            nmod_poly_mat_clear(shuf_pp->c_hat[i]);
            nmod_poly_mat_clear(shuf_pp->c_star[i]->c);
            nmod_poly_mat_clear(a_mats[i]);
        }
        free(shuf_pp->c_hat);
        free(shuf_pp->c_star);
        flint_free(c_prime);
        free(a_mats);
        evmlr_commit_clear(shuf_pp->D);
        nmod_poly_mat_clear(shuf_sp->r_D);
        free(shuf_sp->pi);
        for (slong i = 0; i < N; i++) {
            nmod_poly_mat_clear(d_dagger[i]);
        }
        free(d_dagger);

        if (j == k - 1) {
            for (slong i = 0; i < N; i++) {
                nmod_poly_mat_init(results[i], L_next, 1, MOD_Q);
                nmod_poly_mat_set(results[i], shuffled_msgs[i]);
            }
        } else {
            for (slong i = 0; i < N; i++) {
                evmlr_voting_layer_clear(&curr_cts[i]);
                deserialize_layer(&curr_cts[i], shuffled_msgs[i], L_next - K_LWR * (K_LWE + 1));
            }
        }

        for (slong i = 0; i < N; i++) {
            nmod_poly_mat_clear(decrypted_msgs[i]);
            nmod_poly_mat_clear(shuffled_msgs[i]);
        }
    }

    free(decrypted_msgs);
    free(shuffled_msgs);
    for (slong i = 0; i < N; i++) {
        evmlr_voting_layer_clear(&curr_cts[i]);
    }
    free(curr_cts);
    free(active_subs);

    return failed ? -1 : N;
}

// counting(...)
slong evmlr_voting_counting(nmod_poly_mat_t* results, evmlr_shuffle_proof_t* shuffle_proofs,
                          const evmlr_voting_submission_t* submissions, slong num_submissions,
                          const evmlr_voting_pp_t pp, const evmlr_voting_sk_t sk, flint_rand_t state) {
    return counting_impl(results, shuffle_proofs, submissions, num_submissions, pp, sk, state, NULL);
}

void evmlr_voting_layer_init(evmlr_voting_layer_t layer, slong otse_len) {
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_init(layer->enc_cipher[i]->uT, 1, K_LWE, MOD_Q);
        nmod_poly_init(layer->enc_cipher[i]->v, MOD_Q);
    }
    nmod_poly_mat_init(layer->otse_cipher->c, otse_len, 1, MOD_Q);
}

void evmlr_voting_layer_clear(evmlr_voting_layer_t layer) {
    for (int i = 0; i < K_LWR; i++) {
        nmod_poly_mat_clear(layer->enc_cipher[i]->uT);
        nmod_poly_clear(layer->enc_cipher[i]->v);
    }
    nmod_poly_mat_clear(layer->otse_cipher->c);
}

void evmlr_voting_submission_init(evmlr_voting_submission_t sub, const evmlr_voting_pp_t pp) {
    evmlr_voting_layer_init(sub->ballot->layer, pp->L_max);
    evmlr_user_proof_init(sub->proof);
}

void evmlr_voting_submission_clear(evmlr_voting_submission_t sub, const evmlr_voting_pp_t pp) {
    (void) pp;
    evmlr_voting_layer_clear(sub->ballot->layer);
    evmlr_user_proof_clear(sub->proof);
}

void evmlr_voting_pp_clear(evmlr_voting_pp_t pp) {
    for (slong j = 0; j < pp->k; j++) {
        nmod_poly_mat_clear(pp->pks[j]->A);
        nmod_poly_mat_clear(pp->pks[j]->t);
    }
    free(pp->pks);
    evmlr_hpke_ctx_clear(pp->hpke_ctx);
    evmlr_shuffle_ctx_clear(pp->shuf_ctx);
}

void evmlr_voting_sk_clear(evmlr_voting_sk_t sk) {
    for (slong j = 0; j < sk->k; j++) {
        nmod_poly_mat_clear(sk->sks[j]->s);
    }
    free(sk->sks);
}


#ifdef MAIN
#include "evmlr_main.h"

#ifndef VOTING_TEST_K
#define VOTING_TEST_K 3 // with LaZer, each voter's proof needs about 2 GB at 3 servers
#endif

static void test_voting_protocol(flint_rand_t state) {
    slong k_servers = VOTING_TEST_K;
    evmlr_voting_pp_t pp;
    evmlr_voting_sk_t sk;

    evmlr_voting_setup(pp, sk, k_servers, state);

    // Prepare 6 submissions for 5 voters (voter 2 submits twice), and with
    // user proofs a seventh, from voter 6, whose ballot is altered after its
    // proof was made: counting must drop it.
    const int with_proofs = evmlr_user_proof_available(k_servers);
    slong num_subs = with_proofs ? 7 : 6;
    evmlr_voting_submission_t subs[num_subs];
    for (slong i = 0; i < num_subs; i++) {
        evmlr_voting_submission_init(subs[i], pp);
    }

    // Set voter IDs and votes (each vote is a 1x1 matrix with a distinct candidate polynomial)
    slong voter_ids[7] = {1, 2, 3, 2, 4, 5, 6};
    nmod_poly_mat_t expected_votes[5];
    for (int i = 0; i < 5; i++) {
        nmod_poly_mat_init(expected_votes[i], 1, 1, MOD_Q);
    }
    
    // Voter 1: vote candidate 10
    nmod_poly_set_coeff_ui(nmod_poly_mat_entry(expected_votes[0], 0, 0), 0, 10);
    // Voter 2: first vote is candidate 99 (superseded), second vote is candidate 20
    nmod_poly_mat_t superseded_vote;
    nmod_poly_mat_init(superseded_vote, 1, 1, MOD_Q);
    nmod_poly_set_coeff_ui(nmod_poly_mat_entry(superseded_vote, 0, 0), 0, 99);
    
    nmod_poly_set_coeff_ui(nmod_poly_mat_entry(expected_votes[1], 0, 0), 0, 20);
    // Voter 3: vote candidate 30
    nmod_poly_set_coeff_ui(nmod_poly_mat_entry(expected_votes[2], 0, 0), 0, 30);
    // Voter 4: vote candidate 40
    nmod_poly_set_coeff_ui(nmod_poly_mat_entry(expected_votes[3], 0, 0), 0, 40);
    // Voter 5: vote candidate 50
    nmod_poly_set_coeff_ui(nmod_poly_mat_entry(expected_votes[4], 0, 0), 0, 50);

    // Perform casting
    evmlr_voting_casting(subs[0], voter_ids[0], expected_votes[0], pp, state); // Voter 1
    evmlr_voting_casting(subs[1], voter_ids[1], superseded_vote, pp, state);   // Voter 2 (first vote)
    evmlr_voting_casting(subs[2], voter_ids[2], expected_votes[2], pp, state); // Voter 3
    evmlr_voting_casting(subs[3], voter_ids[3], expected_votes[1], pp, state); // Voter 2 (second vote)
    evmlr_voting_casting(subs[4], voter_ids[4], expected_votes[3], pp, state); // Voter 4
    evmlr_voting_casting(subs[5], voter_ids[5], expected_votes[4], pp, state); // Voter 5
    if (with_proofs) {
        evmlr_voting_casting(subs[6], voter_ids[6], expected_votes[0], pp, state); // Voter 6
        nmod_poly_struct *c = nmod_poly_mat_entry(subs[6]->ballot->layer->otse_cipher->c, 0, 0);
        nmod_poly_set_coeff_ui(c, 0, nmod_add(nmod_poly_get_coeff_ui(c, 0), 1, c->mod));
    }

    // Run counting
    nmod_poly_mat_t results[5];
    evmlr_shuffle_proof_t shuffle_proofs[VOTING_TEST_K];
    
    slong num_results = evmlr_voting_counting(results, shuffle_proofs, subs, num_subs, pp, sk, state);

    if (with_proofs) {
        TEST_ONCE("voting protocol: every honest voter's proof of encryption verifies") {
            int ok = 1;
            for (slong i = 0; i < 6; i++) ok &= evmlr_voting_verify_submission(pp, subs[i]);
            TEST_ASSERT(ok && !evmlr_voting_verify_submission(pp, subs[6]), end);
        } TEST_END;
    }

    TEST_BEGIN("voting protocol: number of valid results is correct") {
        TEST_ASSERT(num_results == 5, end);
    } TEST_END;

    TEST_BEGIN("voting protocol: decrypted votes match expected votes") {
        // Since the votes are shuffled, we check that each result matches one expected vote, and all are unique
        int matched[5] = {0, 0, 0, 0, 0};
        for (int i = 0; i < 5; i++) {
            int found = 0;
            for (int j = 0; j < 5; j++) {
                if (!matched[j] && nmod_poly_mat_equal(results[i], expected_votes[j]) == 1) {
                    matched[j] = 1;
                    found = 1;
                    break;
                }
            }
            TEST_ASSERT(found == 1, end);
        }
    } TEST_END;

end:
    nmod_poly_mat_clear(superseded_vote);
    for (int i = 0; i < 5; i++) {
        nmod_poly_mat_clear(expected_votes[i]);
        nmod_poly_mat_clear(results[i]);
    }
    for (int i = 0; i < VOTING_TEST_K; i++) {
        evmlr_proof_clear(shuffle_proofs[i], pp->shuf_ctx);
    }
    for (slong i = 0; i < num_subs; i++) {
        evmlr_voting_submission_clear(subs[i], pp);
    }
    evmlr_voting_pp_clear(pp);
    evmlr_voting_sk_clear(sk);
}

void bench_voting_protocol(flint_rand_t state) {
    slong k_servers = 2;
    slong N = 100; // 10

    printf("\n=== Voting Protocol Benchmark (N = %ld voters, k = %ld servers) ===\n", N, k_servers);

    // 1. Setup Phase
    uint64_t start_setup = cpucycles();
    evmlr_voting_pp_t pp;
    evmlr_voting_sk_t sk;
    evmlr_voting_setup(pp, sk, k_servers, state);
    uint64_t end_setup = cpucycles();
    printf("Setup Phase: %lu cycles\n", (unsigned long)(end_setup - start_setup));

    // Initialize N submissions
    evmlr_voting_submission_t subs[N];
    for (slong i = 0; i < N; i++) {
        evmlr_voting_submission_init(subs[i], pp);
    }

    nmod_poly_mat_t votes[N];
    for (slong i = 0; i < N; i++) {
        nmod_poly_mat_init(votes[i], 1, 1, MOD_Q);
        nmod_poly_set_coeff_ui(nmod_poly_mat_entry(votes[i], 0, 0), 0, i + 1);
    }

    // 2. Casting Phase (Single Voter vs Total)
    uint64_t start_casting = cpucycles();
    for (slong i = 0; i < N; i++) {
        evmlr_voting_casting(subs[i], i + 1, votes[i], pp, state);
    }
    uint64_t end_casting = cpucycles();
    printf("Casting Phase (total for %ld voters): %lu cycles (avg %lu per voter)\n",
           N, (unsigned long)(end_casting - start_casting), (unsigned long)((end_casting - start_casting) / N));

    // 3. Counting: user proofs, then per server decryption and the shuffle proof.
    nmod_poly_mat_t results[N];
    evmlr_shuffle_proof_t shuffle_proofs[k_servers];
    counting_stats_t st;
    slong n_results = counting_impl(results, shuffle_proofs, (const evmlr_voting_submission_t *) subs, N,
                                    pp, sk, state, &st);

    printf("Verify User Proofs Phase (all %ld voters): %lu cycles\n", N, (unsigned long) st.verify_user);
    printf("Peel Phase (total for %ld servers): %lu cycles\n", k_servers, (unsigned long) st.decrypt);
    printf("Shuffle Prove Phase (total for %ld servers): %lu cycles (avg %lu per server)\n",
           k_servers, (unsigned long) st.shuffle_prove, (unsigned long) (st.shuffle_prove / k_servers));
    printf("Shuffle Verify Phase (total for %ld servers): %lu cycles (avg %lu per server)\n",
           k_servers, (unsigned long) st.shuffle_verify, (unsigned long) (st.shuffle_verify / k_servers));
    if (subs[0]->proof->data != NULL) {
        printf("User proof: %zu bytes (%.1f KiB) per voter\n", subs[0]->proof->len, subs[0]->proof->len / 1024.0);
    }

    uint64_t total_cycles = (end_setup - start_setup) + (end_casting - start_casting) +
                            st.verify_user + st.decrypt + st.shuffle_prove + st.shuffle_verify;
    printf("\n--- Breakdown of Phases (%ld voters, %ld servers) ---\n", N, k_servers);
    printf("Total protocol execution cost: %lu cycles\n", (unsigned long)total_cycles);
    printf("  1. Setup:                      %5.2f%%\n", 100.0 * (double) (end_setup - start_setup) / total_cycles);
    printf("  2. Casting (with user proofs): %5.2f%%\n", 100.0 * (double) (end_casting - start_casting) / total_cycles);
    printf("  3. Verify user proofs:         %5.2f%%\n", 100.0 * (double) st.verify_user / total_cycles);
    printf("  4. Peel:                       %5.2f%%\n", 100.0 * (double) st.decrypt / total_cycles);
    printf("  5. Shuffle proving:            %5.2f%%\n", 100.0 * (double) st.shuffle_prove / total_cycles);
    printf("  6. Shuffle verification:       %5.2f%%\n", 100.0 * (double) st.shuffle_verify / total_cycles);
    printf("=======================================================================\n\n");

    for (slong i = 0; i < N; i++) {
        nmod_poly_mat_clear(votes[i]);
        if (i < n_results) nmod_poly_mat_clear(results[i]);
        evmlr_voting_submission_clear(subs[i], pp);
    }
    for (int i = 0; i < k_servers; i++) {
        evmlr_proof_clear(shuffle_proofs[i], pp->shuf_ctx);
    }
    evmlr_voting_pp_clear(pp);
    evmlr_voting_sk_clear(sk);
}

int main(int argc, char *argv[]) {
    evmlr_mode_t mode = evmlr_mode(argc, argv);

    flint_rand_t state;
    evmlr_rand_init(state);

    if (evmlr_runs_tests(mode))   test_voting_protocol(state);
    if (evmlr_runs_benches(mode)) bench_voting_protocol(state);

    flint_rand_clear(state);
    return test_status();
}

#endif
