#ifndef EVMLR_VOTING_H
#define EVMLR_VOTING_H

#include "evmlr_shuffle.h"
#include "evmlr_ballot.h"
#include "sha.h"

// Public parameters for the voting protocol
typedef struct {
    slong k;                    // Number of mixnet servers (k >= 1)
    slong L_max;                // Maximum vector length for the outermost layer
    evmlr_hpke_ctx_t hpke_ctx;  // HPKE context
    evmlr_shuffle_ctx_t shuf_ctx; // Unified shuffle context (with commitment context)
    evmlr_mlpke_pk_t* pks;      // Public keys for servers 1 to k
} evmlr_voting_pp_struct;
typedef evmlr_voting_pp_struct evmlr_voting_pp_t[1];

// Secret keys for the mixnet servers
typedef struct {
    slong k;
    evmlr_mlpke_sk_t* sks;      // Secret keys for servers 1 to k
} evmlr_voting_sk_struct;
typedef evmlr_voting_sk_struct evmlr_voting_sk_t[1];

// A ciphertext layer (holds a single HPKE cipher representation)
typedef struct {
    evmlr_mlpke_cipher_t enc_cipher[K_LWR];
    evmlr_otse_ciphertext_t otse_cipher;
} evmlr_voting_layer_struct;
typedef evmlr_voting_layer_struct evmlr_voting_layer_t[1];

// Ballot ciphertext containing the outermost encrypted layer
typedef struct {
    evmlr_voting_layer_t layer; // The outermost ciphertext layer
} evmlr_voting_ciphertext_struct;
typedef evmlr_voting_ciphertext_struct evmlr_voting_ciphertext_t[1];

// Submission from a voter: voter ID and the ballot's outermost layer, which is
// the only public one. (The voter's proof of correct encryption, in LaZer, is
// on the lazer branch.)
typedef struct {
    slong voter_id;
    evmlr_voting_ciphertext_t ballot;
} evmlr_voting_submission_struct;
typedef evmlr_voting_submission_struct evmlr_voting_submission_t[1];

// setup(k, state) -> (pp, sk)
void evmlr_voting_setup(evmlr_voting_pp_t pp, evmlr_voting_sk_t sk, slong k, flint_rand_t state);

// casting(submission, voter_id, vote, pp, state)
void evmlr_voting_casting(evmlr_voting_submission_t submission, slong voter_id, const nmod_poly_mat_t vote, const evmlr_voting_pp_t pp, flint_rand_t state);

// counting(results, shuffle_proofs, submissions, num_submissions, pp, sk, state)
slong evmlr_voting_counting(nmod_poly_mat_t* results, evmlr_shuffle_proof_t* shuffle_proofs, 
                          const evmlr_voting_submission_t* submissions, slong num_submissions,
                          const evmlr_voting_pp_t pp, const evmlr_voting_sk_t sk, flint_rand_t state);

// Memory Management
void evmlr_voting_pp_clear(evmlr_voting_pp_t pp);
void evmlr_voting_sk_clear(evmlr_voting_sk_t sk);
void evmlr_voting_submission_init(evmlr_voting_submission_t sub, const evmlr_voting_pp_t pp);
void evmlr_voting_submission_clear(evmlr_voting_submission_t sub, const evmlr_voting_pp_t pp);

void evmlr_voting_layer_init(evmlr_voting_layer_t layer, slong otse_len);
void evmlr_voting_layer_clear(evmlr_voting_layer_t layer);

#endif // EVMLR_VOTING_H
