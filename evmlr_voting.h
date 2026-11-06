#ifndef EVMLR_VOTING_H
#define EVMLR_VOTING_H

#include "evmlr_shuffle.h"
#include "evmlr_user_proof.h"
#include "sha.h"

// Public parameters for the voting protocol
typedef struct {
    slong k;                    // Number of mixnet servers (k >= 1)
    slong L_max;                // Maximum vector length for the outermost layer
    evmlr_hpke_ctx_t hpke_ctx;  // HPKE context
    evmlr_shuffle_ctx_t shuf_ctx; // Unified shuffle context (with commitment context)
    evmlr_mlpke_pk_t* pks;      // Public keys for servers 1 to k
    slong ncand;                // Number of candidates: a vote is X^j, j < ncand, or 0
    uint8_t eid[16];            // Election identifier, random, in every voter's proof
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

// Submission from a voter: voter ID, the ballot's outermost layer, which is the
// only public one, and the voter's proof that it is a correct k-layer
// encryption (evmlr_user_proof.h). Without LaZer there is no proof
// (proof->data == NULL) and counting does not check one.
typedef struct {
    slong voter_id;
    evmlr_voting_ciphertext_t ballot;
    evmlr_user_proof_t proof;
} evmlr_voting_submission_struct;
typedef evmlr_voting_submission_struct evmlr_voting_submission_t[1];

// setup(k, ncand, state) -> (pp, sk)
void evmlr_voting_setup(evmlr_voting_pp_t pp, evmlr_voting_sk_t sk, slong k, slong ncand, flint_rand_t state);

// casting(submission, voter_id, vote, pp, state)
void evmlr_voting_casting(evmlr_voting_submission_t submission, slong voter_id, const nmod_poly_mat_t vote, const evmlr_voting_pp_t pp, flint_rand_t state);

// A submission's ballot as published bytes: the outermost layer's MLPKE
// ciphertexts (uT, v) and its OTSE ciphertext c, LOG_Q_CEIL bits a
// coefficient. encode allocates *out, which the caller frees, and returns its
// length; decode fills an initialised submission's ballot and returns 1 only
// for a canonical encoding of exactly len bytes. The voter's proof is already
// bytes (sub->proof).
size_t evmlr_voting_ballot_encode(uint8_t **out, const evmlr_voting_submission_t sub);
int evmlr_voting_ballot_decode(evmlr_voting_submission_t sub, const uint8_t *buf, size_t len);

// Whether a submission's proof of correct encryption verifies, for this
// election and the submission's voter ID. Servers check it before decrypting
// (Section 3.3), and counting drops those that fail.
int evmlr_voting_verify_submission(const evmlr_voting_pp_t pp, const evmlr_voting_submission_t sub);

// counting(results, shuffle_proofs, submissions, num_submissions, pp, sk, state):
// the number of results, or -1 if a server's proof of shuffle and decryption
// did not verify.
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
