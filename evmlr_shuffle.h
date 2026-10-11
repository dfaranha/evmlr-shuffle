#ifndef EVMLR_SHUFFLE_EVMLR_SHUFFLE_H
#define EVMLR_SHUFFLE_EVMLR_SHUFFLE_H

#include "evmlr_params.h"
#include "evmlr_commit.h"
#include "evmlr_hpke.h"
#include "evmlr_zk_proof.h"

typedef struct {
    evmlr_commit_ctx_t com_ctx;
    evmlr_hpke_ctx_t hpke_ctx;
    slong N; // number of elements
    slong L; // vector length
} evmlr_shuffle_ctx_struct;
typedef evmlr_shuffle_ctx_struct evmlr_shuffle_ctx_t[1];

typedef struct {
    size_t* pi; // permutation array (size N)
    nmod_poly_mat_t* d_dagger; // (2*ETA*(K_LWE + L)) x 1  * N matrix
    nmod_poly_mat_t r_D; // 2*K_SIS x 1 matrix
    const evmlr_mlpke_sk_struct *sk; // the server's key, for the proof of correct decryption
} evmlr_shuffle_sp_struct; // Secret parameters
typedef evmlr_shuffle_sp_struct evmlr_shuffle_sp_t[1];

typedef struct {
    evmlr_commit_t D; // commitment to d_dagger
    nmod_poly_mat_t* c_hat; // shuffled inner ciphertexts (L x 1) * N matrix
    evmlr_otse_ciphertext_t* c_star; // symmetric ciphertexts of size N
    // The proof of correct decryption (Section 3.3): the server's public key,
    // and the seed ciphertexts c'_i (K_LWR = 1) whose seeds give d_dagger.
    const evmlr_mlpke_pk_struct *pk;
    const evmlr_mlpke_cipher_struct *c_prime; // N
} evmlr_shuffle_pp_struct; // Public parameters
typedef evmlr_shuffle_pp_struct evmlr_shuffle_pp_t[1];

typedef struct {
    evmlr_commit_t P, W; // commitments
    nmod_poly_mat_t u; // vector size N -1
    evmlr_zk_proof_t zk;   // ZK⋆ for equations (1)-(3), the openings and is_bin
} evmlr_shuffle_proof_struct; // Proof
typedef evmlr_shuffle_proof_struct evmlr_shuffle_proof_t[1];

void evmlr_shuffle_ctx_init(evmlr_shuffle_ctx_t ctx, slong N, slong L, flint_rand_t state);

void evmlr_shuffle_ctx_clear(evmlr_shuffle_ctx_t ctx);

void evmlr_proof_init(evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx);

void evmlr_proof_clear(evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx);

void evmlr_shuffle_prove(evmlr_shuffle_proof_t proof, const evmlr_shuffle_sp_t sp, const evmlr_shuffle_pp_t pp, const evmlr_shuffle_ctx_t ctx, flint_rand_t state);

/** The encoded size of @p proof in bytes; parts[0] is P, W and u, parts[1] ZK⋆. */
size_t evmlr_shuffle_proof_size(size_t parts[2], const evmlr_shuffle_proof_t proof,
                                const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_pp_t pp);

int evmlr_shuffle_verify(const evmlr_shuffle_proof_t proof, const evmlr_shuffle_ctx_t ctx, const evmlr_shuffle_pp_t pp);

#endif //EVMLR_SHUFFLE_EVMLR_SHUFFLE_H
