/**
 * @file
 *
 * An election end to end, with ELECTION_VOTERS voters, NCAND candidates and
 * ELECTION_SERVERS mix servers, each party using only what it has:
 *
 *   1. Setup: the public parameters and every server's key pair.
 *   2. Voting: each voter encrypts its vote, X^j for one of NCAND candidates,
 *      in k layers, and proves the ballot a correct k-layer encryption
 *      (LaZer).
 *   3. The board verifies every ballot's proof.
 *   4. Each server in turn removes its layer from every ciphertext, shuffles,
 *      and publishes the outputs with a proof of shuffle and of correct
 *      decryption (ZK*); anyone verifies that proof against the server's
 *      public statement before the next server takes the outputs.
 *   5. The last server's outputs are the votes, which anyone tallies.
 *
 * Then the pipeline is attacked: a ballot changed after its proof must be
 * refused by the board, and a server's proof must not verify for an output it
 * changed, nor for a ballot it replaced by a copy of another. A last check
 * records a known gap: a voter's proof does not bind the voter, so a copied
 * ballot verifies for another voter (the board would have to catch it).
 *
 * The server step is evmlr_voting.c's own (voting_server_mix), so this file
 * includes it, without its MAIN section. Unlike evmlr_voting.bin, there is no
 * revoting here: every voter casts one ballot.
 */

#ifdef MAIN
#undef MAIN
#define ELECTION_MAIN
#endif
#include "evmlr_voting.c"
#ifdef ELECTION_MAIN
#define MAIN
#endif

#include "evmlr_main.h"

#ifndef ELECTION_VOTERS
#define ELECTION_VOTERS 25
#endif
#ifndef NCAND
#define NCAND 8
#endif
/* With LaZer, each voter's proof needs about 1.5 GB at 3 servers. */
#ifndef ELECTION_SERVERS
#define ELECTION_SERVERS 3
#endif

/* The vote X^j, as the 1 x 1 matrix casting takes. */
static void make_vote(nmod_poly_mat_t v, slong j) {
    nmod_poly_mat_init(v, 1, 1, MOD_Q);
    nmod_poly_set_coeff_ui(nmod_poly_mat_entry(v, 0, 0), j, 1);
}

/* The candidate a decrypted vote is for, or -1 if it is not X^j, j < NCAND. */
static slong candidate(const nmod_poly_mat_t m) {
    const nmod_poly_struct *p;
    slong j = -1;

    if (m->r != 1 || m->c != 1) {
        return -1;
    }
    p = nmod_poly_mat_entry(m, 0, 0);
    for (slong i = 0; i < nmod_poly_length(p); i++) {
        ulong c = nmod_poly_get_coeff_ui(p, i);
        if (c == 1 && i < NCAND && j < 0) {
            j = i;
        } else if (c != 0) {
            return -1;
        }
    }
    return j;
}

static int cmp_slong(const void *a, const void *b) {
    slong x = *(const slong *) a, y = *(const slong *) b;
    return (x > y) - (x < y);
}

/* The current ciphertexts, from the board's ballots. */
static void ballots_to_layers(evmlr_voting_layer_struct *cts,
                              evmlr_voting_submission_t *subs, slong n,
                              const evmlr_voting_pp_t pp) {
    for (slong i = 0; i < n; i++) {
        evmlr_voting_layer_init(&cts[i], pp->L_max);
        for (int r = 0; r < K_LWR; r++) {
            nmod_poly_mat_set(cts[i].enc_cipher[r]->uT, subs[i]->ballot->layer->enc_cipher[r]->uT);
            nmod_poly_set(cts[i].enc_cipher[r]->v, subs[i]->ballot->layer->enc_cipher[r]->v);
        }
        nmod_poly_mat_set(cts[i].otse_cipher->c, subs[i]->ballot->layer->otse_cipher->c);
    }
}

static void test_election(flint_rand_t state) {
    const slong n = ELECTION_VOTERS, k = ELECTION_SERVERS;
    evmlr_voting_pp_t pp;
    evmlr_voting_sk_t sk;
    evmlr_voting_submission_t *subs = malloc(n * sizeof(evmlr_voting_submission_t));
    evmlr_voting_layer_struct *cts = malloc(n * sizeof(evmlr_voting_layer_struct));
    nmod_poly_mat_t *out = malloc(n * sizeof(nmod_poly_mat_t));
    slong *votes = malloc(n * sizeof(slong)), *tally = malloc(n * sizeof(slong));
    slong count[NCAND] = { 0 };
    counting_stats_t stats;
    int with_proofs, board_ok = 1, servers_ok = 1, valid = 1;
    int have_cts = 0, have_out = 0;

    memset(&stats, 0, sizeof(stats));
    evmlr_voting_setup(pp, sk, k, state);
    with_proofs = evmlr_user_proof_available(k);

    /* Voting. The votes are the test oracle, kept apart from what the board,
     * the servers and the verifier use. */
    for (slong i = 0; i < n; i++) {
        nmod_poly_mat_t v;
        evmlr_voting_submission_init(subs[i], pp);
        votes[i] = evmlr_utils_uniform_below(NCAND);
        make_vote(v, votes[i]);
        evmlr_voting_casting(subs[i], i, v, pp, state);
        nmod_poly_mat_clear(v);
    }

    TEST_ONCE("election: the board accepts every voter's ballot") {
        if (!with_proofs) {
            printf("(built without LaZer: no ballot proofs to check) ");
        }
        for (slong i = 0; i < n && with_proofs; i++) {
            board_ok &= evmlr_voting_verify_submission(pp, subs[i]);
        }
        TEST_ASSERT(board_ok, end);
    } TEST_END;

    if (with_proofs) {
        TEST_ONCE("election: the board refuses a ballot changed after its proof") {
            nmod_poly_struct *c = nmod_poly_mat_entry(subs[0]->ballot->layer->otse_cipher->c, 0, 0);
            ulong keep = nmod_poly_get_coeff_ui(c, 0);
            nmod_poly_set_coeff_ui(c, 0, nmod_add(keep, 1, c->mod));
            int ok = evmlr_voting_verify_submission(pp, subs[0]);
            nmod_poly_set_coeff_ui(c, 0, keep);
            TEST_ASSERT(ok == 0, end);
        } TEST_END;

        TEST_ONCE("election: KNOWN GAP: a ballot copied by another voter verifies") {
            /* The proof covers the ballot and the keys, not the voter: the
             * same submission under another voter's ID passes. */
            slong id = subs[0]->voter_id;
            subs[0]->voter_id = n;
            int ok = evmlr_voting_verify_submission(pp, subs[0]);
            subs[0]->voter_id = id;
            TEST_ASSERT(ok == 1, end);
        } TEST_END;
    }

    /* The shuffle context for this number of ballots, as counting sets it. */
    evmlr_shuffle_ctx_clear((evmlr_shuffle_ctx_struct *) pp->shuf_ctx);
    evmlr_shuffle_ctx_init((evmlr_shuffle_ctx_struct *) pp->shuf_ctx, n, pp->L_max, state);
    sync_hpke_ctx(((evmlr_shuffle_ctx_struct *) pp->shuf_ctx)->hpke_ctx, pp->hpke_ctx);
    ballots_to_layers(cts, subs, n, pp);
    have_cts = 1;

    /* Mixing: server j publishes out and its proof; anyone verifies. */
    for (slong j = 0; j < k; j++) {
        slong L_next = (k - j - 1) * K_LWR * (K_LWE + 1) + 1;
        evmlr_shuffle_proof_t proof;
        evmlr_shuffle_pp_t st;

        voting_server_mix(proof, st, out, cts, n, j, pp, sk, state, &stats);
        have_out = 1;
        servers_ok &= evmlr_shuffle_verify(proof, pp->shuf_ctx, st);

        if (j == 0) {
            TEST_ONCE("election: a server's proof fails for an output it changed") {
                nmod_poly_struct *c = nmod_poly_mat_entry(st->c_hat[0], 0, 0);
                ulong keep = nmod_poly_get_coeff_ui(c, 0);
                nmod_poly_set_coeff_ui(c, 0, nmod_add(keep, 1, c->mod));
                int ok = evmlr_shuffle_verify(proof, pp->shuf_ctx, st);
                nmod_poly_set_coeff_ui(c, 0, keep);
                TEST_ASSERT(ok == 0, end);
            } TEST_END;

            TEST_ONCE("election: a server's proof fails for a ballot it replaced") {
                /* Output 0 replaced by a copy of output 1: one ballot dropped,
                 * another counted twice. */
                nmod_poly_mat_t keep;
                nmod_poly_mat_init(keep, pp->L_max, 1, MOD_Q);
                nmod_poly_mat_set(keep, st->c_hat[0]);
                for (slong r = 0; r < L_next; r++) {
                    nmod_poly_set(nmod_poly_mat_entry(st->c_hat[0], r, 0),
                                  nmod_poly_mat_entry(st->c_hat[1], r, 0));
                }
                int ok = evmlr_shuffle_verify(proof, pp->shuf_ctx, st);
                nmod_poly_mat_set(st->c_hat[0], keep);
                nmod_poly_mat_clear(keep);
                TEST_ASSERT(ok == 0, end);
            } TEST_END;
        }

        voting_statement_clear(st, n);
        evmlr_proof_clear(proof, pp->shuf_ctx);
        if (j < k - 1) {
            for (slong i = 0; i < n; i++) {
                evmlr_voting_layer_clear(&cts[i]);
                deserialize_layer(&cts[i], out[i], L_next - K_LWR * (K_LWE + 1));
                nmod_poly_mat_clear(out[i]);
            }
            have_out = 0;
        }
    }

    TEST_ONCE("election: every server's proof verifies") {
        TEST_ASSERT(servers_ok, end);
    } TEST_END;

    /* The tally, of the last server's outputs. */
    for (slong i = 0; i < n; i++) {
        tally[i] = candidate(out[i]);
        valid &= tally[i] >= 0;
        if (tally[i] >= 0) {
            count[tally[i]]++;
        }
    }

    TEST_ONCE("election: every output is a valid vote") {
        TEST_ASSERT(valid, end);
    } TEST_END;

    TEST_ONCE("election: the tally is the votes cast") {
        qsort(tally, n, sizeof(slong), cmp_slong);
        qsort(votes, n, sizeof(slong), cmp_slong);
        TEST_ASSERT(memcmp(tally, votes, n * sizeof(slong)) == 0, end);
    } TEST_END;

    printf("\n    %ld voters, %d candidates, %ld servers; tally:", n, NCAND, k);
    for (int j = 0; j < NCAND; j++) {
        printf(" %ld", count[j]);
    }
    printf("\n");

end:
    for (slong i = 0; i < n; i++) {
        if (have_out) nmod_poly_mat_clear(out[i]);
        if (have_cts) evmlr_voting_layer_clear(&cts[i]);
        evmlr_voting_submission_clear(subs[i], pp);
    }
    free(out);
    free(cts);
    free(subs);
    free(votes);
    free(tally);
    evmlr_voting_pp_clear(pp);
    evmlr_voting_sk_clear(sk);
}

#ifdef MAIN
int main(int argc, char *argv[]) {
    flint_rand_t state;

    (void) argc;
    (void) argv;
    setvbuf(stdout, NULL, _IONBF, 0);
    evmlr_rand_init(state);
    test_election(state);
    flint_rand_clear(state);
    return test_status();
}
#endif
