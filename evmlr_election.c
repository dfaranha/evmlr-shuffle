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
 * changed, nor for a ballot it replaced by a copy of another; and a ballot
 * copied by another voter must be refused, since each voter's proof is bound
 * to the election and the voter.
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
#include "fastrandombytes.h"
#include <stdio.h>
#include <time.h>

/* Wall-clock seconds, for the phase timings the election reports. */
static double now_s(void) {
    struct timespec t;

    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec / 1e9;
}

/* The election's size. The codebases benchmarked against this one share the
 * knobs MSGS (voters), NCAND (candidates), MIXERS (mix servers) and PARTIES
 * (trustees); MSGS and MIXERS are this file's ELECTION_VOTERS and
 * ELECTION_SERVERS, which still work. The servers decrypt, so there are no
 * trustees and PARTIES can only be 0. */
#if defined(MSGS) && !defined(ELECTION_VOTERS)
#define ELECTION_VOTERS MSGS
#endif
#if defined(MIXERS) && !defined(ELECTION_SERVERS)
#define ELECTION_SERVERS MIXERS
#endif
#if defined(PARTIES) && PARTIES != 0
#error "evmlr-shuffle: the mix servers decrypt, so there are no trustees and PARTIES can only be 0"
#endif
#ifndef ELECTION_VOTERS
#define ELECTION_VOTERS 25
#endif
#ifndef NCAND
#define NCAND 8
#endif
/* With LaZer, each voter's proof needs about 1.5 GB at 3 servers. Its
 * parameters exist for 2 to 4 servers (evmlr_user_proof.c). */
#ifndef ELECTION_SERVERS
#define ELECTION_SERVERS 3
#endif
#if ELECTION_SERVERS < 2 || ELECTION_SERVERS > 4
#error "evmlr-shuffle: the voters' proof has parameters for 2 to 4 servers (MIXERS)"
#endif

/* The ballot cache. Casting is most of an election's time at 1000 voters (the
 * voters' LaZer proofs), so with EVMLR_BALLOT_CACHE=file an election keeps its
 * ballots: if the file does not exist, the election is set up from a fresh
 * seed and the file gets the seed, the casting time, and each voter's vote,
 * ballot bytes and proof; if it does, setup is replayed from its seed, which
 * gives the same keys and election identifier the proofs are bound to, and the
 * ballots are read from it instead of cast. Everything after casting runs as
 * without the cache, the board's check of every proof included. A file made
 * for another size is refused. The votes are the tests' oracle only. */
#define CACHE_MAGIC "evmlr-ballots-1"

typedef struct {
    slong n, ncand, k;
    double t_cast;
    uint8_t seed[32];
} cache_header_t;

static void cache_prg(void *ctx, void *buf, size_t len) {
    prg_bytes((prg_t *) ctx, (unsigned char *) buf, len);
}

/* Setup with every random draw from the seed: evmlr_utils_random, for the
 * public matrices, the keys and the election identifier, and a flint state. */
static void cache_setup(evmlr_voting_pp_t pp, evmlr_voting_sk_t sk, slong k,
        const uint8_t seed[32]) {
    prg_t prg;
    flint_rand_t st;
    ulong s[2];

    prg_setseed(&prg, seed);
    prg_bytes(&prg, (unsigned char *) s, sizeof(s));
    flint_rand_init(st);
    flint_rand_set_seed(st, s[0], s[1]);
    evmlr_utils_random_source(cache_prg, &prg);
    evmlr_voting_setup(pp, sk, k, NCAND, st);
    evmlr_utils_random_source(NULL, NULL);
    flint_rand_clear(st);
}

static int read_all(FILE *f, void *p, size_t len) {
    return fread(p, 1, len, f) == len;
}

/* Reads voter i's record into an initialised submission. */
static int cache_read_voter(FILE *f, evmlr_voting_submission_t sub, slong i, slong *vote) {
    uint64_t bl, pl;
    uint8_t *b;
    int ok;

    if (!read_all(f, vote, sizeof(*vote)) || !read_all(f, &bl, sizeof(bl)) || bl > (1u << 30)) {
        return 0;
    }
    b = malloc(bl);
    ok = read_all(f, b, bl) && evmlr_voting_ballot_decode(sub, b, bl);
    free(b);
    if (!ok || !read_all(f, &pl, sizeof(pl)) || pl > (1u << 30)) {
        return 0;
    }
    sub->voter_id = i;
    free(sub->proof->data);
    sub->proof->data = pl ? malloc(pl) : NULL;
    sub->proof->len = pl;
    return read_all(f, sub->proof->data, pl);
}

static void cache_write_voter(FILE *f, slong vote, const uint8_t *b, uint64_t bl,
        const evmlr_voting_submission_t sub) {
    uint64_t pl = sub->proof->len;

    fwrite(&vote, sizeof(vote), 1, f);
    fwrite(&bl, sizeof(bl), 1, f);
    fwrite(b, 1, bl, f);
    fwrite(&pl, sizeof(pl), 1, f);
    fwrite(sub->proof->data, 1, pl, f);
}

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

/* What a verifier of server j sets in its statement before reading the
 * server's bytes: the server's key, and, from the list the server took as
 * input, the OTSE ciphertexts padded to L_max and the seed ciphertexts. */
static void verifier_statement(evmlr_shuffle_pp_struct *st, const evmlr_voting_layer_struct *cts,
                               slong n, slong j, const evmlr_voting_pp_t pp) {
    evmlr_mlpke_cipher_struct *cp = flint_malloc(n * sizeof(evmlr_mlpke_cipher_struct));

    st->pk = pp->pks[j];
    st->c_star = malloc(n * sizeof(evmlr_otse_ciphertext_t));
    for (slong i = 0; i < n; i++) {
        cp[i] = *cts[i].enc_cipher[0];
        nmod_poly_mat_init(st->c_star[i]->c, pp->L_max, 1, MOD_Q);
        nmod_poly_mat_zero(st->c_star[i]->c);
        for (slong r = 0; r < cts[i].otse_cipher->c->r; r++) {
            nmod_poly_set(nmod_poly_mat_entry(st->c_star[i]->c, r, 0),
                          nmod_poly_mat_entry(cts[i].otse_cipher->c, r, 0));
        }
    }
    st->c_prime = cp;
}

/* Whether server j's publication buf verifies against the list cts. */
static int verify_publication(const uint8_t *buf, size_t len, const evmlr_voting_layer_struct *cts,
                              slong n, slong j, const evmlr_voting_pp_t pp) {
    evmlr_shuffle_pp_t st;
    int ok;

    verifier_statement(st, cts, n, j, pp);
    ok = evmlr_shuffle_verify_bytes(st, buf, len, pp->shuf_ctx);
    voting_statement_clear(st, n);
    return ok;
}

/* Bytes of one ring element mod q as published. */
#define POLY_BYTES (DEGREE_N * LOG_Q_CEIL / 8)

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
    int with_proofs, board_ok = 1, servers_ok = 1, valid = 1, read_ok = 1;
    size_t ballot_bytes = 0, proof_bytes = 0, *pub_bytes = calloc(k, sizeof(size_t));
    int have_cts = 0, have_out = 0;
    /* Wall-clock times of the phases, reported at the end; the attack tests
     * are not counted. */
    double t0, t_setup, t_cast, t_board = 0;
    double *t_mix = calloc(k, sizeof(double)), *t_ver = calloc(k, sizeof(double));
    uint64_t *c_dec = calloc(k, sizeof(uint64_t)), *c_prove = calloc(k, sizeof(uint64_t));

    const char *cache = getenv("EVMLR_BALLOT_CACHE");
    FILE *cache_in = NULL, *cache_out = NULL;
    char cache_tmp[4096];
    cache_header_t hdr;

    memset(&stats, 0, sizeof(stats));
    if (cache != NULL && *cache != '\0') {
        char magic[sizeof(CACHE_MAGIC)];

        cache_in = fopen(cache, "rb");
        if (cache_in != NULL) {
            if (!read_all(cache_in, magic, sizeof(magic)) || memcmp(magic, CACHE_MAGIC, sizeof(magic)) != 0
                    || !read_all(cache_in, &hdr, sizeof(hdr))) {
                fprintf(stderr, "evmlr: %s is not a ballot cache\n", cache);
                exit(1);
            }
            if (hdr.n != n || hdr.ncand != NCAND || hdr.k != k) {
                fprintf(stderr, "evmlr: %s holds %ld voters, %ld candidates and %ld servers, "
                        "not %ld, %d and %ld\n", cache, hdr.n, hdr.ncand, hdr.k, n, NCAND, k);
                exit(1);
            }
        } else {
            memset(&hdr, 0, sizeof(hdr));
            hdr.n = n;
            hdr.ncand = NCAND;
            hdr.k = k;
            evmlr_utils_random(hdr.seed, sizeof(hdr.seed));
        }
    }

    t0 = now_s();
    if (cache != NULL && *cache != '\0') {
        cache_setup(pp, sk, k, hdr.seed);
    } else {
        evmlr_voting_setup(pp, sk, k, NCAND, state);
    }
    with_proofs = evmlr_user_proof_available(k);
    t_setup = now_s() - t0;

    /* Voting. The votes are the test oracle, kept apart from what the board,
     * the servers and the verifier use. */
    t0 = now_s();
    for (slong i = 0; i < n; i++) {
        nmod_poly_mat_t v;
        evmlr_voting_submission_init(subs[i], pp);
        if (cache_in != NULL) {
            if (!cache_read_voter(cache_in, subs[i], i, &votes[i])) {
                fprintf(stderr, "evmlr: %s ends or is damaged at voter %ld\n", cache, i);
                exit(1);
            }
            continue;
        }
        votes[i] = evmlr_utils_uniform_below(NCAND);
        make_vote(v, votes[i]);
        evmlr_voting_casting(subs[i], i, v, pp, state);
        nmod_poly_mat_clear(v);
    }
    t_cast = now_s() - t0;
    if (cache_in != NULL) {
        fclose(cache_in);
        printf("    (ballots read from %s in %.2f s; the casting time reported is the one "
               "measured when it was made)\n", cache, t_cast);
        t_cast = hdr.t_cast;
    } else if (cache != NULL && *cache != '\0') {
        hdr.t_cast = t_cast;
        /* Written whole to a temporary file, then renamed: a run stopped
         * part way leaves no cache to be read as damaged. */
        snprintf(cache_tmp, sizeof(cache_tmp), "%s.tmp", cache);
        cache_out = fopen(cache_tmp, "wb");
        if (cache_out == NULL) {
            perror(cache_tmp);
        } else {
            fwrite(CACHE_MAGIC, 1, sizeof(CACHE_MAGIC), cache_out);
            fwrite(&hdr, sizeof(hdr), 1, cache_out);
        }
    }

    /* Publication: each ballot goes to the board as bytes and is read back in
     * place, so that the board and the servers use only what they read. The
     * voter's proof is bytes already. */
    for (slong i = 0; i < n; i++) {
        uint8_t *b;
        size_t bl = evmlr_voting_ballot_encode(&b, subs[i]);

        ballot_bytes += bl;
        proof_bytes += subs[i]->proof->len;
        if (cache_out != NULL) {
            cache_write_voter(cache_out, votes[i], b, bl, subs[i]);
        }
        read_ok &= evmlr_voting_ballot_decode(subs[i], b, bl);
        free(b);
    }
    if (cache_out != NULL && (fclose(cache_out) != 0 || rename(cache_tmp, cache) != 0)) {
        perror(cache);
    }

    TEST_ONCE("election: every ballot reads back from its published bytes") {
        TEST_ASSERT(read_ok, end);
    } TEST_END;

    TEST_ONCE("election: the board accepts every voter's ballot") {
        if (!with_proofs) {
            printf("(built without LaZer: no ballot proofs to check) ");
        }
        t0 = now_s();
        for (slong i = 0; i < n && with_proofs; i++) {
            board_ok &= evmlr_voting_verify_submission(pp, subs[i]);
        }
        t_board = now_s() - t0;
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

        TEST_ONCE("election: the board refuses a ballot copied by another voter") {
            /* The proof is bound to the election and the voter: the same
             * submission under another voter's ID does not verify. */
            slong id = subs[0]->voter_id;
            subs[0]->voter_id = n;
            int ok = evmlr_voting_verify_submission(pp, subs[0]);
            subs[0]->voter_id = id;
            TEST_ASSERT(ok == 0, end);
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

        uint64_t dec0 = stats.decrypt, prove0 = stats.shuffle_prove;
        uint8_t *pub;
        size_t len;
        t0 = now_s();
        voting_server_mix(proof, st, out, cts, n, j, pp, sk, state, &stats);
        /* The server publishes its bytes and keeps nothing else: its proof,
         * its statement and its outputs in memory are dropped. */
        len = evmlr_shuffle_encode(&pub, proof, pp->shuf_ctx, st);
        pub_bytes[j] = len;
        voting_statement_clear(st, n);
        evmlr_proof_clear(proof, pp->shuf_ctx);
        for (slong i = 0; i < n; i++) nmod_poly_mat_clear(out[i]);
        t_mix[j] = now_s() - t0;
        c_dec[j] = stats.decrypt - dec0;
        c_prove[j] = stats.shuffle_prove - prove0;

        /* Anyone: the statement from the previous list and the bytes. */
        t0 = now_s();
        verifier_statement(st, cts, n, j, pp);
        servers_ok &= evmlr_shuffle_verify_bytes(st, pub, len, pp->shuf_ctx);
        t_ver[j] = now_s() - t0;

        if (j == 0) {
            TEST_ONCE("election: a server's proof fails for an output it changed") {
                pub[K_SIS * POLY_BYTES] ^= 1;
                int ok = verify_publication(pub, len, cts, n, j, pp);
                pub[K_SIS * POLY_BYTES] ^= 1;
                TEST_ASSERT(ok == 0, end);
            } TEST_END;

            TEST_ONCE("election: a server's proof fails for a ballot it replaced") {
                /* Output 0 replaced by a copy of output 1: one ballot dropped,
                 * another counted twice. */
                size_t at0 = K_SIS * POLY_BYTES, at1 = (K_SIS + pp->L_max) * POLY_BYTES;
                uint8_t *keep = malloc(L_next * POLY_BYTES);
                memcpy(keep, pub + at0, L_next * POLY_BYTES);
                memcpy(pub + at0, pub + at1, L_next * POLY_BYTES);
                int ok = verify_publication(pub, len, cts, n, j, pp);
                memcpy(pub + at0, keep, L_next * POLY_BYTES);
                free(keep);
                TEST_ASSERT(ok == 0, end);
            } TEST_END;

            TEST_ONCE("election: a server's publication with a byte appended is refused") {
                uint8_t *longer = malloc(len + 1);
                memcpy(longer, pub, len);
                longer[len] = 0;
                int ok = verify_publication(longer, len + 1, cts, n, j, pp);
                free(longer);
                TEST_ASSERT(ok == 0, end);
            } TEST_END;
        }
        free(pub);

        /* The next list, and in the end the votes: the outputs as read. */
        for (slong i = 0; i < n; i++) {
            nmod_poly_mat_init(out[i], L_next, 1, MOD_Q);
            for (slong r = 0; r < L_next; r++) {
                nmod_poly_set(nmod_poly_mat_entry(out[i], r, 0), nmod_poly_mat_entry(st->c_hat[i], r, 0));
            }
        }
        have_out = 1;
        voting_statement_clear(st, n);
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
    printf("    timing, wall clock: setup %.2f s; casting %.2f s, %.2f ms per "
           "ballot; board check %.2f s, %.2f ms per ballot\n", t_setup,
           t_cast, 1e3 * t_cast / n, t_board, 1e3 * t_board / n);
    printf("    sizes: ballot %.1f KiB and its proof %.1f KiB on average; per server, "
           "outputs and proof, KiB per ballot:", ballot_bytes / 1024.0 / n,
           proof_bytes / 1024.0 / n);
    for (slong j = 0; j < k; j++) printf(" %.1f", pub_bytes[j] / 1024.0 / n);
    printf("\n");
    for (slong j = 0; j < k; j++) {
        printf("    timing, server %ld: mix %.2f s (decryption %.2f Gcycles, "
               "proof %.2f Gcycles), verify %.2f s\n", j + 1, t_mix[j],
               c_dec[j] / 1e9, c_prove[j] / 1e9, t_ver[j]);
    }

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
    free(t_mix);
    free(t_ver);
    free(c_dec);
    free(c_prove);
    free(pub_bytes);
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
