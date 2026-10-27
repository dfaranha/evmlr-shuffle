# evmlr-shuffle

[![CI](https://github.com/dfaranha/evmlr-shuffle/actions/workflows/ci.yml/badge.svg)](https://github.com/dfaranha/evmlr-shuffle/actions/workflows/ci.yml)

Implementation of the Proof of Shuffle and primitives of the paper "Efficient Verifiable Mixnets from Lattices,
Revisited" by Jonathan Bootle, Vadim Lyubashevsky, and Antonio Merino-Gallardo (https://eprint.iacr.org/2025/658).

## Overview

This repository provides an implementation of the Proof of Shuffle protocol based on lattice-based cryptography. 
The implementation includes the necessary primitives and algorithms to create and verify shuffles of encrypted messages.

### Requirements

FLINT is required to run the code in this repository. 
We recommend installing FLINT via the package manager or directly from the [FLINT website](http://flintlib.org/).
The code has been tested with FLINT versions 3.3.1 and 3.6.0.

[LaZer](https://github.com/dfaranha/lazer), for the voters' proofs of
correct encryption, is the submodule `third_party/lazer`, on the `skip-zeros`
branch of a fork with fixes and speed-ups. Fetch it with
`git submodule update --init third_party/lazer` (not recursive); the first
`make` then builds it and HEXL, which takes a few minutes and needs cmake and
unzip. `make LAZER_DIR=/path/to/lazer` uses another checkout. Without LaZer
those proofs are skipped (`lazer/README.md`).

## Primitives

The implementation includes the following key primitives:

- **Commitment Scheme**: A lattice-based commitment scheme based on the instantiation by Ajtai.
- **MLPKE**: Module-Lattice Public Key Encryption scheme, this scheme also underlies Kyber's encryption.
- **OTSE**: A lattice-based One-Time Symmetric Encryption scheme.
- **HPKE**: A lattice-based Hybrid Public Key Encryption scheme, relies on **OTSE** and **MLPKE**.

And the proofs that make the mixnet verifiable (`PROOF-SYSTEM.md`, option A′):

- **ZK⋆** (`evmlr_zk_proof.c`, `SHUFFLE-ZK.md`): an LNP22-style proof system
  over FLINT, linear in time and memory in the number of messages. Each server
  proves its shuffle (Protocol 1) and its decryption of the layer it removes
  (Section 3.3) in one ZK⋆ statement.
- **The voter's proof of correct encryption** (`evmlr_user_proof.c`): one
  LaZer linear proof per ballot (`evmlr_ballot.c`), across all its layers,
  which also shows that the vote is X^j or 0 (one candidate, or none);
  servers check it before decrypting.
- **Voting** (`evmlr_voting.c`): casting, then counting through every
  server, verifying every proof.

## Running the Code

`make` compiles every binary; it no longer runs anything, so it is safe to use
as a quick syntax check. Parallel builds are supported: `make -j$(nproc)`.

| Command | What it does |
| --- | --- |
| `make` / `make build` | Compile every binary |
| `make test` | Run the test suites only — fast, this is the inner development loop |
| `make bench` | Run the benchmark suites only — slow |
| `make run` | Run tests and benchmarks for every binary (the old `make` behaviour) |
| `make <name>` | Build and run one binary, e.g. `make shuffle` or `make commit` |
| `make election` | Run an election end to end: 25 voters, 8 candidates, 3 servers (about 7.5 minutes and 1.5 GB) |
| `make help` | List the available targets |
| `make clean` | Remove build artifacts |

The binaries themselves take an optional mode argument, so a single component
can be exercised directly:

```sh
./evmlr_shuffle.bin test    # tests only
./evmlr_shuffle.bin bench   # benchmarks only
./evmlr_shuffle.bin         # both (same as `all`)
```

Test failures are reported through the exit status, so `make test` fails loudly
and can be wired into CI.

`make election` runs the voting protocol end to end, each party with only what
it has (`evmlr_election.c`): the voters encrypt their votes, X^j for one of the
candidates, and prove their ballots; the board verifies them; each server in
turn removes its layer, shuffles, and proves both, and its proof is verified
against its public statement before the next server runs; the last outputs are
tallied against the votes. It also checks that the board refuses a ballot
changed after its proof, and that a server's proof fails for an output it
changed or a ballot it replaced. A `KNOWN GAP` check records that a voter's
proof does not bind the voter, so a copied ballot verifies for another voter.
The size is set at build time, e.g.
`rm -f evmlr_election.bin && make election EXTRA_CFLAGS=-DELECTION_VOTERS=4`
(also `-DNCAND`, `-DELECTION_SERVERS`). It is not part of `make test`.

### Continuous integration

`.github/workflows/ci.yml` builds and runs the test suites on every push and
pull request, in two configurations: the usual `-march=native` build and a
portable one (`ARCH=`) that checks the code still compiles without it.

The workflow pins `ubuntu-26.04` rather than `ubuntu-latest`, because this code
needs the FLINT >= 3.2 random-state API (`flint_rand_init`) and Ubuntu 24.04 —
which `ubuntu-latest` still resolves to — only packages FLINT 3.0.1.

Benchmarks are not run in CI; shared runners make the timings meaningless. To
treat compiler warnings as errors, add `EXTRA_CFLAGS=-Werror` to the build step.

Build flags can be overridden without editing the Makefile:

```sh
make ARCH=                      # portable build, without -march=native
make OPT=-O0                    # unoptimised, for debugging
make EXTRA_CFLAGS=-fsanitize=address
```

Even the portable build needs an x86-64 processor with AES-NI and AVX2:
`fastrandombytes.c` uses the former and the NTT in `evmlr_zk.c` the latter, and
both get the flags for them whatever `ARCH` is.

To tweak the parameters of the schemes, mainly the number of messages, you can
modify `evmlr_params.h` in the root directory. Header dependencies are tracked,
so editing it rebuilds everything that depends on it.

## TODO

- [ ] Optimize the implementation for performance. Multiplication in R_q now
      uses the CRT decomposition (`evmlr_crt.c`); the remaining headroom is in
      keeping operands in the split representation between operations instead
      of converting per multiplication.
- [ ] Free the keypairs allocated inside the benchmark timing loops (`bench()`
      in `evmlr_mlpke.c` and `evmlr_hpke.c` regenerate a keypair per iteration
      without clearing the previous one). Harness-only, but it is why leak
      detection is disabled for the benchmark phase in CI.
- [ ] Add more detailed documentation and comments in the code.
- [ ] Separate the tests and benchmarks into their own files (they can already be run independently via `make test` / `make bench`, but still live behind `#ifdef MAIN` in the implementation files).
- [ ] Fix a bug where if a proof of shuffle is run multiple times it sometimes
      fails (this is likely due to a variable changing state unexpectedly).
      Not reproducible as of the memory-ownership fixes: 400 consecutive proofs
      (`./evmlr_shuffle.bin bench`, four runs of 100) completed without a
      failure, and the suites are clean under ASan, UBSan and valgrind. The
      ownership bugs fixed there -- outputs being re-initialised on top of a
      live allocation -- are a plausible cause, but this has not been confirmed,
      so the item stays open until someone reproduces it or agrees to close it.
- [x] Split ZK⋆'s carries into two blocks, Protocol 1's few large ones and the
      decryption's many small ones, each with its own projection and width.
- [x] Implement the proof of correct decryption that each mixing server owes
      (knowledge of the secret key, the bound on the seed decryption error, and
      correct rounding), with the shuffle in one ZK⋆ statement.
- [x] Prove the shuffle in zero-knowledge, soundly at q = 3109 (ZK⋆, which
      lifts to a proof modulus p = 2^52 - 395). The earlier linear and binary
      proofs over R_q could not be sound at that modulus (`PROOF-SYSTEM.md`)
      and are removed.
- [ ] The voter's proof needs about 2 GB at three servers and 4.5 GB at four
      (LaZer's prover); the voting test runs it at `VOTING_TEST_K`.
- [x] Voters prove correct encryption of their whole ballot (LaZer), checked
      before any server decrypts.

**WARNING**: This is a prototype implementation for research purposes only. It is not optimized for performance or security.
