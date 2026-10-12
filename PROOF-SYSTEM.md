# The proof system: why it has to change, and to what

This note is about `ZK⋆`, the zero-knowledge proof system that Protocol 1 and
Section 3.3 of Bootle, Lyubashevsky and Merino-Gallardo (ePrint 2025/658) rely
on for every linear relation, norm bound and binary constraint. The paper leaves
it abstract and takes its sizes from the LaZer library's linear proofs. This
repository implements its own, in `evmlr_lin_proof.c` and `evmlr_bin_proof.c`.
Those proofs cannot be made sound at the paper's parameters. The recommendation
is to use LaZer, as the paper did.

## 1. The current proofs cannot be fixed in place

Every relation is stated modulo `q = 3109` over `R = Z[x]/(x^512 + 1)`, and the
proofs work in that same ring: masks `y`, responses `z = y + c s`, and a
verifier that checks `A z - c t = w` and a norm bound on `z`. Soundness then
rests on MSIS modulo 3109 at the norm of what the extractor gets, and
zero-knowledge on masks much wider than `c s`. At `q = 3109` the two cannot
both hold, and soundness cannot hold on its own either.

The numbers for the HPKE encryption proof, whose witness `(r, e2, e3, s̄)` has
`‖s‖ ≈ 53`:

| challenge | operator norm `T` | mask width at `M = 3` | at `α = 1` | MSIS bound extracted | `q` |
| --- | --- | --- | --- | --- | --- |
| `ν = 20` ternary (`|C| ≥ 2^128` needs `ν ≥ 19`) | 12.5 | 7300 | 660 | `2^22.5`–`2^25.9` | `2^11.6` |
| `ν = 36` ternary | 17 | 9900 | 900 | `2^23.8`–`2^27.2` | `2^11.6` |

The mask must be about `α T ‖s‖` wide, and at any useful `α` that is already
larger than `q / 2 = 1554`. Even with no zero-knowledge margin, the vector the
extractor recovers is 11 to 15 bits longer than `q`, and MSIS with a bound at
or above `q` is trivial: `(q, 0, ..., 0)` is a solution. No choice of
challenge, `σ` or rejection rate changes that. The current code shows the
symptoms:

- `set_gaussian` gives `σ ≈ 31000`, so a mask reduced mod `q` is close to
  uniform, and the verifier's `4 N σ²` bound is 130 to 530 times the largest
  squared norm a vector mod `q` can have. It accepts everything.
- The linear proof's challenge has 36 coefficients uniform mod `q` rather than
  `±1`, so even the extracted `c̄ s` is not short.
- Com⋆ is binding for exact openings at `q = 3109`, but a proof of knowledge
  of an opening extracts relaxed openings far above `q`, so binding through
  the proof is lost too.

## 2. What the paper does: lift to a larger proof modulus

LaZer (Lyubashevsky, Seiler, Steuer; built on LNP22) proves a statement
`A s = t mod p` for a small `p` by moving it to a ring with a much larger
modulus `q'`. Over the integers, `A s - t = p k` for a carry vector `k`, which
it adds to the witness with an approximate ℓ∞ bound; the relation then holds
mod `q'`, and because nothing wraps mod `q'`, it holds over the integers and
therefore mod `p`. Norms are proven exactly in ℓ2 (LNP22), binary constraints
directly, and the ring is a degree-64 subring, so a degree-512 element is 8
coefficients' worth of degree-64 elements. Challenges have coefficients in
`[-8, 8]` with a bounded operator norm.

LaZer's `scripts/lin-codegen.sage` derives all of this from a
description of the statement. Run on two of ours:

| statement | dimension | `q'` | knowledge error | proof |
| --- | --- | --- | --- | --- |
| HPKE seed encryption (`K_LWR = 1`), `s̄` binary, `r, e2, e3` CBD(2) | 3 × 6 | `2^36` | `2^-127` | 21.9 KiB |
| Protocol 1 at `N = 10`, `L = 1`: equations (1)–(3) and the openings of `D`, `P`, `W` | 16 × 262 | `2^42` | `2^-127` | 393 KiB, 39 KiB a user |

The second is in line with the paper's 110 KB per user per server, which also
includes the decryption proof. Both descriptions are in the appendix.

Measured on this laptop (i7-10510U, one core), proving random satisfiable
instances with the generated parameters:

| statement | proof | prove | verify | peak memory |
| --- | --- | --- | --- | --- |
| HPKE seed encryption | 21.1 KiB | 0.21 s | 0.10 s | small |
| Protocol 1, `N = 4` | 162 KiB (40 KiB a user) | 4.7 s | 3.2 s | 2.5 GB |
| Protocol 1, `N = 10` | | | | killed by the OOM killer above 5.7 GB |

So LaZer suits the fixed-shape proofs, but one statement for the whole shuffle
grows by roughly 0.6 GB a message. Where that memory goes has not been
profiled; the `N = 10` run first crashed on the stack in the Schwartz-Zippel
accumulation over its 2000 binary coefficients. Splitting the statement into
blocks is not free: `D` commits all `N` vectors `d†`, so its opening involves
all of them, and blocks would need a commitment per message, which changes
Protocol 1.

LaZer's linear proofs run on this machine, which has no AVX-512 (an
i7-10510U): only its LaBRADOR code uses AVX-512, and the Kyber1024 demo proves
and verifies in 0.19 s here. The README lists AVX-512 as a requirement for the
library as a whole.

## 3. Options

The proofs fall into two kinds. The user's proof of correct encryption and the
server's proof of correct decryption have a fixed shape per message. The
shuffle's statement grows with `N` and has rounds: `P` before `α, β, λ`, `W`
before `γ`.

**A. LaZer for everything.** Express every relation as a LaZer linear
statement mod `q`, generate parameters with `lin-codegen.sage`, and convert
between FLINT and LaZer at the boundary.

- For: closest to the paper; exact ℓ2 and binary proofs, lifting from mod `q`,
  and the security accounting all come with it; least new cryptography.
- Against: the shuffle as one statement does not fit in memory beyond a
  handful of messages (above); a new dependency (gcc ≥ 13, MPFR, HEXL, Sage);
  parameters per statement shape; and LaZer's linear proof is one-shot, so
  Protocol 1's rounds must go through Com⋆ commitments mod `q` with binary
  messages, which is why `w†` exists at all.

**A′. LaZer for encryption and decryption, our own proofs for the shuffle
(recommended).** LaZer where it fits, at 21 KiB and 0.3 s for the HPKE part,
and the shuffle on the `lnp` branch's machinery from `lattice-voting-ctrsa21`
(ABDLOP commitments, LNP22 binary proofs, JL approximate range proofs,
garbage-term aggregation, over FLINT), which already runs multi-round proofs at
about 0.1 s a message with modest memory.

- For: each part on the tool that suits it; the shuffle stays fast and small,
  and its commitments can span rounds.
- Against: two proof systems to maintain; the `lnp` machinery has to gain the
  lifting from mod `q` with a proven carry, which it does not have (its
  statements are mod its own `p ≈ 2^40`), and its ℓ2 bounds come from the
  response rather than an exact proof; the shuffle and the decryption proof
  must agree on `D`, which crosses the two systems.

**B. Our own proofs for everything.** As A′, with the encryption and
decryption proofs on the `lnp` machinery too. FLINT only, one system, but the
largest job: the parts LaZer would have provided (lifting, exact ℓ2) are
needed for every proof, and all parameters and soundness arguments are ours to
derive and review.

**B′. A′ or B, with a lighter shuffle.** Two changes to Protocol 1 that our own
machinery allows and LaZer's one-shot proof does not:

- *Commit `W`, and `P`, in BDLOP form inside the proof* rather than as Com⋆
  commitments of binary decompositions. That removes `w†`, 12 binary ring
  elements a message, about half the binary part.
- *The relaxed Lemma 5 from `lattice-voting-ctrsa21`'s `fix-pkc`*: commit
  `σ_i` as a monomial `x^{π(i)}` and prove only that `δ σ_i` is short, instead
  of `is_bin(σ_i)`. In `R_q` this fails by two orders of magnitude, because
  Lemma 1's ceiling is `q^{1/2} ≈ 56` against an extracted norm of at least
  `4 σ_S sqrt(512) ≈ 8500` (`σ_S ≥ 21.485 sqrt(ν) ≈ 94` at `ν = 19`). It works
  only if the product argument moves to the proof modulus `q' ≈ 2^36`–`2^42`,
  where the ceiling is `2^18`–`2^21`, with each message's ciphertext relation
  lifted as `c⋆_i - H' B(η) d†_i + q k_i = ĉ_{π(i)}` over the integers. It
  saves only `is_bin(σ_i)`, one ring element a message, and needs a soundness
  argument of its own, like `fix-pkc`'s `SOUNDNESS.md`.

`d†` stays binary in every option: it is the decomposition of the pad, and
binariness is what makes `G d† = d` determine it, which ties the shuffle to the
decryption proof.

**C. Keep the current proofs as a functional prototype**, documented as not
sound, and invest in the mixnet's other parts first.

## 3a. What was built (option A′)

- **The voter's proof of correct encryption: LaZer**, as A′ has it, on the
  `lazer` branch, which adds LaZer as an optional build dependency. It is one
  linear statement per ballot across all `k` layers, 68.5 KiB at two
  servers. This branch builds the ballots (`evmlr_ballot.c`) but does not
  prove them.
- **The server's proof of correct decryption: ZK⋆, in the same statement as
  the shuffle** (`SHUFFLE-ZK.md`, section 1.1), not LaZer.
  - The decryption and the shuffle must agree on `d†`, and `D` commits every
    message's `d†` at once.
  - A LaZer proof that opens `D` would be one statement over all `N`
    messages, which LaZer's memory does not allow past about ten (section 2).
    Per-message commitments `D_i` would change Protocol 1 and cost about
    `N · K_SIS` more opening rows.
  - In one ZK⋆ statement, `d†` is simply one witness variable, and the proof
    is the single "shuffle & decryption proof" whose size the paper reports.
  - It needed ZK⋆ to take rows with their own moduli and many rows (one per
    message and pad position), and `κ = 5`.
- **The earlier proofs** (`evmlr_lin_proof.c`, `evmlr_bin_proof.c`,
  `evmlr_enc_proof.c`, `evmlr_lin_comp.c`) are removed.

## 4. Mapping the relations to LaZer statements

Each proof below is one statement, so that the witnesses that must agree are
the same variables. Where the paper links proofs, it does so through a public
Com⋆ commitment whose opening is a row of each statement: the shuffle and the
decryption proof both open `D` to the same `d†`.

| proof | rows | witness and constraints |
| --- | --- | --- |
| user, per layer | HPKE seed encryption (mod `q`); rounding (3) (mod `2^ζ`); `c⋆ = m + H' B(η) d†` (mod `q`) | `r, e2, e3` CBD(η) ℓ2; `s̄`, `d†`, `r†` binary; `m` free |
| server, decryption | `A s + e = t`; `e'_{i,j} = c'^T (-s, 1) - ⌊q/2⌉ s̄_i[j]`; rounding (3); opening of `D` | `s, e` ℓ2; `e'` ℓ∞ `< q/4`; `s̄`, `d†`, `r†` binary; `r_D` ℓ2 |
| server, shuffle | Protocol 1 (1)–(3); openings of `D`, `P`, `W` | `d†`, `σ`, `w†` binary; `r_D, r_P, r_W` ℓ2 |

The rounding relation (3) is mod `2^ζ = 64` while the rest are mod `q`, but they
share `s̄` and `d†`. Since `gcd(64, 3109) = 1`, both fit in one statement mod
`64 q`: multiply the mod-`2^ζ` rows by `q` and the mod-`q` rows by 64, since
`q x ≡ 0 (mod 64 q)` exactly when `x ≡ 0 (mod 64)`. `lin-codegen.sage` needs the
statement modulus to be invertible mod `q'`, which `64 q` is, but it computes
`P = (mod - 1) / 2` as the centred range, which is not an integer for an even
modulus; that may need a small change there, or a per-row modulus.

`lin-codegen.sage` also divides by zero when no part of the witness is
ℓ2-bounded (`alpha3 = 0` in `lnp-tbox-codegen.sage`); every statement above has
such a part, so this is a note rather than a blocker.

## 5. Plan, if A (the LaZer steps also apply to A′)

1. Build: LaZer as a pinned dependency (submodule or `LAZER_DIR`), parameters
   generated into headers checked in alongside the `.py` descriptions, and a
   conversion layer between `nmod_poly_mat_t` and `polyvec_t` / `polymat_t`.
2. The user's HPKE proof alone, replacing `proof_hpke`, with the parameters
   above. Tests: honest proof verifies; a proof for a ciphertext with a
   non-binary seed, or noise outside CBD(η), does not.
3. The full user proof per layer, including the rounding rows and the OTSE row;
   this settles the two-modulus question.
4. The shuffle proof as one statement, replacing `evmlr_lin_proof` and
   `evmlr_bin_proof` there; `D`, `P`, `W` stay Com⋆ commitments mod `q`.
5. The server's decryption proof, which does not exist yet, sharing `D` with
   the shuffle.
6. Remove the hand-rolled proofs.

## 6. Questions

- Is a LaZer dependency acceptable, or does the repository need to stay
  FLINT-only (option B)?
- For the shuffle, is changing Protocol 1 acceptable (B′: BDLOP-committed `W`
  and `P`; the relaxed Lemma 5 over `q'`), or should it stay as the paper
  states it?
- Should Protocol 1's parameters be generated per `N`, or for a fixed maximum
  `N` with the lists padded?
- Is the user's proof meant to be one statement per layer, as above, or one
  across all `ρ` layers? The paper's 322 KB per user does not say.

## Appendix: the `lin-codegen.sage` inputs

```python
# HPKE seed encryption, K_LWR = 1: [A^T | I | 0 ; t^T | 0 | 1 | round(q/2)] (r, e2, e3, sbar) = (u, v)
deg, mod, dim = 512, 3109, (3, 6)
wpart = [list(range(5)), [5]]
wl2   = [1.2*sqrt(512*5*1.0), 0]   # CBD(2) has variance 1
wbin  = [0, 1]
wlinf = 2

# Protocol 1, N = 10, L = 1: N equations (1)-(3) + 3 openings of K_SIS = 2 rows;
# witness d_dagger (120) | sigma (10) | w_dagger (120) binary, r_D, r_P, r_W (12) CBD(2)
deg, mod, dim = 512, 3109, (16, 262)
wpart = [list(range(250)), list(range(250, 262))]
wl2   = [0, 1.2*sqrt(512*12*1.0)]
wbin  = [1, 0]
wlinf = 2
```
