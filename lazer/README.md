# LaZer parameters for the user's proof

`evmlr_user_proof.c` proves a ballot's correct layered encryption, and that
the vote it carries is X^j or 0, with LaZer's linear proof (option A′ in
`PROOF-SYSTEM.md`). LaZer's proof
parameters depend on the statement's shape, which depends on the number of
servers `k`, so there is one header per `k`:

| `k` | statement | proof | prove / verify | prover memory |
| --- | --- | --- | --- | --- |
| 2 | 17 × 68 | 107.5 KiB measured (112.8 predicted) | 7.2 / 5.2 Gcycles | 0.6 GB |
| 3 | 29 × 128 | 195.8 KiB predicted | | about 2 GB (estimated) |
| 4 | 44 × 206 | 316.5 KiB predicted | | about 4.5 GB (estimated) |

**The vote.** Each layer's pad at the last position masks the vote, and the
innermost layer's pad is nothing but that; before, those positions were left
out of the witness and the vote was unconstrained. The statement now also has,
per layer, the rounding bits of that position (and of the K_LWE positions of
the innermost layer's pad that feed it through H''), the vote m (binary) and a
copy u with ||u|| <= 1, a row for the outermost ciphertext at the vote's
position, c*_0[3 (k - 1)] = m + sum_i a_i[3 (k - 1 - i)], and a row m - u = 0.
A binary m equal to a u of norm at most 1 is X^j or 0. That costs 39, 45 and 66
KiB at k = 2, 3 and 4 (from 73.7, 151.2 and 250.7 KiB), most of it the binary
witness for the pad positions; the expected prover repetitions fall (at k = 4
from 13.0 to 7.3).

The parameters ask LaZer for a root Hermite factor of 1.0036 (`DELTA_TARGET`
in `user_params.py`). LaZer's default, 1.0044, is what it calls 128-bit, but
under the lattice-estimator's core-SVP model, the one the other codebases'
security is stated in, these statements were then at 102-104 bits. At 1.0036
they are at 134.9-137.1 bits for hiding (MLWE) and 135.2-137.5 for binding
(MSIS), for 1-3% larger proofs; under the estimator's MATZOV cost model the
old parameters were already at about 130.

The `user<k>.py` files describe the statements and are written by
`user_params.py <k>`. The `user<k>.h` headers are generated from them and
checked in, so building needs LaZer's library but not Sage.

## Building

LaZer is the submodule `third_party/lazer`: branch `skip-zeros` of
[this fork](https://github.com/dfaranha/lazer), which drops an unused matrix
allocation that roughly doubled the prover's peak memory, fixes the toolbox
prover's proofs without the approximate infinity-norm part, and speeds it up.
Fetch it with `git submodule update --init third_party/lazer`; `make` here
builds it, HEXL included, through LaZer's own Makefile, and links its
`liblazer.a`, HEXL and MPFR. `make LAZER_DIR=/path/to/lazer` uses a checkout
elsewhere. Without LaZer, the user proof refuses and its tests are skipped.

LaZer's prover recurses over the binary coefficients. From three servers on,
it overflows a default 8 MB stack, so `evmlr_user_proof.c` runs LaZer on a
thread of its own with a 1 GB stack.

## Regenerating a header

From the top of this repository:

```
cd lazer && python3 user_params.py 3
cd ../third_party/lazer/scripts
sage lin-codegen.sage ../../../lazer/user3.py > ../../../lazer/user3.h
```

The statement holds mod `64 q`: rows mod `q` are scaled by 64, and the
rounding rows mod `2^ζ = 64` are scaled by `q`. `lin-codegen.sage` took the
centred bound on the statement's coefficients to be `P = (mod-1)/2`, which is
not an integer for an even modulus; the bound it means is `floor(mod/2)`, the
same for odd moduli. `skip-zeros` has that fix (`2165f60`), and the option to
set the target root Hermite factor (`f73d99a`). The headers here were
generated from `2165f60`.
