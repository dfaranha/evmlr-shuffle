# LaZer parameters for the user's proof

`evmlr_user_proof.c` proves a ballot's correct layered encryption with
LaZer's linear proof (option A′ in `PROOF-SYSTEM.md`). LaZer's proof
parameters depend on the statement's shape, which depends on the number of
servers `k`, so there is one header per `k`:

| `k` | statement | proof | prove / verify | prover memory |
| --- | --- | --- | --- | --- |
| 2 | 11 × 42 | 70.3 KiB measured (73.7 predicted) | 9.4 / 2.5 Gcycles | 0.55 GB |
| 3 | 22 × 96 | 151.2 KiB predicted | | about 2 GB (estimated) |
| 4 | 36 × 168 | 250.7 KiB predicted | 9.6 s / 7.6 s on a Xeon Silver 4314 (before the change below) | about 4.5 GB (estimated) |

The parameters ask LaZer for a root Hermite factor of 1.0036 (`DELTA_TARGET`
in `user_params.py`). LaZer's default, 1.0044, is what it calls 128-bit, but
under the lattice-estimator's core-SVP model, the one the other codebases'
security is stated in, these statements were then at 102-104 bits. At 1.0036
they are at 133.5-136.1 bits for hiding (MLWE) and 136.1-137.8 for binding
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
