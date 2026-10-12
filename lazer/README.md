# LaZer parameters for the user's proof

`evmlr_user_proof.c` proves a ballot's correct layered encryption with
LaZer's linear proof (option A′ in `PROOF-SYSTEM.md`). LaZer's proof
parameters depend on the statement's shape, which depends on the number of
servers `k`, so there is one header per `k`:

| `k` | statement | proof | prove / verify | prover memory |
| --- | --- | --- | --- | --- |
| 2 | 11 × 42 | 68.5 KiB | ~2 s / ~1.5 s | 0.55 GB |
| 3 | 22 × 96 | | | about 2 GB (estimated) |
| 4 | 36 × 168 | | | about 4.5 GB (estimated) |

The `user<k>.py` files describe the statements and are written by
`user_params.py <k>`. The `user<k>.h` headers are generated from them and
checked in, so building needs LaZer's library but not Sage.

## Building

LaZer comes from [this fork](https://github.com/dfaranha/lazer), which drops
an unused matrix allocation that roughly doubled the prover's peak memory.
Clone it next to this checkout and build it:

```
git clone https://github.com/dfaranha/lazer ../lazer
cd ../lazer/third_party && unzip hexl-development.zip && cd hexl-development
cmake -S . -B build -DHEXL_BENCHMARK=OFF -DHEXL_TESTING=OFF -DCMAKE_POLICY_VERSION_MINIMUM=3.5
cmake --build build
cd ../.. && make lib-static
```

(The policy flag is for CMake 4, which refuses a dependency of HEXL that
asks for CMake older than 3.5; LaZer's own Makefile runs the same configure
without it.) `make` here then finds `../lazer` and links its `liblazer.a`,
HEXL and MPFR; `make LAZER_DIR=/path/to/lazer` uses a checkout elsewhere.
Without LaZer, the user proof refuses and its tests are skipped.

LaZer's prover recurses over the binary coefficients. From three servers on,
it overflows a default 8 MB stack, so `evmlr_user_proof.c` runs LaZer on a
thread of its own with a 1 GB stack.

## Regenerating a header

```
cd ../lazer/scripts
python3 ../../evmlr-shuffle/lazer/user_params.py 3
sage lin-codegen.sage user3.py > user3.h
```

`lin-codegen.sage` needs one change. The statement holds mod `64 q`: rows mod
`q` are scaled by 64, and the rounding rows mod `2^ζ = 64` are scaled by `q`.
The script takes the centred bound on the statement's coefficients to be
`P = (mod-1)/2`, which is not an integer for an even modulus. The bound it
means is `floor(mod/2)`, which is the same for odd moduli:

```
-P = (mod-1)/2
+P = floor(mod/2)
```

The headers here were generated that way, from LaZer commit `415967c`.
