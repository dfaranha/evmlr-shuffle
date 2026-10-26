# Build knobs. Override on the command line, e.g.
#   make ARCH=            # portable binaries (no -march=native)
#   make OPT=-O0          # unoptimised, for debugging
#   make EXTRA_CFLAGS=-fsanitize=address
ARCH        ?= -march=native -mtune=native
OPT         ?= -O3
EXTRA_CFLAGS ?=

CC  = gcc
CXX = g++

CFLAGS   = $(OPT) $(ARCH) -Wall -ggdb -pthread $(EXTRA_CFLAGS)
DEPFLAGS = -MMD -MP
LIBS     = -lflint -lgmp -lstdc++ -lm

# LaZer, for the user's proof of correct encryption (evmlr_user_proof.c), is
# the submodule third_party/lazer: branch tbox-fixes of dfaranha/lazer, LaZer
# with fixes to its toolbox prover, a leak fix and speed-ups. It is built on
# first use, HEXL included (a few minutes), by LaZer's own Makefile. Point
# LAZER_DIR at another checkout, or set it empty to build without LaZer, in
# which case the user proof refuses and the voting protocol skips it; the
# default is empty too while the submodule is not checked out. Run make clean
# after switching, since the objects differ.
LAZER_DIR ?= $(if $(wildcard third_party/lazer/Makefile),$(abspath third_party/lazer))
ifneq ($(LAZER_DIR),)
LAZER_LIB = $(LAZER_DIR)/liblazer.a
# Where tbox-fixes builds HEXL; an older LaZer may have put it in lib.
HEXL_LIB ?= $(firstword $(wildcard $(LAZER_DIR)/third_party/hexl-development/build/hexl/lib/libhexl.a) \
                        $(LAZER_DIR)/third_party/hexl-development/build/hexl/lib64/libhexl.a)
CFLAGS  += -DEVMLR_LAZER -I$(LAZER_DIR) -I.
LIBS    := $(LAZER_LIB) $(HEXL_LIB) -lmpfr $(LIBS)
endif

PREFIX  = evmlr
TARGETS = mlpke commit otse hpke shuffle voting ballot zk zk_proof user_proof
BINS    = $(TARGETS:%=$(PREFIX)_%.bin)

# Objects every binary needs: shared helpers plus the test/benchmark harness.
COMMON_OBJS = $(PREFIX)_utils.o $(PREFIX)_crt.o test.o bench.o cpucycles.o randombytes.o

# Extra objects required by individual binaries.
$(PREFIX)_hpke_EXTRA      = $(PREFIX)_otse.o $(PREFIX)_mlpke.o
$(PREFIX)_shuffle_EXTRA   = $(PREFIX)_hpke.o $(PREFIX)_commit.o $(PREFIX)_mlpke.o $(PREFIX)_otse.o sha224-256.o fastrandombytes.o $(PREFIX)_challenge.o gaussian.o $(PREFIX)_zk.o $(PREFIX)_zk_proof.o
$(PREFIX)_voting_EXTRA    = $(PREFIX)_shuffle.o $(PREFIX)_hpke.o $(PREFIX)_commit.o $(PREFIX)_mlpke.o $(PREFIX)_otse.o sha224-256.o fastrandombytes.o $(PREFIX)_challenge.o $(PREFIX)_ballot.o $(PREFIX)_user_proof.o gaussian.o $(PREFIX)_zk.o $(PREFIX)_zk_proof.o
# The election includes evmlr_voting.c for its server step, so it links what
# voting links.
$(PREFIX)_election_EXTRA  = $($(PREFIX)_voting_EXTRA)
$(PREFIX)_ballot_EXTRA    = $(PREFIX)_hpke.o $(PREFIX)_mlpke.o $(PREFIX)_otse.o
$(PREFIX)_user_proof_EXTRA = $(PREFIX)_ballot.o $(PREFIX)_hpke.o $(PREFIX)_mlpke.o $(PREFIX)_otse.o
$(PREFIX)_zk_EXTRA        = sha224-256.o fastrandombytes.o
$(PREFIX)_zk_proof_EXTRA  = $(PREFIX)_zk.o sha224-256.o fastrandombytes.o gaussian.o

.PHONY: all build test bench run clean help election $(TARGETS)

## all:   build every binary (does not run anything)
all: build

## build: compile every binary
build: $(BINS)

## test:  build, then run the test suites only (fast)
test: $(BINS)
	@fail=0; for b in $(BINS); do \
		echo "=== $$b ==="; ./$$b test || fail=1; \
	done; exit $$fail

## bench: build, then run the benchmark suites only (slow)
bench: $(BINS)
	@fail=0; for b in $(BINS); do \
		echo "=== $$b ==="; ./$$b bench || fail=1; \
	done; exit $$fail

## run:   build, then run tests and benchmarks for every binary
run: $(BINS)
	@fail=0; for b in $(BINS); do \
		echo "=== $$b ==="; ./$$b all || fail=1; \
	done; exit $$fail

## election: build and run an election end to end (minutes; not in test).
##           EXTRA_CFLAGS=-DELECTION_VOTERS=<n> sets its size (25), likewise
##           -DNCAND (8) and -DELECTION_SERVERS (3)
election: $(PREFIX)_election.bin
	./$<

## <name>: build and run one binary, e.g. `make shuffle` (see TARGETS below)
$(TARGETS): %: $(PREFIX)_%.bin
	./$<

# Some sources use x86 intrinsics unconditionally and therefore need those
# instruction sets enabled even when ARCH does not imply them (e.g. ARCH=).
fastrandombytes.o: EXTRA_CFLAGS += -maes -msse4.1
gaussian.o:        EXTRA_CFLAGS += -msse4.1
evmlr_zk.o evmlr_zk.main.o: EXTRA_CFLAGS += -mavx2

.SECONDARY: # keep the %.main.o intermediates so rebuilds stay incremental

.SECONDEXPANSION: # expand $(<name>_EXTRA) after the stem is known
%.bin: %.main.o $$($$*_EXTRA) $(COMMON_OBJS) | $(LAZER_LIB)
	$(CC) $(CFLAGS) $^ -o $@ $(LIBS)

# The translation unit that provides main(); compiled with -DMAIN so that the
# test/benchmark section of the file is included. Every object waits for LaZer,
# whose build generates the lazer.h some of them include.
%.main.o: %.c | $(LAZER_LIB)
	$(CC) $(CFLAGS) $(DEPFLAGS) -DMAIN -c $< -o $@

%.o: %.c | $(LAZER_LIB)
	$(CC) $(CFLAGS) $(DEPFLAGS) -c $< -o $@

%.o: %.cpp | $(LAZER_LIB)
	$(CXX) $(CFLAGS) $(DEPFLAGS) -c $< -o $@

# LaZer and HEXL, built in the submodule by LaZer's own Makefile.
ifneq ($(LAZER_LIB),)
$(LAZER_LIB):
	$(MAKE) -C $(LAZER_DIR) liblazer.a
endif

help:
	@echo "Targets:"
	@sed -n 's/^## //p' $(MAKEFILE_LIST)
	@echo
	@echo "TARGETS = $(TARGETS)"

clean:
	rm -f *.o *.d *.so *.bin

# Header dependencies recorded by -MMD, so that editing e.g. evmlr_params.h
# rebuilds everything that includes it.
-include $(wildcard *.d)
