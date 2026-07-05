# Assay — one-command reproduction.
# Each target fails loudly; `make verify` is the whole pipeline.

# Use the pinned toolchain installed by scripts/setup.sh into .tools/ (gitignored).
# We both (a) export it on PATH so saw/isabelle find their bundled helpers (z3, etc.) at
# runtime, and (b) call the tools by EXPLICIT path below — GNU Make 3.81 exec's single-command
# recipes directly and resolves them against Make's own PATH, not the exported one.
TOOLS_BIN   := $(CURDIR)/.tools/bin
export PATH := $(TOOLS_BIN):$(PATH)

SAW         := $(TOOLS_BIN)/saw
ISABELLE    := $(TOOLS_BIN)/isabelle
CLANG       ?= clang

TARGET_C    := target/pqclean
BITCODE     := build/mldsa_ntt.bc
SAW_SCRIPT  := proof/saw/mldsa_ntt.saw
ISA_SESSION := Assay

.PHONY: all verify target-identity bitcode saw isabelle tier2 tier2-inv barrett barrett-solver lift-check mutation-test qseal-tbs qseal-ref writeup clean

all: verify

## Full pipeline: target bytes pinned (target-identity) → lift in sync (lift-check) → C ≡ Cryptol
## (SAW) → reduce.c model ≡ FIPS spec (Isabelle) → forward-NTT model ≡ FIPS-204 transform (Isabelle,
## Tier2) → inverse-NTT model ≡ FIPS-204 inverse transform (Isabelle, Tier2_InvWork)
verify: target-identity lift-check saw isabelle tier2 tier2-inv barrett
	@echo "✔ pipeline complete — all checked steps passed"

## Integrity gate: the vendored C under proof is byte-for-byte the pinned snapshot.
target-identity:
	./scripts/check_target_identity.sh

## Composition gate: committed Isabelle model == cryptol-to-isabelle(Cryptol model). Fast; SAW bundle only.
lift-check:
	./scripts/lift_check.sh

## Non-vacuity guard: assert SAW REJECTS a deliberately-wrong model.
mutation-test:
	CLANG=$(CLANG) ./scripts/mutation_test.sh

## Compile the target C subroutine to LLVM bitcode for SAW
bitcode:
	@mkdir -p build
	CLANG=$(CLANG) ./scripts/build_bitcode.sh $(TARGET_C) $(BITCODE)

## Prove the C implementation matches the Cryptol model
saw: bitcode
	@echo ">> SAW: proving C ≡ Cryptol"
	$(SAW) $(SAW_SCRIPT)

## Run the Isabelle session: model ≡ FIPS-204 spec
isabelle:
	@echo ">> Isabelle: proving reduce.c model ≡ FIPS-204 spec"
	$(ISABELLE) build -D spec/isabelle -v $(ISA_SESSION)

## Tier2 Isabelle session: lifted forward NTT ≡ FIPS-204 negacyclic transform (fwd_ntt_correct)
## plus the model bridge (Mont_Bridge) tying the SAW-checked montgomery model to it; the bridge
## reuses the Assay session (montgomery_reduce_correct), so both -d dirs are needed.
tier2:
	@echo ">> Isabelle (Tier2): forward NTT ≡ FIPS-204 transform + montgomery-model bridge"
	$(ISABELLE) build -d spec/isabelle -d spec/isabelle/tier2 -v Tier2

## Tier2_InvWork Isabelle session: lifted inverse NTT ≡ FIPS-204 inverse negacyclic transform
## (inv_ntt_correct) plus the model bridge (invntt_bridge) tying the SAW-checked montgomery invntt
## to it, montgomery-scaled by mont/256. Child of Tier2 (reuses the forward chain + Assay heap).
tier2-inv:
	@echo ">> Isabelle (Tier2_InvWork): inverse NTT ≡ FIPS-204 inverse transform + montgomery-model bridge"
	$(ISABELLE) build -d spec/isabelle -d spec/isabelle/tier2 -v Tier2_InvWork

## Barrett Route Y session: the lifted BV Barrett model (barrettBV) == x mod q for x < 2^46,
## proven in Isabelle Word_Lib (barrettBV_bridge_holds). Mechanizes the escape-2 wide-Barrett
## admit end to end (replaces the nine bvToInt homomorphisms admitted in the SAW spike).
barrett:
	@echo ">> barrett lift-check: Barrett_Lift.thy == cryptol-to-isabelle(barrett_bridge.cry)"
	./scripts/lift_check_barrett.sh
	@echo ">> Isabelle (Barrett): lifted BV Barrett model ≡ x mod q (Route Y, no smt/oracle)"
	$(ISABELLE) build -d spec/isabelle/tier2/barrett -v Barrett

## Out-of-band (~33 min): prove the deployed barrett_reduce == x mod q for x < 2^46 directly on the
## RustCrypto MIR, via SAW's bitwuzla backend. This closes the escape-2 obligation that
## field_ops_bridged.saw assumes for speed. Not in `verify` (too slow for the fast pipeline); needs
## bitwuzla on PATH (pinned 0.9.1 by scripts/setup.sh). Route Y (`make barrett`) is the oracle-free twin.
barrett-solver:
	@echo ">> SAW + bitwuzla: barrett_reduce == x mod q for x < 2^46 (escape-2 admit, closed)"
	@echo ">> (needs the RustCrypto MIR harness: implementations/rustcrypto-ml-dsa/build/mldsa_harness.linked-mir.json)"
	cd implementations/rustcrypto-ml-dsa/proof/ntt && $(SAW) barrett_reduce_bitwuzla.saw

## Q-SEAL protocol property (independent of the ML-DSA primitive). Fast (<1s). Property 1 of
## Q-SEAL v0.1 section 16: the fixed-length TBS-V1 transcript serializer is bijective and injective,
## i.e. no transcript-level malleability. Model + proof in qseal/.
qseal-tbs:
	@echo ">> cryptol + z3: Q-SEAL TBS-V1 transcript is bijective and injective (no transcript malleability)"
	./qseal/verify_tbs.sh

## SAW: the C reference TBS-V1 (de)serializer (qseal/ref/) equals the Cryptol model, so it places
## every field at its FIPS-spec offset. Needs clang + saw on PATH (.tools/bin).
qseal-ref:
	@echo ">> SAW: C reference TBS-V1 (de)serializer == Cryptol model (bijective); fields at spec offsets"
	./qseal/verify_ref.sh

## Build the technical writeup (placeholder — wire up your renderer of choice)
writeup:
	@echo "See docs/writeup/verifying-third-party-pqc-with-saw-and-isabelle.md"

clean:
	rm -rf build output heaps browser_info *.saw-cache saw-out
