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

.PHONY: all verify target-identity bitcode saw isabelle tier2 tier2-inv barrett barrett-solver lift-check mutation-test qseal-tbs qseal-ref qseal-assert qseal-hybrid qseal-nonce qseal-validate qseal-evidence qseal-demo writeup clean

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

## Q-SEAL CREATE_ASSERTION (section 16 property 2): the applet builds TBS-V1 from the validated
## request, so the signed transcript binds the challenge and the host cannot spoof applet identity.
## cryptol binding properties + SAW C == model.
qseal-assert:
	@echo ">> cryptol + SAW: CREATE_ASSERTION binds the validated challenge (no host-spoofed transcript)"
	./qseal/verify_assertion.sh

## Q-SEAL HYB-1 hybrid acceptance (section 16 property 3): with the ECDSA/ML-DSA verifiers
## uninterpreted, SAW proves acceptance requires BOTH signatures over the same transcript, and the
## downgrade variant (accept on either) is caught. This is the "hybrid is not decorative" property.
qseal-hybrid:
	@echo ">> SAW: hybrid accept requires BOTH signatures over the same transcript; downgrade variant caught"
	./qseal/verify_hybrid.sh

## Q-SEAL single-use challenge store (section 16 property 4): a consumed request_id cannot be accepted
## twice. cryptol proves the model (no_replay etc.) and that a no-consume verifier is replayable; SAW
## proves the C reference nonce store equals the model. This is the first STATEFUL protocol property.
qseal-nonce:
	@echo ">> cryptol + SAW: single-use challenge store; a consumed request_id cannot be accepted twice; no-consume bug caught"
	./qseal/verify_nonce.sh

## Q-SEAL request validation (section 16 property 7): a malformed version/suite/type/origin fails
## before signing. cryptol proves the model (malformed_never_signs etc.); SAW proves the C validate
## + validate-then-sign path equals the model; a no-suite-check gate is caught.
qseal-validate:
	@echo ">> cryptol + SAW: a malformed request (bad version/suite/type/origin) fails before signing; no-suite-check bug caught"
	./qseal/verify_validate.sh

## Q-SEAL evidence-fragment reassembly (section 16 property 6): reassembly produces exactly the
## original evidence bytes or fails closed. cryptol proves the round trip + fail-closed on a dropped or
## mis-sized fragment; SAW proves the C reassembler equals the model; a no-completeness reassembler is
## caught.
qseal-evidence:
	@echo ">> cryptol + SAW: evidence-fragment reassembly round-trips or fails closed; no-completeness bug caught"
	./qseal/verify_evidence.sh

## Runnable demo: real ECDSA P-256 + ML-DSA-44 over the verified TBS-V1 transcript. Needs cargo, no
## proof toolchain. Valid accepts; tampered and downgrade attestations reject.
qseal-demo:
	@echo ">> Q-SEAL hybrid attestation demo (valid accepts; tampered + downgrade reject)"
	cd qseal/demo && cargo run --quiet

## The writeups: the NTT/SAW/Isabelle technical piece, and the Q-SEAL eSIM-attestation post
## (docs/writeup/verified-esim-attestation.{md,html}; the .html is self-contained for GitHub Pages).
writeup:
	@echo "docs/writeup/verifying-third-party-pqc-with-saw-and-isabelle.md  (NTT primitive, technical)"
	@echo "docs/writeup/verified-esim-attestation.md  (Q-SEAL eSIM post; .html is the servable page)"

clean:
	rm -rf build output heaps browser_info *.saw-cache saw-out
