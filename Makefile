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

.PHONY: claim-lint qseal-evidence-scale all verify target-identity bitcode saw isabelle tier2 tier2-inv tier2-signed tier2-invsigned barrett barrett-solver lift-check mutation-test mlkem-reduce mlkem-ntt mlkem-isabelle qseal-tbs qseal-ref qseal-assert qseal-hybrid qseal-nonce qseal-validate qseal-evidence qseal-mutants qseal-reachability cve-anchor qseal-demo writeup clean

all: verify

## Full pipeline: target bytes pinned (target-identity) → lift in sync (lift-check) → C ≡ Cryptol
## (SAW) → reduce.c model ≡ FIPS spec (Isabelle) → forward-NTT model ≡ FIPS-204 transform (Isabelle,
## Tier2) → inverse-NTT model ≡ FIPS-204 inverse transform (Isabelle, Tier2_InvWork) → ML-KEM
## forward-NTT model ≡ FIPS-203 residue transform (Isabelle, Kem_Work). The ML-KEM C ≡ Cryptol legs
## (mlkem-reduce, mlkem-ntt) gate separately on every push in saw.yml.
verify: target-identity lift-check saw isabelle tier2 tier2-inv tier2-signed tier2-invsigned barrett mlkem-isabelle
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

## ML-KEM go-wide slice 1: the ML-KEM-512 reduce layer, C == Cryptol (bit-exact) plus the
## math-level Montgomery/Barrett correctness by direct z3 at 16-bit widths, with result+1
## non-vacuity mutants. See docs/ROADMAP.md (Tier A) and target/README.md (ML-KEM target).
mlkem-reduce:
	@mkdir -p build
	CLANG=$(CLANG) ./scripts/build_bitcode.sh target/pqclean-mlkem build/mlkem_ntt.bc
	@echo ">> SAW: ML-KEM-512 reduce layer == Cryptol model + math correctness (16-bit, direct SMT)"
	$(SAW) proof/saw/mlkem_reduce.saw

## ML-KEM-512 forward + inverse NTT: C ntt()/invntt() == Cryptol model (7 Cooley-Tukey /
## Gentleman-Sande levels, -fwrapv bitcode, montgomery_reduce + barrett_reduce uninterpreted
## overrides). Uses SBV unint_z3: the what4 w4_unint_z3 backend does not terminate on the forward
## goal within 9 min, the reverse of the reduce-layer solver behaviour. Both directions carry
## inline result(+1) non-vacuity mutants.
mlkem-ntt:
	@mkdir -p build
	CLANG=$(CLANG) ./scripts/build_bitcode.sh target/pqclean-mlkem build/mlkem_ntt.bc
	@echo ">> SAW: ML-KEM-512 forward + inverse NTT == Cryptol model (wrapv, SBV unint_z3)"
	$(SAW) proof/saw/mlkem_ntt.saw

## ML-KEM-512 Isabelle: lifted forward NTT model ≡ FIPS-203 degree-2 residue transform. Builds
## Kem_Work, which pulls its parent Kem_Base (AFP Number_Theoretic_Transform + SAW Cryptol) first.
## Kem_Base = brick (a) montgomery_reduce_correct_kem. Kem_Work = brick (b) 7-level CT routing +
## brick (c) ntt_residue (ntt output k == the FIPS-203 residue coeff of f mod (X^2 - 17^(2*brv7 i+1))).
## Kem_Work is a leaf checking-session (no persisted heap), so it re-checks whenever its content
## changes. The no-sorry/oops/admit grep in verify.yml already covers spec/isabelle/kem.
mlkem-isabelle:
	@echo ">> Isabelle (Kem_Work): ML-KEM forward NTT model ≡ FIPS-203 residue spec (bricks a/b/c)"
	$(ISABELLE) build -d spec/isabelle/kem -v Kem_Work

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

## Tier2_Signed Isabelle session: the forward transform theorem on the SIGNED centered window
## (ntt_signed_correct) — ntt_bridge extended from the non-negative [0,Q) input window to
## |coeff| < Q (ntt_bounded 8380416 w), the inputs the deployed reference forward NTT receives.
## Child of Tier2; reuses mbfly0..7 / nttLevel_bounded / applyN_inv without reproving the chain.
tier2-signed:
	@echo ">> Isabelle (Tier2_Signed): forward NTT ≡ FIPS-204 transform on the signed |coeff| < Q window"
	$(ISABELLE) build -d spec/isabelle -d spec/isabelle/tier2 -v Tier2_Signed

## Tier2_InvSigned Isabelle session: the inverse transform theorem on the SIGNED centered window
## (invntt_signed_correct) — invntt_bridge extended from [0,Q) to |coeff| < Q (ntt_bounded 8380416 w),
## the centered inputs invntt_tomont's call site receives. Child of Tier2_InvWork; reuses
## mbfly_inv0..7 / invlevelN_bounded / applyG_inv / the invf-scale helpers.
tier2-invsigned:
	@echo ">> Isabelle (Tier2_InvSigned): inverse NTT ≡ FIPS-204 inverse transform on the signed |coeff| < Q window"
	$(ISABELLE) build -d spec/isabelle -d spec/isabelle/tier2 -v Tier2_InvSigned

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

## Forward NTT on the DEFAULT (nsw) bitcode: overflow-free AND == model under the
## +/-(2^31-2^27) input window, discharging the forward -fwrapv => no-UB meta-step as a theorem.
## ~12.5 h wall (bitwuzla per ~3000 unrolled side conditions); out of band, never in CI/make saw.
ntt-nsw:
	@echo ">> SAW + bitwuzla: forward ntt on the nsw bitcode, overflow-free + == model (~12.5 h)"
	PATH="$(TOOLS_BIN):$$PATH" $(SAW) proof/saw/ntt_nsw.saw

## Q-SEAL protocol property (independent of the ML-DSA primitive). Fast (<1s). Property 1 of
## Q-SEAL v0.1 section 16: the fixed-length TBS-V1 transcript serializer is bijective and injective,
## i.e. no transcript-level malleability. Model + proof in qseal/.
qseal-tbs:
	@echo ">> cryptol + z3: Q-SEAL TBS-V1 + TBS-V2 transcripts bijective/injective; V2 pair commitment signed (no transcript malleability)"
	./qseal/verify_tbs.sh

## SAW: the C reference TBS-V1 and TBS-V2 (de)serializers (qseal/ref/) each equal their Cryptol
## model, so every field sits at its spec offset (V2 includes the signed pair_commitment). Needs
## clang + saw on PATH (.tools/bin).
qseal-ref:
	@echo ">> SAW: C reference TBS-V1 + TBS-V2 (de)serializers == Cryptol models (bijective); fields at spec offsets"
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
## qseal-evidence-scale: the same evidence reference at a larger fragment arity than the readable 4x32
## instance. EVIDENCE_SCALE=<frag-size>x<num-frags>, default 255x4 (1020 bytes). Cost is quadratic in
## the fragment count, so this is a separate target rather than part of the push check.
qseal-evidence-scale:
	@EVIDENCE_SCALE=$${EVIDENCE_SCALE:-255x4} ./qseal/verify_evidence.sh

qseal-evidence:
	@echo ">> cryptol + SAW: evidence-fragment reassembly round-trips or fails closed; no-completeness bug caught"
	./qseal/verify_evidence.sh

## Q-SEAL reachability (section 16 property 5): PROFILE_ACTION_OBSERVED (type 0x04) cannot be reached
## through a host-exposed APDU path. Checked in ProVerif (symbolic model), since this is reachability
## over the command surface, not a fixed-format identity. Needs proverif (opam switch or .tools/bin).
qseal-reachability:
	@echo ">> ProVerif: OBSERVED assertion reachable only via the internal callback; host-path mutant refuted"
	./qseal/verify_reachability.sh

## CVE-2026-24850 anchor: FIPS 204 hint-decode canonicity. The rule is FIPS 204's (external referent),
## the caught defect is the exact GHSA-5x2r-hc65-25f9 bug (`<=` for strict `<`, accepting a repeated
## index). cryptol shows the CVE decoder accepts a non-canonical hint; SAW proves the C reference
## canonical predicate == the model and the `<=` variant is rejected.
cve-anchor:
	@echo ">> cryptol + SAW: FIPS 204 hint canonicity; the CVE-2026-24850 (<= for <) variant is caught"
	./cve-anchor/verify.sh

## Mutation-adequacy report for the Q-SEAL C references: apply relational/logical operator mutations
## claim-lint: the mechanical half of the pre-submission review checklist. Catches
## the defect classes that had to be found by hand once already: a SAW proof with no non-vacuity guard, a
## ProVerif model whose events cannot fire, an assumed spec nobody justified, a comment citing a path
## that does not exist. Fast, no toolchain needed, so it belongs in every push check.
claim-lint:
	@./scripts/claim-lint.sh

## one at a time and rerun the matching SAW proof, measuring how many mutants the proofs kill. Slower
## (~1 min, rebuilds + reruns SAW per mutant); a report, not a gate, so it is not in the saw.yml push
## check. Runs on a copy; tracked files are untouched.
qseal-mutants:
	@echo ">> mutation-adequacy: operator mutants of the C references vs the SAW proofs (kill ratio)"
	python3 qseal/mutation/mutate.py

## Runnable demo: real ECDSA P-256 + ML-DSA-44 over the verified TBS-V1 transcript. Needs cargo, no
## proof toolchain. Valid accepts; tampered and downgrade attestations reject.
qseal-demo:
	@echo ">> Q-SEAL hybrid attestation demo (valid accepts; tampered + downgrade reject)"
	cd qseal/demo && cargo run --quiet

## Cap-V1 capability layer (Rust verifier, Kani proof). The fixed-format agent-delegation TBS
## serializer is a bijection and injective (no token-level malleability), proved with Kani/CBMC over
## the full 191-byte buffer. Needs cargo + kani on PATH. Model + proof in cap/, spec in docs/cap/.
cap-kani:
	@echo ">> Kani: Cap-V1 format bijection + delegation attenuation + accept gates + signature/key binding + single-use + revocation"
	./cap/verify_cap.sh

## Cap-V1 real hybrid crypto: run actual ECDSA P-256 + ML-DSA-44 over serialize(cap), driving the
## verified accept_chain2_signed. Valid accepts; tampered, downgrade, confused-deputy (valid sig wrong
## key), and expired all reject. Needs cargo; no proof toolchain. This is the "PQ actually runs" check.
cap-hybrid:
	@echo ">> Cap-V1 hybrid crypto: real ECDSA + ML-DSA-44 over serialize(cap); valid accepts, tamper/downgrade/confused-deputy/expired reject; plus the key-id KAT"
	cd cap && cargo test --features hyb1-keyid --quiet

## Cap-V1 runnable demo: an orchestrator->agent->worker delegation chain with real hybrid crypto,
## every accept/reject decided by the Kani-verified accept_chain_full. Self-checks, exits nonzero
## on any wrong verdict. Needs cargo only.
cap-demo:
	@echo ">> Cap-V1 demo: delegation chain accepts; replay/tamper/escalation/confused-deputy/downgrade/terminal-redelegation/revoked reject"
	cd cap/demo && cargo run --quiet

## The writeups: the NTT/SAW/Isabelle technical piece, and the Q-SEAL eSIM-attestation post
## (docs/writeup/verified-esim-attestation.{md,html}; the .html is self-contained for GitHub Pages).
writeup:
	@echo "docs/writeup/verifying-third-party-pqc-with-saw-and-isabelle.md  (NTT primitive, technical)"
	@echo "docs/writeup/verified-esim-attestation.md  (Q-SEAL eSIM post; .html is the servable page)"

clean:
	rm -rf build output heaps browser_info *.saw-cache saw-out
