# Roadmap

The whole strategy is **depth, scoped tight**. One finished proof beats three half-built ones.

## v1 — the Montgomery-reduction primitive (DONE) + the reduce.c layer
- Delivered: `montgomery_reduce` in **PQClean's reference ML-DSA C**, proven end-to-end
  (C ≡ Cryptol via SAW; model ≡ independent FIPS-derived spec via Isabelle). `make verify` green.
- NB: `montgomery_reduce` is an *implementation device* the FIPS-204 NTT relies on (Montgomery
  reduction is not itself specified in FIPS 204) — not a "FIPS-numbered sub-algorithm". It is also
  parameter-set-independent (valid for ML-DSA-44/65/87) and the least bug-prone function in the stack.
  **This is a pipeline warm-up on third-party reference C, not an ML-DSA assurance milestone.**
- Rounding out the layer (DONE): both legs for `reduce32`, `caddq`, `freeze` (same translation unit) —
  SAW C ≡ Cryptol AND Isabelle model ≡ spec, no holes. `caddq`'s `(a>>31)&Q` is the branch-free
  signedness exercise `montgomery_reduce` isn't; `reduce32`'s Barrett output bound is a floor-division
  interval proof (and surfaced OF-2, a doc-comment off-by-one on its low end). `freeze` is compositional.
- Hard gate (composition soundness): `make lift-check` mechanizes the `cryptol-to-isabelle` step —
  regenerate the Isabelle model from the `.cry` SAW checks and diff against the committed theory, so
  the end-to-end chain has no eyeball-maintained link.
- Forward NTT C-to-model fidelity (DONE): SAW proves `ntt(a[256])` ≡ Cryptol `ntt` under
  two's-complement wrapping (`-fwrapv` bitcode), montgomery_reduce as an uninterpreted override.
  This is C ≡ Cryptol model, NOT C ≡ FIPS-204 transform, and it does NOT prove overflow-freedom.
  (FIPS functional correctness of the forward NTT is Tier 2 / v1.5, in progress.)

## v1.5 — forward NTT overflow-freedom + an Isabelle NTT spec
- The remaining, *cryptographically meaningful* part: prove every `montgomery_reduce` input stays in
  range and no intermediate overflows `int32` across all 256 coefficients / 8 levels — i.e. the
  **coefficient-bound composition** invariant (this is what the `-fwrapv` functional-equivalence proof
  deliberately sidesteps). Needs a montgomery_reduce output-bound (|t| < Q) carried through the
  butterflies under an input bound.
- This is the actual historical ML-DSA bug class (cf. ePrint 2026/1032's optimized-path overflow that
  survived KATs; Apple's missing-reduction InvNTT bug). It also needs an Isabelle FIPS-204 NTT spec
  (negacyclic, 8-level) validated against FIPS 204 Algorithms 41–42 — itself a substantial formalization.
- **Overflow-freedom: DONE in Isabelle (2026-06-11).** Theorem `ntt_overflow_free`
  (`spec/isabelle/Assay_Equivalence.thy`, no holes, `make verify` exits 0): for inputs within
  `+/-(2^31 - 2^27)`, the lifted model NTT keeps every coefficient within `+/-2080309256 < 2^31 - 1`
  through all 8 levels. The per-butterfly bounds (`sint_add/sub_inrange`, `butterfly_node_*_bound`)
  establish that **every int32 add/sub stays in range (no overflow)** and that every
  `montgomery_reduce` input stays in its (half-open) precondition — the **coefficient-bound
  composition** invariant the `-fwrapv` proof sidesteps. Done by induction over the 8 levels (one
  lemma `nttLevel_bounded`: a level grows `|coeff|` by `<= Q`, the montgomery output bound), NOT by
  SAW unrolling. Key device: a *total* invariant over all indices (OOB falls back to the last
  element, so we never reason about modular index bounds). The brute-force SAW attempt
  (~3000 obligations, did not complete) is preserved on branch `v1.5-saw-overflow-wip`.
- **C-side bridge (argued, not separately mechanized):** the SAW `-fwrapv` proof gives C ≡ model for
  all inputs; the Isabelle result shows the model does not wrap under the bound; the two bitcodes
  differ only in nsw poison, absent when no overflow occurs — so the reference C NTT is overflow-free
  (no signed-overflow UB) and equals the spec under the bound. Mechanizing this last bridge in SAW is
  what proved impractical; it is a standard, sound meta-level argument.
- **Forward-NTT FIPS functional correctness: DONE (2026-06-22), not yet CI-gated.** Theorem
  `fwd_ntt_correct` (`spec/isabelle/tier2/work/Negacyclic_Bridge.thy`, session `Tier2`, no `sorry`/`oops`,
  build exits 0): for `bounded w` and `k < 256`,
  `cf (nttFwdAllRef w) k = (sum j<256. cf w j * 1753^((2*brv8 k + 1)*j)) mod 8380417` — the lifted
  forward NTT computes the FIPS-204 negacyclic DFT coefficient at bit-reversed output index `brv8 k`.
  Stated about the SAW-anchored lifted model. Built from `fwd_as_bfly` (word seam) + the closed-form
  stage invariant `inv_form` (lower/upper recursion) + induction `applyN_inv`; self-contained, does not
  use the AFP recursive-FFT theorem. Next: wire `Tier2` into `make verify` / CI (currently ungated; the
  proof-hole grep excludes `tier2`).
- **Still open:** the *inverse* NTT == FIPS-204 Algorithm 42 and the `256^-1` normalization (the AFP
  `IFNTT_correct` / round-trip lemmas are available to reuse); a forward+inverse round-trip in Isabelle.

## v2 — verify a used-but-unverified implementation
**Target chosen by survey (2026-06-11): the RustCrypto `ml-dsa` crate.** Rationale over the earlier
`mldsa-native` plan: `mldsa-native` is a verification flagship (CBMC for the C, HOL-Light/s2n-bignum
for the asm, even an `isabelle/` proof dir), so re-doing it with SAW is redundant and finds nothing.
The RustCrypto `ml-dsa` crate is the opposite: the de-facto Rust ML-DSA crate (large supply-chain
reach), **explicitly never independently audited** (its own docs say so for all RustCrypto PQC), and
with a **history of advisories in non-trivial paths** — a timing side-channel in `decompose`
(RUSTSEC-2025-0144) and a correctness issue where verification accepted duplicate hint indices because a
`<` became `<=`, violating FIPS 204 (GHSA-5x2r-hc65-25f9). That last one is exactly the spec-conformance
class a verify-against-FIPS-204 pipeline checks, and it slipped in via a one-character change — evidence
the arithmetic is subtle enough to warrant independent machine-checking. SAW reaches Rust via `mir-json`
+ `crucible-mir` (maintained, schema v11). Any issue is handled by coordinated disclosure through
RustCrypto's RUSTSEC/GHSA process (per CLAUDE.md: recorded privately, human-routed, never auto-filed).

Crate layout maps to targets (highest-risk first):
- `hint.rs` (hint encode/decode/use-hint — home of the duplicate-index bug), `verifying.rs`
  (norm + hint checks), `algebra.rs` + `ntt.rs` (the arithmetic, analogous to our v1 work),
  `signing.rs` (`decompose`, home of the timing bug), `sampling.rs`, `encode.rs`.

Phased (multi-month):
- **v2.0 — toolchain spike.** Stand up SAW-Rust: pinned Rust nightly + build `mir-json` matching SAW
  1.5.1's schema (v11); get the crate's `algebra.rs`/`ntt.rs` core to MIR and a first trivial
  `mir_verify`. De-risks the whole effort; this is the gating unknown.
- **v2.1 — spec-conformance of the hint/verify logic.** Model FIPS 204's hint rules (strictly
  increasing indices, `MakeHint`/`UseHint`) and prove `hint.rs`/`verifying.rs` conform. This is where
  a defect of the GHSA genre would surface.
- **v2.2 — arithmetic.** `algebra.rs`/`ntt.rs` reduce + NTT: functional correctness against a Cryptol
  model, plus the overflow/coefficient-bound reasoning (reuse the v1.5 Isabelle machinery; Rust
  release-mode arithmetic wraps, so overflow bugs are possible).
- **Outcomes, honestly:** any issue is routed through coordinated disclosure (RUSTSEC/GHSA); a clean
  result is an independent formal-verification record for the de-facto Rust ML-DSA crate. **Risk:**
  SAW-Rust is more experimental than SAW-C, and RustCrypto's generics/traits can be awkward for MIR;
  budget for tooling friction. Fallback target if Rust fights us: wolfSSL `wolfcrypt/src/dilithium.c`
  (own implementation, deployed in wolfBoot, C = best SAW fit, not independently machine-verified).
- Note: the already heavily-verified targets (`mldsa-native`, Apple corecrypto, OpenSSL/BoringSSL/AWS-LC)
  add little from independent re-verification; v2 deliberately avoids them.

## v3 — constant-time / secret-independence (frontier)
- **Different tool, not this pipeline.** SAW≡Cryptol functional equivalence is not the CT tool; use
  ct-verif / SideTrail-style product programs, Binsec/Rel, or the Jasmin constant-time type system.
- **Different targets.** `montgomery_reduce` is already trivially CT (branch/division/table-free). The
  real CT risk is rejection sampling (`rej_eta`, `poly_uniform*`, challenge gen) and
  `decompose`/`make_hint`/`use_hint` — data-dependent control flow on secret-adjacent values.

## Non-goals (for now)
- Full end-to-end ML-DSA. Whole-algorithm correctness. Multiple implementations at once.

## Disclosure
- OF-1 (`montgomery_reduce` doc-comment strict-bound off-by-one at an endpoint) and OF-2 (`reduce32`
  doc-comment low-end bound `-6283008` reachably `-6283009` under its one-sided precondition) were
  **disclosed 2026-06-09 as pq-crystals/dilithium#114** (origin; PQClean is archiving; mldsa-native /
  liboqs are downstream). The AVX2 path has no `reduce.c`, so the comments don't repeat there. Both are
  doc/contract issues, not miscomputations. Next: await maintainer response, then offer a PR for their
  preferred phrasing.
