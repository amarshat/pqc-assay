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
- **Inverse NTT (fork 1): in progress.** See the fork-1 section below.

## fork 1 — complete the NTT (inverse NTT, then the -fwrapv seam)
Goal: extend the forward result to the **inverse** NTT (`invntt_tomont` = `mont * NTT^-1`,
folding the `256^-1` normalization), so the published chain covers forward **and** inverse rather
than the forward half only. Pieces, in order:
1. **Cryptol inverse model (DONE).** `invntt`/`invnttLevel`/`invf=41978` added to
   `model/cryptol/MLDSA_NTT.cry` (Gentleman-Sande, 8 levels, final `montgomery_reduce(invf*b)`).
   Round-trip `invntt(ntt(x)) = mont*x mod q` validated in Cryptol.
2. **SAW C ≡ Cryptol (DONE).** `proof/saw/mldsa_ntt.saw` proves the C `invntt_tomont` ≡ Cryptol
   `invntt` (mirror of the forward proof; `make saw` exits 0).
3. **Lift (DONE).** `cryptol-to-isabelle` regenerated; `make lift-check` green.
4. **Isabelle `invntt_bridge` (DONE).** montgomery `invntt` model ≡ FIPS-204 inverse transform mod q,
   the inverse mirror of `ntt_bridge`. `spec/isabelle/tier2/invwork/Inv_Mont_Bridge.thy`, session
   `Tier2_InvWork` (exit 0, no `sorry`/`oops`). Route A (self-contained closed form, no AFP locale):
   - montgomery `invntt` ≡ normal `nttInvAllRef` mod q + the `invf = mont²/256` scale
     (`Rcong_invcore` + `invntt_scale_bridge`);
   - normal `nttInvAllRef` ≡ the FIPS-204 inverse negacyclic DFT (`inv_ntt_correct`), via the
     Gentleman-Sande mirror of the forward closed form: `inv_as_bfly` (word seam) + `ginv_form`
     stage invariant + `ginv_lower`/`ginv_upper` recursion + `applyG_inv` induction, with the
     per-layer twiddle `gtwid_lo`/`gtwid_hi` reduced to the normal table via the bit-reversal
     identity `gz_brv`;
   - composed into `invntt_bridge`. Wired into `make verify` (`tier2-inv` target); the no-`sorry`
     CI grep already covers `spec/`. README claim table + `docs/ASSUMPTIONS.md` updated.
   - (Sub-step 1, `Tier2_Inv`/`Negacyclic_Inv.thy`, the AFP-locale negacyclic invertibility, was the
     route-B prerequisite; route A does not use it, so it is now optional/unused on the main chain.)
5. **Inverse overflow-freedom (DONE) + the `-fwrapv` no-UB seam (argued, as for the forward).** The
   Gentleman-Sande low legs are unreduced so a coefficient doubles each layer; under the input
   precondition `|coeff| < Q` (`bounded`, `B_0 = 8380416`) the eight layers stay within
   `2^8·B_0 = 2145386496 < 2^31` and the final scale reduces to `< Q`. Proven as `invntt_overflow_free`
   (`Tier2_InvWork`, exit 0; the analog of forward `ntt_overflow_free`), composing the per-layer
   doubling bounds (`invcore_bounded`, built on `gs_node_low_bound`/`gs_node_high_bound`, which encode
   the int32 no-overflow) with the final `montgomery_reduce(invf·.)` scale. The `|coeff| < Q` window is
   tight (`256·Q` would overflow) but matches the reduced inputs `invntt_tomont` is fed. Remaining: the
   `-fwrapv` ⇒ no-signed-overflow-UB bridge to the C is the SAME scoped/argued meta-step as the forward
   (not separately mechanized).

The forward+inverse chain is now the **complete-NTT** publication anchor (it closes the "no inverse /
one argued link" gap that drew the ePrint rejections); both directions are functional-correct AND
overflow-free in Isabelle, with the single argued `-fwrapv` ⇒ no-UB link shared by both.

6. **Forward functional theorem lifted to the signed centered window (DONE, 2026-08-01).**
   `ntt_signed_correct` (`spec/isabelle/tier2/signwork/Signed_Bridge.thy`, session `Tier2_Signed`, no
   sorry/oops/smt, in-session verified, gated in `make verify` via `tier2-signed`) extends the functional
   forward bridge from the non-negative `[0,Q)` input window (`ntt_bridge`) to the signed centered window
   `|coeff| < Q` (`ntt_bounded 8380416 w`), the inputs the deployed forward NTT actually receives
   (keygen/sign feed negative `s1`/`s2` coefficients). This closes the forward half of the `[0,Q)`
   functional restriction: on deployed centered inputs the forward now has BOTH overflow-freedom and
   functional model-to-spec equality. Cheap (~200 lines) because the abstract closed form `applyN_inv`
   needs no non-negativity and `mbfly0..7` are already on the signed view, so the fix was swapping
   `ntt_bridge`'s non-negative Rcong base for a reflexive one.

7. **Inverse functional theorem lifted to the signed centered window (DONE, 2026-08-02).**
   `invntt_signed_correct` (`spec/isabelle/tier2/invsignwork/Inv_Signed_Bridge.thy`, session
   `Tier2_InvSigned`, no sorry/oops/smt, in-session verified, gated in `make verify` via
   `tier2-invsigned`) is the inverse mirror: it lifts `invntt_bridge` from `[0,Q)` to the signed
   `|coeff| < Q` window (`ntt_bounded 8380416 w`) the same way. `invntt_scale_bridge` split into a
   sign-agnostic scale part (`invntt_scale_coeff` + `invf_scale_cong`) and one `[0,Q)`-locked step
   (`Rcong_invcore`); only the locked step was replaced, by the abstract route
   (`sf(invnttCore w) ≡ invBfly(sf w) mod q` via `mbfly_inv0..7` + reflexive base, then the abstract
   `applyG_inv`). So **both NTT directions are now functional-correct on the signed centered window the
   deployed code uses** (overflow-freedom was already there for both). This was the last remaining
   `[0,Q)` functional restriction in the whole NTT chain.

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
+ `crucible-mir` (maintained; the SAW 1.5.1 bundle is schema v8). Any issue is handled by coordinated disclosure through
RustCrypto's RUSTSEC/GHSA process (per CLAUDE.md: recorded privately, human-routed, never auto-filed).

Crate layout maps to targets (highest-risk first):
- `hint.rs` (hint encode/decode/use-hint — home of the duplicate-index bug), `verifying.rs`
  (norm + hint checks), `algebra.rs` + `ntt.rs` (the arithmetic, analogous to our v1 work),
  `signing.rs` (`decompose`, home of the timing bug), `sampling.rs`, `encode.rs`.

Phased (multi-month):
- **v2.0 — toolchain spike.** Stand up SAW-Rust: pinned Rust nightly + build `mir-json` matching SAW
  1.5.1's schema (v8); get the crate's `algebra.rs`/`ntt.rs` core to MIR and a first trivial
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

## Next targets after fork 1 (shortlist)
A 2026-06 deep-research scan ranked 20 production crypto libraries (secp256k1, rustls-webpki, OpenSSL,
rust-lightning, openCryptoki, tpm2-tss, liboqs, wolfSSL, NSS, Mbed TLS, ...). That list ranks by
deployment / "payment fit" / defect odds. It underweights the one filter that decides feasibility here:
**toolchain fit.** SAW → Cryptol → Isabelle is an *arithmetic-equivalence* tool. It is strong on
bit-exact modular arithmetic (what we proved for ML-DSA) and weak on DER/ASN.1 parsing, stateful
protocol machines, and cert path-validation — where fuzzing/CBMC/Frama-C are the cheaper fit. Filtering
the 20 to "where this exact pipeline has an edge" collapses it to a handful:

- **Tier A (leverage — do first, builds on what exists):** finish the ML-DSA *arithmetic* story beyond
  the NTT (decompose/rounding/packing; partly touched in the v2 Rust audit), or cross to **ML-KEM**
  arithmetic (reduce + NTT). Reuses the Cryptol specs, the wired toolchain, and the v1.5 bound machinery.
  Strongest *paper* ("complete verified ML-DSA arithmetic", not "a 4th unrelated thing") and lowest
  start-up cost. Recommended next, after fork 1 lands and one artifact is published.

  **STARTED 2026-07-14: the ML-KEM cross.** The sequencing gate is met (fork 1 landed:
  `invntt_bridge` mechanized; artifacts published: Zenodo preprint + the Q-SEAL paper under review).
  Target vendored at the same PQClean pin into `target/pqclean-mlkem/` (see `target/README.md`).
  Scope, deliberately one slice: the ML-KEM-512 `clean` reduce layer + forward NTT, C ≡ Cryptol in
  SAW first (16-bit reductions, expected below the SMT wall — itself a boundary datum for paper-1),
  then FIPS 203 transform correctness in Isabelle by reusing the Tier-2 stage-invariant machinery
  (ML-KEM's 7-layer NTT is the same induction stopped one level early, at degree-2 blocks). Not in
  `make verify` until the first proof lands.

  Slice 1 DONE (2026-07-14): reduce layer, `make mlkem-reduce`.
  Slice 2 DONE (2026-07-16): forward NTT C ≡ Cryptol. `make mlkem-ntt` proves
  `PQCLEAN_MLKEM512_CLEAN_ntt(a[256])` ≡ Cryptol `ntt` (7 Cooley-Tukey levels), on the -fwrapv
  bitcode with montgomery_reduce as an uninterpreted override, ~3.5 s, in `saw.yml`. Two solver
  datums for the paper: (a) the equality discharges under SBV `unint_z3` but the what4 `w4_unint_z3`
  backend does not terminate within 9 min on it, the reverse of the reduce layer where z3 worked and
  cvc5 stalled; (b) unlike ML-DSA, the int16 butterfly cannot overflow int, so the C is UB-free with
  no coefficient bound, but the ~2700 nsw side conditions on the default bitcode do not discharge as
  one monolithic goal (either backend), so -fwrapv is still used for the equivalence (see
  ASSUMPTIONS).

  Slice 3 STARTED (2026-07-16): FIPS 203 forward-transform correctness in Isabelle. Foundation
  landed (`spec/isabelle/kem/`, session `Kem_Base` builds green, 0 sorry): the forward model
  `model/cryptol/MLKEM_NTT.cry` lifts via cryptol-to-isabelle to `MLKEM_NTT.thy` on the AFP
  `Number_Theoretic_Transform` + `Cryptol` base. The math differs from the ML-DSA Tier-2: mod 3329
  has a 256th root of unity but no 512th, so X^256+1 splits only into 128 degree-2 factors. The
  target theorem is the INCOMPLETE transform: for i<128, the output pair (f_hat[2i], f_hat[2i+1]) is
  the residue of f mod (X^2 - zeta^(2*brv7(i)+1)), i.e. f_hat[2i] = sum_j f[2j]*g^j and
  f_hat[2i+1] = sum_j f[2j+1]*g^j mod q with g = zeta^(2*brv7(i)+1), zeta=17. Remaining bricks
  (multi-session, mirrors the ML-DSA Tier-2 shape): (a) a normal-domain reference twin of the model
  + a montgomery bridge (the zetas table and fqmul are montgomery-domain, as in ML-DSA Mont_Bridge);
  (b) the 7-layer Cooley-Tukey routing == the even/odd length-128 sub-transforms (the incomplete-split
  analogue of the ML-DSA CT_Routing/Negacyclic_Bridge, NOT a direct reuse); (c) the degree-2 residue
  characterization as the spec, chained onto AFP length-128 NTT facts. All three bricks have since
  landed hole-free; Kem_Work is now gated in `make verify` (see the 2026-07-23 progress entry below).
  Progress (2026-07-17): brick (a) COMPLETE. `Kyber_Mont.thy` (Kem_Base builds green, 0 sorry),
  theorem `montgomery_reduce_correct_kem`: for -2^15*q <= sint_seq a < 2^15*q, the lifted ML-KEM
  `montgomery_reduce` satisfies 2^16 * sint_seq(result) == sint_seq a (mod q=3329) and strict
  -q < result < q. Full chain, mirroring ML-DSA end to end: `mont_core_kem` (integer core:
  T==A*QINV(mod 2^16) + int16/range bounds => r=(A-T*q)div 2^16 correct) -> `red_value_kem` +
  `tcong_kem` (word layer, QINV = -3327 = 62209 mod 2^16, no int32 overflow) -> `bval_kem` +
  `probe_sext32` (seq->word lowering of the lifted def) -> assembled. Stated over sint_seq (the
  signed reading of the bits SAW checks C against), as the ML-DSA montgomery_reduce_correct;
  the model's si16/si32-wrapped mont_correct predicate is the same value, linking si16==sint_seq
  is a deferred cosmetic bridge (not a correctness gap).
  Progress (2026-07-18): brick (b) routing seams landed (Kem_Work session, `work/Kyber_Route.thy`,
  builds green on the Kem_Base heap, 0 sorry). Three reusable facts the 7-level routing consumes:
  `ntt_unfold` (the model foldl over level indices 0..6 == the explicit 7-fold nttLevel
  composition, via foldl_seq.rep_eq); `sint_add16`/`sint_sub16` (int16 +/- compute integer +/-
  when the true result stays in [-2^15, 2^15), the no-overflow seam for the butterfly's
  unreduced adds); `butterfly_law_kem` (packages the foundation lemmas: for any table index k and
  coeff |x| <= B <= 32767, fqmul zetas[k] x is a correct normal-domain product, -q < it < q and
  2^16*it == zetas[k]*x mod q). This mirrors Bridge_Word's op_add/red_mul/red_sub seams, which
  landed before the full per-layer laws. Next: the per-level coefficient laws (nttLevel i output
  == abstract butterfly on sint coeffs), the ML-KEM analogue of layer1_coeff. Level 0 (len=128,
  twolen=256, base=1, twiddle zetas[1]) matches ML-DSA layer1; needs the [16]-word index unfold
  (map_seq_nth on seq_compr + word-indexed @ access, m mod 256 < 128 test, m+/-128), then chain
  the 7 levels with a magnitude-bound invariant (|coeff| grows <= q per level, stays < 2^15).
  Then brick (c) degree-2 residue spec.
  Progress (2026-07-19): index helpers for the per-level unfold landed (Kem_Work green, 0 sorry):
  `to_nat_from_nat16`/`pos_nat_from_nat16` recover the nat index from the [16] word for the model's
  `a @ m = nth_seq a (pos_nat m)` access, the ML-KEM analogue of ML-DSA `idx_val` at 16-bit width
  (same word_seq_convs + unat_of_nat route, minus the zext). Next: the remaining index helpers
  (div 256 = 0 for the twiddle index, the `m mod 256 < 128` half-test, `pos_nat (m +/- 128)`), then
  assemble level0_lo/hi (nttLevel 0 access == a[n] +/- fqmul(zetas[1], a[n+/-128])) as one apply-script
  mirroring Bridge_Word.layer1_lo/hi.
  Progress (2026-07-19, cont.): level-0 coefficient law COMPLETE (Kem_Work green, 0 sorry). The full
  index-helper set landed (to_nat_plus128/minus128, to_nat_zidx_lo0/hi0, half_test0, all via the
  word_seq_convs + unat route), then `level0_lo`/`level0_hi` assembled and combined into
  `level0_coeff`: for n<256, nttLevel 0 a at n = (n<128 ? a[n] + fqmul(zetas[1], a[n+128]) :
  a[n-128] - fqmul(zetas[1], a[n])). Word-exact, the ML-KEM analogue of Bridge_Word.layer1_coeff.
  Next: levels 1..6 (same recipe, different len/twolen/base and twiddle index range: level i has
  len=128>>i, base=2^i, and the twiddle spans base..base+2^i-1, so the zetas index is no longer the
  constant 1), then chain via a magnitude-bound invariant into the sint recurrence. Then brick (c).
  Progress (2026-07-20): level-1 coefficient law LANDED (Kem_Work green, clean rebuild, 0 sorry).
  Both level-1 blockers cracked:
  (1) Shift reduction. The level constants are seq shifts (`len = 0x80 >> i`, `twolen = 0x100 >> i`,
  `base = 0x1 << i`) which the level-0 narrow simp did not evaluate for i>=1. The Cryptol backtick
  form `>>`{16,[16],Bit}` does not parse in a lemma prop, and the `right_shift_op` form does not
  match the goal (simp normalizes the shift amount `to_int (1::[16])` to `bl_to_bin(seq_to_list 1)`
  before the rewrite can fire). Fix: two-part, all `by eval`, fed into the SAME narrow first simp
  (no broad `cryptol_prim_defs`/`word_seq_convs`): `amt1: bl_to_bin (seq_to_list (1::[16])) = 1`
  collapses the normalized shift amount to the literal `1`, then `right_shift (0x80::[16]) 1 = 0x40`
  / `right_shift (0x100::[16]) 1 = 0x80` / `left_shift (0x1::[16]) 1 = 0x2` reduce the constants.
  For levels i=2..6 the analogue is `bl_to_bin (seq_to_list (i::[16])) = i` plus the three literal
  shift reductions at that i (values: len=128>>i, twolen=256>>i, base=2^i).
  (2) presburger hang avoided by construction: no `n+64<256` partner bound (both legs stay
  `nth_list`, match un-reduced), upper-leg twiddle stated literally as `2 + (n-64) div 128`.
  Landed: to_nat_plus64/minus64, to_nat_zidx1_lo/hi, half_test1, level1_lo/hi, level1_coeff (for
  n<256, nttLevel 1 a at n = n mod 128<64 ? a[n] + fqmul(zetas[2 + n div 128], a[n+64]) :
  a[n-64] - fqmul(zetas[2 + (n-64) div 128], a[n])). Next: levels 2..6 by the same recipe, then
  chain the 7 levels via the magnitude-bound invariant into the sint recurrence. Then brick (c).
  Progress (2026-07-20, cont.): levels 2..6 coefficient laws LANDED (Kem_Work green, 0 sorry), same
  recipe as level 1 with the per-i shift reductions (len=128>>i, twolen=256>>i, base=2^i) and the
  widening twiddle span (zetas index base..base+2^i-1). The 7 levels chain through a per-level
  magnitude-bound + congruence invariant (generic machinery: |coeff| grows <= q per level, stays
  < 2^15) into the sint recurrence `ntt_recurrence` (the montgomery model `ntt` at output k equals
  `applyNK 7 (sfk w) k` mod q on a reduced input). Brick (b) done.
  Progress (2026-07-22..23): brick (c) COMPLETE, and the whole ML-KEM forward chain is now CI-gated.
  `work/Kyber_Residue.thy` (session Kem_Work, 0 sorry/oops) proves the closed-form stage invariant
  (`inv_formK` lower/upper-leg recursion + `applyNK_inv` induction, twiddle bit-reversal reduction)
  and composes it with `ntt_recurrence` into the final theorem `ntt_residue`: for a reduced input
  (`boundedK 3328 w`) and k < 256,

      sint_seq (ntt w ! k) mod 3329
        = (SUM m<128. sfk w (k mod 2 + m*2) * 17^((2*brv7 (k div 2) + 1)*m)) mod 3329

  i.e. output position k = 2i+c is the even (c=0) / odd (c=1) coefficient of the FIPS-203 degree-2
  residue f mod (X^2 - 17^(2*brv7(i)+1)); `ntt` is the montgomery-domain model SAW checks the C
  against. That is the FIPS-203 forward NTT for Kyber's incomplete split. Verified in-session
  2026-07-23 (`isabelle build -d spec/isabelle/kem -v Kem_Work` -> `Finished Kem_Base` +
  `Finished Kem_Work`, exit 0; re-runs and fails on an injected false lemma, so the gate is not
  vacuous). Wired into `make verify` via the new `mlkem-isabelle` target (was excluded); the
  no-sorry grep in verify.yml already covers spec/isabelle/kem. The C == Cryptol legs (mlkem-reduce,
  mlkem-ntt) stay gated on every push in saw.yml. Also confirmed the brick-(a) "si16 == sint_seq
  deferred cosmetic bridge" is genuinely cosmetic, not a seam: the whole chain
  (montgomery_reduce_correct_kem, butterfly_law_kem, ntt_residue) is stated over sint_seq, the signed
  reading of the exact bits SAW checks; si16 is only an internal model alt-predicate of equal value.
  Scope, stated plainly: this is FORWARD NTT + reduce ONLY for ML-KEM. There is no ML-KEM inverse
  NTT (contrast ML-DSA, which has forward + inverse). Overflow-freedom needs no coefficient-bound
  induction here: the int16 butterfly cannot overflow int32, so the C is UB-free with no coefficient
  bound (see ASSUMPTIONS, ML-KEM forward NTT slice 2). The honest paper claim is "the method
  generalizes across two NIST standards, shown end-to-end on the forward transform + reduce for
  both," NOT "complete NTT for both." ML-KEM inverse NTT is future work.
- **Tier B (greenfield, deliberate new domain):** **bitcoin-core/secp256k1 field reduction** (the
  5×52 / 10×26 limb reduce — same shape as our Montgomery/Barrett work). Best *external* story
  (wallet/Bitcoin money, name recognition) and clean methodological transfer. Caveat: novelty is
  narrower than the doc implies (safegcd inverse and a scalarmult subset already have public proofs),
  so scope the first slice to field reduction, not the whole signing path. **curve25519-dalek**
  non-fiat backends are a secondary Tier-B option.
- **Avoid for this pipeline (despite high doc ranks):** rustls-webpki cert validation, openCryptoki
  PKCS#11 templates, tpm2-tss marshalling, GnuTLS/OpenSSL X.509/CMS. Parser/state-machine heavy; you'd
  fight the toolchain, and the defects there are parsing bugs fuzzing finds more cheaply.

Effort reality-check: the doc's "L = 2–4 months for one researcher" is optimistic for the full
SAW→Isabelle pipeline. The ML-DSA forward NTT alone was weeks of grind for one subroutine, and the
inverse is still in progress. Scope first slices to a single arithmetic kernel, not a library.

**Sequencing rule (hard-learned):** do not start a new target until fork 1 lands AND one credible
artifact is published. The ePrint rejections (3×) came from shipping proof work without a landed
publication; broadening targets before fixing that just repeats the pattern. Leverage beats greenfield
until there is one external win on the board.

## Non-goals (for now)
- Full end-to-end ML-DSA. Whole-algorithm correctness. Multiple implementations at once.

## Disclosure
- OF-1 (`montgomery_reduce` doc-comment strict-bound off-by-one at an endpoint) and OF-2 (`reduce32`
  doc-comment low-end bound `-6283008` reachably `-6283009` under its one-sided precondition) were
  **disclosed 2026-06-09 as pq-crystals/dilithium#114** (origin; PQClean is archiving; mldsa-native /
  liboqs are downstream). The AVX2 path has no `reduce.c`, so the comments don't repeat there. Both are
  doc/contract issues, not miscomputations. Next: await maintainer response, then offer a PR for their
  preferred phrasing.
