# NTT composition — scope (2026-06-18)

## STATUS UPDATE (2026-06-18)

- **1A DONE** (`ntt_full_check.saw`, saw exit 0): composed full transform faithful to the
  independent FIPS transcription + round-trip `inv(fwd(w)) == 256·w mod q`. Committed.
- **1B NOT PURSUED — by design.** `Polynomial::ntt` / `NttPolynomial::ntt_inverse` are `pub(crate)`
  and the transform is inlined: no callable entry to override-verify without **editing the pinned
  vendored target**. We do NOT patch the pin (verifying the crate *as published* is the whole point;
  a logic-free wrapper still perturbs the artifact + invites "did it change inlining?"). The
  `pub(crate)` boundary is correct encapsulation, NOT an upstream defect — nothing to disclose.
- **Tier-1 is therefore CLOSED at an honest boundary:** layers + composed spec mechanized; the
  8-layer *call order* is by-inspection of pinned `ntt.rs:80-87`/`142-149`, documented in
  ASSUMPTIONS as a reachability fact (same category as the existing monomorphization assumption).
- **Next real mechanization = Tier 2 (Isabelle)** — pure math on the spec side, needs no callable
  `ntt()`, no patch. Detailed scope appended at the bottom.

---


We have all 16 individual layers proven equal to the FIPS 204 Alg 41/42 layer
*bodies* (`layer_ntt_fwd.saw` / `layer_ntt_inv.saw`). "Composition" = lift that
from per-layer to the whole transform. There are TWO distinct tiers; they answer
different questions and only Tier 1 is needed for the project's stated goal.

---

## Tier 1 — Operational composition: `ntt()` == FIPS 204 Algorithm 41 (full loop)

**Claim:** the implementation's full forward transform equals the 8-fold
composition of the layer maps, which is exactly the FIPS 204 Alg 41 loop as the
standard writes it (Alg 41 *is* the butterfly-layer loop; FIPS defines the NTT
operationally). Same for `ntt_inverse()` vs Alg 42 (+ the 256^-1 tail scaling).

This is what satisfies CLAUDE.md's goal ("forward NTT equivalent to the FIPS 204
sub-algorithm"). It is mostly mechanical.

**Two sub-steps:**

1A. **Cryptol: define the composed spec + prove it equals the standard's loop.**
   Add `nttFwdAll w = nttLayerFwd 1 128 127 (... (nttLayerFwd 128 1 0 w))` (foldl
   over the 8 (len,iter,m0) tuples) to a spec file. Prove `nttFwdAll` equals the
   FIPS-204 reference NTT loop (`fips204_ntt.cry` already has the per-layer Alg 41
   body; the full loop is the same 8 applications). Largely definitional / by
   `rewrite`; the per-layer faithfulness is already mechanized (`comp_faithful.saw`).
   Effort: S. Risk: low.

1B. **SAW: impl `ntt()` == `nttFwdAll`, using the 8 layer proofs as overrides.**
   - BLOCKER (recon 2026-06-18): the harness does NOT monomorphize a standalone
     `Polynomial::ntt` / `NttPolynomial::ntt_inverse` — only `ntt_layer<…>` /
     `ntt_inverse_layer<…>` are in the MIR. Add a harness entry (e.g.
     `pub fn ntt_poly44(p: …) -> …` calling `.ntt()` / `.ntt_inverse()`), rebuild
     MIR, grab the new `_inst` name.
   - Then `mir_verify` the full `ntt()` with the 8 layer specs as overrides. Each
     layer application becomes ONE override (not 128 butterflies), so the
     simulation is ~8 override applications — cheap, dodges the v1 "1024-butterfly
     / ~3000-obligation" wall. The m-counter threading (0→128 fwd, 256→128→…→1)
     and the order of the 8 layers is the content the proof checks.
   - The field-op overrides stay uninterpreted (same as the layer proofs); the op
     correctness remains the field_ops_bridged obligation.
   Effort: M (harness change + MIR rebuild + override plumbing). Risk: medium
   (override matching on Elem-array args at the ntt() boundary; the `_inst` /
   disambiguator gotchas from before).

   *Alternative if 1B's harness route fights us:* a SAW-level lemma chain — verify
   `ntt()` directly with the layer overrides without a new entry, IF some existing
   monomorphized path (sign/keygen) reaches `Polynomial::ntt`. Recon: `::ntt`
   appears but no `Polynomial…::ntt::_inst` — so it's likely inlined; the harness
   entry is the clean route.

**Tier-1 done = "forward (and inverse) NTT end-to-end == FIPS 204 Alg 41/42",
tool-checked, modulo the documented field-op (Barrett) assumption.** This is the
headline upgrade from "16 layer bodies" to "the transform."

---

## Tier 2 — Semantic correctness: Alg 41 loop == the NTT-as-transform (FFT theorem)

**Claim:** the Alg 41 butterfly loop actually computes the negacyclic NTT, i.e.
the evaluation map `ŵ[k] = Σ_j w[j]·ζ^((2·brv(k)+1)·j)` over `Z_q[x]/(x^256+1)`.
This is the Cooley–Tukey *correctness* theorem, NOT FIPS equivalence (FIPS also
defines the NTT operationally, so Tier 1 already meets the standard).

- **Where:** Isabelle. Lift the composed Cryptol layer map via cryptol-to-isabelle
  (pipeline already exists: `scripts/lift_check.sh`, `spec/isabelle/`), then prove
  the lifted 8-layer composition equals a definitional summation/evaluation spec.
- **Shape:** induction over the 8 levels, à la v1's `ntt_overflow_free`
  (`spec/isabelle/Assay_Equivalence.thy`) — but proving the *value* (the transform
  identity), not just coefficient bounds. v1 never did NTT transform correctness;
  this is genuinely new and is the real research content.
- Effort: L (this is a multi-day Isabelle proof — the FFT identity, root-of-unity
  bookkeeping, bit-reversal indexing). Risk: high (it's the hard theorem).

**Tier-2 is optional for FIPS compliance, valuable for a paper / for "we proved
the NTT *is* the NTT".**

---

## Recommendation

Do **Tier 1** next (1A then 1B). It's the honest "end-to-end forward NTT"
deliverable, it's S+M effort, low/medium risk, and it directly closes the
CLAUDE.md goal. Park Tier 2 as a separate research push (pairs naturally with the
Barrett-tactic upstream work).

**First concrete move:** 1A (Cryptol composed spec + faithfulness to the Alg-41
loop) — no harness/MIR changes, validates the composition shape, and is a clean
standalone commit. Then tackle 1B's harness entry.

## Honesty notes (for ASSUMPTIONS.md when this lands)
- Tier 1 inherits the field-op (Barrett) assumption and the uninterpreted-routing
  framing from the layer proofs.
- Tier 1 proves equality to FIPS *Algorithm 41/42* (operational), NOT to the
  summation transform — state this explicitly so "we proved the NTT" isn't read as
  the FFT-correctness theorem (that's Tier 2).

---

## Tier 2 — detailed scope (the FFT-correctness theorem, Isabelle)

**Goal.** Prove the composed 8-layer forward map computes the negacyclic NTT, i.e.
the definitional transform on Z_q[x]/(x^256+1):

    ntt_hat[k]  =  sum_{j=0}^{255}  w[j] * zeta^((2*brv8(k)+1)*j)   mod q

(and the inverse the dual, with the 256^-1 normalization). This is Cooley-Tukey
*correctness*, NOT FIPS equivalence — FIPS 204 defines the NTT operationally as
the butterfly loop (which Tier 1 already matches), so Tier 2 is a research/paper
result ("the algorithm really is the transform"), not a compliance requirement.

**Why Isabelle, not SAW.** This is a universally-quantified identity over the ring,
proved by induction over the 8 decimation levels — exactly the structure SAW's
SMT backend can't do (it would unroll/bit-blast). It also lives entirely on the
SPEC side: no callable `ntt()`, no pinned-target patch, no MIR. Clean.

**Pipeline (pieces that already exist).**
- `cryptol-to-isabelle` lift (scripts/lift_check.sh pattern) — lift the composed
  layer map. NOTE: today the lift is wired for the v1 model (model/cryptol/
  MLDSA_NTT.cry); Tier 2 lifts the v2 `fips204_ntt.cry` (the plain-`%q` reference,
  cleaner to reason about in Isabelle than the BV surface forms).
- v1 already does **level induction over the NTT** for overflow-freedom
  (Assay_Equivalence.thy `ntt_overflow_free`, `sint_add_inrange`, the "8 levels"
  bound argument). That gives the *induction skeleton*; Tier 2 reuses the shape but
  proves the *value* (the transform identity), not just coefficient bounds.
- MLDSA_NTT_Spec.thy currently has ONLY the reduction primitives — **the
  definitional NTT transform spec does not exist yet and must be written.**

**Work breakdown.**
1. Write the definitional spec: `ntt_hat`, `intt_hat`, the zeta powers as a clean
   Isabelle function (proving the table == zeta^brv is a small lemma). [S]
2. Lift the composed layer map (`nttFwdAllRef`) to Isabelle; confirm via lift-check. [S]
3. The core theorem `lifted_nttFwdAll = ntt_hat`: induction over the 8 levels. The
   real work — Cooley-Tukey decimation step, root-of-unity bookkeeping, bit-reversal
   index algebra. [L, the hard part]
4. Inverse + the 256^-1 normalization (ntt_hat is invertible; intt_hat ∘ ntt_hat = id). [M]
5. Non-vacuity / sanity: the round-trip already holds at the Cryptol level
   (ntt_full_check.saw); mirror it as an Isabelle `value`/lemma. [S]

**Recon to do FIRST (cheap, decides feasibility).**
- Search AFP for an existing NTT/FFT formalization (number-theoretic transform,
  negacyclic convolution, discrete Fourier over Z_q) to reuse rather than prove
  Cooley-Tukey from scratch. This could collapse step 3 from weeks to days, or
  confirm it's bespoke.
- Confirm cryptol-to-isabelle lifts `fips204_ntt.cry`'s foldl/comprehension cleanly
  (the `@`/index forms; v1 hit `nth_seq`/SeqOOB quirks — see memory).

**Effort/risk.** Step 3 is L / high-risk (it's a real theorem; weeks without an AFP
base, days with one). Steps 1-2,4-5 are S-M. Recommend the AFP recon BEFORE
committing — it's the swing factor.

**Deliverable if it lands.** "The forward NTT in a deployed PQC library is proven,
end-to-end, to compute the FIPS-204 negacyclic transform" — modulo the documented
field-op (Barrett) assumption and the by-inspection call-order. That IS a paper
(or a strong section in the existing one), and pairs naturally with the
Barrett-tactic upstream work for a "v2: from boundary to closure" follow-up.
