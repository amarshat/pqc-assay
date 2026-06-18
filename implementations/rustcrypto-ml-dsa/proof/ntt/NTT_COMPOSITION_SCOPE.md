# NTT composition — scope (2026-06-18)

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
