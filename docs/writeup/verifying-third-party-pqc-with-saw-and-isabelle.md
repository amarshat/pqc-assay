# Verifying third-party post-quantum C against its spec, with SAW + Cryptol + Isabelle

> Draft outline, not finished prose. This applies the SAW + Cryptol + Isabelle approach Apple
> open-sourced for `corecrypto` (May 2026) to third-party reference code. No Apple code, proofs, or
> theories are used; the Isabelle spec is written from FIPS 204.

## 1. Why

- What Apple's May 2026 corecrypto release open-sourced, and the gap: these tools have mostly been
  driven on Apple's own code, not on third-party C.
- Why reference C, and why ML-DSA.

## 2. The toolchain

- SAW, Cryptol, cryptol-to-isabelle, Isabelle (+ AFP): what each does and how they connect. All from
  Galois / the open ecosystem.

## 3. Setup (the parts the docs skip)

- Version pins and the gotchas hit along the way: arm64 macOS code-signing/quarantine `Killed: 9`;
  building the AFP + SAW `Cryptol` Isabelle session; GNU Make 3.81 resolving single-command recipes
  against its own PATH.

## 4. The target

- `reduce.c`: `montgomery_reduce`, `reduce32`, `caddq`, `freeze`. Montgomery reduction computes
  `a·2⁻³² mod Q`; it's an implementation device, not a FIPS-204 object. SAW covers all four; the
  Isabelle leg covers `montgomery_reduce` so far. The NTT is not modeled.

## 5. C → Cryptol → SAW

- Modeling at bit-exact widths; arithmetic vs logical shift; the documented preconditions (and the
  int32 overflow that forces `reduce32`'s). The mutation test that checks the proof isn't vacuous.

## 6. Lifting to Isabelle and proving equivalence

- cryptol-to-isabelle in practice; the `seq`/`word` coercion library; the proof structure (integer
  core, `seq`→`word` bridge, `sint` of the word computation, the `T ≡ a·QINV (mod 2³²)` congruence).
  Mechanizing the lift so the committed theory is diffed against the `.cry` SAW checks.

## 7. Results and limits

- What's proven, under which assumptions (link `docs/ASSUMPTIONS.md`). The OF-1 doc off-by-one in the
  upstream `montgomery_reduce` comment.
- What's not proven: the forward NTT, optimized/native code, constant-time. Why `montgomery_reduce` is
  the easy target, and where the real risk is: reduction-bound composition across the NTT
  (ePrint 2026/1032; Apple's InvNTT bug).

## 8. Second case study: RustCrypto `ml-dsa` and the Barrett reduction wall

The `reduce.c` work above targets PQClean C. The second target is the RustCrypto `ml-dsa` crate,
pinned to 0.1.1, the de-facto pure-Rust ML-DSA. SAW reaches it through `mir-json` and `crucible-mir`
(MIR schema v11, matching SAW 1.5.1), so the object under proof is the crate's MIR, not a C
transcription. The crate has never been independently audited, and two of its advisories are the
kind a verify-against-FIPS-204 pipeline is meant to catch: a `<` that should have been `<=` accepted
duplicate hint indices (GHSA-5x2r-hc65-25f9), and a timing side-channel in `decompose`
(RUSTSEC-2025-0144).

The arithmetic at issue is `barrett_reduce`. The NTT butterflies multiply two field elements
`a, b < q = 8380417`, so the product is below `2^46`, and reduce it with Barrett's method: widen to
`u128`, multiply by `M = floor(2^46 / q) = 8396807`, shift right by 46, subtract `quotient * q`, then
do one conditional subtract. The obligation is `barrett_reduce(x) == x mod q` for every `x < 2^46`.

### The wall

That obligation does not go through as a bit-vector proof. The `u128` multiply by `M` puts a full
128-bit multiplier in the SAT/SMT problem, and multiplier reasoning is where these solvers fall over.
A direct `mir_verify` of `barrett_reduce == x mod q` with z3 ran 3h15m without converging (saw-script
discussion #3306; the SAW maintainer confirmed SMT tools "fundamentally struggle with" Barrett).
Checking the equivalence against a bit-exact model instead of against `x mod q`, and against a
`urem`-free carry-fold reference, does not help: abc's default SAT sweep on `barrett_reduce ==
barrettBV` and z3 on `barrett_reduce == brefMod` both stalled at 360s. The pinned toolchain has no
multiplier-strong solver (no bitwuzla, no boolector). The multiplier miter is the wall, and it does
not move with the solvers on hand.

### Splitting the obligation

The Barrett identity is arithmetic, so the way around an intractable bit-vector proof is to prove it
as arithmetic, in a proof assistant, and keep the bit-vector work to the part that is tractable. The
decomposition has three pieces:

1. A bit-exact Cryptol model, `barrettBV` (in `barrett_bridge.cry`), that transcribes the impl
   operation for operation: `zext` to 128 bits, multiply by `M`, shift right 46, subtract
   `quotient * q`, truncate, conditional subtract.
2. The modular identity `barrettBV x == x mod q` for `x < 2^46`, proven in Isabelle. This is Route Y.
3. Faithfulness of `barrettBV` to the deployed MIR.

Route Y is the piece this work closes. `cryptol-to-isabelle` lifts `barrettBV` into Isabelle, and
`barrettBV_bridge_holds` proves the identity over the lifted model. The proof pushes the unsigned
interpretation `uint` through each word operation onto an integer Barrett core: `uint` of the `zext`
is preserved (`uint_up_ucast`); the two multiplies do not overflow because the product stays below
`2^69 < 2^128` (`uint_word_ariths`); the shift is integer division (`uint_shiftr_eq`); the subtract
does not underflow because the Barrett quotient satisfies `quotient * q <= x` (`uint_sub_lem`); the
truncation is lossless because the remainder is below `2q < 2^32` (`unsigned_ucast_eq`). What is left
is an integer statement, closed by `barrett_core` (the Barrett identity `x - floor(x*M / 2^46)*q` lies
in `[0, 2q)`, and one conditional subtract makes it `x mod q`) and `barrett_core_bounds`, both proven
with algebra and `linarith`, no SMT.

Two things make this a statement about the deployed code and not an isolated lemma. First, the lifted
model is gated: `scripts/lift_check_barrett.sh` regenerates the theory with `cryptol-to-isabelle` and
requires it to match the committed `Barrett_Lift.thy` byte for byte, apart from the theory name
(renamed to dodge a case-insensitive-filesystem collision). So the `barrettBV` Route Y reasons about
is the tool lift of the same `.cry` SAW checks against, not a hand-transcription that can drift.
Second, "no SMT" is checked by the Isabelle kernel, not by grep: an ML block runs
`Thm_Deps.has_skip_proof` and `Thm_Deps.all_oracles` on the theorem and fails the build if its
transitive proof cone uses any oracle, which rules out `sorry`, the SMT oracle, and the translator's
prove-anything `unsupported` axiom in one check.

### What this closes, and what it does not

Route Y closes the arrow `barrettBV == x mod q`. It does not remove the admit in the SAW proof.
`field_ops_bridged.saw` still assumes `barrett_reduce == x mod q` wholesale with
`mir_unsafe_assume_spec`, because the remaining link, `MIR barrett_reduce == barrettBV` at full width,
is the multiplier miter the solvers stall on. Route Y does not touch that link. Faithfulness of
`barrettBV` to the MIR rests on construction (a line-for-line transcription of the source) and on the
bit-vector equivalence holding at width `< 2^24`, which SAW does prove. So the admit is now backed by
a proven model identity instead of resting on that identity being taken on trust, but the field
multiply's reduction is not verified end to end against the Rust.

Being precise here matters, because the gap is the one recent critiques go after. "Verification
theatre" (ePrint 2026/192) and the analysis of the hax pipeline at symbolic.software make the same
point: a translation from source to a proof object is only as good as the guarantee that the proof
object is the source. Here the two crossings, MIR to Cryptol and Cryptol to Isabelle, are handled
differently and stated separately. The Cryptol-to-Isabelle crossing is gated by the lift-check. The
MIR-to-Cryptol crossing is the open admit, named as such, with small-width evidence in place of a
full-width proof.

### Positioning

Barrett reduction has been verified before, and the split used here is not new. libcrux (Cryspen, via
hax and F\*) verifies ML-DSA and ML-KEM field arithmetic, `barrett_reduce` included, on deployed Rust.
CryptoLine and its Jazzline extension verify Kyber and Dilithium NTT arithmetic, Barrett and
Montgomery, by combining algebraic reasoning with range-restricted SMT precisely to avoid bit-blasting
the multiply. So the contribution is not a first proof of Barrett, and it is not that SMT cannot do
the arithmetic while this method can; sidestepping the multiply with algebra plus range reasoning is
the standard move in this subfield.

What is specific here is the combination and the honesty about its seam: a reproducible, kernel-checked
audit of an unmodified third-party crate (RustCrypto `ml-dsa`, not written for verification) that
couples MIR-level SAW proofs with an Isabelle arithmetic proof, gates the tool crossing it can gate,
and names the single admit it cannot yet discharge, together with the reason (the multiplier miter)
and the evidence standing in for it.

## 9. What I'd want from the tools next

- Concrete asks, filed against the relevant repos.
- A multiplier-aware equivalence backend reachable from SAW (bitwuzla, or abc's CEC engine wired
  through the `w4`/`offline_aig` path), which is what the `MIR barrett_reduce == barrettBV` link needs.

## Appendix: reproduce

- `./scripts/setup.sh && ./scripts/setup_isabelle_cryptol.sh && make verify`
