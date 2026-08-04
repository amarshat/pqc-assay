# Verifying third-party post-quantum C against its spec, with SAW + Cryptol + Isabelle

*Amar Akshat &middot; [github.com/amarshat](https://github.com/amarshat)*

This applies the SAW + Cryptol + Isabelle approach Apple open-sourced for `corecrypto` in May 2026 to
third-party reference code: the unmodified PQClean / pq-crystals ML-DSA reference C, and separately the
RustCrypto `ml-dsa` crate. No Apple code, proofs, or theories are used; the Isabelle spec is written from
FIPS 204 directly. Everything below is machine-checked in this session's toolchain unless it's explicitly
marked argued or assumed; nothing here is claimed proven that a tool didn't actually discharge.

## 1. Why

Apple's corecrypto release showed the toolchain, SAW plus Cryptol plus an Isabelle-formalized FIPS
specification, works end to end on production crypto. But it was driven on Apple's own code, which Apple
wrote, controls, and could annotate for the prover. Most ML-DSA deployments don't run Apple's code. They
run the PQClean / pq-crystals reference, or a third-party reimplementation like RustCrypto's, as-is,
without cooperation from the authors and without the freedom to rewrite the source for verifiability. That
is the position any third-party auditor is actually in, and it's a different problem: the target wasn't
built to be proved about.

The NTT is the right subroutine to test this on. It's the arithmetic core of both ML-DSA and ML-KEM,
verification-grade bugs in it (reduction placement, overflow) pass test vectors and have shown up in real
implementations, and a single-primitive proof of the modular reduction alone doesn't reach it: the
transform composes hundreds of reductions across eight interleaved levels, and getting a bound or a
correctness statement through that composition is where the difficulty actually lives.

## 2. The toolchain

SAW (the Software Analysis Workbench) proves a compiled function equivalent to a Cryptol specification by
symbolic execution plus SMT; it targets LLVM bitcode for C and, via `mir-json`, Rust MIR. Cryptol is a
word-level specification language. Isabelle/HOL is an interactive theorem prover. `cryptol-to-isabelle`,
first shipped with saw-script 1.5.1, lifts a Cryptol module into an Isabelle theory, which is what lets a
SAW proof (C or Rust equal to a Cryptol model) and an Isabelle proof (that same model equal to a
closed-form spec) compose into one chain instead of two disconnected results. All of it is from Galois and
the open verification ecosystem; nothing here is a new tool.

## 3. Setup (the parts the docs skip)

Version pins and the gotchas hit along the way: arm64 macOS code-signing and quarantine producing
`Killed: 9` on a perfectly good binary; building the AFP plus SAW `Cryptol` Isabelle session (heavy, tens
of minutes cold); GNU Make 3.81 resolving single-command recipes against its own PATH rather than the
shell's, so a bare tool name silently fails to resolve even after `export PATH`. All of it is in
`scripts/setup.sh`, pinned, so it doesn't need rediscovering.

## 4. The target

Two independent targets, on two toolchains:

- **PQClean / pq-crystals ML-DSA-44 reference C**, `reduce.c` (`montgomery_reduce`, `reduce32`, `caddq`,
  `freeze`) and `ntt.c` (the forward and inverse NTT), vendored and pinned by commit hash, byte-identical
  to the pq-crystals/dilithium origin up to a namespace prefix.
- **RustCrypto's `ml-dsa` crate**, reached through `mir-json` and `crucible-mir`, verified directly against
  its MIR rather than a hand transcription.

Both directions of the ML-DSA NTT are modeled and verified now, not just the reduction layer: SAW proves
the C forward and inverse transforms bit-exactly equal to Cryptol models under an overflow-checking build,
and Isabelle proves those lifted models equal, mod q, to the FIPS-204 forward and inverse negacyclic DFT.
The same construction is also applied to ML-KEM-512's forward NTT against FIPS 203, as a check that the
method isn't specific to ML-DSA (Section 7).

## 5. C to Cryptol to SAW

Modeling at bit-exact widths: arithmetic versus logical shift, the documented preconditions, the int32
overflow that forces `reduce32`'s particular bound. Every reduction-layer and NTT proof carries a mutation
test, a deliberately wrong model or spec, checked to be rejected with a counterexample, so a proof that
happens to hold vacuously (an unsatisfiable precondition, say) gets caught rather than banked.

## 6. Lifting to Isabelle and proving equivalence

`cryptol-to-isabelle` in practice: the `seq`/`word` coercion library, and a proof structure that recurs
across every layer, an integer core, a `seq`-to-`word` bridge, the `sint` of the word computation, and a
congruence back to the arithmetic contract (`T ≡ a·QINV (mod 2³²)` for Montgomery reduction, the analogous
shape for Barrett). The lift itself is mechanized so it can't silently drift from what SAW checks: a CI
step regenerates the Isabelle theory from the `.cry` source with `cryptol-to-isabelle` and diffs it,
byte for byte, against the committed copy.

The NTT proofs add one more device worth naming on its own, because it's the thing that made an
eight-level induction tractable at all. Cryptol's index operation is strict, but an out-of-bounds access
returns the last element of the sequence rather than failing. That means a coefficient bound can be stated
as a *total* invariant, over every index, not only the ones the current level actually touches. Every
indexed access is then just a bounded list member, in-bounds or not, so the induction never has to reason
about the level-parameterized shifts and divisions that address the butterfly network, the exact
arithmetic that makes the direct SMT approach to this class of goal intractable (Section 8). It's a change
of proof structure, not of solver, and it's reused unchanged for the overflow bound, the transform
congruence, both NTT directions, and the ML-KEM transfer.

## 7. Results and limits

What's proven, and under which window (full detail in `docs/ASSUMPTIONS.md`):

- `reduce.c`'s four primitives, C equal to Cryptol (SAW) and model equal to FIPS-derived spec (Isabelle),
  each on its true reachable output window.
- The forward NTT: one connected chain, SAW (C equal to model) plus Isabelle (model equal to the FIPS-204
  negacyclic DFT, mod q), on the signed centered window the deployed code actually uses. The last link,
  that the overflow-checking build coincides with the ordinary one, is mechanized too: SAW re-verifies the
  *default* build directly, discharging around 3000 unrolled signed-overflow side conditions together with
  the model equality, via `bitwuzla` (12.5 hours, run out of band, not part of the fast CI gate).
- The inverse NTT: the same chain, mirrored in the Gentleman-Sande direction, with ML-DSA's 256⁻¹
  normalization folded into the mechanized theorem rather than argued around it. Its overflow-freedom bound
  is likewise mechanized on the signed window. The one link that stays argued, not mechanized, is that same
  overflow-build-coincides-with-default step; a same-shape attempt at closing it the way the forward one
  closed ran a measured 55 hours across roughly 4600 obligations and didn't finish (Section 8's boundary,
  it turns out, has more than one edge).
- ML-KEM-512's `reduce.c` and forward NTT against FIPS 203, the same three-tool construction, re-derived for
  a structurally different, *incomplete* transform (Kyber's modulus has no 512th root of unity, so the
  output is 128 degree-two residues, not 256 single coefficients).
- Two documentation off-by-ones in the reference's stated output windows (`montgomery_reduce`'s and
  `reduce32`'s comments are each wrong at one boundary input), disclosed upstream to pq-crystals/dilithium.
  Neither is a functional bug: on every input this verification checked, the reference NTT computes the
  correct transform. That absence of a real finding is itself part of the result, not just a footnote to it.

What's not proven: the optimized AVX2/aarch64 paths, the `mldsa-native` successor, constant-time behavior
of any of it. Reduction-bound composition across a full transform, not a single primitive, is where the
real risk in this class of code lives (an eprint audit and Apple's own disclosed inverse-NTT bug both
found exactly this class of defect); a lone `montgomery_reduce` proof, however clean, doesn't reach it.

## 8. Second case study: RustCrypto `ml-dsa` and the Barrett reduction wall

The `reduce.c` work above targets PQClean C. The second target is the RustCrypto `ml-dsa` crate, pinned to
0.1.1, the de-facto pure-Rust ML-DSA. SAW reaches it through `mir-json` and `crucible-mir`, so the object
under proof is the crate's MIR, not a C transcription. The crate has never been independently audited, and
one of its disclosed advisories is exactly the kind a verify-against-FIPS-204 pipeline is meant to catch: a
`<` that should have been `<=` accepted duplicate hint indices, later assigned CVE-2026-24850.

The arithmetic at issue is `barrett_reduce`. The NTT butterflies multiply two field elements
`a, b < q = 8380417`, so the product is below `2^46`, and reduce it with Barrett's method: widen to `u128`,
multiply by `M = floor(2^46 / q) = 8396807`, shift right by 46, subtract `quotient * q`, then do one
conditional subtract. The obligation is `barrett_reduce(x) == x mod q` for every `x < 2^46`.

### The wall

That obligation does not go through as a bit-vector proof, at least not with the eager back-ends most SAW
setups reach for. The `u128` multiply by `M` puts a full 128-bit multiplier in the SAT/SMT problem, and
multiplier reasoning is where these solvers fall over. A direct `mir_verify` with z3 ran over three hours
without converging. A SAW maintainer put it plainly on saw-script discussion #3306: "proving the
implementation of Barrett reduction is one of those things that SMT-based tools like SAW fundamentally
struggle with." Checking the equivalence against a bit-exact model instead of against `x mod q` directly,
and against a `urem`-free carry-fold reference, doesn't help either: abc's default SAT sweep and z3 on the
carry-fold form both stall at the timeout. Across an increasing input bound the pattern is stark and
reproducible (z3, single thread, 300s cap):

| input bound | wall-clock |
|---|---|
| x < 2^20 | 3.7s |
| x < 2^28 | 4.1s |
| x < 2^30 | 7.3s |
| x < 2^32 | 27.9s |
| x < 2^34 | 183.6s |
| x < 2^36 | times out |
| x < 2^46 (the real domain) | times out |

Flat, then a factor of four to seven per two added bits, crossing the timeout between 2^34 and 2^36. The
formula doesn't change size with the input bound; the live bit width does, and that's what the solvers
choke on.

### Splitting the obligation

The Barrett identity is arithmetic, so the way around an intractable bit-vector proof is to prove it as
arithmetic, in a proof assistant, and keep the bit-vector work to the part that's actually tractable. To
isolate whether bit-blasting itself, not the underlying relation, is the wall, pose the identical
obligation in unbounded-integer arithmetic instead: ask z3 (logic NIA) whether
`x - floor(x*M/2^46)*q` lands in `[0, 2q)` for every x in `[0, 2^46)`. It returns `unsat` (the identity
holds everywhere) in **0.04 seconds**. The bit-vector form of the exact same goal doesn't complete in over
300. A mutation check, replacing `q` by `q+1`, flips the integer query to `sat` with an explicit witness,
so the fast answer isn't a modeling artifact letting something vacuous through. Same relation, same
domain, two encodings, about four orders of magnitude apart.

That gave three routes past the wall, all now realized rather than just proposed:

1. **The total-invariant induction** (Section 6) is what makes the NTT's own overflow bound tractable in
   the first place, independent of Barrett specifically.
2. **An integer-and-word lift**: `cryptol-to-isabelle` lifts the bit-exact Cryptol model of
   `barrett_reduce` into Isabelle, and a proof pushes the unsigned interpretation through each word
   operation (the `zext`, the two multiplies, the shift, the subtract, the truncation) onto that same
   integer core, closing `barrettBV(x) == x mod q` for all `x < 2^46` with no SMT call at all, checked
   oracle-free by the Isabelle kernel's own dependency tracker. This is the piece that used to be the open
   admit here; it isn't anymore.
3. **A compositional layer specification**: build the NTT layer's spec from the same uninterpreted field
   operations the SAW override already returns, so an obligation over 256 output positions discharges by
   term rewriting instead of bit-blasting 256 independent modular reductions. All eight forward layers
   verify against FIPS-204 Algorithm 41 this way.

And separately from the Isabelle route, adding `bitwuzla` (CEGAR-style abstraction-refinement, aimed
specifically at wide multiplication) to the pinned toolchain closes the deployed obligation directly: it
proves `barrett_reduce(x) == x mod q` on the actual MIR, full `2^46` domain, in 1402 seconds, where every
eager back-end tried failed to complete at all. The same backend later retired the forward NTT's
overflow-build link too (Section 7). So the wide-domain Barrett obligation is now closed two ways: by a
multiplier-strong solver directly on the deployed code, and, independently, oracle-free, in Isabelle on the
lifted model.

### What this closes, and what's still argued

The MIR-to-Cryptol crossing (that the lifted `barrettBV` model faithfully transcribes the deployed
`barrett_reduce`) rests on construction, a line-for-line transcription, plus the bit-vector equivalence
holding at narrower widths where SAW does prove it directly; it isn't a symbolic full-width proof of
faithfulness on its own; `bitwuzla`'s direct MIR proof is what removes the need to lean on that. The
Cryptol-to-Isabelle crossing is gated mechanically (byte-for-byte diff against the regenerated lift), so it
doesn't drift. Being precise about exactly which seam is which matters, because this is exactly the kind of
gap that recent critiques of verified-crypto pipelines go after: a source-to-proof-object translation, or a
verified system generally, is only as trustworthy as its stated boundary between what's machine-checked and
what's taken on trust, and blurring that boundary is what produces false assurance. The discipline here is
a claim table (in the paper) that tags every result mechanized, argued, or assumed, and nothing above that
table.

### Positioning

Barrett reduction has been verified before, and the algebra-over-bit-blasting move isn't new: libcrux
(Cryspen, via hax and F\*) verifies ML-DSA and ML-KEM field arithmetic, `barrett_reduce` included, on
shipped Rust; CryptoLine verifies Kyber and Dilithium NTT arithmetic, Barrett and Montgomery included, by
discharging the nonlinear multiplies algebraically and the range conditions with SMT, precisely to keep the
multiply out of the bit-blaster, and the Jazzline work composes such proofs into Jasmin and EasyCrypt
developments. So the contribution isn't a first proof of Barrett, and it isn't that SMT categorically can't
do this arithmetic while some other technique can. What's specific here is the combination on an unmodified
third-party target: a reproducible, kernel-checked audit of a crate that was never written for
verification, coupling MIR-level SAW proofs with an Isabelle arithmetic proof, a measured map of exactly
where eager bit-blasting gives out, and three concrete, realized routes past it rather than one.

## 9. What I'd want from the tools next

The ask this write-up made a version ago, a multiplier-aware equivalence backend reachable from SAW, is
now answered: `bitwuzla` is in the pinned toolchain and closes exactly the obligation that motivated the
ask. What's still open: a SAW-native tactic that automates the bit-vector-to-bounded-integer lift (a Galois
maintainer's read on the same discussion thread was that SAW "ought to have some kind of solver or tactic"
for this and doesn't yet), so this class of proof stops being a bespoke Isabelle detour every time it comes
up. And, separately, pointing the same pipeline at the deployed optimized AVX2/aarch64 kernels, where the
error-prone arithmetic actually ships, is the natural next target; everything here is the reference C and
one third-party crate, not the fast paths.

## Appendix: reproduce

`./scripts/setup.sh && ./scripts/setup_isabelle_cryptol.sh && make verify`
