# Verifying third-party post-quantum C against its spec, with SAW + Cryptol + Isabelle

*Amar Akshat &middot; [github.com/amarshat](https://github.com/amarshat)*

Apple open-sourced their SAW + Cryptol + Isabelle verification of `corecrypto` in May 2026. I ran the
same approach on code Apple didn't write: the unmodified PQClean / pq-crystals ML-DSA reference C, and
separately the RustCrypto `ml-dsa` crate. No Apple code, proofs, or theories in here; the Isabelle spec is
written from FIPS 204 directly. Everything below is machine-checked in this session's toolchain unless I
say otherwise. If I couldn't get a tool to actually prove something, I call it argued or assumed, not
proven.

## 1. Why

Apple's release proved the toolchain works end to end on production crypto. But it was Apple's own code:
they wrote it, they control it, they can annotate it however the prover needs. Almost nobody runs Apple's
ML-DSA. Most deployments run the PQClean / pq-crystals reference, or something like RustCrypto's
reimplementation, as-is, with no help from the authors and no freedom to touch the source for
verifiability. That's the position a third-party auditor is actually in.

I picked the NTT because it's the arithmetic core of both ML-DSA and ML-KEM, and because the bugs that
matter there (wrong reduction placement, overflow) pass test vectors and have shown up in shipped code. A
proof of the modular reduction on its own doesn't get you there. The transform chains hundreds of those
reductions across eight levels, and that's where a correctness argument actually gets hard.

## 2. The toolchain

SAW (the Software Analysis Workbench) proves a compiled function equal to a Cryptol spec, by symbolic
execution and SMT. It targets LLVM bitcode for C and, through `mir-json`, Rust MIR. Cryptol is a
word-level spec language. Isabelle/HOL is an interactive theorem prover. `cryptol-to-isabelle`, shipped
with saw-script 1.5.1, lifts a Cryptol module into an Isabelle theory, so a SAW proof (C or Rust equal to
a Cryptol model) and an Isabelle proof (that model equal to a closed-form spec) chain into one result
instead of sitting as two separate ones. All Galois tooling. Nothing here is a new tool.

## 3. Setup (the parts the docs skip)

Version pins, and the gotchas: arm64 macOS quarantine killing a perfectly good binary with `Killed: 9`;
building the AFP plus SAW `Cryptol` Isabelle session, which takes tens of minutes cold; GNU Make 3.81
resolving single-command recipes against its own PATH instead of the shell's, so a bare tool name fails to
resolve even after `export PATH`. All pinned in `scripts/setup.sh` so nobody has to hit these twice.

## 4. The target

Two targets, two toolchains:

- **PQClean / pq-crystals ML-DSA-44 reference C**: `reduce.c` (`montgomery_reduce`, `reduce32`, `caddq`,
  `freeze`) and `ntt.c` (forward and inverse NTT). Vendored and pinned by commit hash; byte-identical to
  pq-crystals/dilithium up to a namespace prefix.
- **RustCrypto's `ml-dsa` crate**, reached through `mir-json` and `crucible-mir`, verified against its MIR
  directly, not a hand transcription.

Both NTT directions are done now, not just the reduction layer. SAW proves the C forward and inverse
transforms bit-exact equal to Cryptol models on an overflow-checking build, and Isabelle proves those
lifted models equal, mod q, to the FIPS-204 forward and inverse negacyclic DFT. I also ran the same thing
on ML-KEM-512's forward NTT against FIPS 203, mostly to check the method wasn't a one-off (Section 7).

## 5. C to Cryptol to SAW

Bit-exact widths: arithmetic vs. logical shift, the documented preconditions, the int32 overflow that
forces `reduce32`'s particular bound. Every reduction-layer and NTT proof gets a mutation test, a
deliberately broken model or spec that has to be rejected with a counterexample. Catches vacuous proofs
before they get banked as results.

## 6. Lifting to Isabelle and proving equivalence

`cryptol-to-isabelle` in practice: the `seq`/`word` coercion library, and the same proof shape every time,
an integer core, a `seq`-to-`word` bridge, `sint` of the word computation, a congruence back to the
arithmetic contract (`T ≡ a·QINV (mod 2³²)` for Montgomery reduction, similar shape for Barrett). The lift
itself is checked mechanically, not by eye: CI regenerates the Isabelle theory from the `.cry` source with
`cryptol-to-isabelle` and diffs it byte for byte against the committed copy.

One trick made the eight-level induction tractable, and it's worth calling out on its own. Cryptol's
index operation is strict, but an out-of-bounds access returns the last element of the sequence instead
of failing. So the coefficient bound can be stated over *every* index, not just the ones the current level
touches. Every indexed access becomes a bounded list member whether it's in range or not, and the
induction never has to reason about the level-parameterized shifts and divisions that address the
butterfly network. That index arithmetic is exactly what makes the direct SMT approach fall over (Section
8). Same trick, reused unchanged, for the overflow bound, the transform congruence, both NTT directions,
and the ML-KEM transfer.

## 7. Results and limits

What's proven, and under which window (full detail in `docs/ASSUMPTIONS.md`):

- `reduce.c`'s four primitives: C equal to Cryptol (SAW), model equal to FIPS-derived spec (Isabelle),
  each on its true reachable output window.
- The forward NTT, one connected chain: SAW (C equal to model), Isabelle (model equal to the FIPS-204
  negacyclic DFT, mod q), on the signed centered window the deployed code uses. I also closed the last
  link, that the overflow-checking build behaves the same as the ordinary one: SAW re-verifies the
  *default* build directly, roughly 3000 unrolled signed-overflow side conditions plus the model equality,
  via `bitwuzla`. Took 12.5 hours. Runs out of band, not in the fast CI gate.
- The inverse NTT, same chain, mirrored in the Gentleman-Sande direction, with ML-DSA's 256⁻¹
  normalization folded into the mechanized theorem instead of argued around it. Overflow-freedom is
  mechanized on the signed window too. What's still argued: the same overflow-build-matches-default step.
  I tried closing it the same way the forward one closed. Ran 55 hours across about 4600 obligations and
  didn't finish. Turns out the boundary in Section 8 has more than one edge.
- ML-KEM-512's `reduce.c` and forward NTT against FIPS 203, same three-tool construction, re-derived for a
  structurally different, *incomplete* transform (Kyber's modulus has no 512th root of unity, so the
  output is 128 degree-two residues, not 256 single coefficients).
- Two doc off-by-ones in the reference's stated output windows (`montgomery_reduce`'s and `reduce32`'s
  comments are each wrong at one boundary input), disclosed upstream to pq-crystals/dilithium. Neither is
  a functional bug. On every input I checked, the reference NTT computes the correct transform, and that's
  a result on its own, not just an absence of findings to report.

Not proven: the optimized AVX2/aarch64 paths, the `mldsa-native` successor, constant-time behavior of any
of it. The real risk in this class of code is reduction-bound composition across a full transform, not a
single primitive: an eprint audit and Apple's own disclosed inverse-NTT bug both landed exactly there. A
clean `montgomery_reduce` proof by itself doesn't reach that.

## 8. Second case study: RustCrypto `ml-dsa` and the Barrett reduction wall

The `reduce.c` work above is PQClean C. The second target is RustCrypto's `ml-dsa` crate, pinned to 0.1.1,
the de-facto pure-Rust ML-DSA. SAW reaches it through `mir-json` and `crucible-mir`, so the proof is
against the crate's actual MIR, not a transcription. The crate's never been independently audited, and one
of its disclosed advisories is exactly what a verify-against-FIPS-204 pipeline should catch: a `<` that
should've been `<=`, accepting duplicate hint indices, later assigned CVE-2026-24850.

The arithmetic in question is `barrett_reduce`. The NTT butterflies multiply two field elements
`a, b < q = 8380417`, so the product is under `2^46`. Barrett's method reduces it: widen to `u128`,
multiply by `M = floor(2^46 / q) = 8396807`, shift right 46, subtract `quotient * q`, one conditional
subtract. The obligation is `barrett_reduce(x) == x mod q` for every `x < 2^46`.

### The wall

I expected this to be routine. It wasn't. The `u128` multiply by `M` puts a full 128-bit multiplier
straight into the SMT problem, and multiplier reasoning is where these solvers fall apart. I ran a direct
`mir_verify` with z3. After three hours it still hadn't converged, so I killed it. A SAW maintainer's
answer to the same question, on [saw-script discussion
#3306](https://github.com/GaloisInc/saw-script/discussions/3306), was blunt: "proving the implementation
of Barrett reduction is one of those things that SMT-based tools like SAW fundamentally struggle with."
I also tried checking against a bit-exact model instead of `x mod q` directly, and against a `urem`-free
carry-fold rewrite. Neither helped; abc and z3 both stalled at the same timeout on those too. The pattern
across an increasing input bound is stark (z3, single thread, 300s cap):

| input bound | wall-clock |
|---|---|
| x < 2^20 | 3.7s |
| x < 2^28 | 4.1s |
| x < 2^30 | 7.3s |
| x < 2^32 | 27.9s |
| x < 2^34 | 183.6s |
| x < 2^36 | times out |
| x < 2^46 (the real domain) | times out |

Flat, then roughly four to seven times slower per two added bits, dead between 2^34 and 2^36. The formula
doesn't grow with the input bound. The live bit width does, and that's what breaks the solver.

### Splitting the obligation

If bit-blasting is the wall and not the arithmetic itself, the arithmetic should go through fine somewhere
else. I posed the same identity in unbounded-integer arithmetic: ask z3 (logic NIA) whether
`x - floor(x*M/2^46)*q` lands in `[0, 2q)` for every x in `[0, 2^46)`. It came back `unsat`, meaning the
identity holds everywhere, in 0.04 seconds. Same relation, same domain, four orders of magnitude faster
than the bit-vector version, which hadn't finished at all. I mutated `q` to `q+1` to check the fast answer
wasn't vacuous; it flipped straight to `sat` with an explicit witness.

That gave three ways past the wall. All three are now real, not just ideas on paper:

1. **The total-invariant induction** from Section 6 is what makes the NTT's own overflow bound go through.
   Nothing Barrett-specific about it.
2. **Lift Barrett into Isabelle as integers.** `cryptol-to-isabelle` lifts the bit-exact Cryptol model of
   `barrett_reduce`, and a proof pushes the unsigned interpretation through each word operation (`zext`,
   the two multiplies, the shift, the subtract, the truncation) down onto that same integer core. Closes
   `barrettBV(x) == x mod q` for all `x < 2^46`, no SMT call anywhere, checked oracle-free by Isabelle's
   own dependency tracker. This used to be an open admit in the proof. Not anymore.
3. **Build the layer spec out of the same uninterpreted field operations the SAW override already
   returns**, so an obligation over 256 output positions gets solved by rewriting instead of bit-blasting
   256 separate modular reductions. All eight forward layers verify against FIPS-204 Algorithm 41 this
   way.

Separately, I added `bitwuzla` (CEGAR-style abstraction-refinement, built for exactly this kind of wide
multiplication) to the toolchain, and it closes the deployed obligation directly: `barrett_reduce(x) == x
mod q` on the actual MIR, full `2^46` domain, in 1402 seconds. Every eager back-end I tried didn't finish
at all. The same solver later closed the forward NTT's overflow-build link too (Section 7). So the
wide-domain Barrett obligation is closed two separate ways now: a multiplier-strong solver directly on the
deployed code, and, independently, oracle-free, in Isabelle.

### What this closes, and what's still argued

The MIR-to-Cryptol crossing, that the lifted `barrettBV` model actually matches the deployed
`barrett_reduce`, rests on construction (a line-for-line transcription) plus SAW proving the bit-vector
equivalence at narrower widths. It's not a symbolic full-width proof of faithfulness by itself.
`bitwuzla`'s direct MIR proof is what removes the need to lean on that. The Cryptol-to-Isabelle crossing is
gated mechanically, so it can't drift. I try to keep these seams named separately rather than blurred into
one "it's verified" claim, because blurring exactly this kind of seam is what recent critiques of
verified-crypto pipelines go after, and rightly so. The paper carries a claim table tagging every result
mechanized, argued, or assumed, and I don't claim anything past what's in that table.

### Positioning

None of this is a first proof of Barrett, and algebra-over-bit-blasting isn't a new idea. libcrux (Cryspen,
via hax and F\*) verifies ML-DSA and ML-KEM field arithmetic, `barrett_reduce` included, on shipped Rust.
CryptoLine verifies Kyber and Dilithium NTT arithmetic, Barrett and Montgomery included, by discharging the
nonlinear multiplies algebraically and the range conditions with SMT, the same move of keeping the
multiply out of the bit-blaster. Jazzline composes that into Jasmin and EasyCrypt developments. What I
think is new here: doing this on an unmodified third-party crate that was never written for verification,
coupling MIR-level SAW proofs with an Isabelle arithmetic proof, with a measured map of exactly where
eager bit-blasting gives out and three separate routes past it instead of one.

## 9. What I'd want from the tools next

Last version of this writeup asked for a multiplier-aware equivalence backend reachable from SAW. Answered
now: `bitwuzla` is in the pinned toolchain and closes exactly that obligation. Still open: a SAW-native
tactic that automates the bit-vector-to-bounded-integer lift, so this doesn't stay a bespoke Isabelle
detour every time it comes up. A Galois maintainer on the same discussion thread said SAW "ought to have
some kind of solver or tactic" for this and doesn't yet. And the obvious next target: point the same
pipeline at the deployed optimized AVX2/aarch64 kernels, where the error-prone arithmetic actually ships.
Everything here is the reference C and one third-party crate.

## Appendix: reproduce

`./scripts/setup.sh && ./scripts/setup_isabelle_cryptol.sh && make verify`
