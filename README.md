<p align="center">
  <img src="assay-logo.png" alt="PQC-Assay — C = spec" width="260">
</p>

<h1 align="center">PQC-Assay</h1>
<p align="center"><em>(formerly "Assay")</em></p>

<p align="center">
  <a href="https://github.com/amarshat/pqc-assay/actions/workflows/verify.yml"><img src="https://github.com/amarshat/pqc-assay/actions/workflows/verify.yml/badge.svg" alt="verify"></a>
  <a href="https://github.com/amarshat/pqc-assay/actions/workflows/saw.yml"><img src="https://github.com/amarshat/pqc-assay/actions/workflows/saw.yml/badge.svg" alt="saw"></a>
  <a href="https://github.com/amarshat/pqc-assay/actions/workflows/rust.yml"><img src="https://github.com/amarshat/pqc-assay/actions/workflows/rust.yml/badge.svg" alt="rust"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT"></a>
  <img src="https://img.shields.io/badge/Isabelle-2025--2-9cf.svg" alt="Isabelle2025-2">
  <img src="https://img.shields.io/badge/SAW-1.5.1-orange.svg" alt="SAW 1.5.1">
  <img src="https://img.shields.io/badge/proofs-no%20sorry%20%7C%20no%20smt-success.svg" alt="no sorry, no smt">
</p>

Machine-checking post-quantum reference C against its specification, using the
SAW → Cryptol → Isabelle pipeline.

PQC-Assay builds a reproducible refinement chain for the **unmodified PQClean reference C** for
ML-DSA (FIPS 204): fixed-width C semantics, through a SAW-anchored Cryptol model and a lifted
word-level Isabelle model, up to an independent FIPS-204 specification, with the machine arithmetic's
in-range preconditions proven separately. The toolchain (SAW → Cryptol → Isabelle) is the one Apple
used for its 2026 `corecrypto` work (see [Background](#background-if-formal-verification-is-new-to-you));
this project uses none of Apple's code or theories, and the Isabelle spec is written from FIPS 204.

Current scope is the `reduce.c` arithmetic layer (both legs) and the forward NTT (functional
equivalence + a machine-checked overflow-freedom / coefficient-bound result).
Montgomery reduction is an implementation device the NTT uses; it is not defined in FIPS 204. None of
this is the optimized/assembly code that ships in production (see [Roadmap](docs/ROADMAP.md)).

## What's proven

`make verify` checks both legs (exit 0):

- **SAW (C ≡ Cryptol)** — bit-for-bit:
  - The `reduce.c` layer: `montgomery_reduce` (`−2³¹·Q ≤ a ≤ Q·2³¹`), `reduce32` (`a ≤ 2³¹−2²²−1`),
    `caddq`, `freeze` — these also assert no signed-overflow UB in range.
  - The forward NTT `ntt(a[256])`, under two's-complement wrapping (`-fwrapv`). This is functional
    equivalence for all inputs; overflow-freedom is proven separately in Isabelle (below).

  A mutation test confirms the reduce proof is non-vacuous, and CI diffs the lifted Isabelle model
  against the Cryptol model SAW checks.
- **Isabelle (model ≡ spec)** — the whole `reduce.c` layer, no `sorry`/`oops`:
  - `montgomery_reduce` meets `is_montgomery_reduction` (`2³²·r ≡ a (mod Q)`, `−Q < r < Q`) on
    `−2³¹·Q ≤ a < 2³¹·Q`.
  - `caddq` (residue-preserving, maps `[−Q,Q)` into `[0,Q)`); `reduce32` (residue-preserving, output
    in the true window `[−6283009, 6283008]`) on `a ≤ 2³¹−2²²−1`; `freeze = caddq∘reduce32` (output
    in `[0,Q)`), proven compositionally.
- **Isabelle (forward-NTT overflow-freedom)** — `ntt_overflow_free`, no `sorry`/`oops`: for inputs
  with every coefficient in `±(2³¹−2²⁷)`, the model NTT keeps every coefficient `< 2³¹` through all
  8 levels, so **no `int32` add/sub overflows** and every `montgomery_reduce` input stays in range.
  This is the coefficient-bound composition the `-fwrapv` proof sidesteps — proven by induction over
  the 8 levels (one per-level lemma iterated, montgomery output bound `|t| < Q`), not by SAW
  unrolling. The C-side claim (the reference NTT has no signed-overflow UB) follows by composing this
  with the `-fwrapv` C≡model equivalence; that last bridge is an argued meta-step, not separately
  mechanized (see [`docs/ASSUMPTIONS.md`](docs/ASSUMPTIONS.md), Roadmap v1.5).

Chained with the SAW leg, this gives C ≡ spec for the full `reduce.c` arithmetic layer (each function
computes a correct residue mod Q within its proven output window), plus a machine-checked
coefficient-bound / overflow-freedom result for the forward NTT.

While doing this we found two off-by-one errors in PQClean's reduce.c doc comments — `montgomery_reduce`
(strict bound fails at one unreachable endpoint; OF-1) and `reduce32` (documented `−6283008` low end is
reachably `−6283009` under its own one-sided precondition; OF-2). Both are doc/contract issues, not
miscomputations. See `docs/ASSUMPTIONS.md`.

## In progress: forward-NTT functional correctness

The shipped result above proves the forward NTT is overflow-free, not that it computes the *right*
transform. The next milestone (Tier 2, WIP, not yet gated in `make verify`) is functional
correctness: that the forward NTT computes the FIPS-204 negacyclic NTT, reusing the Cooley-Tukey
correctness argument from the Archive of Formal Proofs and stating it about the SAW-anchored lifted
model (not a hand-written one), so the seam to the C stays faithful.

Machine-checked so far (Isabelle, no `sorry`/`oops`, no `smt`; session builds exit 0):

- **All 8 per-layer butterfly laws**, word-exact: each output coefficient of a lifted NTT layer
  equals the FIPS-204 butterfly (add leg / subtract leg, twiddle `zetabrv[n div (2·len) + m0 + 1]`),
  reasoned at the native 32/64-bit word level through the `montgomery_reduce`-based reduction.
- **`fwd_as_bfly`** — the decoupling point: the whole lifted forward NTT equals an 8-fold *abstract*
  Cooley-Tukey butterfly transform on the integer-coefficient view (`cf (nttFwdAllRef w) n =
  fwdBfly (cf w) n` for in-range inputs). This separates the finished word-level seam from the
  remaining combinatorial argument.

Still to do: derive the bit-reversal permutation from the real twiddle schedule and chain onto the
negacyclic-NTT correctness bridge to land the full FIPS-204 equivalence. Until that lands this is an
intermediate result, and the Tier-2 session is intentionally excluded from CI gating. See
[`docs/ROADMAP.md`](docs/ROADMAP.md).

## Scope and limitations

The proof is correct and honestly scoped, but it targets the easy function. Concretely:

- `montgomery_reduce` is the least bug-prone thing in the stack — branch-free, two multiplies and a
  shift, unchanged in pq-crystals for years. ML-DSA's real correctness risk is reduction-bound
  composition across the NTT/InvNTT (e.g. ePrint [2026/1032](https://eprint.iacr.org/2026/1032), an
  optimized-path overflow that passed test vectors; and the missing-reduction bug Apple's SAW work
  caught in ML-DSA InvNTT). A single-primitive proof cannot reach that. The forward NTT with
  coefficient-bound tracking is the next step.
- The verified range (`|a| ≤ 2³¹·Q ≈ 2⁵⁴`) is about 256× wider than anything ML-DSA feeds the
  function (call sites produce `≲ Q² ≈ 2⁴⁶`), which is why OF-1's endpoint never occurs in practice.
- `montgomery_reduce` is identical across ML-DSA-44/65/87, so the "-44" pin is cosmetic and the
  result holds for all three.
- This is reference C. The code that ships (AVX2/aarch64; OpenSSL, BoringSSL, AWS-LC; PQ Code Package
  `mldsa-native`) is different, and verified with other tools (CBMC, HOL-Light). Pointing this
  pipeline at `mldsa-native` is v2.

So: a working end-to-end pipeline on third-party reference C, plus two minor upstream doc fixes (OF-1,
OF-2). Not an ML-DSA assurance result.

## Background (if formal verification is new to you)

In May 2026 Apple open-sourced the [formal verification of `corecrypto`](https://github.com/apple/corecrypto/tree/2026-05),
the cryptography on Apple devices, covering ML-KEM and ML-DSA (FIPS 203/204). Formal verification here
means a machine-checked proof that the code computes what the spec says for every input, not just the
cases a test happens to hit. Apple used [Galois](https://github.com/GaloisInc/saw-script)'s SAW +
Cryptol and the [Isabelle](https://isabelle.in.tum.de/) prover, and caught bugs that testing had
missed. PQC-Assay applies the same public approach to third-party reference C.

## Pipeline

```
   target C subroutine
          │  (1) hand-translate
          ▼
   Cryptol model  ──(2) SAW: C ≡ Cryptol──►  ✔
          │  (3) cryptol-to-isabelle
          ▼
   Isabelle model ──(4) model ≡ FIPS spec──►  ✔ (reduce.c layer)
                                  ▲
                  spec written from FIPS 204; no Apple artifacts
```

Detail in [`docs/PIPELINE.md`](docs/PIPELINE.md).

## Reproduce

macOS on Apple Silicon (pinned toolchain; see `docs/ASSUMPTIONS.md`).

```bash
./scripts/setup.sh                   # install pinned SAW, Cryptol, Isabelle, cryptol-to-isabelle
./scripts/setup_isabelle_cryptol.sh  # AFP + build the SAW 'Cryptol' Isabelle session (slow, once)
make verify                          # both legs; non-zero exit = a proof failed
make saw                             # SAW leg only (fast, no Isabelle)
```

## Layout

| Path | What |
|------|------|
| `target/`  | The C under verification, with pinned provenance |
| `model/`   | Cryptol model of the primitives |
| `proof/`   | SAW scripts (C ≡ Cryptol) |
| `spec/`    | Isabelle spec + the equivalence proof |
| `docs/`    | Roadmap, assumptions, pipeline, writeup |
| `scripts/` | Toolchain setup and pipeline orchestration |

## Tools

SAW + Cryptol and `cryptol-to-isabelle` (saw-script 1.5.1) from Galois; Isabelle + AFP. The pipeline
structure follows Apple's published corecrypto approach; no Apple code or theories are used.

## License

Project code: [MIT](LICENSE). The vendored C in `target/` is PQClean/pq-crystals reference code (CC0;
see [`target/README.md`](target/README.md)). The Isabelle spec is original; no Apple artifacts are
included.
