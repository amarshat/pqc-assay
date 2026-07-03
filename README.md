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
  <a href="https://doi.org/10.5281/zenodo.21178811"><img src="https://zenodo.org/badge/DOI/10.5281/zenodo.21178811.svg" alt="DOI"></a>
</p>

Machine-checking post-quantum reference C against its specification, using the
SAW → Cryptol → Isabelle pipeline.

PQC-Assay builds a reproducible refinement chain for the **unmodified PQClean reference C** for
ML-DSA (FIPS 204): fixed-width C semantics, through a SAW-anchored Cryptol model and a lifted
word-level Isabelle model, up to an independent FIPS-204 specification, with the machine arithmetic's
in-range preconditions proven separately. The toolchain (SAW → Cryptol → Isabelle) is the one Apple
used for its 2026 `corecrypto` work (see [Background](#background-if-formal-verification-is-new-to-you));
this project uses none of Apple's code or theories, and the Isabelle spec is written from FIPS 204.

Current scope is the `reduce.c` arithmetic layer (both legs) and the forward and inverse NTT: C≡Cryptol
functional equivalence, a machine-checked overflow-freedom / coefficient-bound result (forward), and
(in the `Tier2` / `Tier2_InvWork` sessions, both gated in `make verify`) full FIPS-204 functional-
correctness theorems for the lifted normal-domain transforms. The bridges linking those transforms back
to the montgomery-domain models the SAW C≡Cryptol legs check are now proven (`ntt_bridge` forward,
`invntt_bridge` inverse), so C → FIPS-204 forward NTT and C → FIPS-204 inverse NTT are each a single
machine-checked chain mod q, modulo the scoped `-fwrapv` no-UB assumption (see the claim table below).
Montgomery reduction is an
implementation device the NTT uses; it is not defined in FIPS 204. None of this is the
optimized/assembly code that ships in production (see [Roadmap](docs/ROADMAP.md)).

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

## Forward-NTT functional correctness (proven, gated in `make verify`)

The overflow-freedom result above does not say the forward NTT computes the *right* transform. That
theorem is now proven, in a separate Isabelle session (`Tier2`), no `sorry`/`oops`, no `smt`, build
exits 0:

```
theorem fwd_ntt_correct:
  bounded w  ⟹  k < 256  ⟹
    cf (nttFwdAllRef w) k = (∑ j<256. cf w j · ζ^((2·brv₈ k + 1)·j)) mod q      (ζ = 1753, q = 8380417)
```

The lifted forward NTT, at each output position `k`, computes the FIPS-204 negacyclic DFT coefficient
at the bit-reversed index `brv₈ k` — i.e. ML-DSA's natural-input → bit-reversed-output convention.
The statement is about the lifted **normal-domain** model `nttFwdAllRef` (a lift of a normal-domain
Cryptol NTT, machine-checked equal to its original recursive twiddle table, not a hand-written model).
The SAW C≡Cryptol leg checks the C against the **montgomery-domain** model; connecting that model to
`nttFwdAllRef` (montgomery ≡ normal, mod q) is the `work/Mont_Bridge.thy` work, now finished:
`ntt_bridge` proves `sint_seq (ntt w ! k) mod q = (∑ j<256. cf w j · ζ^((2·brv₈ k + 1)·j)) mod q`
where `ntt` is the montgomery model SAW checks the C against. So the two ends join into one chain.

How it is built (Isabelle, no holes):

- **`fwd_as_bfly`** — the lifted forward NTT equals an 8-fold abstract Cooley-Tukey butterfly transform
  on the integer-coefficient view (`cf (nttFwdAllRef w) n = fwdBfly (cf w) n`), decoupling the
  finished word-level seam from the combinatorial argument.
- **`inv_form`** — a closed-form stage invariant (the sub-DFT held after each layer), with exact
  `inv_form_lower` (additive butterfly leg) and `inv_form_upper` (subtractive leg, a congruence mod
  `q` using `ζ²⁵⁶ ≡ −1`).
- **`applyN_inv`** — induction over the 8 layers, discharging each step with the recursion lemmas and
  the per-layer twiddle closed form `z_closed` (`zetabrv[i] = ζ^(brv₈ i) mod q`). At layer 8 this is
  `fwd_ntt_correct`.

The route is self-contained (a direct closed-form negacyclic DFT), so it does not depend on aligning
with the recursive Cooley-Tukey transform in the Archive of Formal Proofs.

The inverse NTT (`Tier2_InvWork`) mirrors this for the Gentleman-Sande direction: `inv_as_bfly`
(the lifted `nttInvAllRef` is an 8-fold abstract GS transform `invBfly`), a closed-form stage invariant
`ginv_form` with exact `ginv_lower` (additive leg) and `ginv_upper` (subtractive leg, a congruence mod
`q`), and `applyG_inv` (induction over the 8 layers). The per-layer twiddle reduces to the normal table
via `gtwid_lo`/`gtwid_hi` (`±zt(2^(8−t)−1−hi)`), proven from the bit-reversal identity
`gz_brv`. At layer 8 this is `inv_ntt_correct`; composed with the montgomery-scale bridge
(`invntt_scale_bridge`) it is `invntt_bridge`.

Status: `Tier2` (forward) and `Tier2_InvWork` (inverse) are first-class `make` targets and part of
`make verify` (`lift-check saw isabelle tier2 tier2-inv`). The no-`sorry`/`oops`/`admit` gate runs over
all of `spec/` (including both) on every push (`saw.yml`); the full Tier2 + Tier2_InvWork *build* runs
in `verify.yml` (manual `workflow_dispatch`, like the rest of the Isabelle leg, because of CI cost).
The inverse NTT and its `256⁻¹` (= `mont/256`) normalization are now machine-checked (`invntt_bridge`),
and inverse overflow-freedom too (`invntt_overflow_free`, under the `|coeff| < Q` input window — tight,
because the Gentleman-Sande low leg doubles the bound per level). Still open: constant-time, and
scoping the `-fwrapv` ⇒ no-UB seam (the same argued meta-step the forward already relies on). See
[`docs/ROADMAP.md`](docs/ROADMAP.md).

### Claim status (forward-NTT chain)

What is and is not machine-checked, end to end. "Machine-checked" = a tool exited 0 on the stated
theorem this is built from; "argued" = a sound but un-mechanized meta-step; "assumed" = taken on faith
with justification in [`docs/ASSUMPTIONS.md`](docs/ASSUMPTIONS.md); "not claimed" = out of scope.

| Link in the chain | Status |
|---|---|
| `reduce.c` primitives (`montgomery_reduce`/`reduce32`/`caddq`/`freeze`) ≡ Cryptol | machine-checked (SAW + Z3) |
| C `ntt(a[256])` ≡ Cryptol montgomery `ntt` (under `-fwrapv` wrapping; functional) | machine-checked (SAW) |
| montgomery NTT overflow-freedom / coefficient bound | machine-checked (Isabelle `ntt_overflow_free`) |
| `-fwrapv` wrapping ⇒ no signed-overflow UB in the C | argued (meta-step, not mechanized) |
| Cryptol montgomery `ntt` lifts to Isabelle | machine-checked (cryptol-to-isabelle; builds) |
| montgomery lifted `ntt` ≡ normal `nttFwdAllRef` (mod q) | machine-checked (Isabelle `Mont_Bridge`, `mbfly0`..`mbfly7` composed) |
| normal `nttFwdAllRef` ≡ FIPS-204 forward NTT | machine-checked (Isabelle `fwd_ntt_correct`) |
| montgomery `ntt` ≡ FIPS-204 forward NTT (mod q), composed | machine-checked (Isabelle `ntt_bridge`) |
| C `invntt_tomont(a[256])` ≡ Cryptol montgomery `invntt` (under `-fwrapv` wrapping; functional) | machine-checked (SAW) |
| montgomery lifted `invntt` ≡ normal `nttInvAllRef` (mod q), incl. the `mont/256` scale | machine-checked (Isabelle `Rcong_invcore` + `invntt_scale_bridge`) |
| normal `nttInvAllRef` ≡ FIPS-204 inverse NTT (mod q) | machine-checked (Isabelle `inv_ntt_correct`) |
| montgomery `invntt` ≡ FIPS-204 inverse NTT (mod q), composed | machine-checked (Isabelle `invntt_bridge`) |
| inverse NTT overflow-freedom / coefficient bound (under `\|coeff\| < Q` input) | machine-checked (Isabelle `invntt_overflow_free`) |
| constant-time / side channels | not claimed |

With `ntt_bridge` (forward) and `invntt_bridge` (inverse) the two machine-checked ends join in both
directions: C → FIPS-204 forward NTT *and* C → FIPS-204 inverse NTT are each one connected
machine-checked chain mod q, with the only non-mechanized step the `-fwrapv` ⇒ no-UB meta-argument
(the "argued" row above). Both directions are also overflow-free (`ntt_overflow_free` /
`invntt_overflow_free`); the inverse needs the tight `|coeff| < Q` input window (a precondition, not a
gap — `256·(Q−1)` just fits int32). What is *not* claimed: that this is the hard or shipping code (it
is the reference C, and the field arithmetic is the easy primitive), or constant-time.

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
   Isabelle model ──(4) model ≡ FIPS spec──►  ✔ reduce.c layer
          │        ├─(4') montgomery ntt ≡ FIPS-204 forward NTT (mod q) ─► ✔ ntt_bridge
          │        └─(4'') montgomery invntt ≡ FIPS-204 inverse NTT (mod q) ─► ✔ invntt_bridge
          ▼
                  spec written from FIPS 204; no Apple artifacts
```

Steps (4') and (4'') close the forward- and inverse-NTT chains: `ntt_bridge` / `invntt_bridge` prove
the montgomery-domain models the SAW legs check the C against equal the FIPS-204 negacyclic DFT and its
inverse, mod q (the inverse montgomery-scaled by `mont/256`). The only non-mechanized link in either
chain is `-fwrapv ⇒ no signed-overflow UB` (see the claim table above).

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
