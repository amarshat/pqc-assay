# The verification pipeline

This follows the structure of Apple's published corecrypto work, applied to third-party C. No Apple
code or theories are used.

```
 target C (target/pqclean/..., vendored, pinned)
     │ (1) hand-translate                      → model/cryptol/MLDSA_NTT.cry
     ▼
 Cryptol model
     │ (2) SAW llvm_verify: C bitcode ≡ Cryptol → proof/saw/mldsa_ntt.saw   (-fwrapv build)
     │ (2') SAW: no signed overflow, default build → proof/saw/ntt_nsw.saw, poly_nsw.saw
     ▼
 C ≡ Cryptol
     │ (3) cryptol-to-isabelle                  → spec/isabelle/MLDSA_NTT.thy (make lift-check)
     ▼
 lifted Isabelle model
     │ (4) Isabelle: model ≡ FIPS 204           → spec/isabelle/, spec/isabelle/tier2/
     ▼
 C (-fwrapv build) computes the FIPS 204 result mod q on the stated input windows;
 default-build status is per the README claim table
```

1. C to Cryptol is written by hand and can be wrong. Step 2 is what checks it against the
   actual C.
2. SAW loads `-O0` LLVM bitcode and proves each function computes its Cryptol term for every
   input in scope. Functional proofs run on the `-fwrapv` build. Step 2' runs the default build,
   where signed add, sub and mul carry LLVM's `nsw` (no signed wrap) flag and SAW must show none
   overflows; `scripts/check_wrapv_diff.sh` checks the two builds differ only in `nsw` and
   `inbounds` flags (it recompiles from source, so it assumes clang is deterministic). Every spec in
   `proof/saw`, `qseal`, `cve-anchor` and `esim-eid` has a paired mutant that must fail, except
   `ntt_nsw.saw` (one 12.5 h run, exempt, see its header) and three scripts outside the pipeline
   (two inverse-NTT probes and the Q-SEAL tactic-collapse demonstration); `make claim-lint` checks this. The Rust MIR proofs are not covered by it.
3. cryptol-to-isabelle (shipped with saw-script 1.5.1) lifts the Cryptol model into Isabelle.
   `make lift-check` regenerates the lifted theory and diffs it against the committed one, so this
   step is not maintained by eye.
4. Isabelle proves the lifted models against a spec written from FIPS 204:
   - `Assay_Equivalence.thy`: the `reduce.c` contracts and forward-NTT overflow freedom;
   - `tier2/work`, `invwork`, `signwork`, `invsignwork`: forward and inverse NTT ≡ the FIPS 204
     transforms mod q, on signed inputs;
   - `tier2/inv`: the NTT turns multiplication in `R_q` into pointwise products, with a model of
     the locale at the ML-DSA parameters;
   - `convwork`, `accwork`, `verwork`: the multiply, a row of `A*y`, and a row of verification's
     `A*z - c*t1*2^13`, in `R_q`.

The ML-KEM leg (`MLKEM_NTT.cry`, `mlkem_*.saw`, `spec/isabelle/kem/`) follows steps 1 to 4 for the
reduce layer and the forward NTT. It has no default-build step and its inverse is not done against
FIPS 203. Its SAW legs run in `saw.yml`, its Isabelle leg in `make verify`.

`make verify` runs the gated steps; see the README for the claim table and `docs/ASSUMPTIONS.md` for
what each step trusts.
