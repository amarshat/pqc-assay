# Auditing the HQC decapsulation artifact

A checklist for someone who did not write this code and wants to know whether the HQC
decapsulation results (A-HQC-DEC, A-HQC-DEC51, A-HQC-DEC51-F in `docs/ASSUMPTIONS.md`) hold. Each
item says what to run, what output to expect, and what to read by hand, because a SAW run that
exits 0 shows only that the C matches the script, not that the script says the right thing.

Times are for an Apple M2 Max; the fault maps are much slower than the proofs.

## 0. Tools

- `scripts/setup.sh` installs SAW 1.5.1 with its bundled solvers into `.tools/`. Check
  `.tools/bin/saw --version` reports 1.5.1.
- Bitcode is compiled with Homebrew `llvm@22` (clang 22.1.8), `-O0 -g`, target
  `x86_64-apple-darwin`. Other clang versions give different IR, and then the fault-site numbering
  in section 4 changes (the proofs should still pass).
- The C under test is vendored: `target/hqc` (v5.0.0) and `target/hqc-5.1` (v5.1.0), with the
  upstream commits recorded in `target/README.md`. Diff them against upstream before anything else.

## 1. The implicit-rejection proofs

| run | expect |
| --- | --- |
| `make hqc-decaps` | `VERIFIED` for v5.0.0 hqc-1, hqc-3, hqc-5; the three CVE-2024-54137 mutants refuted |
| `make hqc-decaps51` | `VERIFIED` for v5.1.0 hqc-1, hqc-3, hqc-5; mutants mask, nov, both refuted |
| `make hqc-decaps51-O2` | `VERIFIED` for the `-O2` unit |
| `make hqc-decaps51-hardened` | `VERIFIED` for v4, v4.1, v4.2, v4.3 |
| `make hqc-decaps51-spec` | `VERIFIED` against `SpecV51_{1,3,5}::Decaps`; spec mutations m1, m2 refuted; separator instance verified and the separator-17 mutant refuted |

`proof/hqc-decaps/logs/proof-times.txt` has the wall clock of each script.

What to read:

- [ ] Every `llvm_unsafe_assume_spec` in `proof/hqc-decaps/decaps51_1.saw` and `spec51_1.saw`.
  These are assumed, not proved. For each one, check against the C that the footprint (which
  pointers it reads, which it writes, how many bytes) is what the callee does, and that the return
  value it promises matches the callee: `hqc_pke_decrypt` is assumed to return 0 in `decaps51_*`
  and 0 or 1 in `spec51_*`.
- [ ] That `vect_compare` is proved (`llvm_verify`), not assumed, at the lengths used.
- [ ] The postcondition of `kem_spec`: the output buffer equals `decaps c dk` and the return value
  is 0 on every input. Nothing else about the caller's memory is claimed.
- [ ] `model/cryptol/hqc-decaps/DecapsV51_1.cry` was written from the C. `SpecV51_1.cry` was written
  from the HQC specification of 12 October 2026, page 43; compare it with the document line by line.
  The one place it follows the code rather than the document is the XOF.Init separator byte (A-HQC-DEC51
  item 9).
- [ ] The mutants are produced by `sed` or `awk` in the Makefile, and each recipe stops if the
  mutation did not change the file. `scripts/check_mutant_log.sh` requires each refutation to fail
  at the output postcondition, not at a type error or a setup failure.
- [ ] The primitives are uninterpreted (`w4_unint_yices`). A proof over them holds for real hashes;
  a counterexample may need hash values that a real hash produces only with negligible probability.

## 2. The CVE witness

`scripts/hqc_cve_witness.sh` downloads two hqc-128 archives from the HQC team's
site (30 October 2024 and 19 February 2025), checks their hashes, flips one bit of v in an honest
ciphertext, and compares the returned key byte for byte with the accept key and the rejection key,
both recomputed with the implementation's own decryption and hash. Expect the 2024 build to return
the accept key with status 0 and the 2025 build the rejection key with status -1, and both to
return the encapsulated key on the honest ciphertext. This is one input, not a proof. Also note the
2025 build reports the rejection in its return status; the witness checks key selection only.

## 3. Fault-map controls

- [ ] `make hqc-decaps51-faultctl`: with no fault and the region's `nsw`/`nuw` flags dropped, every
  variant still equals the specification; and the premises of P2, P2K and P2theta are satisfiable.
- [ ] `make hqc-decaps51-firedctl`: with the fault pinned to an instance that never executes
  (`fault_J == 1000000`), SAW proves the fired flag stays 0, for the P1 template and for the
  two-run template under the P2K premise. If either said FIRES here, every fired verdict would be
  meaningless. The target then rebuilds and cross-checks `proof/hqc-decaps/logs/sites.tsv`.

## 4. The fault maps

`make hqc-decaps51-faults` runs `scripts/hqc_decaps51_faultmap.sh` for shipped, v4, v4.1, v4.2 and
v4.3. It takes days on one machine; `JOBS=n` sets the parallelism and `RESUME=1` keeps finished
verdicts.

What to check:

- [ ] Site enumeration. `scripts/hqc_decaps_faults.py` writes one faulted copy of the IR per site
  and lists them in `MANIFEST.tsv`. Enumerate the sites yourself from `build/hqc-decaps51/dec_1<tag>.ll`
  (the region is `hqc_kem_decaps_internal` from after the zero-initialization of its locals to the
  end of the key selection; fault kinds V value, S store skip, C call skip, E loop exit) and compare
  your list with the manifest.
- [ ] Fault semantics. Diff a few `f???.ll` against the unfaulted `.ll`. The globals `fault_J` and
  `fault_v*` should only be read by the injected code; `fault_fired` should be set only when the
  chosen instance runs; the instance counter should live in the function's own stack frame.
- [ ] Verdict assignment. `scripts/hqc_decaps_faults_run.sh` and `scripts/hqc_decaps_ni_run.sh`
  turn SAW logs into verdicts. A refutation counts only if SAW failed at the postcondition; any other
  failure is ERROR and is never counted as a verdict. A run that hits the time limit is TIMEOUT.
- [ ] `scripts/hqc_decaps_sites.py` joins the verdicts into `proof/hqc-decaps/logs/sites.tsv`, one
  row per site and variant, and checks that each pass ran on exactly the sites it should: P3 and P2
  on the P1 failures, P2K and P2theta where P2 fails, the P1 fired check on every P1-resilient site,
  and each two-run fired check on every site where its property holds, with every fired check
  saying FIRES. It exits 1 if any of this fails. Its summary on stderr is:

```
shipped  sites  55  P1   4  P1-fail  50 (P3 12 held, 38 violated)  error 1  timeout 0  P2 13 P2K 1 P2T 20 P2K-fail 36  fired   4  two-run fired 34 checks at 34 sites
v4       sites 104  P1  79  P1-fail  22 (P3 13 held,  9 violated)  error 3  timeout 0  P2 15 P2K 1 P2T  0 P2K-fail  6  fired  79  two-run fired 16 checks at 16 sites
v4.1     sites 113  P1  89  P1-fail  20 (P3 12 held,  8 violated)  error 4  timeout 0  P2 13 P2K 1 P2T  0 P2K-fail  6  fired  89  two-run fired 14 checks at 14 sites
v4.2     sites 150  P1 121  P1-fail  19 (P3 12 held,  7 violated)  error 6  timeout 4  P2 13 P2K 0 P2T  0 P2K-fail  6  fired 121  two-run fired 13 checks at 13 sites
v4.3     sites 126  P1 102  P1-fail  19 (P3 12 held,  7 violated)  error 5  timeout 0  P2 13 P2K 0 P2T  0 P2K-fail  6  fired 102  two-run fired 13 checks at 13 sites
total    P1 fired 395  two-run fired 90 checks at 90 sites
```

  Every ERROR and TIMEOUT P1 verdict is a loop exit forced past the end (kind E).
- [ ] `proof/hqc-decaps/logs/faultmaps.tar.gz` has every per-site SAW log, verdict file and TSV of
  the maps (including the true-skip `_xs` and first-store `_st` runs), with home paths replaced by
  `$ROOT`. `scripts/hqc_decaps_sites.py <extracted>/faultmaps` reproduces `sites.tsv` byte for byte.
  The passes ran on two machines, an Apple M2 Max and an Apple M4 Pro; A-HQC-DEC51-F in
  `docs/ASSUMPTIONS.md` records which ran where. TIMEOUT verdicts depend on the machine.
- [ ] Spot-check verdicts by hand: pick a RESILIENT, a BROKEN and a PRESERVED site, regenerate the
  SAW script from its template with the `sed` in the runner's `attempt` function, and run it.

The P2K, P2theta and two-run fired passes were run as separate commands when the maps were made
and were added to `hqc_decaps51_faultmap.sh` afterwards with the same settings. The driver has not
been run end to end since that change.

## 5. Code generation

`make hqc-decaps51-cc` (`scripts/hqc_decaps51_cc.sh`) fetches upstream v5.1.0 (`hqc.c` is not
vendored), builds the key selection under clang 22 and Apple clang 14 at several optimization
levels, as a single unit and with LTO, on x86-64 and AArch64, and counts branches on the acceptance
mask. Output: `proof/hqc-decaps/logs/cc.txt`.

- [ ] The scanner matches instruction patterns (a test or cmp on the mask followed by a conditional
  jump; `cbz`, `cbnz`, `tbz`, `tbnz` on AArch64). A zero means those patterns are absent, not that
  the function is constant-time. Read the assembly of the rows that matter.
- [ ] The unpatched single unit (`tu`) with clang 22 at `-O3` must report a branch; if it reports 0,
  the scanner is broken.

## 6. Cost

`make hqc-decaps51-bench` (`scripts/hqc_decaps51_bench.sh`): paired rounds of shipped against the
hardened variant, same keys checked. Logs: `proof/hqc-decaps/logs/bench*.txt`. One machine, one
load level; expect the overhead to move by tenths of a percent between runs.

## Not covered by any of this

The PKE, the decoder, SHA-3 and the XOF are uninterpreted. The AVX2 build is not covered. Faults
are single faults in one region of one function, at hqc-1, on `-O0` bitcode; the compiler is
trusted. Timing is checked only by the pattern scan in section 5. Nothing here is a physical fault
experiment.
