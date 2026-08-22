#!/usr/bin/env bash
# Q-SEAL evidence-fragment reassembly (section 16 property 6: reassembly produces exactly the original
# evidence bytes or fails closed). Two checks:
#   1. cryptol + z3: the model QSEAL_Evidence.cry proves reassemble_round_trip and fail-closed on a
#      dropped or mis-sized fragment, and shows a no-completeness reassembler corrupts (:sat).
#   2. clang + SAW: the C reference qseal/ref/evidence.c equals the model, and the no-completeness
#      variant is rejected by the reassemble spec.
# Exits non-zero on any failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

if ! command -v cryptol >/dev/null 2>&1 || ! command -v saw >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$PATH"
fi
command -v cryptol >/dev/null 2>&1 || { echo "FAIL: cryptol not found (expected on PATH or in .tools/bin)"; exit 2; }
command -v saw     >/dev/null 2>&1 || { echo "FAIL: saw not found (expected on PATH or in .tools/bin)"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

# Timings from these scripts are only meaningful with the machine and toolchain named, so print them.
echo "== $(basename "$0") on $(uname -srm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || (grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2- | sed 's/^ //') || echo 'unknown CPU')"
echo "== toolchain: $(if command -v saw >/dev/null 2>&1; then saw --version | head -1 | sed 's/^/saw /'; else echo 'saw n/a'; fi); $(if command -v cryptol >/dev/null 2>&1; then cryptol --version | head -1; else echo 'cryptol n/a'; fi); $(if command -v proverif >/dev/null 2>&1; then proverif -help 2>&1 | head -1 | cut -d, -f1; else echo 'proverif n/a'; fi); $(${CLANG:-clang} --version | head -1)"

# 1. Model-level properties.
cd "$HERE/model"
OUT="$(cryptol -b /dev/stdin <<'EOF' 2>&1
:l QSEAL_Evidence.cry
:set prover=z3
:prove reassemble_round_trip
:prove dropped_fragment_rejected
:prove wrong_total_rejected
:sat bug_corrupts
EOF
)"
echo "$OUT" | grep -vE '^\s+(0x|\[0x|0,|\[0,)' | head -30

QED="$(printf '%s\n' "$OUT" | grep -c 'Q.E.D.' || true)"
SAT="$(printf '%s\n' "$OUT" | grep -c 'Satisfiable' || true)"
UNSAT="$(printf '%s\n' "$OUT" | grep -c 'Unsatisfiable' || true)"
CEX="$(printf '%s\n' "$OUT" | grep -c 'Counterexample' || true)"
if [ "$QED" -ne 3 ] || [ "$SAT" -ne 1 ] || [ "$UNSAT" -ne 0 ] || [ "$CEX" -ne 0 ]; then
  echo "FAIL: model check expected 3 Q.E.D. + 1 Satisfiable (the corrupting bug) + 0 Unsatisfiable/Counterexample; got QED=$QED SAT=$SAT UNSAT=$UNSAT CEX=$CEX"
  exit 1
fi
echo "OK: model reassembly properties (3/3 Q.E.D.) and the no-completeness reassembler corrupts (SAT)"

# 2. C reference == model.
mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/evidence.c" -o "$HERE/build/evidence.bc"
cd "$HERE/proof"
saw evidence.saw

# Optional: prove the same reference at a larger fragment arity. The checked-in instance is 4 fragments
# of 32 bytes, which is readable but far smaller than a deployed READ_EVIDENCE response (an ML-DSA-44
# signature alone is 2420 bytes). Set EVIDENCE_SCALE to "<frag-size>x<num-frags>" to generate and prove
# another instance from the same C, e.g. EVIDENCE_SCALE=255x4. Cost grows fast in the fragment count,
# since the permutation and placement scans are quadratic in it; see qseal/README.md for measured sizes.
if [ -n "${EVIDENCE_SCALE:-}" ]; then
  FS="${EVIDENCE_SCALE%x*}"; NF="${EVIDENCE_SCALE#*x}"
  echo ">> evidence at ${NF} fragments x ${FS} bytes = $((NF * FS)) bytes"
  python3 "$HERE/proof/gen_evidence_instance.py" "$FS" "$NF" "$HERE/build"
  "$CLANG" -c -emit-llvm -O0 -g -DQSEAL_FRAG_SIZE="$FS" -DQSEAL_NUM_FRAGS="$NF" -I "$HERE/ref" \
           "$HERE/ref/evidence.c" -o "$HERE/build/evidence_${FS}x${NF}.bc"
  cd "$HERE/build"
  SOUT="$(saw "evidence_${FS}x${NF}.saw")"
  echo "$SOUT"
  SOK="$(printf '%s\n' "$SOUT" | grep -c '^VERIFIED:' || true)"
  SMUT="$(printf '%s\n' "$SOUT" | grep -c '^MUTATION CAUGHT:' || true)"
  if [ "$SOK" -ne 1 ] || [ "$SMUT" -ne 1 ]; then
    echo "FAIL: scaled evidence instance expected 1 VERIFIED + 1 MUTATION CAUGHT; got VERIFIED=$SOK MUTATION=$SMUT"
    exit 1
  fi
  echo "OK: evidence reassembly verified at ${NF}x${FS}"
fi
