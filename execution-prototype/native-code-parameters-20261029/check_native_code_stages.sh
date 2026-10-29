#!/usr/bin/env bash
# Ubuntu source-bit reproduction: parameters, two source searches,
# native row serialization, bounded nonhalting selector initialization.
# Requires build artifacts of earlier native-core-cost and native-start stages.
set -euo pipefail
Q="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$Q/../.." && pwd)"
LOGDIR="${NATIVE_CODE_LOGDIR:-$REPO/.native-code-assembly-logs}"
mkdir -p "$LOGDIR"
source "$Q/lean-env.sh"
cd "$Q"
for parent in "$REPO/execution-prototype/native-core-cost-20261028/PhysicalNumericLift.olean" \
  "$REPO/execution-prototype/native-start-20261029/NativeCanonicalLinked.olean"; do
  if ! test -f "$parent"; then
    echo "Missing original-source Lean predecessor: $parent" >&2
    echo 'First run check_native_physical_40x896.sh and check_native_canonical_start.sh' >&2
    exit 4
  fi
done
for m in NativeParametersCore NativeParametersPhysical NativeParametersMonolithic \
  NativeGraphSearchPhysical NativeTwoSearchStages NativeSerializerPhysical \
  NativeFinishSuffixProbe NativeFinishChunked; do
  echo "LEAN_SOURCE_MODULE $m"
  if grep -E '\b(sorry|admit|native_decide)\b' "$m.lean" > "$LOGDIR/$m.placeholders"; then
    echo "Proof placeholder in $m" >&2; exit 5
  fi
  timeout --signal=TERM --kill-after=6s 42 lean -o "$m.olean" "$m.lean" > "$LOGDIR/$m.build.log" 2>&1 || {
    echo "Lean module failed: $m" >&2; tail -n 25 "$LOGDIR/$m.build.log" >&2; exit 6;
  }
done
run_lean () {
  local key="$1"; shift
  echo "EXECUTE_ORIGINAL_SOURCE $key"
  /usr/bin/time -f 'PROCESS_WALL=%es RSS_KB=%MkB' \
    timeout --signal=TERM --kill-after=7s 73 lean --run "$@" > "$LOGDIR/$key.log" 2>&1 || {
      echo "Source runtime failed: $key" >&2; tail -n 30 "$LOGDIR/$key.log" >&2; exit 7;
    }
}
run_lean core-run-1-8 NativeParametersCoreRunner.lean 1 8 150000
run_lean physical-run NativeParametersPhysicalRunner.lean 50000
run_lean linked-run NativeParametersMonolithicRunner.lean 40000
run_lean parameter-boundary-audit NativeParametersBoundaryAudit.lean
run_lean graph-run NativeGraphSearchRunner.lean 150000
run_lean two-search-run NativeTwoSearchRunner.lean 150000
run_lean serializer-run NativeSerializerRunner.lean 180000
run_lean finish-prefix-120k NativeFinishSuffixRunner.lean 120000
run_lean finish-chunk-trial NativeFinishChunkedRunner.lean 1000000 2
python3 build_native_code_results.py "$LOGDIR"
python3 validate_native_code_results.py
python3 -m py_compile *.py
bash -n "$Q/check_native_code_stages.sh"
echo 'NATIVE_ORIGINAL_CODE_STAGE_QA_PASS; native assembly not proved globally, selector suffix not halted'
