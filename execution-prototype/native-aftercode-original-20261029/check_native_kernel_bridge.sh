#!/usr/bin/env bash
# Kernel-verifiable semantics for upstream primitive instructions.
set -euo pipefail
Q="$(cd "$(dirname "$0")" && pwd)"
LOG="$Q/../../.native-code-assembly-logs"
mkdir -p "$LOG"
source "$Q/../native-code-parameters-20261029/lean-env.sh"
export LEAN_PATH="$LEAN_PATH:$Q"
cd "$Q"
for mod in NativeCompactInterpreterProof NativeDirectTraceProof NativeSourceFastMeter; do
  echo "KERNEL_MODULE $mod"
  if grep -nE '^[[:space:]]*(sorry|admit|native_decide)([[:space:]]|$)' "$mod.lean"; then
    echo "Forbidden proof placeholder" >&2; exit 11;
  fi
  timeout --signal=TERM --kill-after=6s 75 lean -o "$mod.olean" "$mod.lean" > "$LOG/$mod.kernel.log" 2>&1 || {
    tail -n 25 "$LOG/$mod.kernel.log" >&2; exit 12;
  }
  if grep -E 'sorryAx|unsolved goals|error:' "$LOG/$mod.kernel.log"; then
    echo "Kernel audit not clean" >&2; exit 13;
  fi
done
grep -F "'IndependentNativeCompactProof.runOne_exact' depends on axioms: [propext, Classical.choice, Quot.sound]" \
  "$LOG/NativeCompactInterpreterProof.kernel.log" >/dev/null || exit 14
for theorem in all_fuel_exact bitStep_exact sourceArray_is_ofFn direct_table_fuel_exact; do
  grep -F "'IndependentNativeTraceProof.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" \
    "$LOG/NativeDirectTraceProof.kernel.log" >/dev/null || exit 15
done
grep -F "'IndependentNativeTraceProof.direct_table_replays_original_trace' depends on axioms:" \
  "$LOG/NativeDirectTraceProof.kernel.log" >/dev/null || exit 16
grep -F ' Classical.choice,' "$LOG/NativeDirectTraceProof.kernel.log" >/dev/null || exit 17
grep -F ' Quot.sound]' "$LOG/NativeDirectTraceProof.kernel.log" >/dev/null || exit 18
grep -F "'IndependentNativeFastMeter.cachedExpectedWords_correct' depends on axioms: [propext, Classical.choice, Quot.sound]" "$LOG/NativeSourceFastMeter.kernel.log" >/dev/null || exit 19
bash -n "$Q/check_native_kernel_bridge.sh"
echo "NATIVE_COMPACT_KERNEL_BRIDGE_PASS; universal runOne + all-fuel + original-trace, standard axioms only"
