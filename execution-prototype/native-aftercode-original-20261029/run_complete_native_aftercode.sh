#!/usr/bin/env bash
# Bounded physically executed original afterCode. Rebuild source proof first.
# This command needs the pinned OpenAI/math 4.34.1 dependencies on Ubuntu.
set -euo pipefail
Q="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$Q/../.." && pwd)"
LOGROOT="$REPO/.native-code-assembly-logs"
mkdir -p "$LOGROOT"
mkdir -p "$Q"
EXPECTED_COMMIT="7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
ACTUAL_COMMIT="$(git -C "$HOME/eth-lean-check-20261027/openai-math" rev-parse HEAD)"
if [[ "$ACTUAL_COMMIT" != "$EXPECTED_COMMIT" ]]; then
  echo "Upstream OpenAI/math HEAD not pinned: $ACTUAL_COMMIT" >&2
  exit 3
fi
"$Q/check_native_kernel_bridge.sh"
source "$Q/../native-code-parameters-20261029/lean-env.sh"
export LEAN_PATH="$LEAN_PATH:$Q"
LOG="$(mktemp "$LOGROOT/complete-aftercode-XXXXXXXX.raw.log")"
echo "FULL_ORIGINAL_LOG=$LOG"
cd "$Q"
(
  ulimit -v 33554432
  /usr/bin/time -f 'WALL=%es MAX_RSS_KB=%MkB EXIT=%x' \
    timeout --signal=TERM --kill-after=12s 355 \
    lean --run NativeSourceFastMeterRunner.lean 5000000 68 0
) > "$LOG" 2>&1 || {
  tail -n 20 "$LOG" >&2
  echo "Original complete afterCode run failed/timeout; retained $LOG" >&2
  exit 21
}
grep -F 'FAST_METER_FINISHED_ORIGINAL_FULL_896_STACKS_PASS expectedZeroWordBits=5120003 sourceInstructionSteps=290560512' "$LOG" >/dev/null || exit 22
python3 "$Q/build_full_aftercode_results.py" --log "$LOG" --baseline "$Q/fast-meter-8m-audit.raw.txt" --out "$LOG.json"
python3 "$Q/validate_full_aftercode.py"
echo "FULL_NATIVE_AFTERCODE_SOURCE_QA_PASS; not full NativeLeafPreparation or high-query SAT"
