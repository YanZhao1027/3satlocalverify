#!/usr/bin/env bash
# Real original upstream afterCode compiled instruction stream on Ubuntu.
# No source-level skips, no oracle #SAT replacement. Time and memory may be high.
set -euo pipefail
Q="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$Q/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
test -d "$UPSTREAM"
PIN="7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
ACTUAL="$(git -C "$UPSTREAM/.." rev-parse HEAD)"
if [[ "$ACTUAL" != "$PIN" ]]; then
  echo "Pinned OpenAI math source mismatch: $ACTUAL" >&2
  exit 3
fi
source "$Q/../native-code-parameters-20261029/lean-env.sh"
export LEAN_PATH="$LEAN_PATH:$Q"
test -f "$REPO/execution-prototype/native-code-parameters-20261029/NativeFinishChunked.olean" || {
  echo "Build predecessor stage via check_native_code_stages.sh first" >&2; exit 4;
}
LOGROOT="$REPO/.native-code-assembly-logs"
mkdir -p "$LOGROOT"
WORKDIR="$(mktemp -d "$LOGROOT/original-aftercode-replay-XXXXXXXX")"
echo "ORIGINAL_AFTERCODE_REPLAY_LOGDIR=$WORKDIR"
cd "$Q"
for mod in NativeFinishOriginalDirect NativeFinishStepSemanticAudit NativeStepKernelProof; do
  if grep -E '\b(sorry|admit|native_decide)\b' "$mod.lean"; then
    echo "Unaccepted proof placeholder in $mod" >&2; exit 5;
  fi
  timeout --signal=TERM --kill-after=6s 75 lean -o "$mod.olean" "$mod.lean" > "$WORKDIR/$mod.build.log" 2>&1 || {
    tail -n 30 "$WORKDIR/$mod.build.log" >&2; exit 6;
  }
done
/usr/bin/time -f 'SEMANTIC_WALL=%es SEMANTIC_RSS_KB=%MkB' \
  timeout --signal=TERM --kill-after=6s 75 \
  lean --run NativeFinishStepSemanticAuditRunner.lean > "$WORKDIR/semantics.log" 2>&1 || {
    tail -n 30 "$WORKDIR/semantics.log" >&2; exit 7;
  }
/usr/bin/time -f 'WALL=%es RSS_KB=%MkB EXIT=%x' \
  timeout --signal=TERM --kill-after=8s 180 \
  lean --run NativeFinishOriginalDirectRunner.lean 1000000 8 > "$WORKDIR/original.log" 2>&1 || {
    tail -n 30 "$WORKDIR/original.log" >&2; exit 8;
  }
grep -q "NativeStepKernelProof.compact_set_agrees" "$WORKDIR/NativeStepKernelProof.build.log"
if grep -q "sorryAx" "$WORKDIR/NativeStepKernelProof.build.log"; then
  echo "Kernel theorem unexpectedly depends on sorryAx" >&2; exit 9
fi
python3 "$Q/verify_replay.py" --log "$WORKDIR/original.log" --semantics "$WORKDIR/semantics.log"
python3 "$Q/validate_original_aftercode.py"
python3 -m py_compile "$Q"/*.py
bash -n "$Q/check_original_aftercode.sh"
echo "ORIGINAL_AFTERCODE_SOURCE_QA_PASS; prefix unhalted; proof boundaries retained"
# Independent universal theorem (halt/goto/set); no sorry.
