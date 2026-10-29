#!/usr/bin/env bash
# Rebuild universal exact-opcode and finite-fuel semantics theorems from source.
# Does not run the full 8M-step experiment or claim to solve #SAT.
set -euo pipefail
Q="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$Q/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
PIN="7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
if [[ "$(git -C "$UPSTREAM/.." rev-parse HEAD)" != "$PIN" ]]; then
  echo "Upstream OpenAI/math pin mismatch" >&2
  exit 3
fi
source "$Q/../native-code-parameters-20261029/lean-env.sh"
export LEAN_PATH="$Q:$LEAN_PATH"
test -f "$HOME/3satlocalverify/execution-prototype/native-code-parameters-20261029/NativeFinishChunked.olean" || {
  echo "Missing earlier source-stage dependencies; build first" >&2
  exit 4
}
LOGROOT="${PRIMITIVE_PROOF_LOGDIR:-$REPO/.native-code-assembly-logs}"
mkdir -p "$LOGROOT"
WORKDIR="$(mktemp -d "$LOGROOT/primitive-kernel-XXXXXXXX")"
echo "PRIMITIVE_KERNEL_LOGDIR=$WORKDIR"
cd "$Q"
for mod in NativeFinishOriginalDirect NativeCompactInterpreterProof NativeDirectTraceProof NativeAfterCodeDirectCertificate; do
  if grep -E '\b(sorry|admit|native_decide)\b' "$mod.lean"; then
    echo "Unaccepted proof placeholder in $mod" >&2
    exit 5
  fi
  echo "KERNEL_BUILD=$mod"
  timeout --signal=TERM --kill-after=7s 65 \
    lean -o "$mod.olean" "$mod.lean" > "$WORKDIR/$mod.output.txt" 2>&1 || {
      tail -n 35 "$WORKDIR/$mod.output.txt" >&2
      exit 6
    }
done
python3 "$Q/verify_kernel_axioms.py" \
  --interpreter "$WORKDIR/NativeCompactInterpreterProof.output.txt" \
  --trace "$WORKDIR/NativeDirectTraceProof.output.txt" \
  --specialization "$WORKDIR/NativeAfterCodeDirectCertificate.output.txt"
python3 "$Q/validate_primitive_kernel_archive.py"
bash -n "$Q/check_primitive_kernel.sh"
echo "UNIVERSAL_ORIGINAL_BITPROGRAM_KERNEL_QA_PASS; no full NativeCodeAssembly global equality claimed"
