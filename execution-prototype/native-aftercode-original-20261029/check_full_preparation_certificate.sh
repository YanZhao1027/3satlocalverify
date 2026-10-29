#!/usr/bin/env bash
# Kernel-check full original native preparation's symbolic semantics, not HALT.
set -euo pipefail
Q="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$Q/../.." && pwd)"
UPSTREAM="$HOME/eth-lean-check-20261027/openai-math/lean"
PIN="7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
if [[ "$(git -C "$UPSTREAM/.." rev-parse HEAD)" != "$PIN" ]]; then
  echo "Original OpenAI/math revision mismatch" >&2
  exit 3
fi
source "$Q/../native-code-parameters-20261029/lean-env.sh"
export LEAN_PATH="$Q:$LEAN_PATH"
LOGROOT="$REPO/.native-code-assembly-logs"
mkdir -p "$LOGROOT"
WORK="$(mktemp -d "$LOGROOT/full-native-symbolic-XXXXXXXX")"
echo "G05_SYMBOLIC_OUTPUT=$WORK"
cd "$Q"
./check_primitive_kernel.sh > "$WORK/dependency-proofs.log" 2>&1 || {
  tail -n 40 "$WORK/dependency-proofs.log" >&2
  exit 4
}
timeout --signal=TERM --kill-after=8s 70 \
  lean -o NativeFullPreparationDirectCertificate.olean \
       NativeFullPreparationDirectCertificate.lean > "$WORK/stage5-kernel.log" 2>&1 || {
  tail -n 60 "$WORK/stage5-kernel.log" >&2
  exit 5
}
python3 - "$WORK/stage5-kernel.log" <<'PY'
import pathlib
import re
import sys
s=pathlib.Path(sys.argv[1]).read_text()
names={
    "original_full_code_table_is_source",
    "every_finite_full_preparation_prefix_exact",
    "every_full_preparation_step_exact",
    "original_full_program_entry"
}
found=re.findall(r"'IndependentFullPreparationDirectCertificate\.([^']+)' depends on axioms: \[([^\]]+)\]",s,re.S)
assert len(found)==4
assert {a for a,_ in found}==names
for _,axioms in found:
    assert {x.strip() for x in axioms.split(",")}=={"propext","Classical.choice","Quot.sound"}
print("G05_FULL_PREPARATION_SYMBOLIC_KERNEL_PASS theorems=4")
PY
if [[ "$#" -gt 0 ]]; then
  if [[ "$1" == "--sample" ]]; then
    /usr/bin/time -f 'ELAPSED=%es RSS_KB=%M EXIT=%x' \
      timeout --signal=TERM --kill-after=8s 75 \
      lean --run NativeFullPreparationLazyProbe.lean > "$WORK/stage5-nine-opcodes.log" 2>&1 || {
      tail -n 35 "$WORK/stage5-nine-opcodes.log" >&2
      exit 6
    }
    grep -q '^FULL_NATIVE_LAZY_SAMPLE_PASS originalSourceLabels=12539 entry=3 sites=9 noWholeTable=true$' \
      "$WORK/stage5-nine-opcodes.log"
    echo "G05_NINE_ORIGINAL_SITES_SAMPLE_PASS"
  fi
fi
python3 "$REPO/scripts/research_board.py" --check
echo "G05_FULL_PREPARATION_SYMBOLIC_QA_PASS; full original HALT not established"
