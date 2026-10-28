#!/usr/bin/env bash
# Check the independently published native-leaf bridge against PINNED upstream.
# Fails closed on Lean errors, timeouts, incomplete proofs and unexpected axioms.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
LOGDIR="${NATIVE_AUDIT_LOGDIR:-$REPO/.native-leaf-audit-logs}"
mkdir -p "$LOGDIR"
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$UPSTREAM" && lake env printenv LEAN_PATH 2>/dev/null):$REPO/execution-prototype:$HERE"
cd "$HERE"
mods=(NativeLeafCostBridge NativeLeafBudgetFeasible NativeLeafRealized)
for mod in "${mods[@]}"; do
  if grep -En '\b(sorry|admit|native_decide)\b' "$mod.lean" > "$LOGDIR/$mod.placeholders"; then
    echo "REJECTED untrusted placeholder found in $mod.lean" >&2
    cat "$LOGDIR/$mod.placeholders"
    exit 2
  fi
  echo "LEAN_BUILD $mod"
  /usr/bin/time -f "WALL=%es RSS_KB=%MkB" timeout 60 lean -o "$mod.olean" "$mod.lean" > "$LOGDIR/$mod.lean.log" 2>&1 || {
    echo "FAILED_LEAN $mod" >&2; tail -n 35 "$LOGDIR/$mod.lean.log" >&2; exit 3;
  }
done
echo 'LEAN_AXIOM_AUDIT'
timeout 60 lean NativeLeafCostAxioms.lean > "$LOGDIR/native-axioms.log" 2>&1 || {
  tail -n 35 "$LOGDIR/native-axioms.log" >&2; exit 4;
}
echo 'ORIGINAL_UPSTREAM_FINAL_AXIOM_AUDIT'
timeout 60 lean OriginalFinalAxioms.lean > "$LOGDIR/original-final-axioms.log" 2>&1 || {
  tail -n 35 "$LOGDIR/original-final-axioms.log" >&2; exit 5;
}
cat "$LOGDIR/native-axioms.log" "$LOGDIR/original-final-axioms.log" > "$LOGDIR/combined-axioms.log"
python3 - "$LOGDIR/combined-axioms.log" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text()
groups=re.findall(r"depends on axioms: \[(.*?)\]",s,re.S)
assert len(groups)==5,f'Expected 5 axiom reports, got {len(groups)}'
allowed={'propext','Classical.choice','Quot.sound'}
for g in groups:
  actual={x.strip() for x in g.split(',') if x.strip()}
  assert actual<=allowed,f'Unexpected axioms: {actual-allowed}'
print('AXIOMS_CHECKED',len(groups),'ALLOWED_ONLY',','.join(sorted(allowed)))
PY
echo 'NATIVE_LEAF_COST_BRIDGE_VERIFIED'
