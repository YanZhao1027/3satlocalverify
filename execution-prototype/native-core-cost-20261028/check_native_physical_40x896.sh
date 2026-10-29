#!/usr/bin/env bash
# Reproduce original physical 40x896 paper-leaf hash-parameter stage.
# Fail closed on every missing proof/trace/output or source opcode mismatch.
# This does NOT run the full HighQueryProgram or the final #SAT solver.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
LOGDIR="${PHYSICAL_HASH_LOGDIR:-$REPO/.native-physical-40x896-logs}"
mkdir -p "$LOGDIR"
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$UPSTREAM" && lake env printenv LEAN_PATH 2>/dev/null):$REPO/execution-prototype:$REPO/execution-prototype/native-leaf-execution-20261028:$REPO/execution-prototype/native-leaf-nonterminal-20261028:$HERE"
cd "$HERE"

for mod in FastLinearizedCompiler PhysicalPortMapProof MeasurePhysicalHash40Stream PhysicalNumericLift; do
  echo "LEAN_COMPILE_PROOF $mod"
  if grep -En '\b(sorry|admit|native_decide)\b' "$mod.lean" > "$LOGDIR/$mod.placeholders"; then
    echo "FAIL: forbidden Lean proof placeholder in $mod" >&2; exit 7
  fi
  timeout --signal=TERM --kill-after=6s 35 lean -o "$mod.olean" "$mod.lean" > "$LOGDIR/$mod.build.log" 2>&1 || {
    echo "FAILED_MODULE $mod" >&2; tail -n 25 "$LOGDIR/$mod.build.log" >&2; exit 8;
  }
done

run() {
  local name="$1"; shift
  echo "LEAN_RUN $name"
  /usr/bin/time -f 'ORIGINAL_PROCESS_WALL=%es RSS_KB=%MkB' \
    timeout --signal=TERM --kill-after=8s 73 lean "$@" > "$LOGDIR/$name.log" 2>&1 || {
      echo "FAIL: $name" >&2; tail -n 30 "$LOGDIR/$name.log" >&2; exit 9;
    }
}

run physical-axioms PhysicalProofAxioms.lean
run fast-abi-audit --run FastHashABISourceAudit.lean
run physical-numeric-verified --run PhysicalNumericRunner.lean 12000 verify
run physical-lockstep-audit --run PhysicalLockstepAudit.lean

echo 'LEAN_EXPORT original physical input and 637 original source instructions'
/usr/bin/time -f 'ORIGINAL_OPCODE_EXPORT_WALL=%es RSS_KB=%MkB' \
  timeout --signal=TERM --kill-after=8s 45 \
  lean --run ExportPhysicalOriginalOps.lean > "$LOGDIR/physical-original-opcodes.txt" 2> "$LOGDIR/export.log" || {
  echo 'FAIL: Original source opcode export' >&2; tail -n 25 "$LOGDIR/export.log" >&2; exit 10;
}
cmp "$LOGDIR/physical-original-opcodes.txt" physical-original-opcodes.txt || {
  echo 'FAIL: Original source code / physical frame differs from audited snapshot' >&2; exit 11;
}

python3 build_physical_results.py "$LOGDIR"
python3 validate_physical_results.py
python3 -m py_compile build_physical_results.py validate_physical_results.py
echo 'ORIGINAL_40X896_NATIVE_HASH_ABI_3585_STEP_AUDIT_PASS -- NOT the full SAT solver'
