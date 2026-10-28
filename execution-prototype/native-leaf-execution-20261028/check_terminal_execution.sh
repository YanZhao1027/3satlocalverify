#!/usr/bin/env bash
# Reproduce the actual original native-leaf TERMINAL-PATH executions and
# separate Lean proof that they are trace-equivalent to the unmodified leaf.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
LOGDIR="${NATIVE_EXEC_LOGDIR:-$REPO/.native-terminal-audit-logs}"
mkdir -p "$LOGDIR"
export PATH="$HOME/.elan/bin:$PATH" ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$UPSTREAM" && lake env printenv LEAN_PATH 2>/dev/null):$REPO/execution-prototype:$HERE"
cd "$HERE"
modules=(OriginalTerminalTraceProof TerminalBranchExecution TerminalTrace ReadyTerminalTrace \
  CompiledTerminalEquivalence OriginalMachineCostBridge TerminalResourceCertificate)
for mod in "${modules[@]}"; do
  if grep -En '\b(sorry|admit|native_decide)\b' "$mod.lean" > "$LOGDIR/$mod.placeholders"; then
    echo "REJECTED_PROOF_PLACEHOLDER $mod" >&2
    exit 2
  fi
  echo "LEAN_PROOF $mod"
  timeout 35 lean -o "$mod.olean" "$mod.lean" > "$LOGDIR/$mod.log" 2>&1 || {
    echo "FAILED_LEAN $mod" >&2; tail -n 32 "$LOGDIR/$mod.log" >&2; exit 3;
  }
done
for mod in NativeExecutionAxioms TraceAccountingAudit TerminalBatch; do
  echo "LEAN_AUDIT_OR_EXECUTION $mod"
  timeout 35 lean "$mod.lean" > "$LOGDIR/$mod.log" 2>&1 || {
    echo "FAILED_LEAN $mod" >&2; tail -n 25 "$LOGDIR/$mod.log" >&2; exit 4;
  }
done
python3 - "$LOGDIR/NativeExecutionAxioms.log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
found=re.findall(r'depends on axioms: \[(.*?)\]',s,re.S)
assert len(found)==12,f'Expected 12 proof axiom reports; got {len(found)}'
allowed={'propext','Classical.choice','Quot.sound'}
for x in found:
  actual={v.strip() for v in x.split(',') if v.strip()}
  assert actual<=allowed,f'Unexpected axiom: {actual-allowed}'
print('LEAN_AXIOMS_CHECKED',len(found),'ALLOWED_ONLY',sorted(allowed))
PY
for line in '("empty_3", true)' '("empty_5", true)' '("empty_clause_3", true)'; do
  grep -Fq "$line" "$LOGDIR/TraceAccountingAudit.log" || {
    echo "FAILED_PREFIX_ACCOUNTING $line" >&2; exit 5;
  }
done
python3 parse_terminal_batch.py "$LOGDIR/TerminalBatch.log"
python3 validate_terminal_results.py
printf 'NATIVE_TERMINAL_REPRODUCTION_PASS\n'
