#!/usr/bin/env bash
# Ubuntu reproduction of authentic ORIGINAL OpenAI finite nonterminal native
# hash-parameter arithmetic and real clause-count program. This is NOT the
# complete high-query SAT solver. Fails closed on timeouts/incorrect answers.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
LOGDIR="${NATIVE_CORE_LOGDIR:-$REPO/.native-core-cost-logs}"
mkdir -p "$LOGDIR"
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$UPSTREAM" && lake env printenv LEAN_PATH 2>/dev/null):$REPO/execution-prototype:$REPO/execution-prototype/native-leaf-execution-20261028:$REPO/execution-prototype/native-leaf-nonterminal-20261028:$HERE"
cd "$HERE"

for mod in CompactNative40 MeasureHashArithmetic HashArithmeticCases HashArithmeticFormal MeasureHashABI; do
  if grep -En '\b(sorry|admit|native_decide)\b' "$mod.lean" > "$LOGDIR/$mod.placeholders"; then
    echo "PROOF_PLACEHOLDER_REJECTED $mod" >&2; exit 3
  fi
  echo "LEAN_MODULE $mod"
  timeout --signal=TERM --kill-after=5s 32 lean -o "$mod.olean" "$mod.lean" > "$LOGDIR/$mod.build.log" 2>&1 || {
    tail -n 32 "$LOGDIR/$mod.build.log" >&2; exit 4;
  }
done

run_check () {
  local label="$1"; shift
  echo "LEAN_RUN $label"
  /usr/bin/time -f 'PROCESS_WALL=%es RSS_KB=%MkB' \
    timeout --signal=TERM --kill-after=5s 52 lean "$@" > "$LOGDIR/$label.log" 2>&1 || {
      echo "LEAN_CHECK_FAILED $label" >&2; tail -n 32 "$LOGDIR/$label.log" >&2; exit 5;
    }
}

run_check start-component-sizes --run StartComponentSizes.lean
run_check measure-clause --run MeasureNativeStages.lean clause 10000
run_check clause-count-audit --run ClauseCountAudit.lean
run_check measure-hash-arith --run MeasureHashArithmeticRunner.lean 50000
run_check hash-arith-variants --run HashArithmeticVariants.lean 100000
run_check hash-arith-code-audit --run HashArithmeticCodeAudit.lean 426 100
run_check hash-arith-original-fulltrace --run HashArithmeticCodeAudit.lean 426 3006
run_check hash-arith-space-audit --run HashArithmeticSpaceAudit.lean
run_check measure-hash-abi --run MeasureHashABIRunner.lean 20000
run_check abi-original-fulltrace --run HashABISourceAudit.lean 3585
run_check hash-arith-axioms HashArithmeticAxioms.lean

python3 build_native_core_results.py "$LOGDIR"
python3 validate_native_core_results.py

python3 - "$LOGDIR/hash-arith-axioms.log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
xs=re.findall(r'depends on axioms: \[(.*?)\]',s,re.S)
assert len(xs)==2,xs
allowed={'propext','Classical.choice','Quot.sound'}
for x in xs:
 actual={v.strip() for v in x.split(',') if v.strip()}
 assert actual<=allowed,f'Unexpected axiom: {actual-allowed}'
print('STANDARD_LEAN_AXIOMS_ONLY original plus independent concrete theorem')
PY

echo 'AUTHENTIC_NATIVE_HASH_ARITHMETIC_QA_PASS'
