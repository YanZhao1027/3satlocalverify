#!/usr/bin/env bash
# Recheck an authentic nonterminal CNF through original NativeTerminal and
# Native.loadLeaf; verify the independent linearized compiler's limited tests.
# This deliberately does NOT execute or claim the original high-query solver.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$ROOT/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
LOGDIR="${NATIVE_EXEC_LOGDIR:-$REPO/.native-nonterminal-audit-logs}"
mkdir -p "$LOGDIR"
export PATH="$HOME/.elan/bin:$PATH" ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$UPSTREAM" && lake env printenv LEAN_PATH 2>/dev/null):$REPO/execution-prototype:$REPO/execution-prototype/native-leaf-execution-20261028:$ROOT"
cd "$ROOT"

for mod in NonterminalPrefixProbe NonterminalSourceProof NativeNonterminalClassifier LinearizedCompiler LinearizedPrefixRunner; do
  echo "CHECK_PROOF_OR_MODULE $mod"
  if grep -En '\b(sorry|admit|native_decide)\b' "$mod.lean" > "$LOGDIR/$mod.placeholders"; then
    echo "FAIL: source contains a proof placeholder: $mod" >&2; exit 3
  fi
  timeout 40 lean -o "$mod.olean" "$mod.lean" > "$LOGDIR/$mod.build.log" 2>&1 || {
    echo "FAIL: module $mod" >&2; tail -n 30 "$LOGDIR/$mod.build.log" >&2; exit 4;
  }
done

for mod in NonterminalAxioms NonterminalBatch NonterminalAccountingAudit NonterminalClassifierSmoke; do
  echo "RUN_LEAN_CHECK $mod"
  timeout 45 lean "$mod.lean" > "$LOGDIR/$mod.eval.log" 2>&1 || {
    echo "FAIL: run $mod" >&2; tail -n 30 "$LOGDIR/$mod.eval.log" >&2; exit 5;
  }
done

python3 - "$LOGDIR/NonterminalAxioms.eval.log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
assert s.count('depends on axioms:')==9,s
matches=re.findall(r'depends on axioms: \[(.*?)\]',s,re.S)
assert len(matches)==9,len(matches)
allowed={'propext','Classical.choice','Quot.sound'}
for x in matches:
    actual={a.strip() for a in x.split(',') if a.strip()}
    assert actual<=allowed,actual-allowed
print('LEAN_STANDARD_AXIOMS_ONLY: 9 proofs')
PY

grep -Fq 'steps := 248' "$LOGDIR/NonterminalClassifierSmoke.eval.log"
grep -Fq 'zeroClause := false' "$LOGDIR/NonterminalClassifierSmoke.eval.log"
grep -Fq 'hasFormula := true' "$LOGDIR/NonterminalClassifierSmoke.eval.log"

grep -Fq '("nonterminal_unit_4000", true)' "$LOGDIR/NonterminalAccountingAudit.eval.log" || {
  echo 'FAIL: all-prefix occupied-stack-bits accounting discrepancy' >&2; exit 6;
}

python3 parse_nonterminal_batch.py "$LOGDIR/NonterminalBatch.eval.log"
python3 validate_nonterminal_results.py

echo 'RUN_CODE_DIFFERENTIAL: first 60 static labels'
timeout 50 lean --run LinearizedDifferential.lean 60 > "$LOGDIR/diff-first-60.log" 2>&1
# Make PASS string mandatory: do not mistake an empty output for agreement.
grep -Fq 'source_code_vs_flat_compared=60;mismatches=0' "$LOGDIR/diff-first-60.log"

echo 'RUN_STATE_DIFFERENTIAL: first 100 actual steps, full PC+register+stack equality'
timeout 60 lean --run OriginalVsLinearizedPrefix.lean 100 > "$LOGDIR/original-vs-linearized-100.log" 2>&1
grep -Fq 'original_bitprogram_vs_compact_array_exact_state;steps=100;equal=true' "$LOGDIR/original-vs-linearized-100.log"

echo 'RUN_HIGH_LABEL_DIFFERENTIAL: static position 2800'
timeout 35 lean --run LinearizedChunkDifferential.lean 2800 1 > "$LOGDIR/original-label-2800.log" 2>&1
grep -Fq 'ORIGINAL_OPCODE_CHUNK start=2800 count=1 checked=1 mismatches=0 total=2856' "$LOGDIR/original-label-2800.log"

echo 'NONTERMINAL_PREFIX_TEST_SUITE_PASS -- not the high-query algorithm'
