#!/usr/bin/env bash
set -euo pipefail
R="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
E="$(cd "$R/.." && pwd)"
P="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH 2>/dev/null):$E:$E/general-ve-20261028:$R"
cd "$R"
for f in MemoComplexity PermutationCorrect PrimalWidthBarrier PaperScaleBridge WidthFixtures StarCountSmoke; do
  echo "LEAN_CHECK $f"
  timeout 35 lean -o "$f.olean" "$f.lean" >/dev/null
done
lean ComplexityAxioms.lean > complexity-axioms.log
python3 width_profile.py --out width-profile-results.json > width-profile.log
python3 complete_graph_witness.py > complete-graph.log
python3 complexity_regression.py > complexity-regression.log
lean WidthReverse.lean > width-reverse.log
lean StarCountSmoke.lean > star-count-smoke.log
printf 'ALL_COMPLEXITY_CHECKS_PASSED\n'
