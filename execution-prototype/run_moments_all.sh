#!/bin/sh
set -eu
ROOT="$HOME/eth-lean-check-20261027"
R="$ROOT/execution-prototype"
PROJECT="$ROOT/openai-math/lean"
PATH="$HOME/.elan/bin:$PATH"
export PATH ELAN_TOOLCHAIN=eth-lean-4.34.1 ELAN_NO_OVERRIDE_NOTICE=1
LEAN_PATH="$(cd "$PROJECT" && lake env printenv LEAN_PATH 2>/dev/null):$R"
export LEAN_PATH
cd "$R"
printf '\n[1/5] Compile kernel-checked finite CNF <-> Moments bridge\n'
lean -o MomentsSAT.olean MomentsSAT.lean
printf '\n[2/5] Print axioms of bridge correctness, full DFS, exact cost\n'
lean MomentsAxiomCheck.lean | tee moments-axioms.log
printf '\n[3/5] Run 68 deterministic original vs reconnected Lean regressions\n'
python3 regression_moments.py
printf '\n[4/5] Run DIMACS examples in certified Moments sparse solver\n'
./run_moments.sh fixtures/shared-core.cnf fixtures/contradiction.cnf fixtures/empty-formula.cnf fixtures/empty-clause.cnf
printf '\n[5/5] Ten-variable 45-clause stress + operation accounting\n'
./run_moments.sh fixtures/all-pairs-10.cnf
if [ "${1:-}" = '--stress' ]; then
  printf '\n[Optional] Twelve-variable, 66-clause heavy case\n'
  ./run_moments.sh fixtures/all-pairs-12.cnf
fi
printf '\nFORMAL_MOMENTS_BRIDGE_ALL_PASS\n'
