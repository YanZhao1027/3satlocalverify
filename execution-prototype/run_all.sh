#!/bin/sh
set -eu
ROOT="$HOME/eth-lean-check-20261027"
R="$ROOT/execution-prototype"
cd "$R"
export PATH="$HOME/.elan/bin:$PATH" ELAN_NO_OVERRIDE_NOTICE=1
printf '\n[1] Original OpenAI Lean disjoint DFS 68-case regression, Python independent reference\n'
python3 regression.py
printf '\n[2] Native structural port vs original Lean exact trace matching\n'
python3 compare_traces.py
printf '\n[3] Original Lean disjoint branch pressure cases\n'
"$R/run_sparse.sh" "$R/fixtures/all-pairs-6.cnf" "$R/fixtures/all-pairs-8.cnf" "$R/fixtures/all-pairs-10.cnf" "$R/fixtures/all-pairs-12.cnf" > "$R/hard-cases.log" 2>&1
grep '^FILE ' "$R/hard-cases.log"
printf '\n[4] Original Lean Walsh finite search and certified moments computation\n'
cd "$ROOT/openai-math/lean"
lake env lean "$R/WalshSmoke.lean" > "$R/walsh-smoke.log" 2>&1
lake env lean "$R/MomentsSmoke.lean" > "$R/moments-smoke.log" 2>&1
printf 'Walsh samples:\n'; grep -E '^true|^some ' "$R/walsh-smoke.log"
printf 'Moments result: '; grep '^(' "$R/moments-smoke.log"
printf '\n[5] Native port vs independent brute force, analytic larger cases\n'
python3 "$R/native_sparse.py" --oracle "$R/fixtures/random-3sat-18.cnf" "$R/fixtures/all-pairs-16.cnf"
python3 "$R/native_sparse.py" "$R/fixtures/all-pairs-24.cnf" "$R/fixtures/all-pairs-32.cnf"
printf '\n[6] Small-case timing comparison\n'
python3 "$R/benchmark.py"
printf '\nALL SIX EXPERIMENT STAGES PASSED\n'
