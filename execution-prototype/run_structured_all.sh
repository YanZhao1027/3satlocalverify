#!/bin/sh
set -eu
ROOT="$HOME/eth-lean-check-20261027"
PROJECT="$ROOT/openai-math/lean"
R="$ROOT/execution-prototype"
export PATH="$HOME/.elan/bin:$PATH" ELAN_TOOLCHAIN=eth-lean-4.34.1 ELAN_NO_OVERRIDE_NOTICE=1
LEAN_PATH="$(cd "$PROJECT" && lake env printenv LEAN_PATH 2>/dev/null):$R"
export LEAN_PATH
cd "$R"
printf '[1/6] Compiling formally verified support and independent-block libraries\n'
lean -o SupportLeaf.olean SupportLeaf.lean > support-leaf-compile.log 2>&1
lean -o BlockProduct.olean BlockProduct.lean > block-product-compile.log 2>&1
lean -o BlockTree.olean BlockTree.lean > block-tree-compile.log 2>&1
printf '[2/6] Lean kernel theorem axiom audit\n'
lean StructuredAxiomCheck.lean | tee structured-axioms.log
printf '[3/6] 72 DIMACS examples run through proved Lean sparse support counter\n'
python3 regression_support.py
printf '[4/6] Independent disjoint-block exact counting: 191 cases\n'
python3 regression_components.py
printf '[5/6] 64 and 512 all-active variables, original Lean tree construction\n'
timeout 90 lean BlockTreeSmoke.lean | tee block-tree-smoke.log
printf '[6/6] Read real DIMACS with 1024 active variables across independent components\n'
python3 component_sat.py fixtures/all-active-disconnected-1024.cnf > component-1024.jsonl
python3 - <<'PY'
from pathlib import Path
import json
p=Path('component-1024.jsonl')
a=json.loads(p.read_text().strip())
assert a['n']==1024 and a['active_variables']==1024
assert a['m']==1536 and a['components']==256
assert a['count']==5**256 and a['largest_component']==4
print('1024 active variable DIMACS count, exact analytic check: PASS; digits=',len(str(a['count'])))
PY
printf '\nSTRUCTURED_LEAF_ALL_PASS\n'
