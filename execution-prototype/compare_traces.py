#!/usr/bin/env python3
"""Compare native outer-branch steps to the canonical OpenAI Lean implementation."""
import json
from pathlib import Path
from native_sparse import parse_dimacs, sparse_count
root=Path(__file__).resolve().parent
cases=json.loads((root/'regression-summary.json').read_text())['input_cases']
branch_total=0
for case in cases:
    n,formula,m=parse_dimacs(Path(case['path']))
    answer,stats=sparse_count(formula,n,2,100000)
    assert answer==case['expected']==case['count'],f'answer mismatch for {case["path"]}'
    for key in ('steps','branches','leaves','maxPending'):
        assert stats[key]==case[key],f'trace mismatch {key} for {case["path"]}: {stats[key]} vs {case[key]}'
    branch_total+=stats['branches']
print(f'PASS: {len(cases)}/{len(cases)} native vs original Lean counts, step counts, branch counts, leaf counts and frontier maxima')
print(f'Original Lean branch operations matched: {branch_total}')
