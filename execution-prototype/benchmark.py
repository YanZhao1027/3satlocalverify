#!/usr/bin/env python3
"""Simple reproducible timing comparison; not an asymptotic benchmarking claim."""
import json, statistics
from pathlib import Path
from time import perf_counter
from native_sparse import parse_dimacs, sparse_count
root=Path(__file__).resolve().parent
cases=['random-3sat-18.cnf','all-pairs-32.cnf']
records=[]
for name in cases:
    path=root/'fixtures'/name
    n,formula,m=parse_dimacs(path)
    outputs=[]
    for threshold in (2,1000000):
        timing=[]
        for _ in range(9):
            start=perf_counter()
            answer,stats=sparse_count(formula,n,threshold,20000)
            timing.append(perf_counter()-start)
        outputs.append(answer)
        record={'formula':name,'n':n,'m':m,'threshold':threshold,'count':answer,
                'median_seconds':round(statistics.median(timing),7),
                'min_seconds':round(min(timing),7),
                **stats}
        records.append(record)
        print(json.dumps(record,sort_keys=True),flush=True)
    assert outputs[0]==outputs[1]
    if name=='all-pairs-32.cnf':
        assert outputs[0]==33
    if name=='random-3sat-18.cnf':
        assert outputs[0]==499
(root/'benchmark-summary.json').write_text(json.dumps(records,indent=2)+'\n')
