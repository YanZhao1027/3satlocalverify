#!/usr/bin/env python3
"""Random differential validation of disconnected exact counting. No external downloads."""
from __future__ import annotations
import itertools,json,random,time
from pathlib import Path
from component_sat import count_components
from native_sparse import parse_dimacs, brute_count
root=Path(__file__).resolve().parent
fixtures=root/'fixtures'
original=json.loads((root/'regression-summary.json').read_text())['input_cases']
rng=random.Random(2026102804)
records=[]
start=time.perf_counter()
for case in original:
    n,F,m=parse_dimacs(Path(case['path']))
    count,stats=count_components(F,n)
    assert count==case['expected']==brute_count(F,n),f'Original regression failed for {case["path"]}'
    records.append((case['path'],n,m,count,stats))
for i in range(120):
    n=1+i%18
    # Randomly split variables into independent blocks, with optional free variables.
    chosen=sorted(rng.sample(range(1,n+1),rng.randint(0,n)))
    blocks=[]
    for j in range(0,len(chosen),3):
        blocks.append(chosen[j:j+3])
    clauses=[]
    for block in blocks:
        for _ in range(rng.randint(0,7)):
            width=rng.randint(1,min(3,len(block)))
            vs=rng.sample(block,width)
            clauses.append(frozenset(v if rng.getrandbits(1) else -v for v in vs))
    if i%17==0: clauses.append(frozenset())
    if i%19==0 and chosen:
        clauses.append(frozenset([chosen[0]]));clauses.append(frozenset([-chosen[0]]))
    F=frozenset(clauses)
    actual,stats=count_components(F,n)
    expected=brute_count(F,n)
    assert actual==expected,f'Random component case {i} mismatch: {actual} vs {expected}'
    records.append((f'generated-{i:03d}',n,len(clauses),actual,stats))
for n in (64,512,1024):
    path=fixtures/f'all-active-disconnected-{n}.cnf'
    nn,F,m=parse_dimacs(path)
    actual,stats=count_components(F,nn)
    assert nn==n and actual==5**(n//4),f'Analytic block formula mismatch {n}'
    assert stats['active_variables']==n and stats['components']==n//4
    records.append((str(path),n,m,actual,stats))
summary={'tested':len(records),'passed':len(records),'failed':0,'original_cases':len(original),'new_random_cases':120,
         'analytic_all_active_cases':3,'max_ambient_dimension':max(r[1] for r in records),
         'max_active_dimension':max(r[4]['active_variables'] for r in records),
         'max_components':max(r[4]['components'] for r in records),
         'elapsed_seconds':round(time.perf_counter()-start,3)}
(root/'regression-components-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
