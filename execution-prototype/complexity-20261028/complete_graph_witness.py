#!/usr/bin/env python3
"""Construct 3-CNFs with complete primal interaction graph, hence first
bucket width n for EVERY elimination order. This is a structural width barrier,
not a lower bound on SAT algorithm runtime or instance hardness.

Hub variable 1 and every pair (i,j) of the other n-1 variables form a clause.
For any distinct vertices u,v, a clause contains both: u/v are adjacent in
primal graph; for n>=3 the graph is complete. No preliminary elimination order
can avoid a first bucket that includes every one of the n variables.
"""
from __future__ import annotations
import itertools,json,time
from pathlib import Path
from width_profile import analyze

ROOT=Path(__file__).resolve().parent
FIXTURES=ROOT/'fixtures'
FIXTURES.mkdir(exist_ok=True)
rows=[]
for n in (8,16,32,64):
    pairs=list(itertools.combinations(range(1,n),2))
    scopes=[frozenset((0,i,j)) for i,j in pairs]
    assert len(scopes)==(n-1)*(n-2)//2
    assert all(len(s)==3 for s in scopes)
    # For EVERY possible choice of first variable, union of all bucket clauses
    # must be all n variables. No heuristic can avoid the first big factor.
    for v in range(n):
        bucket=set().union(*(s for s in scopes if v in s))
        assert bucket==set(range(n)), (n,v,len(bucket))
    # Polarity chosen as deterministic function of pair/variable. The primal
    # factor graph and width lower bound are independent of this choice.
    clauses=[]
    for i,j in pairs:
        hub=1 if (i+j)%2 else -1
        x=(i+1) if i%2 else -(i+1)
        y=(j+1) if (i+j)%3 else -(j+1)
        clauses.append((hub,x,y))
    path=FIXTURES/f'complete-interaction-n{n}.cnf'
    path.write_text(f'c connected 3CNF complete primal interaction graph, n={n}\np cnf {n} {len(clauses)}\n'+
                    '\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
    # Actual static canonical/reverse profile; exact row counts, no allocation.
    a=analyze(n,scopes,'canonical')
    b=analyze(n,scopes,'reverse')
    assert a['peak_bucket_width']==n
    assert b['peak_bucket_width']==n
    assert int(a['max_table_rows'])==2**(n-1)
    assert int(b['max_table_rows'])==2**(n-1)
    rows.append({'n':n,'m':len(clauses),'all_first_buckets_width_n':True,
                 'smallest_first_table_rows':str(2**(n-1)),
                 'canonical_total_rows':a['total_table_rows'],
                 'reverse_total_rows':b['total_table_rows']})

out={'construction':'one hub plus every pair of remaining variables',
     'proof_argument':'Every pair of variables shares a 3-clause, so the primal graph is K_n and the first bucket always includes all n variables.',
     'structural_only':True,'does_not_prove_3SAT_hardness':True,'results':rows}
(ROOT/'complete-interaction-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
