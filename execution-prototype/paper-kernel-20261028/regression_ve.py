#!/usr/bin/env python3
"""Independent exact histogram validation of variable elimination.
  - 68 legacy SAT cases, 48 connected n8/9, 36 connected n10/11
  - deterministic n3..11 random CNFs with tautologies, empty clauses, duplicates
  - narrow chain n16/32/64/128/256: independent transfer-matrix oracle
"""
from __future__ import annotations
import itertools,json,random,statistics,time
from pathlib import Path
from sample_ve import violation_histogram
from native_sparse import parse_dimacs

ROOT=Path(__file__).resolve().parent
ROOT_OLD=ROOT.parent
rng=random.Random(202610280901)

def truth_table_hist(n:int,clauses:frozenset[frozenset[int]])->tuple[int,...]:
    counts=[0]*(len(clauses)+1)
    for a in itertools.product((False,True),repeat=n):
        k=sum(not any(a[abs(l)-1]==(l>0) for l in c) for c in clauses)
        counts[k]+=1
    return tuple(counts)

def trim(h):
    h=list(h)
    while len(h)>1 and h[-1]==0: h.pop()
    return tuple(h)

def chain_clauses(n:int)->list[list[int]]:
    cs=[]
    for i in range(1,n-1):
        cs.append([i if i%3==0 else -i,
                   (i+1) if i%4==0 else -(i+1),
                   (i+2) if i%5==0 else -(i+2)])
    return cs

def chain_transfer_hist(n:int,cs:list[list[int]])->tuple[int,...]:
    # Independent transfer-matrix DP on the last two truth values.
    # This implementation has no Factor class or elimination heuristic.
    def add(a,b):
        out=[0]*max(len(a),len(b))
        for i,x in enumerate(a):out[i]+=x
        for i,x in enumerate(b):out[i]+=x
        return out
    table={(a,b):[1] for a in (False,True) for b in (False,True)}
    for j,c in enumerate(cs):
        t={}
        for (a,b),p in table.items():
            for new in (False,True):
                bits={j+1:a,j+2:b,j+3:new}
                fail=not any(bits[abs(l)] == (l>0) for l in c)
                shifted=[0]*int(fail)+p
                target=(b,new)
                t[target]=add(t.get(target,[]),shifted)
        table=t
    total=[]
    for p in table.values():total=add(total,p)
    return tuple(total)

n_checked=0;original=0;connected=0;random_cases=0;chains=[]
start=time.perf_counter()
legacy=json.loads((ROOT_OLD/'regression-summary.json').read_text())['input_cases']
for case in legacy:
    n,F,_=parse_dimacs(Path(case['path']))
    h,stats=violation_histogram(n,F)
    assert h==trim(truth_table_hist(n,F)),f'legacy hist mismatch {case["path"]}'
    assert h[0]==case['expected']
    n_checked+=1;original+=1

for name in ('connected-oracles.json','primepower-oracles.json'):
    records=json.loads((ROOT/name).read_text())
    for record in records:
        n,F,_=parse_dimacs(Path(record['path']))
        h,stats=violation_histogram(n,F)
        assert h==trim(record['oracle']['hist']),f'connected histogram mismatch {record["path"]}: {h}'
        n_checked+=1;connected+=1

for i in range(120):
    n=3+i%9
    clauses=[]
    for _ in range(rng.randrange(0,18)):
        size=rng.randrange(0,5)
        c=[]
        for _ in range(size):
            v=rng.randrange(1,n+1)
            c.append(v if rng.getrandbits(1) else -v)
        clauses.append(frozenset(c))
    F=frozenset(clauses)
    h,stats=violation_histogram(n,F)
    oracle=trim(truth_table_hist(n,F))
    assert h==oracle,f'random histogram mismatch n={n} i={i}: {h} != {oracle}'
    n_checked+=1;random_cases+=1

for n in (16,32,64,128,256):
    cs=chain_clauses(n)
    path=ROOT/'fixtures'/f'connected-chain-{n}.cnf'
    path.write_text(f'c chain 3SAT all n variables active; treewidth <=2\np cnf {n} {len(cs)}\n'+
                    '\n'.join(' '.join(map(str,c))+' 0' for c in cs)+'\n')
    nn,F,m=parse_dimacs(path)
    t0=time.perf_counter()
    h,stats=violation_histogram(nn,F)
    ve_secs=time.perf_counter()-t0
    t1=time.perf_counter()
    oracle=chain_transfer_hist(n,cs)
    transfer_secs=time.perf_counter()-t1
    assert h==oracle,f'transfer-matrix oracle mismatch n={n}'
    assert stats['active_vars']==n and stats['induced_width']<=2
    chains.append({'n':n,'m':m,'sat_count':str(h[0]),'digits':len(str(h[0])),
                   'histogram_len':len(h),'max_induced_width':stats['induced_width'],
                   'elimination_assignments':stats['local_assignments'],
                   'poly_multiplications':stats['polynomial_coeff_multiplications'],
                   've_sec':round(ve_secs,5),'transfer_sec':round(transfer_secs,5)})
    n_checked+=1

summary={'total_cases':n_checked,'all_passed':True,
         'old_random_cases':original,'connected_test_cases':connected,
         'new_random_cases':random_cases,'independent_chain_cases':len(chains),
         'max_variables':max(a['n'] for a in chains),'chain_results':chains,
         'elapsed_seconds':round(time.perf_counter()-start,4),
         'worst_case_warning':'Variable elimination is exponential in induced width, not generally subexponential in n'}
(ROOT/'ve-regression-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
