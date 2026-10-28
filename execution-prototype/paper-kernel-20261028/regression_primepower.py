#!/usr/bin/env python3
"""Independent connected 10/11 variable #3SAT oracle vs source Z/49 Hermite CRT."""
from __future__ import annotations
import itertools,json,random,re,statistics,subprocess,time
from pathlib import Path

def is_connected(n:int, cs:list[list[int]]) -> bool:
    graph={v:set() for v in range(1,n+1)}
    for C in cs:
        vs=[abs(v) for v in C]
        for v in vs: graph[v].update(vs)
    reached={1};front=[1]
    while front:
        v=front.pop()
        for w in graph[v]:
            if w not in reached:
                reached.add(w);front.append(w)
    return len(reached)==n

def oracle(n:int,clauses:list[list[int]]) -> dict:
    hist=[0]*6
    for bits in itertools.product((False,True),repeat=n):
        k=sum(not any(bits[abs(v)-1]==(v>0) for v in c) for c in clauses)
        hist[k]+=1
    return {'count':hist[0],'hist':hist}


root=Path(__file__).resolve().parent
fixtures=root/'fixtures'/'primepower_connected'
fixtures.mkdir(parents=True,exist_ok=True)
rng=random.Random(202610280851)


def create(n:int) -> list[list[int]]:
    used=set()
    first=rng.sample(range(1,n+1),3)
    scopes=[first]
    used.update(first)
    while len(used)<n:
        missing=sorted(set(range(1,n+1))-used)
        fresh=rng.sample(missing,min(2,len(missing)))
        old=rng.sample(sorted(used),3-len(fresh))
        group=fresh+old
        rng.shuffle(group)
        scopes.append(group)
        used.update(group)
    assert len(scopes)==5
    return [[v*rng.choice([-1,1]) for v in scope] for scope in scopes]

cases=[]
for i in range(36):
    n=10 if i<18 else 11
    cs=create(n)
    assert is_connected(n,cs)
    assert len(set(abs(l) for C in cs for l in C))==n
    assert all(len(C)==3 and len(set(map(abs,C)))==3 for C in cs)
    filename=fixtures/f'conn-{i:02d}-n{n}.cnf'
    filename.write_text(f'c connected 3SAT all {n} variables active\np cnf {n} 5\n'+
                        '\n'.join(' '.join(map(str,c))+' 0' for c in cs)+'\n')
    cases.append({'path':str(filename),'n':n,'oracle':oracle(n,cs)})
(root/'primepower-oracles.json').write_text(json.dumps(cases,indent=2)+'\n')
t0=time.perf_counter()
p=subprocess.run([str(root/'run_primepower.sh'),*[c['path'] for c in cases]],
                 capture_output=True,text=True,timeout=110)
(root/'primepower-batch.stdout.log').write_text(p.stdout)
(root/'primepower-batch.stderr.log').write_text(p.stderr)
assert p.returncode==0, f'Lean exit={p.returncode}: {p.stderr[-1000:]}'
lines=p.stdout.splitlines()
hists=[x for x in lines if x.startswith('HISTP ')]
res=[x for x in lines if x.startswith('PRIME_FILE ')]
times=[x for x in lines if x.startswith('PRIME_TIMING ')]
assert len(hists)==len(cases) and len(res)==3*len(cases) and len(times)==3*len(cases)
costs={1:[1997,2057,2117],2:[965,977,989],3:[731,735,739]}
measurements={1:[],2:[],3:[]}
for i,c in enumerate(cases):
    pth=c['path'];o=c['oracle']
    assert hists[i]==f'HISTP {pth} n={c["n"]} m=5 count={o["count"]} histogram={o["hist"]}',hists[i]
    for mode in (1,2,3):
        j=i*3+mode-1
        exp=f'PRIME_FILE {pth} order={mode} nodes={6//mode} count={o["count"]} costs={costs[mode]} result=PASS'
        assert res[j]==exp,(res[j],exp)
        mt=re.fullmatch(r'PRIME_TIMING (.+) order=(\d+) ms=(\d+)',times[j])
        assert mt and mt.group(1)==pth and int(mt.group(2))==mode
        measurements[mode].append(int(mt.group(3)))
summary={'passed':len(cases),'total':len(cases),'n10':18,'n11':18,'all_3SAT_all_active_connected':True,
         'residue_rings':['ZMod49 nilpotent (7^2)','ZMod11 field','ZMod13 field'],
         'integer_crt_modulus_product':7007,
         'callback_ops':{str(mode):sum(costs[mode]) for mode in (1,2,3)},
         'median_ms':{str(mode):statistics.median(measurements[mode]) for mode in (1,2,3)},
         'elapsed_seconds':round(time.perf_counter()-t0,3),
         'all_coefficients_and_exact_counts_checked_vs_python':True}
(root/'primepower-batch-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
