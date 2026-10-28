#!/usr/bin/env python3
"""Deterministic connected-3SAT oracle vs original Lean CRT and Walsh kernel."""
from __future__ import annotations
import ast, itertools, json, random, re, statistics, subprocess, time
from pathlib import Path

root=Path(__file__).resolve().parent
fixture_dir=root/'fixtures'/'random_connected'
fixture_dir.mkdir(parents=True, exist_ok=True)
rng=random.Random(202610280839)


def make_connected(n:int)->list[list[int]]:
    used=set()
    clauses=[]
    seen=set()
    first=rng.sample(range(1,n+1),3)
    clauses.append([v * rng.choice((-1,1)) for v in first]);seen.update(first)
    while len(seen)<n:
        new=list(set(range(1,n+1))-seen)
        fresh=rng.sample(sorted(new),min(2,len(new)))
        old=rng.sample(sorted(seen),3-len(fresh))
        vs=fresh+old
        rng.shuffle(vs)
        clauses.append([v*rng.choice((-1,1)) for v in vs])
        seen.update(vs)
    while len(clauses)<5:
        vs=rng.sample(range(1,n+1),3)
        clauses.append([v*rng.choice((-1,1)) for v in vs])
    return clauses


def is_connected(n:int,clauses:list[list[int]])->bool:
    g={v:set() for v in range(1,n+1)}
    for c in clauses:
        vs=[abs(v) for v in c]
        for v in vs:
            g[v].update(vs)
    seen={1};pending=[1]
    while pending:
        v=pending.pop()
        for w in g[v]:
            if w not in seen:
                seen.add(w); pending.append(w)
    return len(seen)==n


def oracle(n:int,clauses:list[list[int]]) -> dict:
    hist=[0]*6
    vals=[0]*n
    for a in itertools.product((False,True),repeat=n):
        bad=sum(not any((a[abs(l)-1] == (l>0)) for l in c) for c in clauses)
        hist[bad]+=1
        if bad==0:
            for i in range(n):
                vals[i]+=1 if not a[i] else -1
    return {'count':hist[0],'hist':hist,'walsh0':hist[0],'walshUnits':vals}

records=[]
for i in range(48):
    n=8 if i<24 else 9
    for attempt in range(200):
        cs=make_connected(n)
        if len({tuple(sorted(map(abs,c))) for c in cs})==5:
            break
    else:
        raise AssertionError('could not generate five distinct clause scopes')
    assert len(cs)==5 and is_connected(n,cs)
    assert len({tuple(sorted(map(abs,c))) for c in cs})==5
    assert all(len(c)==3 and len(set(map(abs,c)))==3 for c in cs)
    path=fixture_dir/f'connected-{i:02d}-n{n}.cnf'
    path.write_text(f'c connected 3-SAT test {i}\np cnf {n} 5\n' +
        '\n'.join(' '.join(map(str,c))+' 0' for c in cs)+'\n')
    records.append({'path':str(path),'n':n,'m':5,'oracle':oracle(n,cs)})

(root/'connected-oracles.json').write_text(json.dumps(records,indent=2)+'\n')
start=time.perf_counter()
process=subprocess.run([str(root/'run_crt.sh'),*[r['path'] for r in records]],
                       text=True,capture_output=True,timeout=110)
(root/'connected-batch.stdout.log').write_text(process.stdout)
(root/'connected-batch.stderr.log').write_text(process.stderr)
assert process.returncode==0, f'Lean batch exit {process.returncode}: {process.stderr[-1000:]}'
lines=process.stdout.splitlines()
crts=[s for s in lines if s.startswith('CRT_FILE ')]
oracles=[s for s in lines if s.startswith('ORACLE ')]
timings=[s for s in lines if s.startswith('TIMING ')]
assert len(crts)==len(oracles)==len(timings)==len(records),(len(crts),len(oracles),len(timings))
crt_ms=[];oracle_ms=[]
for i,(record,crtorig,oracline,timing) in enumerate(zip(records,crts,oracles,timings)):
    path=record['path']; ground=record['oracle']
    assert crtorig.startswith(f'CRT_FILE {path} '),f'path mismatch at {i}'
    assert oracline==f'ORACLE {path} count={ground["count"]}',f'oracle mismatch at {i}'
    def extract(key:str,until:str)->str:
        pattern=f'{re.escape(key)}=(.*?){re.escape(until)}'
        m=re.search(pattern,crtorig)
        assert m,(key,i,crtorig)
        return m.group(1)
    assert extract('count',' hist')==str(ground['count'])
    assert ast.literal_eval(extract('hist',' mod7'))==ground['hist']
    assert ast.literal_eval(extract('mod7',' mod11'))==[v%7 for v in ground['hist']]
    assert ast.literal_eval(extract('mod11',' mod13'))==[v%11 for v in ground['hist']]
    assert ast.literal_eval(extract('mod13',' costs'))==[v%13 for v in ground['hist']]
    assert ast.literal_eval(extract('costs',' walsh0'))==[1937,2057,2117]
    assert extract('walsh0',' walshUnits')==str(ground['walsh0'])
    assert ast.literal_eval(extract('walshUnits',' result'))==ground['walshUnits']
    assert crtorig.endswith(' result=PASS')
    m=re.fullmatch(r'TIMING (.*?) oracle_ms=(\d+) crt_and_walsh_ms=(\d+)',timing)
    assert m and m.group(1)==path
    oracle_ms.append(int(m.group(2)));crt_ms.append(int(m.group(3)))
summary={
 'all_passed':True,'tests':len(records),'all_connected_and_all_active':True,
 'n8':24,'n9':24,'m':5,'width':3,
 'crt_moduli':[7,11,13], 'modulus_product':1001,
 'crt_callback_ops_per_instance':6111,
 'oracle_ms_median':statistics.median(oracle_ms),
 'crt_and_walsh_ms_median':statistics.median(crt_ms),
 'crt_and_walsh_ms_min':min(crt_ms),'crt_and_walsh_ms_max':max(crt_ms),
 'python_runner_wall_seconds':round(time.perf_counter()-start,3),
 'field_mod_coefficients_and_walsh_checked_independently':True,
 'no_asymptotic_speedup_claimed':True
}
(root/'connected-batch-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
