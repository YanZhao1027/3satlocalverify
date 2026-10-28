#!/usr/bin/env python3
"""Differential tests of the proved support-compressed Lean DFS against
original uncompressed Lean results and an independent Python truth-table oracle."""
from pathlib import Path
from itertools import product
import json,re,subprocess,time
from native_sparse import parse_dimacs
root=Path(__file__).resolve().parent
cases=json.loads((root/'regression-summary.json').read_text())['input_cases']
large=[root/'fixtures'/f'sparse-universe-{n}.cnf' for n in (40,100,200,512)]
paths=[Path(c['path']) for c in cases] + large
start=time.perf_counter()
proc=subprocess.run([str(root/'run_support.sh'), *map(str,paths)], capture_output=True,text=True,timeout=100)
(root/'regression-support.stdout.log').write_text(proc.stdout)
(root/'regression-support.stderr.log').write_text(proc.stderr)
assert proc.returncode==0, f'Lean returned exit={proc.returncode}: {proc.stderr[-1200:]}'
rows=[line for line in proc.stdout.splitlines() if line.startswith('SUPPORT_FILE ')]
assert len(rows)==len(paths),(len(rows),len(paths))
match_count=0; branch_count=0; max_universe=0; max_support=0
for idx,(path,row) in enumerate(zip(paths,rows)):
    m=re.fullmatch(r'SUPPORT_FILE (.+?) n=(\d+) m=(\d+) active=(\d+) count=(\d+) reference=(\S+) steps=(\d+) branches=(\d+) leaves=(\d+) maxPending=(\d+) candidates=(\d+) maxSupport=(\d+) ms=(\d+) result=(\S+)',row)
    assert m, f'cannot parse {row}'
    filename,n,mcount,s,answer,ref,steps,branches,leaves,pending,candidates,peak,elapsed,status=m.groups()
    assert filename==str(path),f'filename mismatch {filename} != {path}'
    n=int(n); s=int(s); answer=int(answer)
    _,F,clause_count=parse_dimacs(path)
    assert clause_count==int(mcount)
    used=sorted({abs(l) for C in F for l in C})
    assert s==len(used)
    # Independent reference: enumerate only the used coordinates, no Lean evaluator involved.
    # Inactive coordinates are truly free and give the exact multiplicative factor.
    active_solutions=0
    for bits in product((False,True), repeat=len(used)):
        lookup=dict(zip(used,bits))
        active_solutions += all(any(lookup[abs(l)]==(l>0) for l in C) for C in F)
    expected=active_solutions*(1 << (n-len(used)))
    assert answer==expected,f'Independent truth table mismatch {path}: {answer} vs {expected}'
    if idx<len(cases):
        case=cases[idx]
        for key,value in [('count',answer),('steps',int(steps)),('branches',int(branches)),('leaves',int(leaves)),('maxPending',int(pending))]:
            assert value==case[key], f'Mismatch vs original Lean {path}: {key} {value} vs {case[key]}'
        assert ref==str(case['expected']) and status=='PASS'
    else:
        assert ref=='NOT_RUN' and status=='UNVERIFIED_EXTERNALLY'
    max_universe=max(max_universe,n);max_support=max(max_support,s)
    branch_count+=int(branches)
    match_count+=1
result={'tested':match_count,'passed':match_count,'failed':0,'original_lean_trace_matches':len(cases),'large_sparse_instances':len(large),'max_ambient_variables':max_universe,'max_active_support':max_support,'total_branch_operations':branch_count,'elapsed_seconds':round(time.perf_counter()-start,3),'oracle':'independent Python support truth table plus free-variable factor'}
(root/'regression-support-summary.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
