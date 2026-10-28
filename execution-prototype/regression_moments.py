#!/usr/bin/env python3
"""Compare executable certified-Moments leaf + original sparse DFS with original Lean run and independent brute force."""
import json, pathlib, re, subprocess, time
root=pathlib.Path(__file__).resolve().parent
cases=json.loads((root/'regression-summary.json').read_text())['input_cases']
start=time.perf_counter()
p=subprocess.run([str(root/'run_moments.sh'), *[c['path'] for c in cases]],capture_output=True,text=True,timeout=130)
(root/'regression-moments.stdout.log').write_text(p.stdout)
(root/'regression-moments.stderr.log').write_text(p.stderr)
assert p.returncode==0,f'Moments Lean exit={p.returncode}; stderr={p.stderr[-1500:]}'
rows=[r for r in p.stdout.splitlines() if r.startswith('MOMENTS_FILE ')]
assert len(rows)==len(cases),(len(rows),len(cases))
branches=0
for idx,(row,case) in enumerate(zip(rows,cases)):
    match=re.search(r'^MOMENTS_FILE (.+?) n=(\d+) m=(\d+) count=(\d+) reference=(\d+) steps=(\d+) branches=(\d+) leaves=(\d+) maxPending=(\d+) ops=(\d+) ms=(\d+) result=(PASS|FAIL)$',row)
    assert match,f'parse mismatch at case {idx}: {row}'
    path,n,m,count,ref,steps,branches1,leaves,maxPending,ops,ms,status=match.groups()
    assert path==case['path'],f'path mismatch {idx}'
    actual={'count':int(count),'steps':int(steps),'branches':int(branches1),'leaves':int(leaves),'maxPending':int(maxPending)}
    for key,v in actual.items():
        assert v==case[key],f'{idx} {key} mismatch: moments={v} vs source={case[key]}'
    assert int(ref)==case['expected']==int(count),f'oracle mismatch {idx}'
    assert status=='PASS',f'Lean mismatch {idx}'
    assert int(ops) >= 0
    branches+=int(branches1)
summary={'cases':len(cases),'all_pass':len(cases),'branch_operations':branches,'matches_original_source_all_metrics':True,'elapsed_sec':round(time.perf_counter()-start,3)}
(root/'regression-moments-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
