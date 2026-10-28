#!/usr/bin/env python3
"""Compare three *original source* CRT/Hermite interpolation modes on the same 48 connected 3SAT formulas."""
import ast,json,statistics,re,subprocess,time
from pathlib import Path
root=Path(__file__).resolve().parent
cases=json.loads((root/'connected-oracles.json').read_text())
start=time.perf_counter()
proc=subprocess.run([str(root/'run_hermite.sh'),*[c['path'] for c in cases]],
                   capture_output=True,text=True,timeout=110)
(root/'hermite-batch.stdout.log').write_text(proc.stdout)
(root/'hermite-batch.stderr.log').write_text(proc.stderr)
assert proc.returncode==0,f'Lean exit={proc.returncode}: {proc.stderr[-1000:]}'
lines=proc.stdout.splitlines()
hists=[s for s in lines if s.startswith('HIST ')]
res=[s for s in lines if s.startswith('HERMITE_FILE ')]
timings=[s for s in lines if s.startswith('HERMITE_TIMING ')]
assert len(hists)==len(cases)
assert len(res)==len(cases)*3 and len(timings)==len(cases)*3
costs={1:[1937,2057,2117],2:[953,977,989],3:[727,735,739]}
times={1:[],2:[],3:[]}
for i,c in enumerate(cases):
    path=c['path'];expected=c['oracle']
    h=hists[i]
    assert h==f'HIST {path} n={c["n"]} m=5 count={expected["count"]} histogram={expected["hist"]}',h
    for order in (1,2,3):
        j=i*3+order-1
        output=res[j]; t=timings[j]
        assert output==f'HERMITE_FILE {path} order={order} nodes={6//order} count={expected["count"]} costs={costs[order]} result=PASS',output
        m=re.fullmatch(r'HERMITE_TIMING (.+?) order=(\d+) ms=(\d+)',t)
        assert m and m.group(1)==path and int(m.group(2))==order,t
        times[order].append(int(m.group(3)))
results={'cases':len(cases),'all_passed':True,'all_connected_and_all_active':True,'m':5,
         'interpolation_modes':[], 'wall_seconds':round(time.perf_counter()-start,3)}
for order in (1,2,3):
    results['interpolation_modes'].append({'order':order,'nodes':6//order,
           'scalar_callback_ops':sum(costs[order]),
           'per_formula_ms_median':statistics.median(times[order]),
           'per_formula_ms_min':min(times[order]),
           'per_formula_ms_max':max(times[order])})
(root/'hermite-batch-summary.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
