#!/usr/bin/env python3
"""Independent connected-3SAT differential regression for the formally proved
Lean memoized bucket VE -> original OpenAI order-two Hermite/CRT chain.

48 connected n8/9 and 36 connected n10/11, with Python truth-table oracle
saved by earlier independent experiments. No external downloads.
"""
import ast,json,pathlib,re,statistics,subprocess,time

ROOT=pathlib.Path(__file__).resolve().parent
PAPER=ROOT.parent/'paper-kernel-20261028'
cases=[]
for filename in ('connected-oracles.json','primepower-oracles.json'):
    cases += json.loads((PAPER/filename).read_text())
assert len(cases)==84
start=time.perf_counter()
run=subprocess.run([str(ROOT/'run_memo_dual.sh'),'7','4',*[str(r['path']) for r in cases]],
                   capture_output=True,text=True,timeout=110)
(ROOT/'general-memo-batch.stdout.log').write_text(run.stdout)
(ROOT/'general-memo-batch.stderr.log').write_text(run.stderr)
assert run.returncode==0,f'Lean exited={run.returncode}: {run.stderr[-2500:]}'
lines=[s for s in run.stdout.splitlines() if s.startswith('DUAL_FILE ')]
times=[s for s in run.stdout.splitlines() if s.startswith('DUAL_TIME ')]
assert len(lines)==len(times)==len(cases),(len(lines),len(times),len(cases))
all_width=[];all_ms=[]
for case,row,clock in zip(cases,lines,times):
    m=re.fullmatch(r'DUAL_FILE (.+?) n=(\d+) m=(\d+) peakWidth=(\d+) prime=(\d+) precision=(\d+) nodes=(\d+) count=(\d+) coeffs=(\[.*?\]) scalarCallbacks=(\d+) extraValue=(\d+) oracle=(\S+) result=(\w+)',row)
    assert m,f'Unexpected format {row}'
    path,n,clauses,width,prime,precision,nodes,count,hist,ops,extra,oracle,result=m.groups()
    h=ast.literal_eval(hist)
    expected=case['oracle']['hist']
    assert path==str(case['path'])
    assert n==str(case['n']) and clauses=='5'
    assert int(width)<=18
    assert prime=='7' and precision=='4' and nodes=='3'
    assert result=='PASS' and count==str(case['oracle']['count'])
    assert h==expected
    assert oracle==count and int(ops)==989
    all_width.append(int(width))
    tm=re.search(r'\bms=(\d+)$',clock)
    assert tm,clock
    all_ms.append(int(tm.group(1)))
summary={'cases':len(cases),'passed':len(cases),'failed':0,
         'n8_9_cases':48,'n10_11_cases':36,
         'all_cases_connected':True,'all_variables_active':True,
         'modulus':2401,'crt_order':2,'nodes':3,
         'max_bucket_width':max(all_width),
         'median_lean_core_ms':statistics.median(all_ms),
         'max_lean_core_ms':max(all_ms),
         'wall_seconds':round(time.perf_counter()-start,3),
         'checked':'all six histogram coefficients and exact integer #SAT against independent Python truth-table oracles',
         'limitation':'not a worst-case subexponential SAT solver'}
(ROOT/'general-memo-batch-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
