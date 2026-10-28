#!/usr/bin/env python3
"""Independently compare every reachable label with original OpenAI source.
Run bounded Lean subprocesses in parallel. No solver answer or memoized oracle.
A timed-out chunk is an explicit FAILURE, never counted as evidence.
"""
from __future__ import annotations
import concurrent.futures, json, os, pathlib, re, subprocess, sys, time

ROOT=pathlib.Path(__file__).resolve().parent
COUNT=2856
CHUNK=int(os.environ.get('CHUNK_LABELS','160'))
WORKERS=int(os.environ.get('OPCODE_WORKERS','6'))
LIMIT=int(os.environ.get('OPCODE_CHUNK_TIMEOUT','240'))
assert 0<CHUNK<=500 and 0<WORKERS<=8 and 30<=LIMIT<=600
log=pathlib.Path(os.environ.get('NATIVE_EXEC_LOGDIR',str(ROOT.parent.parent/'.native-nonterminal-audit-logs')))
log.mkdir(parents=True, exist_ok=True)
chunks=[(start,min(CHUNK,COUNT-start)) for start in range(0,COUNT,CHUNK)]

def check(start:int,count:int):
    t=time.monotonic(); path=log/f'opcode-chunk-{start}-{count}.log'
    command=['lean','--run','LinearizedChunkDifferential.lean',str(start),str(count)]
    try:
        cp=subprocess.run(command,cwd=ROOT,env=os.environ,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,encoding='utf-8',errors='replace',timeout=LIMIT)
        out=cp.stdout
        matched=bool(re.search(rf'^ORIGINAL_OPCODE_CHUNK start={start} count={count} checked={count} mismatches=0 total={COUNT}$',out,re.M))
        ok=(cp.returncode==0 and matched)
        result={'start':start,'count':count,'status':'PASS' if ok else 'FAIL','exit_code':cp.returncode,'seconds':round(time.monotonic()-t,2)}
    except subprocess.TimeoutExpired as e:
        out=(e.stdout or b'').decode('utf-8',errors='replace') if isinstance(e.stdout,bytes) else (e.stdout or '')
        result={'start':start,'count':count,'status':'TIMEOUT','exit_code':124,'seconds':round(time.monotonic()-t,2)}
    path.write_text(out+'\nRESULT '+json.dumps(result)+'\n');result['log']=str(path)
    return result

results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=WORKERS) as pool:
    futures={pool.submit(check,start,count):(start,count) for start,count in chunks}
    for future in concurrent.futures.as_completed(futures):
        result=future.result();results.append(result)
        print('CHUNK',result['start'],result['count'],result['status'],'sec',result['seconds'],flush=True)
results.sort(key=lambda x:x['start'])
covered=[]
for x in results:
    if x['status']=='PASS':covered.extend(range(x['start'],x['start']+x['count']))
complete=covered==list(range(COUNT))
summary={'source':'Lean OpenAI program.code vs independent linear instructionArray','expected_labels':COUNT,'concurrent_workers':WORKERS,'timeout_per_chunk_seconds':LIMIT,'chunks':results,'all_2856_agree':complete,'total_passed_labels':len(covered)}
p=(log/'original-vs-linearized-full-opcode-audit.json');p.write_text(json.dumps(summary,indent=2)+'\n')
print('RESULT all_2856_agree=',complete,'passed=',len(covered),'of',COUNT,'audit=',p,flush=True)
if not complete:sys.exit(2)
