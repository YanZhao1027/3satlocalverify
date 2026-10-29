#!/usr/bin/env python3
"""Expensive independent upstream StructuredCalls.compiled.start CODE probes.
This is a finite sampled audit, NOT 3036/3036 equivalence.
No timeout is counted as a pass; output written to ignored log directory.
"""
import concurrent.futures,os,pathlib,subprocess,time,json,sys
ROOT=pathlib.Path(__file__).resolve().parent
LOG=pathlib.Path(os.environ.get('ORIGINAL_SOURCE_PROBE_LOGDIR',str(ROOT.parent.parent/'.native-start-source-probe-logs')))
LOG.mkdir(parents=True,exist_ok=True)
labels=[3,41,677,678,3025]

def check(n):
 t=time.monotonic()
 try:
  r=subprocess.run(['lean','--run','NativeStartOriginalCodeProbe.lean',str(n)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,encoding='utf-8',errors='replace',timeout=57,env=os.environ)
  output=r.stdout
  ok=r.returncode==0 and f'ORIGINAL_CODE_MATCH label={n} equal=true' in output
  status='PASS' if ok else 'FAIL'
  exit_code=r.returncode
 except subprocess.TimeoutExpired as e:
  s=e.stdout
  output=(s.decode('utf-8',errors='replace') if isinstance(s,bytes) else (s or ''))
  status='TIMEOUT';exit_code=124
 f=LOG/f'original-start-label-{n}.log'
 f.write_text(output+'\nSTATUS='+status+'\n')
 return {'label':n,'status':status,'exit':exit_code,'seconds':round(time.monotonic()-t,2),'file':str(f)}

with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
 results=list(pool.map(check,labels))
for x in results:print('SAMPLE',x['label'],x['status'],x['seconds'],'sec',flush=True)
summary={'upstream':'Original `StructuredCalls.compiled LeafOuterProgram.start`.code',
 'claim':'5 sampled source opcode labels; not a universal proof','results':results}
p=LOG/'sampled-original-code-audit.json';p.write_text(json.dumps(summary,indent=2)+'\n')
print('SAMPLE_AUDIT_FILE',p,'PASS_COUNT',sum(x['status']=='PASS' for x in results),'of',len(results),flush=True)
if any(x['status']!='PASS' for x in results):sys.exit(2)
