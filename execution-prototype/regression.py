#!/usr/bin/env python3
"""Independent Python brute-force oracle for the original Lean SparseCountProgram.step prototype."""
from __future__ import annotations
import itertools, json, os, pathlib, random, re, subprocess, sys, time
ROOT=pathlib.Path.home()/'eth-lean-check-20261027'/'execution-prototype'
FIXTURES=ROOT/'fixtures'
FIXTURES.mkdir(exist_ok=True)
random_generator=random.Random(20261028)
cases=[]
for i in range(64):
    n=2+(i % 8)
    m=(i*7 + 3) % 23
    clauses=[]
    for j in range(m):
        k=1+random_generator.randrange(3)
        c=[]
        for _ in range(k):
            var=random_generator.randrange(1, n+1)
            c.append(var if random_generator.getrandbits(1) else -var)
        clauses.append(c)
    if i%11==0:
        clauses.append([])  # explicit contradiction by empty clause
    if i%13==0:
        clauses.append([1]); clauses.append([-1])
    # Multi-line DIMACS clause support is exercised every fifth case.
    cnfpath=FIXTURES/f'auto_{i:03d}.cnf'
    lines=['c deterministic randomized CNF', f'p cnf {n} {len(clauses)}']
    for j,c in enumerate(clauses):
        if j%5==0 and len(c)>1:
            lines += [' '.join(map(str,c[:1])), ' '.join(map(str,c[1:]+[0]))]
        else:
            lines += [' '.join(map(str,c+[0]))]
    cnfpath.write_text('\n'.join(lines)+'\n')
    def satisfied(bits):
        return all(any((bits[abs(l)-1] == (l>0)) for l in clause) for clause in clauses)
    expected=sum(satisfied(bits) for bits in itertools.product((False, True), repeat=n))
    cases.append({'path':str(cnfpath),'n':n,'m':len(clauses),'expected':expected})
# Add four hand-written edge cases from the smoke test.
for name, expected in [('shared-core.cnf', 2), ('contradiction.cnf', 0), ('empty-formula.cnf',16),('empty-clause.cnf',0)]:
    cases.append({'path':str(FIXTURES/name),'expected':expected})
start=time.perf_counter()
result=subprocess.run([str(ROOT/'run_sparse.sh'), *[c['path'] for c in cases]], capture_output=True, text=True, timeout=300)
(ROOT/'regression-lean.stdout.log').write_text(result.stdout)
(ROOT/'regression-lean.stderr.log').write_text(result.stderr)
assert result.returncode==0, f'Lean invocation failed with {result.returncode}: {result.stderr[-1500:]}'
lines=[l for l in result.stdout.splitlines() if l.startswith('FILE ')]
assert len(lines)==len(cases), f'expected {len(cases)} output rows but got {len(lines)}'
branch_count=0
max_steps=0
for case,line in zip(cases,lines):
    assert f'FILE {case["path"]} ' in line, line
    match=re.search(r'count=(\d+) reference=(\d+) steps=(\d+) branches=(\d+) leaves=(\d+) maxPending=(\d+) ms=(\d+) result=(PASS|FAIL)',line)
    assert match,line
    count,ref,steps,branches,leaves,pending,ms,status=match.groups()
    assert status=='PASS' and int(count)==int(ref)==case['expected'], f'wrong answer {case}: {line}'
    assert int(steps)==int(branches)+int(leaves), f'bad transitions {line}'
    branch_count+=int(branches)
    max_steps=max(max_steps,int(steps))
    case.update({'count':int(count),'steps':int(steps),'branches':int(branches),'leaves':int(leaves),'maxPending':int(pending),'lean_ms':int(ms)})
assert branch_count>0,'No real source branch exercised'
duration=time.perf_counter()-start
summary={'count':len(cases),'pass':len(cases),'failed':0,'source_branch_operations':branch_count,'max_transitions_in_a_case':max_steps,'lean_process_seconds':round(duration,3),'n_range':[min(c['n'] for c in cases if 'n' in c),max(c['n'] for c in cases if 'n' in c)],'input_cases':cases}
(ROOT/'regression-summary.json').write_text(json.dumps(summary,indent=2))
print('ALL TESTS PASSED')
print(json.dumps({k:v for k,v in summary.items() if k!='input_cases'},indent=2))
print('DETAILS',ROOT/'regression-summary.json')
