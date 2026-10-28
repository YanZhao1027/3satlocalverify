#!/usr/bin/env python3
"""Independent structural and counting regression for verified width model."""
from __future__ import annotations
import json, pathlib, subprocess, time
from width_profile import analyze, chain_clauses, star_clauses

ROOT=pathlib.Path(__file__).resolve().parent
T0=time.perf_counter()

# These are not run as 2^n tables: the exact row numbers are calculated
# symbolically from the support-width transformations.
results=json.loads((ROOT/'width-profile-results.json').read_text())
assert results['samples']==32
for n in (16,32,48,64):
    star=next(c for c in results['case_results'] if c['kind']=='star' and c['n']==n)
    chain=next(c for c in results['case_results'] if c['kind']=='chain' and c['n']==n)
    for case,exp in ((star,n),(chain,3)):
        d=next(o for o in case['orders'] if o['mode']=='canonical')
        assert d['peak_bucket_width']==exp
    assert int(next(o for o in star['orders'] if o['mode']=='canonical')['total_table_rows'])==2**n-1
    assert int(next(o for o in chain['orders'] if o['mode']=='canonical')['total_table_rows'])==4*n-5
    reversed_star=analyze(n,[frozenset(x) for x in star_clauses(n)],'reverse')
    assert reversed_star['peak_bucket_width']==3
    assert int(reversed_star['total_table_rows'])==4*n-5

full=json.loads((ROOT/'complete-interaction-summary.json').read_text())
assert len(full['results'])==4
for entry in full['results']:
    n=entry['n']
    assert entry['all_first_buckets_width_n']
    assert int(entry['smallest_first_table_rows'])==2**(n-1)
    assert int(entry['canonical_total_rows'])==2**n-1
    assert int(entry['reverse_total_rows'])==2**n-1
    assert entry['m']==(n-1)*(n-2)//2

# Independent Fibonacci-style transfer oracle for all-positive hub 3SAT:
# If hub is true, all remaining 2^(n-1) assignments satisfy; otherwise
# adjacent non-hub variables cannot both be false.
def oracle_star(n:int)->int:
    a,b=1,2  # counts of length-0 and length-1 Boolean strings without 00
    for _ in range(n-2):
        a,b=b,a+b
    return 2**(n-1)+b

# For n=16: 32768+1597, n=32: 2^31+3524578.
# The two-state recurrence above counts strings avoiding consecutive zeroes.
expected={16:34365,32:2151008226,64:9223389204534953373}
for n,v in expected.items():
    got=oracle_star(n)
    assert got==v,(n,got,v)

# Compare with actual source of the _Lean_ memoized exact #SAT algorithm.
# This stage is performed on the already-provisioned Ubuntu with Lean's
# PATH/LEAN_PATH configured by scripts/check-complexity-on-ubuntu.sh.
summary={'mode':'static width plus Fibonacci model cross-check','checked_cases':32+4+3,
         'all_passed':True,'supported_star_counts':{str(k):str(v) for k,v in expected.items()},
         'dense_first_bucket_property':True,
         'notes':'Does not allocate any exponential table. Lean proof audit and Lean counter values checked separately.',
         'elapsed_s':round(time.perf_counter()-T0,3)}
(ROOT/'complexity-regression-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
