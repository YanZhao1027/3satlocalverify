#!/usr/bin/env python3
"""Static, NO-EVALUATION bucket-width model for bounded-width SAT formulas.

Matches the source MemoComplexity.lean support-only recurrence. Measures exact
numbers of table rows (2^remaining-scope-card) but NOT machine run time.
Never materializes an exponentially large factor; safe for high-width cases.
"""
from __future__ import annotations
import argparse,json,math,random,statistics,time
from pathlib import Path


def analyze(n:int,scopes:list[frozenset[int]],mode:str)->dict:
    remaining=set(range(n));fs=list(scopes)
    widths=[];rows=[];trace=[]
    while remaining:
        def bucket_info(v:int):
            linked=[s for s in fs if v in s]
            union=set().union(*linked) if linked else set()
            return union
        if mode=='canonical':
            v=min(remaining)
        elif mode=='reverse':
            v=max(remaining)
        elif mode=='min_degree':
            v=min(remaining,key=lambda k:(len(bucket_info(k)),k))
        elif mode=='min_fill':
            def fill_score(k):
                union=bucket_info(k)-{k}
                neighbor_edges=set()
                for scope in fs:
                    vs=sorted(scope-{k})
                    for i in range(len(vs)):
                        for j in range(i+1,len(vs)):
                            neighbor_edges.add((vs[i],vs[j]))
                fill=sum(1 for a in union for b in union if a<b and (a,b) not in neighbor_edges)
                return (fill,len(union),k)
            v=min(remaining,key=fill_score)
        else: raise ValueError(mode)
        union=bucket_info(v)
        kept=[s for s in fs if v not in s]
        survive=frozenset(union-{v})
        rowcount=1<<len(survive)
        widths.append(len(union));rows.append(rowcount)
        trace.append((v,len(union),len(survive)))
        fs=[survive]+kept
        remaining.remove(v)
    return {'mode':mode,'peak_bucket_width':max(widths,default=0),
            'peak_table_scope':max((r.bit_length()-1 for r in rows),default=0),
            'max_table_rows':str(max(rows,default=0)),
            'total_table_rows':str(sum(rows)),
            'trace':trace}


def star_clauses(n:int)->list[tuple[int,int,int]]:
    return [(0,i,i+1) for i in range(1,n-1)]


def chain_clauses(n:int)->list[tuple[int,int,int]]:
    return [(i,i+1,i+2) for i in range(0,n-2)]


def is_connected(n:int, scopes:list[frozenset[int]])->bool:
    seen={0};old=set()
    while seen!=old:
        old=seen.copy()
        for s in scopes:
            if s & seen: seen.update(s)
    return len(seen)==n


def random_scopes(n:int,m:int,seed:int)->list[frozenset[int]]:
    rng=random.Random(seed)
    scopes=[]; seen=set()
    while len(scopes)<m:
        s=frozenset(rng.sample(range(n),3))
        if s not in seen:
            seen.add(s);scopes.append(s)
    assert is_connected(n,scopes)
    return scopes


def profile_case(kind:str,n:int,seed:int=0)->dict:
    if kind=='star': raw=star_clauses(n)
    elif kind=='chain': raw=chain_clauses(n)
    else: raw=random_scopes(n,4*n,seed)
    scopes=[frozenset(c) for c in raw]
    assert all(len(s)==3 for s in scopes)
    assert is_connected(n,scopes)
    results=[analyze(n,scopes,mode) for mode in ('canonical','min_degree','min_fill')]
    for r in results: r.pop('trace')
    return {'kind':kind,'n':n,'clauses':len(scopes),'all_active':True,
            'connected':True,'initial_width':3,'seed':seed,'orders':results}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',default='width-profile-results.json')
    opts=ap.parse_args()
    t0=time.perf_counter()
    cases=[]
    for n in (16,32,48,64):
        cases.append(profile_case('chain',n))
        cases.append(profile_case('star',n))
        for seed in range(6):
            cases.append(profile_case('random',n,10000+n*100+seed))
    summary={}
    for n in (16,32,48,64):
        grp=[d for d in cases if d['kind']=='random' and d['n']==n]
        summary[str(n)]={mode: {'peak_width_median':statistics.median(next(o['peak_bucket_width'] for o in c['orders'] if o['mode']==mode) for c in grp),
                                 'peak_width_min':min(next(o['peak_bucket_width'] for o in c['orders'] if o['mode']==mode) for c in grp),
                                 'peak_width_max':max(next(o['peak_bucket_width'] for o in c['orders'] if o['mode']==mode) for c in grp)}
                          for mode in ('canonical','min_degree','min_fill')}
    result={'samples':len(cases),'note':'STATIC table row count only; no exponential factor tables materialized',
            'case_results':cases,'random_width_summary':summary,'elapsed_sec':round(time.perf_counter()-t0,4)}
    Path(opts.out).write_text(json.dumps(result,indent=2)+'\n')
    print('Verified static support profiles:',len(cases),'elapsed:',result['elapsed_sec'])
    for n in (16,32,48,64):
        star=next(c for c in cases if c['kind']=='star' and c['n']==n)
        chain=next(c for c in cases if c['kind']=='chain' and c['n']==n)
        def get(c,mode,key):return next(o[key] for o in c['orders'] if o['mode']==mode)
        print('n=',n,'chain width',get(chain,'canonical','peak_bucket_width'),
              'star canonical/min-fill',get(star,'canonical','peak_bucket_width'),
              get(star,'min_fill','peak_bucket_width'),
              'star largest predicted cached table',get(star,'canonical','max_table_rows'),
              'random canonical/minfill median',summary[str(n)]['canonical']['peak_width_median'],
              summary[str(n)]['min_fill']['peak_width_median'])
    print('RESULT_FILE',Path(opts.out).resolve())

if __name__=='__main__':main()
