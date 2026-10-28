#!/usr/bin/env python3
"""Compute the full CNF violation-count polynomial by factor variable elimination.

Given m distinct clauses on n variables, return coefficients of
  P_F(X) = sum_{a in {0,1}^n} X^(number of clauses falsified by a).

Unlike enumeration of the 2^n assignments, variable elimination has resource
usage exponential in induced factor width. It may still be exponential when
that width is large; max-width and operation counts are reported explicitly.
This Python implementation is independently tested, NOT extracted from Lean.
"""
from __future__ import annotations
import argparse, json, sys, time
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Dict, Tuple

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
from native_sparse import parse_dimacs

Poly=tuple[int,...]
Assignment=tuple[bool,...]

@dataclass(frozen=True)
class Factor:
    scope: tuple[int,...]
    table: dict[Assignment,Poly]


class Meter:
    def __init__(self):
        self.poly_mul=0
        self.poly_add=0
        self.local_assignments=0
        self.max_joint_scope=0
        self.max_table_entries=0
        self.steps=0
        self.factor_evaluations=0
        self.max_degree=0


def pnorm(p:list[int]|tuple[int,...])->Poly:
    r=list(p)
    while len(r)>1 and r[-1]==0:
        r.pop()
    return tuple(r)


def padd(a:Poly,b:Poly,meter:Meter)->Poly:
    meter.poly_add+=max(len(a),len(b))
    length=max(len(a),len(b))
    return pnorm([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(length)])


def pmul(a:Poly,b:Poly,meter:Meter)->Poly:
    if a==(0,) or b==(0,):return (0,)
    vals=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if not x:continue
        for j,y in enumerate(b):
            if not y:continue
            vals[i+j]+=x*y
            meter.poly_mul+=1
    return pnorm(vals)


def clause_factor(c:frozenset[int])->Factor:
    scope=tuple(sorted({abs(l) for l in c}))
    table={}
    for assignment in product((False,True),repeat=len(scope)):
        lookup=dict(zip(scope,assignment))
        satisfied=any(lookup[abs(l)]==(l>0) for l in c)
        table[assignment]=(1,) if satisfied else (0,1)
    return Factor(scope,table)


def choose_elimination(factors:list[Factor],remaining:set[int]):
    # Dynamic minimum-degree heuristic (bounded path width cases stay small).
    best=None
    for variable in sorted(remaining):
        scope=set()
        for f in factors:
            if variable in f.scope:
                scope.update(f.scope)
        score=(len(scope)-1,variable)
        if best is None or score<best[0]:
            best=(score,variable)
    return best[1]


def eliminate(factors:list[Factor],variable:int,meter:Meter)->list[Factor]:
    touched=[f for f in factors if variable in f.scope]
    rest=[f for f in factors if variable not in f.scope]
    if not touched:
        # No factor depends on this variable; summation gives factor 2.
        return rest+[Factor((),{(): (2,)})]
    union=sorted({v for f in touched for v in f.scope if v!=variable})
    meter.max_joint_scope=max(meter.max_joint_scope,len(union)+1)
    positions=[tuple((union.index(v) if v!=variable else -1) for v in f.scope) for f in touched]
    table={}
    for assignment in product((False,True),repeat=len(union)):
        meter.local_assignments+=1
        over_x=[]
        for x in (False,True):
            acc=(1,)
            for f,pos in zip(touched,positions):
                key=tuple(x if i==-1 else assignment[i] for i in pos)
                acc=pmul(acc,f.table[key],meter)
                meter.factor_evaluations+=1
            over_x.append(acc)
        value=padd(over_x[0],over_x[1],meter)
        meter.max_degree=max(meter.max_degree,len(value)-1)
        table[assignment]=value
    meter.steps+=1
    meter.max_table_entries=max(meter.max_table_entries,len(table))
    return rest+[Factor(tuple(union),table)]


def violation_histogram(n:int,F:frozenset[frozenset[int]],max_width:int=19,max_steps:int=200000):
    if n<0:raise ValueError('negative DIMACS dimension')
    used={abs(l) for c in F for l in c}
    if any(v<1 or v>n for v in used):raise ValueError('invalid variable')
    factors=[clause_factor(c) for c in sorted(F,key=lambda c:(len(c),sorted(c)))]
    meter=Meter()
    meter.max_table_entries=max((len(f.table) for f in factors),default=0)
    remaining=set(used)
    while remaining:
        x=choose_elimination(factors,remaining)
        scope=set(v for f in factors if x in f.scope for v in f.scope)
        if len(scope)>max_width:
            raise RuntimeError(f'induced width={len(scope)-1} exceeds cap {max_width-1}')
        if meter.steps>=max_steps: raise RuntimeError('max steps exceeded')
        factors=eliminate(factors,x,meter)
        remaining.remove(x)
    answer=(1,)
    for factor in factors:
        if factor.scope: raise AssertionError(f'non-constant factor {factor.scope}')
        answer=pmul(answer,factor.table[()],meter)
    free=n-len(used)
    result=tuple(x*(1<<free) for x in answer)
    assert sum(result)==1<<n,f'partition invariant broken, sum={sum(result)} vs 2^{n}'
    stats=dict(n=n,active_vars=len(used),free_vars=free,clause_count=len(F),
               induced_width=max(0,meter.max_joint_scope-1),
               max_factor_table_entries=meter.max_table_entries,
               eliminated_variables=meter.steps,
               local_assignments=meter.local_assignments,
               factor_evaluations=meter.factor_evaluations,
               polynomial_coeff_multiplications=meter.poly_mul,
               polynomial_coeff_additions=meter.poly_add,
               max_polynomial_degree=meter.max_degree,
               histogram_length=len(result))
    return result,stats


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('cnf',nargs='+',type=Path)
    ap.add_argument('--max-width',type=int,default=19)
    ap.add_argument('--out-dir',type=Path)
    ns=ap.parse_args()
    failed=False
    for path in ns.cnf:
        try:
            n,F,m=parse_dimacs(path)
            t=time.perf_counter()
            hist,stats=violation_histogram(n,F,ns.max_width)
            rec={'path':str(path),'hist':hist,'count':hist[0],
                 'ms':round((time.perf_counter()-t)*1000,3),'stats':stats}
            print(json.dumps(rec),flush=True)
            if ns.out_dir:
                ns.out_dir.mkdir(parents=True,exist_ok=True)
                (ns.out_dir/(path.stem+'.hist.json')).write_text(json.dumps(rec,indent=2)+'\n')
        except Exception as e:
            print(json.dumps({'path':str(path),'error':str(e)}),file=sys.stderr)
            failed=True
    return 1 if failed else 0

if __name__=='__main__':sys.exit(main())
