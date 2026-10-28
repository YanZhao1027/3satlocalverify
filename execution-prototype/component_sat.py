#!/usr/bin/env python3
"""Experimental exact #SAT for variable-disconnected CNFs.

Structural justification: Lean's BlockProduct.count_joined and
BlockTree.correct show exact multiplication for independent variable blocks.
This Python DIMACS parser, DSU decomposition and local renumbering are NOT
kernel-verified, so differential tests against independent oracles remain vital.
"""
from __future__ import annotations
import argparse,json,sys,time
from pathlib import Path
from native_sparse import parse_dimacs, sparse_count


def decompose(formula: frozenset[frozenset[int]], n: int):
    used={abs(l) for clause in formula for l in clause}
    if frozenset() in formula:
        return None, n-len(used), len(used)  # A contradictory empty clause has zero models.
    parent={v:v for v in used}
    def root(x):
        while parent[x] != x:
            parent[x]=parent[parent[x]]
            x=parent[x]
        return x
    def union(x,y):
        x,y=root(x),root(y)
        if x!=y:
            parent[max(x,y)]=min(x,y)
    for c in formula:
        ls=sorted({abs(l) for l in c})
        if ls:
            for v in ls[1:]:
                union(ls[0],v)
    components={}
    for v in sorted(used):
        components.setdefault(root(v),set()).add(v)
    grouped={k:set() for k in components}
    for c in formula:
        k=root(abs(next(iter(c))))
        grouped[k].add(c)
    subproblems=[]
    for k in sorted(components):
        vs=sorted(components[k])
        renumber={v:i+1 for i,v in enumerate(vs)}
        clauses=frozenset(frozenset((renumber[abs(l)] if l>0 else -renumber[abs(l)]) for l in c)
                          for c in grouped[k])
        subproblems.append((len(vs), clauses))
    return subproblems,n-len(used),len(used)


def count_components(formula,n,threshold=2,max_nodes=200000,max_component_vars=18):
    chunks,free,support=decompose(formula,n)
    if chunks is None:
        return 0,dict(components=0,free_variables=free,active_variables=support,
                      largest_component=0,branch_operations=0,leaf_calls=0,
                      total_assignments_explored_upper=0)
    total=1 << free
    branches=leaves=0
    candidates=0
    largest=0
    for s, sub in chunks:
        largest=max(largest,s)
        if s>max_component_vars:
            raise RuntimeError(f'component of {s} active variables exceeds --max-component-vars={max_component_vars}')
        value,stats=sparse_count(sub,s,threshold,max_nodes)
        total *=value
        branches += stats['branches']
        leaves += stats['leaves']
        candidates += stats['leaves'] * (1<<s)  # upper bound on leaf-candidate assignments
    return total,dict(components=len(chunks),free_variables=free,
                      active_variables=support,largest_component=largest,
                      branch_operations=branches,leaf_calls=leaves,
                      total_assignments_explored_upper=candidates)


def main():
    parser=argparse.ArgumentParser(description='Exact #SAT via disconnected variable blocks + DPLL leaves')
    parser.add_argument('cnf',nargs='+',type=Path)
    parser.add_argument('--threshold',type=int,default=2)
    parser.add_argument('--max-nodes',type=int,default=200000)
    parser.add_argument('--max-component-vars',type=int,default=18)
    ns=parser.parse_args()
    passed=True
    for path in ns.cnf:
        try:
            n,formula,m=parse_dimacs(path)
            t=time.perf_counter()
            total,st=count_components(formula,n,ns.threshold,ns.max_nodes,ns.max_component_vars)
            dt=time.perf_counter()-t
            print(json.dumps({'path':str(path),'n':n,'m':m,'count':total,
                              'elapsed_seconds':round(dt,6),**st},sort_keys=True),flush=True)
        except Exception as exc:
            print(json.dumps({'path':str(path),'error':str(exc)}),file=sys.stderr)
            passed=False
    return 0 if passed else 1

if __name__=='__main__':
    sys.exit(main())
