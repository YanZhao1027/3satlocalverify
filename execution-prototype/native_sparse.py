#!/usr/bin/env python3
"""Experimental runtime port of OpenAI's disjoint-core SparseCountProgram.

Source for priority/select and childA/childB:
  OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DisjointReuse/
    SparsePriority.lean, DisjointSparsify.lean, SparseCountProgram.lean

The leaf evaluator here is an independently written exact memoized DPLL counter,
not the enormous formalized sqrt-logarithmic NativeLeafProgram. No claimed
2^o(n) running time follows from this prototype.
"""
import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import sys
from time import perf_counter
from typing import FrozenSet

Clause = FrozenSet[int]
Formula = FrozenSet[Clause]
EMPTY_CLAUSE: Clause = frozenset()


def literal_code(lit: int) -> int:
    # Identical to Encoding.literalCode for zero-based Fin n variables.
    return 2 * (abs(lit) - 1) + (1 if lit > 0 else 0)


def clause_key(clause: Clause) -> tuple[int, ...]:
    return tuple(sorted(map(literal_code, clause)))


def absorb(formula: Formula) -> Formula:
    # SAT.absorb: keep only clauses with no strict-subset clause in the family.
    cs = sorted(formula, key=lambda c: (len(c), clause_key(c)))
    antichain: list[Clause] = []
    for c in cs:
        if not any(d.issubset(c) for d in antichain):
            antichain.append(c)
    return frozenset(antichain)


def priority_select(formula: Formula, threshold: int) -> tuple[int, Clause] | None:
    # SparsePriority.select: smaller width first, then larger core.
    best: tuple[int, Clause] | None = None
    best_key: tuple[int, int] | None = None
    ordered = sorted(formula, key=clause_key)
    for clause in ordered:
        c = len(clause)
        if c < 2:
            continue
        lits = sorted(clause, key=literal_code)
        subsets: list[Clause] = []
        for h in range(1, c):
            subsets.extend(frozenset(t) for t in combinations(lits, h))
        for core in sorted(subsets, key=clause_key):
            key = (c, -len(core))
            if best_key is not None and key >= best_key:
                continue
            degree = sum(len(d) == c and core.issubset(d) for d in ordered)
            if degree >= threshold ** (c - len(core)):
                best = (c, core)
                best_key = key
    return best


def children(formula: Formula, width: int, core: Clause) -> tuple[Formula, Formula]:
    # Byte-for-byte set semantics of DisjointBranch.childA and childB,
    # using the same selected family, petals, negated units and SAT.absorb.
    selected = frozenset(c for c in formula if len(c) == width and core.issubset(c))
    remain = formula - selected
    petals = frozenset(c - core for c in selected)
    negate_core = frozenset(frozenset([-l]) for l in core)
    return absorb(remain | {core}), absorb(remain | petals | negate_core)


def assign_literal(formula: Formula, lit: int) -> Formula:
    return frozenset((c - {-lit}) for c in formula if lit not in c)


def exact_leaf_dpll(formula: Formula, n: int) -> int:
    # Count all assignments of the ambient n-variable universe. Even variables
    # absent from the formula contribute a factor of two when they become free.
    @lru_cache(maxsize=300000)
    def count(f: Formula, remaining: int) -> int:
        while True:
            if not f:
                return 1 << remaining
            if EMPTY_CLAUSE in f:
                return 0
            units = [next(iter(c)) for c in f if len(c) == 1]
            if not units:
                break
            lit = min(units, key=literal_code)
            f = assign_literal(f, lit)
            remaining -= 1
        occurrences: dict[int, int] = {}
        for c in f:
            for l in c:
                occurrences[abs(l)] = occurrences.get(abs(l), 0) + 1
        var = max(sorted(occurrences), key=occurrences.get)
        return count(assign_literal(f, var), remaining - 1) + count(assign_literal(f, -var), remaining - 1)
    return count(formula, n)


def parse_dimacs(path: Path) -> tuple[int, Formula, int]:
    header: tuple[int,int] | None = None
    clauses: list[Clause] = []
    current: list[int] = []
    for line in path.read_text().splitlines():
        parts = line.split()
        if not parts or parts[0] in ('c', '%'):
            continue
        if parts[0] == 'p':
            if header is not None or len(parts) != 4 or parts[1] != 'cnf':
                raise ValueError('invalid/duplicate p cnf header')
            header = (int(parts[2]), int(parts[3]))
            continue
        if header is None:
            raise ValueError('missing header before clauses')
        for tok in parts:
            lit = int(tok)
            if lit == 0:
                clauses.append(frozenset(current))
                current = []
            else:
                current.append(lit)
    if header is None or current:
        raise ValueError('missing header or terminating 0')
    n, m = header
    if n < 0 or m != len(clauses):
        raise ValueError('header clause count invalid')
    if any(abs(lit) > n for c in clauses for lit in c):
        raise ValueError('variable outside DIMACS universe')
    return n, frozenset(clauses), m


def brute_count(formula: Formula, n: int) -> int:
    return sum(all(any(bits[abs(l)-1] == (l > 0) for l in c) for c in formula)
               for bits in product((False, True), repeat=n))


def sparse_count(formula: Formula, n: int, threshold: int, max_nodes: int) -> tuple[int, dict]:
    pending = [formula]
    total = 0
    steps = 0
    branches = 0
    leaves = 0
    peak = 1
    leaf_calls = 0
    while pending:
        if steps >= max_nodes:
            raise RuntimeError(f'max_nodes={max_nodes} reached with {len(pending)} pending')
        current = pending.pop()
        selected = priority_select(current, threshold)
        if selected is None:
            total += exact_leaf_dpll(current, n)
            leaves += 1
            leaf_calls += 1
        else:
            a, b = children(current, *selected)
            pending.extend([b, a])
            branches += 1
        steps += 1
        peak = max(peak, len(pending))
    return total, {'steps': steps, 'branches': branches, 'leaves': leaves,
                   'maxPending': peak, 'leafDpllCalls': leaf_calls}


def main() -> int:
    parser=argparse.ArgumentParser(description='Experimental disjoint-core #SAT outer algorithm + exact DPLL leaf')
    parser.add_argument('cnf', nargs='+', type=Path)
    parser.add_argument('--threshold', type=int, default=2)
    parser.add_argument('--max-nodes', type=int, default=20000)
    parser.add_argument('--oracle', action='store_true', help='Check by independent brute force for n<=18')
    ns=parser.parse_args()
    if ns.threshold < 2 or ns.max_nodes < 1:
        parser.error('threshold must be >=2, max_nodes must be >=1')
    all_ok=True
    for path in ns.cnf:
        try:
            n, formula, declared_m = parse_dimacs(path)
            start=perf_counter()
            ans, stats=sparse_count(formula,n,ns.threshold,ns.max_nodes)
            seconds=perf_counter()-start
            record={'path':str(path),'n':n,'m':declared_m,'count':ans,**stats,'seconds':round(seconds,6)}
            if ns.oracle:
                if n > 18:
                    raise ValueError('brute force oracle refused for n>18')
                expected=brute_count(formula,n)
                record['reference']=expected
                record['result']='PASS' if ans==expected else 'FAIL'
                all_ok=all_ok and ans==expected
            print(json.dumps(record,sort_keys=True),flush=True)
        except Exception as e:
            print(json.dumps({'path':str(path),'error':str(e)},sort_keys=True),file=sys.stderr)
            all_ok=False
    return 0 if all_ok else 1

if __name__=='__main__':
    sys.exit(main())
