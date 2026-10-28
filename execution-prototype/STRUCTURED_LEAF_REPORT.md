# Lean-checked structure-aware exact #SAT leaf (2026-10-28)

Host: `zyubuntu-MS-7E51`, Ubuntu 24.04.5 LTS, Lean 4.34.1. This is an experimental next stage after `FORMAL_MOMENTS_BRIDGE.md`. All work was confined to `~/eth-lean-check-20261027/execution-prototype/`; OpenAI's original math repository stayed clean at `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.

## Purpose and status

The official ETH/SubexponentialSAT formal proof passed Comparator in the earlier independent check. Its full `NativeLeafProgram`/Walsh/CRT/`FiniteFallback` machine is still **not** extracted as an efficient native SAT solver. We have now built **two independent structural improvements**, both with general Lean correctness theorems, while expressly **not** claiming the paper's worst-case `2^o(n)` runtime.

1. Enumerate only variables that occur in the current CNF (support compression), multiplying by the full factor for unused variables.
2. Decompose syntactically independent blocks, count each separately, multiply exact results.

These optimizations can be spectacular when the instance has low support or many small components, but are not guaranteed to help a worst-case connected SAT formula.

## 1. Formally proved support-compressed leaf

Source: `SupportLeaf.lean`, imports original OpenAI `SparseCountProgram` transitively through `MomentsSAT`. New declarations:

- `activeVars F` = union of literal-variable sets of every clause.
- `countActive F` enumerates assignments only to `activeVars F`, then multiplies by `2^(n - card(activeVars F))`.
- `countActive_correct`: for every `n` and every `F : SAT.CNF (Fin n)`, `countActive F = SAT.count F`.
- `active_candidates_card`: exactly `2 ^ (activeVars F).card` candidate partial assignments are enumerated.
- `active_candidates_le_ambient`: never more candidates than ambient `2^n`.
- `sparseActiveStep_eq_source`, `sparseActiveRun_eq_source` and `sparseActiveRun_exact`: using `countActive` as the original DFS's leaf changes **no semantic state**. A finished run returns `SAT.count F`.

**Formal audit:** `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. No `sorry` or `admit` in the three new primary Lean modules.

`SupportSparseDimacs.lean` is a DIMACS reader and runnable wrapper for `sparseActiveStep`; `run_support.sh` executes it. It enforces ambient `n ≤ 512`, active support `≤ 15` for predictable testing and a 75-second limit. For small `n ≤ 12` it also computes the original exhaustive `SAT.count`; for larger dimensions, it prints `reference=NOT_RUN` (the Python regression runner provides the independent check). This wrapper does *not* have a separate theorem covering the parser; the core counting routine does.

**Measured local examples:**

| Ambient variables | Active variables | Count | Total leaf candidates | Lean internal per-CNF time |
| ---: | ---: | ---: | ---: | ---: |
| 40 | 2 | `824633720832` | 4 | about 1 ms |
| 100 | 5 | `237684487542793012780631851008` | 128 | about 5 ms |
| 200 | 5 | `301300883298560676664117892313967987972913061334273656619008` | 128 | about 5 ms |
| 512 | 5 | 154-digit exact Nat (stored in regression log) | 128 | successful |

The above timing deliberately excludes Lean's ~4.5-second import/startup cost and is measured by the runtime wrapper. The 512-variable example above has **only five active variables**, unlike the all-active example in the next section.

`regression_support.py` passed **72/72** cases using an independent Python truth-table over the active variables and the proven free-variable power-of-two factor. It matched all five observable branch metrics in the original 68 Lean cases.

## 2. Lean proof that independent blocks multiply

`BlockProduct.lean` defines a representation-preserving disjoint `joined F G : CNF (Fin (n+m))` using explicit index shifts and proves:

```lean
theorem count_joined {n m : Nat} (F : CNF (Fin n)) (G : CNF (Fin m)) :
  SAT.count (joined F G) = SAT.count F * SAT.count G
```

`BlockTree.lean` generalizes this to any recursively composed tree, with `count t` evaluating only small leaves and multiplying. The theorem `BlockTree.correct` establishes equality to the exact global `SAT.count (toCNF t)` **for arbitrary block trees**, not just examples. A source-level `groups_count` theorem shows the repeated four-variable construction has count `5^k`.

The 4-variable block consists of all six positive 2-literal clauses `x_i ∨ x_j` with i<j. Exactly five assignments satisfy each block, because at most one variable can be false. All four variables occur.

`BlockTreeSmoke.lean` executed in Lean and printed:

- 16 groups: n=64, m=96, all 64 variables active, `5^16 = 152587890625`.
- 128 groups: n=512, m=768, all 512 variables active, `5^128` (90 decimal digits; exact output in `block-tree-smoke.log`).

The large `toCNF` materialization and support-cardinality inspection took ~22 seconds in the Lean process; the multiplication-only counter is cheaper. The source theorem ensures **correctness of the exact formula represented by the tree** without enumerating `2^512` assignments.

## 3. Ordinary DIMACS auto-components

`component_sat.py` parses the actual DIMACS file using the previously tested parser, identifies variable connected components of the clause-variable incidence graph via disjoint-set union, renumbers each component locally and uses an exact DPLL leaf + original OpenAI-inspired `SparsePriority` outer branch port. It multiplies the component counts and a `2^free` factor.

Important trust boundary: the original Lean theorem proves independent-block **semantics**, but **the Python DSU, parser and translation are not individually Lean-kernel-verified**. Their correctness is supported by independent cross-tests, not a formal extraction claim. The Python program refuses components above 18 variables by default to avoid unbounded exponential workloads.

`regression_components.py` passed **191/191 tests**: the 68 original cases, 120 fresh deterministic mixed-sign/contradictory/free-variable component formulas checked against Python brute force, and 64/512/1024 all-active analytic instances. The 1024-variable instance has 1536 clauses in 256 independent 4-variable components and count **`5^256`** (179 digits). Python measured ~0.018 seconds for its #SAT computation; this is an *easy decomposable instance*, not hard SAT evidence.

## 4. Remaining paper-specific work

- The research target is still the actual native Walsh/CRT leaf in `SqrtLogSpace/NativeLeafProgram.lean`, `SqrtLogSpace/HighQueryProgram.lean`, and `SqrtLogSpace/FiniteFallback.lean`, where `noncomputable` definitions and huge fixed finite tables obstruct direct extraction.
- Our support and block decomposition leaf has a worst-case `2^s` or `2^w` enumeration term, where s is active support size and w the largest component size. For a fully connected formula with s=n it can be `2^n`, so **no theorem about worst-case ETH / `2^o(n)` follows from this prototype**.
- Next meaningful step would be a computation-aware interface for the original Walsh/CRT leaf and explicit cutoff witness, then replacing the exact leaf while preserving the proved I/O contract and resource accounting.

## Reproduce

```bash
cd ~/eth-lean-check-20261027/execution-prototype
./run_structured_all.sh
./run_support.sh fixtures/sparse-universe-512.cnf
python3 component_sat.py fixtures/all-active-disconnected-1024.cnf
```

Evidence files: `structured-axioms.log`, `block-tree-smoke.log`, `regression-support-summary.json`, `regression-components-summary.json`, `component-large.jsonl`, `component-1024.jsonl`, plus the earlier formal and execution reports. No global proxy changes or system package installation were needed in this stage.
