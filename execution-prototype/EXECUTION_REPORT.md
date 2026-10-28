# Execution experiment: OpenAI SubexponentialSAT components

Completed on Ubuntu workstation `zyubuntu-MS-7E51` on 2026-10-28 (+08:00).
Original Lean source, unchanged: `~/eth-lean-check-20261027/openai-math/lean`, commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. Toolchain Lean 4.34.1. This is a *new execution experiment*, separate from the prior successful Comparator proof check (`../REPRODUCTION_REPORT.md`).

## Overall result

`./run_all.sh` reported **ALL SIX EXPERIMENT STAGES PASSED**. Tests ran on the user's Ubuntu without changing the official OpenAI git checkout, the system proxy, or installed system packages.

### 1. Run the original Lean sparse counting state machine

`SparseDimacs.lean` imports `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram` and **directly calls the upstream `SparseCountProgram.step` and `SparsePriority.select`**. It accepts DIMACS `p cnf n m`, including multiline clauses and free/unused variables; rejects invalid literal indices and more than 12 variables to avoid accidental exponential leaf cost. Threshold `M=2`, step budget `100000`.

`./run_sparse.sh fixtures/shared-core.cnf` yields count **2**, with 2 source branches, 3 source leaves and 5 transitions; the original source `SAT.count` oracle agrees. `./run_sparse.sh fixtures/all-pairs-12.cnf` yields **13**, 10 branches, 11 leaves and 21 transitions.

The upstream `SparseCountProgram.step` uses `SAT.count node.formula` directly as the leaf result. This **does exponential finite enumeration at the leaves**; this experiment therefore runs an actual formalized outer transition algorithm but does not execute the complete subexponential counting program.

The Lean process has substantial startup/import overhead (about 4.5 seconds and about 7 GiB resident memory) which should not be confused with single-formula algorithm runtime. Per-case `ms` fields in the demonstration are not suitable for performance comparison; we instead time the Python version below.

### 2. Differential correctness tests

`python3 regression.py` generated 64 deterministic random CNFs (2..9 variables, 0..22 random clauses, with controlled contradictions and multiline clauses) and tested the original Lean runner. Four hand-written edge cases were added: shared core, contradictory units, empty formula with 4 free variables, and an empty clause. **68/68 cases passed** against the source's own semantic `SAT.count`; all corresponding numeric answers are independently checked by Python brute-force enumeration inside regression.py.

`python3 compare_traces.py` compared the second prototype against the Lean results and found **68/68 exact matches** for counts, transitions, branches, leaves and maximum pending frontier. There were 64 source branching operations over these cases.

Additional all-positive-pairs formulas `\bigwedge_{1<=i<j<=n}(x_i \lor x_j)` have the analytic count **n+1**. The original Lean runner produced 7 for n=6, 9 for n=8, 11 for n=10 and 13 for n=12, all matching the closed form.

### 3. Native Python implementation with explicit counting leaf

`native_sparse.py` is a **new implementation**, not extracted from Lean. It faithfully ports these specific source operations:

- `SparsePriority.violatingCandidates` / `SparsePriority.select`: enumerate clause-core subsets; prefer smallest clause width and then largest core, with the same canonical literal encoding.
- `DisjointBranch.selected`, `childA`, `childB` and `SAT.absorb`: partition satisfying assignments into disjoint core-true/core-false cases.
- `SparseCountProgram` pending depth-first stack and total accumulator.

The Python leaf is **our own exact memoized DPLL solver**, with free-variable factors; it is *not* `NativeLeafProgram.command` or the paper's advanced Walsh/CRT leaf. The outer port is cross-tested against Lean on 68 cases; this is a regression test, not a separate kernel proof of all Python code.

Examples:

| Instance | Independent reference | Python answer | Outer branches | Native elapsed (one observed run) |
| --- | ---: | ---: | ---: | ---: |
| Random 18-variable 55-clause 3-SAT | Python brute force 499 | 499 | 1056 | 0.190 s |
| All-positive pairs n=16, 120 clauses | brute force 17 | 17 | 14 | 0.003 s |
| All-positive pairs n=24, 276 clauses | analytic 25 | 25 | 22 | 0.011 s |
| All-positive pairs n=32, 496 clauses | analytic 33 | 33 | 30 | 0.033 s |

The n=24/32 cases are highly structured easy instances, not evidence of general SAT speed or of a subexponential time bound.

### 4. Original Walsh search executes

`WalshSmoke.lean` directly imports `SqrtLog.WalshExistence` and evaluates `WalshExistence.search`. For `r=2,D=4,q=3`, it finds the four 2-bit vectors `[00,01,10,11]`, evaluates `Good 3 s` to true, and the Walsh sums to `[4,0,0,0]`. The source's theorem `search_some_good` is used as an additional checked fact. An earlier `q=2` sample also succeeds. This is a tiny, **genuine execution of one mathematically relevant leaf ingredient**, not the complete leaf program.

### 5. Original MomentsAlgorithm arithmetic loop executes

`MomentsSmoke.lean` imports `SqrtLog.MomentsAlgorithm` and runs its original `MomentsAlgorithm.run` over a two-index synthetic ring workload. Output: **`(364, 20)`**, meaning computed value 364 and 20 charged primitive arithmetic operations. The file also contains a Lean `example ... := by decide`, which elaborated successfully.

This tests the original head-moments machinery in isolation; it does not connect it to the physical SAT input/output protocol.

### 6. Benchmark limitations

`python3 benchmark.py` ran nine repetitions per configuration and stored medians in `benchmark-summary.json`:

| Instance | M=2 outer branch + DPLL | M=1,000,000 effectively DPLL-only |
| --- | ---: | ---: |
| Random n=18, m=55 | 0.19145 s | 0.00208 s |
| All-positive pairs n=32 | 0.03311 s | 0.02342 s |

**The prototype's sparse outer branching is slower than direct DPLL on these tests.** These tests *do not* implement the subexponential leaf, so they cannot confirm or refute the theoretical running-time claim in the formalized theorem. The threshold is user-selected for demonstration and not the exact asymptotic schedule used in the theorem.

## Exact remaining gap to the complete paper algorithm

In the original repository:

- `SqrtLogSpace/NativeOuter.lean` has a `noncomputable def countingProgram` that depends on `Native.entryProgram`.
- `SqrtLogSpace/NativeEntry.lean` has `noncomputable def entryCommand` and `entryProgram`.
- `SqrtLogSpace/FiniteFallback.lean` defines `noncomputable def tableCount`, `countProgram`, `jointCommand` and `framedCommand`; its generic finite fallback precomputes a fixed table ranging over *every* bounded-size CNF, unlike a normal runtime solver. Even for modest cutoff values the resulting finite state space can be astronomical.
- `SqrtLogSpace/NativeLeafProgram.lean` marks the leaf construction as `noncomputable`; the executable composition includes a large Walsh/CRT and data-structure development, which we have not assembled into a usable solver.
- `SqrtLogSpace/NativeLargeEntry.lean` chooses a cutoff using existence / eventually-at-top arguments, without supplying a convenient concrete numerical witness to executable code.

To get a complete runnable and efficient solver: first replace these nonconstructive witnesses by explicit computational bounds and a practical small-instance fallback; then create/runtime-validate the whole leaf/outer interface while preserving the theorem's counted outputs and time/space semantics; then extract or compile an executable and benchmark on systematic datasets.

No change to the original proofs was needed for these component experiments. Their original kernel-verification result remains as documented in `../REPRODUCTION_REPORT.md`.

## Reproduce

```
cd ~/eth-lean-check-20261027/execution-prototype
./run_all.sh
# Direct execution of source's SparseCountProgram.step on one DIMACS file:
./run_sparse.sh fixtures/shared-core.cnf
# Fast native prototype, with independent brute-force oracle for small input:
 python3 native_sparse.py --oracle fixtures/random-3sat-18.cnf
# Fast larger highly structured CNF:
 python3 native_sparse.py fixtures/all-pairs-32.cnf
```

Generated files include `run-all.log`, `regression-summary.json`, `benchmark-summary.json`, `regression-lean.stdout.log`, `walsh-smoke.log`, and `moments-smoke.log`.
