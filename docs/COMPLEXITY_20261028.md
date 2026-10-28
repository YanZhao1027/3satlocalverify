# 2026-10-28 — Formal cost and width barrier for the independent bucket VE

**Scope:** This report advances the independent Lean-certified variable-elimination prototype, not an implementation or runtime certification of OpenAI's full general SubexponentialSAT machine. Upstream: `openai/math` at commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, Lean 4.34.1.

## 1. Verified quantitative cost certificate

- `MemoComplexity.sampleSupport_length`: enumerating local support `S` produces exactly `2^|S|` assignments.
- `MemoComplexity.makeTable_length`: the implementation's `makeTable` constructs exactly `2^|S|` local rows.
- `MemoComplexity.scope_eliminateMemo_matches` and `run_scopes_match`: the scope-only model follows the actual memoized factor representation at every elimination step.
- `MemoComplexity.sourceTableRows_eq_static`: its per-step row counts **equal** the lengths of tables constructed by the implementation; the model is not merely a simulator's estimate.
- `MemoComplexity.source_table_rows_le`: for a schedule of `t` variable eliminations, **if** every intermediate pre-elimination bucket has at most `w` variables, the total number of materialized output-table rows is at most `t * 2^w`.
- `MemoComplexity.totalRows_full_le`: for `n` eliminations, a generic unconditional row bound is `n * 2^n`. This does not establish subexponential worst-case cost.

**What is counted:** number of rows in newly materialized memo factor tables, not initial clauses' tables, memory bytes, lookup comparisons, bit operations, integer/modular arithmetic, CRT reconstruction operations, Lean process startup, or wall-clock instructions. The actual implementation currently searches table rows linearly, so total time can exceed this row count significantly.

## 2. Formally certified freedom to reorder variables

`PermutationCorrect.marginalMany_perm` proves the Boolean semiring marginal operators commute under permutations; `GeneralVESAT.exactCountWithOrder_correct` establishes the memoized #SAT result is exactly `SAT.count F` for **any full variable permutation**. In particular, a dynamic min-fill heuristic can propose an untrusted order while Lean verifies the permutation certificate; the heuristic's cost benefit is a separate claim.

## 3. Structural width barrier (not a hardness proof)

`PrimalWidthBarrier.complete_pair_cover_forces_width` proves: if every pair of variables jointly occurs in some factor, **every first bucket** has width `n`. `complete_pair_cover_forces_rows` further proves the first newly materialized table has exactly `2^(n-1)` rows. Both are generic Lean theorems with all premises explicit.

`complete_graph_witness.py` builds a concrete **3-CNF** family: take one hub variable and put a clause on `(hub, i, j)` for every pair `i<j` among the other `n-1` variables. Each clause has exactly three distinct literals; all variables are active; the primal graph is complete. The Python generator checks the pair-cover condition for every first variable, and evaluates the exact static row counts. For n=64 this uses **1953** 3-clauses and, regardless of first variable, entails a first memo table of **9,223,372,036,854,775,808 rows** in the raw bucket-VE strategy. This is a structural failure mode of **our implementation**, NOT an inherent lower bound on all SAT algorithms, nor an assertion of instance hardness. We did **not** allocate that table or execute exponential work.

## 4. Order sensitivity and random connected 3-CNF statistics

For the separate connected 'star-chain' 3-CNF with n-2 clauses `(x0 OR xi OR x(i+1))`, fixed canonical elimination produces full width `n`, while reverse order gives width **3**:

| n | canonical width / total table rows | reverse width / total table rows |
|---:|---:|---:|
| 16 | 16 / 65,535 | 3 / 59 |
| 32 | 32 / 4,294,967,295 | 3 / 123 |
| 64 | 64 / 18,446,744,073,709,551,615 | 3 / 251 |

Lean's `WidthFixtures.lean` and `WidthReverse.lean` reproduce the static predictions; `WidthFixtures` includes kernel-checked n=8 width certificates. `StarCountSmoke.lean` executes the **actual memoized Lean #SAT counter** under the safe reverse order, with a general Lean theorem preserving exact correctness. The n=16,32,64 model counts are `34365`, `2151008226`, and `9223389204534953373`, independently checked by a 2-state Fibonacci recurrence (counting Boolean strings with no adjacent false values).

For 6 deterministically sampled random connected 3-CNFs per n, with `m=4n` clauses, the *median* peak bucket widths under fixed order / greedy min-fill were:

| n | fixed order | greedy min-fill |
|---:|---:|---:|
| 16 | 15 | 12.5 |
| 32 | 27 | 22 |
| 48 | 40 | 32.5 |
| 64 | 54.5 | 42.5 |

These are static exact induced widths of the tested orders, **not** optimized treewidth lower bounds, and do not establish worst-case lower bounds for min-fill. The random cases were profiled without allocating factor tables or executing the SAT solver.

## 5. Precise comparison with the original paper's objective

Original `SqrtLog/StatementScale.lean` defines

`runtimeScale(n) = n * (ln ln(n+16))^2 / sqrt(ln(n+16))`.

Original `SqrtLogSpace/Final.lean` states the final **primitive machine** complexity as a polynomial in encoded input length times `2^(A * runtimeScale(n))`, and includes bounds on all-prefix visited tape space. The constants `A` and the polynomial degrees are part of that theorem; there is no promise of useful timing at n=64.

Our `PaperScaleBridge.rows_le_paper_scale` proves an exact **conditional** relationship: if the max bucket width is `≤ A * runtimeScale(n)`, then this VE implementation's table rows lie within a `t * 2^(A * runtimeScale(n))` envelope. It **does not** prove every CNF admits such a width bound; the complete pair-coverage construction shows why our plain bucket method cannot supply it for all CNF.

Even under a width assumption, a table-row bound is insufficient to establish the paper's stronger bit-level time and visited-space theorems. The next meaningful technical bridge lies in the **different** original services: `SqrtLogSpace/NativeLeafProgram.command`, `NativeLeafContract.uniform_contract`, `SqrtLogSpace/NativeLargeEntry.run`, and compilation into the `PrimitiveMachine` traced in `SqrtLogSpace/Final.lean`. A rigorous reproduction must connect runnable service implementation, primitive steps, uniform bound and polynomial space, rather than identifying VE with the paper algorithm.

## 6. Evidence, trust and reproducibility

- Lean theorem checker: `MemoComplexity.lean`, `PermutationCorrect.lean`, `PrimalWidthBarrier.lean`, `PaperScaleBridge.lean`, `WidthFixtures.lean`, `StarCountSmoke.lean` all compiled successfully. `ComplexityAxioms.lean` reports only `propext`, `Classical.choice`, `Quot.sound` for the primary complexity, barrier, permutation and ordered counting theorems, without `sorry` or `native_decide`.
- Python static profiles: `width_profile.py` → `width-profile-results.json` (32 cases); `complete_graph_witness.py` → `complete-interaction-summary.json`; `complexity_regression.py` → `complexity-regression-summary.json` (39 structural/analytic checks).
- Lean `#eval` on structurally easy cases only. All impossible-sized table counts are symbolic static forecasts, not real allocations.
- Upstream original OpenAI checkout remains unchanged.

## 7. Research direction

1. Account for **table lookup comparisons, coefficient bit length, ring arithmetic and CRT calls** in a source-aligned work and peak-space model.
2. Bring **adaptive bucket ordering** into Lean with a checked full-order certificate; benchmark on challenging structures but never assume it makes width sublinear.
3. Identify which upstream Walsh/dyadic/leaf-native services replace full high-width materialization, and attempt an executable local bridge to the primitive machine/cost theorems.
4. Keep separate *formal correctness*, *operational resource accounting*, *worst-case asymptotics* and *practical benchmarks*. Do not represent this work as disproving ETH.
