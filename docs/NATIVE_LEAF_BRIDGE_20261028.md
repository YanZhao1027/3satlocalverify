# Native-leaf runtime bridge — independent Sol-assisted Lean verification

**Date:** 2026-10-28. **Research status:** a genuinely Lean-checked, conditional composition theorem, not a new universal SAT algorithm. This new independent module does not modify the source of OpenAI/math (upstream commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, Lean 4.34.1).

## Original executable pathway and precise sources

| Stage | Source | Why it matters |
| --- | --- | --- |
| Raw leaf evaluator | `SqrtLogSpace/NativeLeafProgram.lean` lines 17–31 | `localCommand k = NativeLeafRun.command (HighQueryProgram.marked k) (HighQueryProgram.accepted k)`; `command k` wraps the actual inner command through `NativeLeafExecution` and `NativeLeafDispatch`, with output stack 263. This is distinct from our independent cached bucket VE. |
| Leaf semantic contract | `SqrtLogSpace/DisjointReuse/DFSVisit.lean` line 69 | `LeafContract` quantifies over valid raw CNF leaf states and gives `BoundedEval leaf t ...` plus `LeafDone` for all valid inputs with a local time and stack-word space bound. |
| Fixed source-level leaf time | `SqrtLogSpace/NativeLeafContract.lean` lines 13–16 | `NativeLeafContract.time n k localTime bound = 3624*bound + 100*(formulaBound n k+1) + 11*n + localTime + 5479`. |
| Uniform source command | `SqrtLogSpace/NativeLeafContract.lean` around line 791 | `uniform_contract` constructs constants depending on fixed clause width and input parameter budgets; proves `LeafContract ... (NativeLeafProgram.command k)` with conditional numerical premises. |
| Asymptotic envelope for actual leaf | `SqrtLogSpace/NativeOuterBudgets.lean` around line 253 | `leafTime_runtimeBound` places that same `NativeLeafContract.time` into an original `runtimeBound D A e inputLength n`, under an explicit upper polynomial bound on stack space. |
| Full native composition | `SqrtLogSpace/NativeLargeEntry.lean` lines 11–125 | Composes frontend, setup, leaf uniform contract, DFS outer program and primitive compiler, proving an actual primitive trace, exact count/answer tapes, and all-prefix visited-space bounds for sufficiently large inputs. |
| Paper endpoint | `SqrtLogSpace/Final.lean` lines 10–114 | `compiled_exact_count_and_sat` and `exact_count_and_sat` for one fixed primitive machine with exact count, SAT decision, original paper-scale time and polynomial all-prefix visited-space. This is an upstream theorem; we did not extract it into a conventional fast executable. |

## Independently checked theorem

** `NativeLeafContract.uniform_contract_and_runtimeBound`** in `execution-prototype/native-leaf-audit-20261028/NativeLeafCostBridge.lean` derives *one conjunction* from the upstream `uniform_contract` and `leafTime_runtimeBound`. It fixes the constants before the input and combines (i) the actual original fixed native leaf's `LeafContract` and (ii) an explicit upper bound on its numerical time budget at the paper's runtime scale.

Unlike our earlier VE table-row proof (`t·2^w`), this new statement is about the original program's **bounded evaluation steps**, but only at the native leaf stage. It does **not** certify the entire bit machine execution independently of the upstream theorems.

Axioms: kernel audit uses only standard Lean `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `admit`, `native_decide` or added axiom. Local verification uses the pinned upstream `.olean` builds. Run:

```bash
execution-prototype/native-leaf-audit-20261028/check_native_leaf_cost.sh
```

## Explicit remaining gaps

- The theorem inherits numerical hypotheses on the lower and upper stack budget. They are not automatic for an arbitrary externally selected `K` and exponent `g`; therefore a separate constructive feasibility proof is important before claiming a nonvacuous uniform instantiation.
- Our independent cached VE correctness and performance measurements do **not** implement or benchmark `NativeLeafProgram.command`; they are different algorithms.
- Replaying a `Computation.Trace` as a Lean theorem is not the same as extracting and executing the full primitive machine with practical wall-clock runtime.
- The original high-query, mark-history, dyadic/structured-leaf subservices and their real machine costs must be traced independently to compare with generic VE on high-interaction CNFs. Our new theorem is not an independent proof that ETH is false.

## Delegated-model methodology and safety

The project owner temporarily authorized using `codex-edge` via the preexisting Germany-only Xray route and selected the locally installed `gpt-6.1-sol` model. The model and German route were explicitly verified. The first two attempts to let Codex execute shell tools failed at Ubuntu's bubblewrap namespace restrictions (`RTM_NEWADDR`, then `uid map: Permission denied`). **We did not bypass this by giving the agent unrestricted shell access.** The coordinator supplied exact source excerpts for a no-tool reasoning pass; Sol proposed the Lean proof text, and the coordinator independently wrote, compiled and checked it. Tool error messages were not treated as success, and no claims of a native executable SAT solver were made. Code review and publication remain the coordinator's responsibility.

## Additional verified result: the upper budget is actually achievable

Sol's follow-up proposal `NativeLeafContract.nativeLeaf_polynomialBudget_feasible` (`NativeLeafBudgetFeasible.lean`) uses the **original** `formulaBound_polynomial` theorem to exhibit an explicit shared budget

`bound = Cs*(L+1)^sd + (101*formulaBound n k+103) + (5*n+6)`.

With constants `c=2+(4+8k)(k+1)2^k`, `g=max(sd,k+1)` and `K=Cs+101*c+114`, it proves **uniformly for every `n≤L`** that the three lower bounds are satisfied and the same `bound≤K*(L+1)^g`. The constants `K,g` are selected before any input `n,L`, not separately for each instance. This closes the particular potential-vacuity gap caused by an arbitrary incompatible external polynomial upper cap.

The coordinator then combined the source `uniform_contract` and `leafTime_runtimeBound` with that independent budget lemma in the new Lean theorem **`NativeLeafContract.uniform_leaf_with_constructed_budget`** (`NativeLeafRealized.lean`). It constructs the budget for every admissible leaf input, and simultaneously supplies the original fixed native leaf program's semantic contract and paper-scale step-time envelope. This substantially strengthens the first, conditional theorem while preserving the restrictions on `n≥cutoff`, input encoding, parameter length and correct threshold representation. It is **not** a proof about the overall primitive machine, nor a speed benchmark or a new algorithm.

Both Sol-proposed modules and the coordinator's derived combination were independently compiled with Lean 4.34.1, then subjected to a shared `#print axioms` audit. These are exact mathematical statements about the upstream original program under its definitions, not computations performed by Sol's disabled shell sandbox.

## Independent audit of the upstream final theorem

`OriginalFinalAxioms.lean` imports the **unaltered upstream** `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final` and reports the axioms of both `compiled_exact_count_and_sat` and `exact_count_and_sat`. The Lean 4.34.1 check completed with exit code 0 and returned only `propext`, `Classical.choice`, `Quot.sound` for each. This confirms the existing upstream theorem has no additional Lean axioms according to this check; it does NOT mean we independently ran the enormous primitive-machine program or verified a practical subexponential SAT performance advantage.
