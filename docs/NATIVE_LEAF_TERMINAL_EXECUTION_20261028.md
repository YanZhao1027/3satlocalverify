# Independent native leaf execution: measured terminal branch vs proven cost models

**Date:** 2026-10-28 · **Lean:** 4.34.1 · **Upstream:** `openai/math` at `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` · **Workstation:** Ubuntu/Ryzen, 109 GiB RAM.

## Precise scope

**We have independently run the original program's *terminal instructions* on physically formatted input. We have NOT run the original full nonterminal `NativeLeafProgram.command` or measured the primitive tape machine's actual microsteps.** The original `NativeLeafProgram.command` (in `SqrtLogSpace/NativeLeafProgram.lean`) is marked `noncomputable` due to its `HighQueryProgram` body. Trying a direct Lean `#eval` fails with `dependsOnNoncomputable`.

The executable source is `NativeLeafDispatch.command (.base .skip)`, from the **original source** `SqrtLogSpace/NativeLeafDispatch.lean`. The sole difference from the unmodified `NativeLeafProgram.command k` is the *nonterminal* branch, which is never executed for an empty formula or a formula containing an empty clause. We compiled this source using the actual `StructuredCalls.compiled`, ran the original `BitProgram.execInstr` instruction semantics, and *separately proved in Lean* that the complete original command and this executable source have the exact same terminating source `Eval` step count and final state for those terminal inputs. The result is not a claim that a new implementation is extensionally equivalent on arbitrary inputs.

## Original source path

- `SqrtLogSpace/NativeLeafProgram.lean`: `localCommand`, `command`, `program` for the full original program.
- `SqrtLogSpace/NativeLeafDispatch.lean`: `command` = original `NativeTerminal.readyCommand` then zero-clause/nonempty guards. The high-query branch is taken only for nonterminal cases.
- `SqrtLogSpace/NativeTerminal.lean`: `readyCommand_eval`, `readyResult_count`, `readyResult_empty_clause`, `readyResult_nonempty`. Formula records and dimension words are original encodings.
- `StructuredCalls.lean`: `Eval` and `compiled_halt_trace`; source costs count actual atoms, guards and called finite subroutine instructions.
- `BitProgram.lean`: actual `execInstr` and `step` for 12 instruction variants, one instruction per bit-program step.
- `BitProgramCompile.lean`: `tm_step`, `tm_trace`, `primitive_execution`. A BitProgram step corresponds exactly to one abstract TM2 block step; primitive bit-level simulation uses the separately defined `primitiveOverhead = compilerOverhead * blockOverhead`.
- `BitProgramSpace.lean`: original `dataBits`, `trace_dataBits` and source stack-size bounds.
- `SqrtLogSpace/DisjointReuse/DFSVisit.lean`: `LeafReady`, `LeafDone`, `BoundedEval` (including all-prefix per-stack bound), which have DIFFERENT units from total allocated stack data bits and primitive visited tape cells.

## Actual executed instruction counts, full physical inputs

These tests install the encoded ambient dimension, threshold 2, occurrence budget word, clause record and persistent context words in the same physical stack slots as the original `LeafReady` format. For the 3-variable cases, Lean proves the entire `LeafReady` predicate (not just an informal assumption).

| Formula | n | Source instructions incl. HALT | Total stack data bits, peak | Longest individual stack, peak | Exact output |
|---|---:|---:|---:|---:|---:|
| Empty CNF | 0 | 74 | 10 | 4 | 1 |
| Empty CNF | 3 | 107 | 18 | 4 | 8 |
| Empty CNF | 8 | 162 | 30 | 9 | 256 |
| Empty CNF | 16 | 250 | 47 | 17 | 65,536 |
| Empty CNF | 32 | 426 | 80 | 33 | 4,294,967,296 |
| CNF with an empty clause | 0 | 132 | 18 | 5 | 0 |
| CNF with an empty clause | 3 | 132 | 23 | 5 | 0 |
| CNF with an empty clause | 16 | 132 | 39 | 17 | 0 |

Twelve measured cases are stored in `execution-prototype/native-leaf-execution-20261028/terminal-batch-results.json`, including **every opcode count**: `set`, `copy`, `bnot`, `band`, `bor`, `bxor`, `branch`, `push`, `pop`, `peek`, `goto`, `halt`. For the 3-variable empty CNF, they are respectively **12, 1, 0, 0, 0, 0, 31, 21, 27, 1, 13, 1 = 107**. The empty-clause test executes **3 `bxor` operations** and 132 total instructions. These are source Boolean/stack instruction counts, **not CPU ALU cycles**.

The observed source steps for empty CNF at the listed n follow `74+11n`, and the empty-clause path uses 132 steps in the listed cases. This is an experimentally checked pattern, not an independently proven general formula. It says nothing about arbitrary hard SAT inputs.

## Step-by-step comparison with proven resource models

| Model / measure | Concrete empty CNF, n=3 | Interpretation |
|---|---|---|
| Actual BitProgram instructions | **107** | Includes the final explicit HALT instruction |
| Corresponding source `StructuredCalls.Eval` steps | **106** | Final HALT is appended by `compiled_halt_trace` |
| Direct original `NativeTerminal.readyCommand_eval` bound plus guards + HALT | **267** | Conservative explicit bound for this terminal input, original theorem |
| Original full `BoundedEval` source time bound | **1490** | Coordinator instantiated `NativeLeafDispatch.command_execution` with stack budget 204; valid all-prefix bound, not a measured count |
| Actual longest stack | **4 bits** | From original `BitProgram.execInstr` trace; all-prefix profiler independently cross-checked |
| Original `BoundedEval` longest-stack cap | **204 bits** | Formally proved for *all execution prefixes* of the actual original `NativeLeafProgram.command 2` on this state |
| Actual total occupied stack data peak | **18 bits** | Original `BitProgram.dataBits` sum of 1,220 stack lengths (excludes 80 fixed register bits and program code) |
| Original `BitProgram.trace_dataBits` | final occupied bits <= initial bits + source steps | Generic formally proved source bound; our measurements are much smaller |
| Original TM2 block steps | equal to source steps | Formally checked `BitProgram.tm_step` / `tm_trace`; **TM2 execution not successfully independently benchmarked** |
| Original primitive tape microstep bound | `primitiveOverhead(program) * steps` | Proven symbolic bound via `BitProgram.primitive_execution`; numeric multiplier remains `noncomputable` and is **not measured** |
| Original primitive all-prefix visited tape cells | not measured | Separate from source stack lengths; no measured equality is claimed |

`OriginalMachineCostBridge.lean` takes the **original full program's** terminal trace to the actual TM2/primitive compiler theorems and original `dataBits` upper bound without changing the machine. The terminal branch is correctly shown only for its selected inputs, not for general nonterminal CNFs.

## Runtime/space verification and safety

- Proofs: `OriginalTerminalTraceProof.lean`, `TerminalBranchExecution.lean`, `CompiledTerminalEquivalence.lean`, `OriginalMachineCostBridge.lean`, `TerminalResourceCertificate.lean`. The third source uses actual physical `LeafReady` state for 3-variable empty CNF.
- Executable profiler: `TerminalTrace.lean`, `ReadyTerminalTrace.lean`, `TerminalBatch.lean`. `TraceAccountingAudit.lean` independently recomputes the true `BitProgram.dataBits` and maximum stack length from **every executed configuration** and verifies profiler counters and opcodes for 3, 5, and empty-clause 3-variable cases. All audits returned `true`.
- Live reproducibility: `check_terminal_execution.sh` compiles proofs, runs `#print axioms`, executes the actual source-instruction simulation, validates every report against independent arithmetic, and terminates on errors. Logs, `.olean`, local agents' private prompts and unsafe diagnostics are not published.

**A failed TM2 interpreter attempt is documented rather than counted as success:** executing the 107-step terminal trace directly via Lean's dependent `TM2.Cfg` evaluation timed out after 55 seconds at roughly 80 GiB maximum process RSS, without completed output. This demonstrates interpreter overhead under this experiment, **not** the mathematical tape-space complexity of the original algorithm. The full primitive machine was not executed. A proper binary interpreter would require an independently validated source-to-machine extractor and a microstep/tape visitation instrumenter.

## Limits and next experiment

The original `HighQueryProgram` and nonterminal native leaf are still `noncomputable` in the executable Lean module; their proof-theoretic `Eval` existence results do not furnish an ordinary fast native binary. No benchmark in this report establishes subexponential worst-case runtime or falsifies ETH. Next, implement a bounded and formally trace-preserving extraction of the **nonterminal query/greedy-round subcommand** into a compact array-based bit interpreter, then measure both actual source steps and primitive stack/tape costs on a small, valid nonterminal CNF. All resource claims must continue to distinguish observed versus theorem-derived bounds.

Sol 6.1 was consulted as a source-reasoning assistant via the authorized scoped German route, with no shell privilege escalation. Its proposal for terminal trace constructors was independently improved and compiled by the coordinator. All actual Lean runs and instrument validations were performed using the Ubuntu connection, not by trusting Sol's statements.
