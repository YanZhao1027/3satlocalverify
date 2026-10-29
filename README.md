# 3satlocalverify — Local #SAT Experiments & Lean Verification

**Independent research reproductions, not a new proof that ETH is false.**

[中文说明](README.zh-CN.md) · [Upstream OpenAI math repository](https://github.com/openai/math) · [Methods and limitations](docs/METHODS_AND_LIMITATIONS.md) · [Reproduction guide](docs/REPRODUCE.md)

This repository archives executable experiments built on an Ubuntu workstation to investigate the formalized **SubexponentialSAT** work. Our code is *separate* from OpenAI's upstream mathematical formalization. The upstream source and its large Lean dependencies are **not** vendored.

## What we actually verified

| Component | Evidence | Scope |
| --- | --- | --- |
| Sparse branching / support-compressed leaves / independent-component counting | Lean correctness theorems and small-instance regressions | Exact counts; some leaves still enumerate assignments |
| General factor/bucket variable elimination | `GeneralVE.run_correct`, `GeneralVESAT.exactCount_correct` | Arbitrary finite CNF, exact semantics; exponential worst-case width |
| Table-cached bucket elimination | `GeneralVE.runMemo_correct`, `MemoVECNF.memoDualJet_derivative_correct` | Same mathematical values, cheaper on tested low-width instances |
| Verified order-2 Hermite jets | `GeneralVEWeighted.dualJet_value_correct` and `dualJet_derivative_correct` | Arbitrary CNF over the defined modular rings |
| Original OpenAI CRT / Hermite reconstruction interface | `VerifiedReconstruction.integer_count_from_verified_CRT` | Conditional on explicit algebraic and sufficient-modulus hypotheses |
| Concrete connected 11-variable CNF | `VerifiedReconstruction.eleven_input_original_CRT_exact` | End-to-end theorem for the actual original `Reconstruction.run`; 3 standard Lean axioms only |
| Cross-checks | 277/277 Python variable-elimination cases; 84/84 connected random Lean/CRT cases | Independent test oracles; not complexity proofs |

Additional low-width connected demonstrations: 16, 32, 48 and 64 variables. For 64 variables and 62 clauses, the cached Lean/CRT run reported **11,370,557,917,191,032** satisfying assignments and a measured core runtime around **770 ms** (not including Lean startup). These are structured instances with small elimination width—not representative of arbitrary hard SAT.

### What this is **not**

- **Not** a practical implementation of the entire paper's worst-case `2^{o(n)}` algorithm.
- **Not** an empirical demonstration of subexponential worst-case complexity or a general performance win against SAT solvers.
- **Not** a kernel proof of the external DIMACS parser or of the independently implemented Python variable-elimination program.
- **Not** a standalone Lean project that compiles without the separately pinned OpenAI `math` dependencies.
- The latest proof concerns correctness of our specific VE → first-order Hermite → original CRT execution path, under stated hypotheses.

## Layout

- `execution-prototype/`: reproducible Lean sources, Python implementations, DIMACS fixtures, regression runners, recorded summaries.
- `docs/`: setup, experiment matrix, verification boundaries, limitations and synchronization details.
- `scripts/`: reproducibility / snapshot synchronization helpers (Git push requires local repository credentials).
- `.github/workflows/`: lightweight Python regression CI; the much heavier Lean verification runs on a provisioned Ubuntu machine.

## Provenance

- Upstream: <https://github.com/openai/math>
- Upstream commit used for local experiments: `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` (verify independently when reproducing).
- Lean version on the workstation: **4.34.1**.
- Local experiments and measured results: **2026-10-28**.

We publish only our independent sources and lightweight test artifacts. No private machine credentials, installed toolchain binaries, third-party repository checkout, or generated cache files belong in this repository.

## License

No redistribution license has been selected for this independent repository yet. **Public visibility does not by itself grant a reuse license.** The separate upstream repositories retain their own licenses.

## New: audited complexity and elimination-order analysis (2026-10-28)

Read [the full Lean-backed cost and width report](docs/COMPLEXITY_20261028.md).

- The actual memoized VE source has a verified **exact table-row accounting model**. With at most `w` variables per intermediate bucket, it creates at most `t * 2^w` output-factor rows in `t` elimination steps; this does **not** bound all machine operations.
- A verified arbitrary-order theorem permits safe variable reordering. In one 64-variable connected 3-CNF, the canonical order costs `2^64-1` *predicted rows*, while reverse order costs 251 rows. Neither huge table was allocated.
- A different complete-interaction 3-CNF family provably forces **width n for any first eliminated variable** within this raw VE framework (conditional combinatorial Lean theorem plus independently generated/checkable fixtures).
- `PaperScaleBridge.lean` formally compares the row envelope to the original paper's `runtimeScale` **only under an explicit small-width hypothesis**; that hypothesis is not universally true for standard VE. This is not the full primitive-machine bit-time analysis of the paper.

To run the checks on a workstation with OpenAI/math/Mathlib already provisioned:

`execution-prototype/complexity-20261028/check_complexity.sh`

## New: GPT-6.1-Sol-assisted, coordinator-audited native-leaf bridge (2026-10-28)

[Source-level report](docs/NATIVE_LEAF_BRIDGE_20261028.md) · [Research/acceptance protocol](docs/SOL_RESEARCH_PROTOCOL_20261028.md) · [Verified Lean modules](execution-prototype/native-leaf-audit-20261028/)

We linked the original OpenAI **fixed native leaf command** and its `LeafContract` to the paper's original runtime envelope; proved a uniform polynomial cap can actually satisfy the leaf's three local budget minima; and independently checked the upstream final theorem's standard axioms. Three new Lean proofs and two original theorem audits pass using Lean 4.34.1, without `sorry` or additional axioms. **This does not extract or benchmark the complete original machine and does not independently establish a subexponential SAT algorithm.** The agent could not use the machine's shell sandbox; the coordinator compiled and verified Sol's proposed code manually.

## Research outlook and honest evidence boundary (2026-10-28)

[Read our current assessment and next nonterminal execution target](docs/RESEARCH_OUTLOOK_20261028.md). The **original nonterminal native leaf remains unexecuted**; terminal-branch trace verification and low-width VE results are not demonstrations of end-to-end subexponential SAT speed. Our next milestone is a verified, actually executed nonterminal query with per-opcode and peak-space records.

## Authentic nonterminal input: classification and leaf loading (2026-10-28)

[Read the verified prefix experiment and its explicit limits](docs/NONTERMINAL_PREFIX_20261028.md). Four genuinely nonterminal CNFs now execute original classification and leaf loading. The first 100 complete machine states match the upstream source interpreter. **The original high-query counting algorithm has not been executed; oracle #SAT counts are reference values, not measured outputs.**

## Real original hash-parameter execution and cost measurements (2026-10-28)

[Measured source-bit costs and exact verification boundaries](docs/NATIVE_CORE_COST_20261028.md). Six input parameter sets actually execute 2,324–3,778 original arithmetic bit instructions, with 426/426 original opcodes and full 3,006-step source trace agreement for the principal case. The real original 16-register/44-stack ABI completes 3,585 instructions with 108 peak occupied stack data bits, 637/637 matching original opcodes and a full original-machine state replay. Full 40×896 preparation and the high-query #SAT solver have **not** yet executed; no end-to-end SAT speed advantage is established.

## Original physical 40×896 native leaf hash preparation now executes (2026-10-29)

[Read the 3,585-step original/physical lockstep audit](docs/NATIVE_PHYSICAL_40X896_20261029.md). A nonempty CNF passes 180 source bit instructions of genuine clause counting; the original hash-parameter ABI then executes 3,585 actual Boolean instructions on 40 registers and 896 physical virtual stacks, with 125 peak occupied stack data bits and correct computed parameters. The original 16/44-port mapping and every opcode variant have kernel-checked refinement theorems. **All 3,585 original/physical machine states match, and every step's 896-stack data occupancy is independently recounted.** This is preparation, not a completed high-query #SAT solver or a subexponential speedup result.

## Real original native startup source execution: 7,085 bit instructions (2026-10-29)

[Read the source-derived complete `start` and `canonicalStart` execution audit](docs/NATIVE_CANONICAL_START_20261029.md). Independent source-faithful linking has executed `LeafOuterProgram.start` in **6,135** Boolean instructions and the larger `NativeLeafSetup.canonicalStart` in **7,085** instructions, both with **125 peak occupied stack-data bits**. Every instruction's 896-stack occupancy was rechecked; full 40-register/896-stack states match at each original subprogram boundary. Upstream original compiled whole-program source opcode equality is **not fully established** (three direct sampled labels match, two direct samples timed out). **No high-query #SAT solving or asymptotic acceleration has been demonstrated.**

## Original parameter generation, both code searches, and serialization execute (2026-10-29)

[Read the actual source-bit instructions and bounded selector prefix](docs/NATIVE_CODE_PARAMETERS_SEARCHES_20261029.md). The original local parameter program ran **9,130** source instructions; the original graph/local searches ran **2,680/5,598** instructions; and original row serialization ran **715** instructions, producing and saving a real 13-bit row. The source-derived one-PC `canonicalStart; parameters` machine completed **19,182** bit instructions with **252 peak occupied stack-data bits**, verified at five full-state boundaries and with an independent every-step full-store scan. The final selector still does **not** halt after two million source instructions and must construct a **5,120,003-bit** encoded zero candidate. Neither the complete original NativeLeafPreparation nor HighQuery/#SAT and no subexponential time advantage has been established.

## Direct original `afterCode` compiler and 8M source-opcode audit (2026-10-29)

[Experiment report](docs/NATIVE_AFTERCODE_ORIGINAL_20261029.md) · [Reproducible code](execution-prototype/native-aftercode-original-20261029/)

All **119/119** actual upstream `StructuredCalls.compiled NativeLeafPreparation.afterCode` opcodes, including entry, match the independent source table in a full **runtime** comparison (**not** yet a Lean kernel equality theorem). Directly executing the *upstream* compiled opcode table on a genuine nonempty-CNF physical state completed **8,000,000 source bit instructions**, producing **140,962/5,120,003** encoded candidate bits without halting; the 13-bit serialized rows were preserved. Another **536/536** finite-state single-step comparisons against upstream `BitProgram.execInstr` pass (**not** a universal interpreter theorem). No completed high-query #SAT, ETH refutation or subexponential runtime demonstration is claimed.

Incremental Lean-kernel semantic bridge: `NativeStepKernelProof.lean` also proves generic compact-vs-upstream semantics for `halt`, `goto` and `set`, backed by an array-update lemma and checked with no `sorryAx`. All other opcode cases and the complete compiler equivalence theorem remain open.

## Completed original afterCode: 290,560,512 real source instructions (2026-10-29)

[Kernel and complete-execution report](docs/NATIVE_COMPACT_KERNEL_AND_AFTERCODE_COMPLETE_20261029.md) · [Source and full evidence archive](execution-prototype/native-aftercode-original-20261029/)

Following the earlier 8M-step prefix, the exact upstream-compiled NativeLeafPreparation.afterCode actually **HALTED at 290,560,512 original Boolean opcodes**, producing the required **5,120,003-bit** encoded zero word. All **896 physical stacks** matched a kernel-proved equivalent of the upstream finishedWords reference. Measured peak **occupied stack DATA** was 5,120,133 bits (not total TM2 tape space); Ubuntu wall time was 258.35 s, exit code 0. Kernel-checked universal one-step, all-fuel and source-trace replay theorems require only the three standard Lean axioms. This is still not a whole NativeLeafPreparation.command one-PC execution, high-query SAT counting, ETH refutation or general subexponential runtime demonstration.
