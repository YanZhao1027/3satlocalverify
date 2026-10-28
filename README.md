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
