# Methods, evidence and limitations

## Formally checked results
- `GeneralVE.run_correct` — generic bucket variable elimination with finite Boolean factors.
- `GeneralVESAT.exactCount_correct` — exact #SAT for arbitrary finite CNF.
- `GeneralVE.runMemo_correct` — table cache preserves bucket semantics.
- `MemoVECNF.memoDualJet_derivative_correct` — Hermite value and derivative from verified bucket sampling.
- `VerifiedReconstruction.integer_count_from_verified_CRT` — conditional original OpenAI CRT correctness, including residue-field, distinct node, nilpotence and modulus hypotheses.
- `VerifiedReconstruction.eleven_input_original_CRT_exact` — concrete 11-variable instance, actual original CRT program.
- Axiom audit: standard `propext`, `Classical.choice`, `Quot.sound`.

## Measurements
- Python VE independent cases: 277/277.
- Lean cached VE / original Hermite CRT connected cases: 84/84.
- CRT operations for six coefficients: ordinary 6×1 6111, Hermite 3×2 2919, Hermite 2×3 2201 (these omit sampling work).
- Low-width chain examples: n=32 #SAT 112892768; n=64 #SAT 11370557917191032. Cached Lean inner-core runtime ≈111 ms and ≈770 ms respectively, excluding process startup.

## Crucial boundaries
- This **does not implement** the entire SubexponentialSAT algorithm or demonstrate a worst-case `2^{o(n)}` SAT runtime.
- Generic VE may have exponential induced width on hard connected instances.
- The DIMACS file parser and Python VE implementation are tested, not fully Lean verified.
- Early sparse and Moments experiments use exhaustive leaves.
- No claim of independent resolution of ETH. Heavy build/toolchain files are not vendored.

Provenance: https://github.com/openai/math, upstream commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, Lean 4.34.1, original Ubuntu experiments 2026-10-28.