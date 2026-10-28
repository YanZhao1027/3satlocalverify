# Ubuntu reproduction guide

The independent source files in `execution-prototype/` import the upstream OpenAI math Lean package. This repository does not vendor the multi-GB Mathlib/OpenAI dependencies.

1. Install Lean 4.34.1 (matching the original environment).
2. Clone https://github.com/openai/math separately and provision its `lean/` Lake dependencies at the pinned version in the README.
3. Define `OPENAI_MATH_LEAN` to the local upstream `math/lean` directory.
4. Compile the independently authored modules in dependency order (for example `GeneralVE.lean`, `MarginalComplete.lean`, `GeneralVESAT.lean`, `GeneralVEExact.lean`, `GeneralVEWeighted.lean`, `DualJetProof.lean`, `MemoVE.lean`, `MemoVECNF.lean`, `VerifiedReconstruction.lean`, `ReconstructionDegree.lean`, `VerifiedComplete.lean`, `VerifiedInteger.lean`, `Concrete2401.lean`, `GeneralVEDual11.lean`, `ConcreteInstance11.lean`). Also compile imported modules in the root/paper-kernel directories.
5. Run `ConcreteInstance11Axioms.lean` to check the final proof axioms.

On the original Ubuntu, the already tested entry point was:

```bash
~/eth-lean-check-20261027/execution-prototype/general-ve-20261028/verify_concrete_instance11.sh
```

A portable wrapper in this repository is provided at `scripts/run-local.sh`. It assumes upstream dependencies are available and required local `.olean` files are already compiled. First-run setup is nontrivial, so do not mistake it for a one-command clean machine installer.

Recorded independently verified regression summaries are checked in; these include the 277-case Python study and 84-case Lean/CRT study.