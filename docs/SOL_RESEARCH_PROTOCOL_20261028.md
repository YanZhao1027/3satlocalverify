# Temporary gpt-6.1-sol delegated research protocol

This is a publication-safe summary of the coordinator-designed prompts actually used on 2026-10-28; private session logs are deliberately **not** uploaded to the public repository.

**Model and route:** Codex CLI `0.164.0`, explicit `gpt-6.1-sol`; scoped launch with existing `codex-edge` Germany HTTP tunnel; no global network setting changes. Worktree branch: `research/codex-sol-native-leaf-20261028`.

**Original delegate task:** Read only the public `3satlocalverify` project and the named upstream `NativeLeafProgram`, `NativeLeafContract`, `NativeOuterBudgets`, `NativeLargeEntry` and `Final` modules. Build a nontrivial Lean connection between native leaf correctness and measured source cost. Avoid `sorry`, `native_decide`, false complexity claims, package updates, network calls by tools, global state changes, commits and pushes. Provide test commands and an honest limitation report.

**Execution issue:** On this Ubuntu host Codex's shell sandbox cannot create its bwrap namespace, even for `pwd`. It fails with an explicit error. We declined to switch to `danger-full-access`.

**Subsequent accepted no-tool research prompt:** Given precisely excerpted original Lean theorem signatures, construct an existential theorem combining the original `NativeLeafContract.uniform_contract` with `NativeOuterBudgets.leafTime_runtimeBound`. Preserve ALL original antecedents, select constants before arbitrary `n`, `inputLength`, `threshold` and factor inputs, ensure the term is the actual `NativeLeafProgram.command`, and output *only* candidate Lean code with no tool calls. The coordinator would compile and independently verify the suggestion.

**Coordinator acceptance:** A returned code block was not treated as a passed proof. The coordinator extracted the text, compiled it with pinned Lean 4.34.1, checked full axiom dependencies with `#print axioms`, checked absence of placeholders, and tested the reproducibility script. Publication follows only after these tests.

**Follow-up delegated prompt:** A separate feasible-budget theorem is solicited to construct an explicit polynomial upper budget from the native leaf's three lower budget requirements. This avoids claiming that the first conditional theorem is meaningful for every arbitrary external choice of constants.
