# Synchronization policy

**Public repository:** https://github.com/YanZhao1027/3satlocalverify

**Original Ubuntu source:** `~/eth-lean-check-20261027/execution-prototype/`.

**Local publication workspace:** `~/3satlocalverify-public/`.

Future updates:

1. Test each change in the independent experiment directory.
2. Refresh the curated staging workspace with `scripts/stage-from-ubuntu.sh`.
3. Review the diff and run the Lean theorem/axiom checks plus regression tests before publication.
4. Use the connected GitHub integration to commit validated files to this public repository, or `git push` if **this repository** has subsequently been granted write credentials.

**Important:** No permanent unattended synchronization is active. The existing Ubuntu SSH deploy keys are specific to other repositories; the newly created repository has not been granted a dedicated deploy key. Do not copy credentials or turn on scheduled pushes until authentication and safeguards are configured. GitHub Actions cannot read a powered-off local workstation.

The 2026-10-28 initial source snapshot was uploaded through the authorized GitHub connector. The local publication workspace is a staging copy, not the source of truth.