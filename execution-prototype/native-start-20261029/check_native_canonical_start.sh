#!/usr/bin/env bash
# Original source-derived LeafOuterProgram.start and NativeLeafSetup.canonicalStart.
# The independent LINKED program is validated against the original component
# traces; do not claim entire original source .code compiler equivalence or
# completed HighQuery/#SAT solver. Fail closed on all errors and timeouts.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
UPSTREAM="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
LOGDIR="${NATIVE_START_LOGDIR:-$REPO/.native-start-canonical-logs}"
mkdir -p "$LOGDIR"
export PATH="$HOME/.elan/bin:$PATH" ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$UPSTREAM" && lake env printenv LEAN_PATH 2>/dev/null):$REPO/execution-prototype:$REPO/execution-prototype/native-leaf-execution-20261028:$REPO/execution-prototype/native-leaf-nonterminal-20261028:$REPO/execution-prototype/native-core-cost-20261028:$HERE"
cd "$HERE"

for mod in NativeStartStages NativeStartLinked NativeCanonicalContinuation NativeCanonicalLinked NativeStartOriginalCodeProbe; do
  echo "LEAN_BUILD $mod"
  if grep -En '\b(sorry|admit|native_decide)\b' "$mod.lean" > "$LOGDIR/$mod.placeholders"; then
    echo "PROOF_PLACEHOLDER_REJECTED $mod" >&2; exit 5
  fi
  timeout --signal=TERM --kill-after=5s 42 lean -o "$mod.olean" "$mod.lean" > "$LOGDIR/$mod.build.log" 2>&1 || {
    echo "MODULE_FAILED $mod" >&2; tail -n 25 "$LOGDIR/$mod.build.log" >&2; exit 6;
  }
done

run() {
  local name="$1"; shift
  echo "LEAN_EXEC $name"
  /usr/bin/time -f 'LEAN_WALL=%es MAX_RSS_KB=%MkB' timeout --signal=TERM --kill-after=6s 48 \
    lean "$@" > "$LOGDIR/$name.log" 2>&1 || {
      echo "RUN_FAILED $name" >&2; tail -n 25 "$LOGDIR/$name.log" >&2; exit 7;
    }
}

run native-start-run --run NativeStartStagesRunner.lean 40000
run linked-start-optimized --run NativeStartLinkedRunner.lean 40000
run linked-boundary-audit --run NativeStartBoundaryAudit.lean
run canonical-stage-run --run NativeCanonicalContinuationRunner.lean 90000
run canonical-linked-run --run NativeCanonicalLinkedRunner.lean 60000
run canonical-linked-audit --run NativeCanonicalBoundaryAudit.lean
run canonical-size NativeCanonicalSize.lean
run source-axioms NativeStartProofAxioms.lean

python3 - "$LOGDIR/source-axioms.log" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
assert s.count('does not depend on any axioms')+s.count('depends on axioms:')==5,s
results=re.findall(r'depends on axioms: \[(.*?)\]',s,re.S)
allowed={'propext','Quot.sound','Classical.choice'}
for r in results:
 real={x.strip() for x in r.split(',') if x.strip()}
 assert real <= allowed,real-allowed
print('ORIGINAL_NATIVE_START_STANDARD_LEAN_AXIOMS_ONLY 5 results')
PY

# Historical direct CODE probes are attached as an archived, incomplete
# SAMPLE. They are NOT rerun as part of quick QA (two labels timed out).
cp original-code-probes-20261029.json "$LOGDIR/sampled-original-code-audit.json"
python3 build_native_start_results.py "$LOGDIR"
python3 validate_native_start_results.py
python3 -m py_compile build_native_start_results.py validate_native_start_results.py original_source_code_samples.py
echo 'ORIGINAL_NATIVE_CANONICAL_START_STAGE_AND_BOUNDARY_QA_PASS -- global compiler equality OPEN; no #SAT solver executed'
