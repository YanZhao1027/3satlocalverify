#!/usr/bin/env python3
"""Offline, fail-closed archived-log-to-JSON checks; not a Lean proof."""
import json
import pathlib
import sys
from build_original_aftercode_results import generate

HERE = pathlib.Path(__file__).resolve().parent
record_path = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "original-aftercode-results.json"
record = json.loads(record_path.read_text())
archive = generate(
    HERE / "aftercode-direct-original-8m-20261029.raw.txt",
    HERE / "step-semantic-audit-20261029.raw.txt",
)
assert record == archive, "Archive was modified or does not match recorded raw evidence"
old_path = HERE.parent / "native-code-parameters-20261029/native-code-assembly-results.json"
old = json.loads(old_path.read_text())["lastSelectorSuffixPrefix"]
assert record["execution"]["checkpoints"][1]["zeroWordBits"] == old["zeroBitsAfter2mInstructions"]
assert record["execution"]["checkpoints"][1]["peakDataBits"] == old["occupiedDataPeakAt2mSteps"]
assert record["execution"]["sourceSteps"] == 8000000
assert record["originalOpcodeTable"]["fullKernelCompilerEqualityTheorem"] is False
assert record["independentInterpreter"]["universalKernelStepEquivalenceTheorem"] is False
assert record["notEstablished"] and record["execution"]["halted"] is False
print("ORIGINAL_AFTERCODE_OFFLINE_ARCHIVE_PASS; 8M source instructions; no full halt, no ETH claim")
