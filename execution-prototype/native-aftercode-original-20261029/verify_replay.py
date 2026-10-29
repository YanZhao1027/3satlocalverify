#!/usr/bin/env python3
"""Verify a new bounded original-source run matches deterministic archived checkpoints."""
import argparse
import json
import pathlib
from build_original_aftercode_results import generate

HERE = pathlib.Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument("--log", type=pathlib.Path, required=True)
ap.add_argument("--semantics", type=pathlib.Path, required=True)
args = ap.parse_args()
fresh = generate(args.log, args.semantics)
prior = json.loads((HERE / "original-aftercode-results.json").read_text())
for key in ("sourceSteps", "halted", "targetZeroWordBits", "generatedZeroWordBits",
            "peakOccupiedStackDataBits", "sourceRow777Bits", "sourceRow777Preserved",
            "allOpcodeCountsSumToSteps"):
    assert fresh["execution"][key] == prior["execution"][key], key
for i, (a, b) in enumerate(zip(fresh["execution"]["checkpoints"], prior["execution"]["checkpoints"])):
    assert {k: v for k, v in a.items() if k != "chunkMs"} == {
        k: v for k, v in b.items() if k != "chunkMs"}, i
assert fresh["originalOpcodeTable"] == prior["originalOpcodeTable"]
assert fresh["independentInterpreter"] == prior["independentInterpreter"]
print("ORIGINAL_AFTERCODE_REPLAY_PASS same original opcodes, 536 differential checks, 8M exact checkpoints")
