#!/usr/bin/env python3
"""Recompute the full archived experiment result from raw original logs."""
import json
from pathlib import Path
from build_full_aftercode_results import HERE, parse

got = json.loads((HERE/"aftercode-original-complete-results.json").read_text())
want = parse(HERE/"aftercode-original-complete.raw.txt", HERE/"fast-meter-8m-audit.raw.txt")
assert got == want
assert got["run"]["sourceBitInstructions"] == sum(got["run"]["opcodeCounts"].values())
assert got["run"]["halted"] and got["run"]["complete896StackMatchesOriginalFinishedWords"]
assert got["semantics"]["hostMeterUniversalProof"] is False
assert got["notEstablished"]
print("ORIGINAL_AFTERCODE_COMPLETE_OFFLINE_ARCHIVE_PASS (not full SAT/ETH)")
