#!/usr/bin/env python3
"""Fail-closed parser of actual complete original BitProgram afterCode run.

The CPU runner charges EVERY primitive opcode using the exact upstream source
compiled table. This parser certifies logs and internal arithmetic only;
the separate Lean files carry the formal semantics proof.
"""
import argparse
import hashlib
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
CATS = ("push", "pop", "peek", "branch", "bitLogic", "goto", "set", "copy", "halt")
NUMS = ("chunk", "steps", "zeroWordBits", "measuredStackBits", "peakDataBits", "sourceChunkMs")

def parse_fields(line):
    return dict(re.findall(r"([A-Za-z][A-Za-z0-9_]*)=([^\s]+)", line))

def parse(path, baseline_path):
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    lines = text.splitlines()

    def unique(prefix):
        matches = [line for line in lines if line.startswith(prefix)]
        assert len(matches) == 1, (prefix, len(matches))
        return parse_fields(matches[0])

    start = unique("FAST_METER_START ")
    assert start["sourceLabels"] == "119"
    assert start["sourceFromOriginal"] == "true"
    assert start["initialBits"] == "126"
    assert start["targetBits"] == "5120003"
    assert start["chunkSize"] == "5000000"
    assert start["chunks"] == "68"
    assert start["baselineMillion"] == "0"
    raw_checkpoints = [parse_fields(x) for x in lines if x.startswith("FAST_METER_PROGRESS ")]
    assert len(raw_checkpoints) == 59
    checkpoints = []
    for i, row in enumerate(raw_checkpoints):
        assert row["sourceRowPreserved"] == "true"
        assert row["halted"] == ("true" if i == 58 else "false")
        assert row["chunk"] == str(i+1)
        assert row["sourcePC"] == ("none" if i == 58 else row["sourcePC"])
        checkpoint = {k:int(row[k]) for k in NUMS}
        checkpoint["halted"] = row["halted"] == "true"
        checkpoint["pc"] = row["sourcePC"]
        if i<58:
            assert checkpoint["steps"] == (i+1)*5_000_000
        else:
            assert checkpoint["steps"] == 290_560_512
        assert checkpoint["measuredStackBits"] <= checkpoint["peakDataBits"]
        checkpoints.append(checkpoint)
    final = unique("FAST_METER_RESULT ")
    assert final["halted"] == "true"
    assert final["steps"] == "290560512"
    assert final["zeroWordBits"] == final["expectedZeroWordBits"] == "5120003"
    assert final["peakOccupiedDataBits"] == "5120133"
    assert final["sourceRowPreserved"] == "true"
    assert final["halt"] == "1"
    assert sum(int(final[k]) for k in CATS) == 290_560_512
    assert checkpoints[-1]["zeroWordBits"] == int(final["zeroWordBits"])
    assert checkpoints[-1]["peakDataBits"] == int(final["peakOccupiedDataBits"])
    fully = unique("FAST_METER_FINISHED_ORIGINAL_FULL_896_STACKS_PASS ")
    assert fully["expectedZeroWordBits"] == "5120003"
    assert fully["sourceInstructionSteps"] == "290560512"
    perf = unique("WALL=")
    assert perf["EXIT"] == "0"
    assert float(perf["WALL"].removesuffix("s")) < 355
    baseline_text = baseline_path.read_text()
    assert "FAST_METER_BASELINE_FULL_STATE_PASS steps=8000000 all40regsEqual=true all896StacksEqual=true allCountersEqual=true" in baseline_text
    return {
        "date": "2026-10-29",
        "originalUpstreamCommit": "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a",
        "originalCommand": "StructuredCalls.compiled NativeLeafPreparation.afterCode 784 788",
        "sourceLabels": 119,
        "initialFormula": "n=3, m=1, nonempty clause x0",
        "priorPhysicalState": "genuine original numeric parameters + both code searches + serialized 13-bit row",
        "run": {
            "sourceBitInstructions": 290_560_512,
            "halted": True,
            "expectedZeroWordBits": 5_120_003,
            "actualZeroWordBits": 5_120_003,
            "maxOccupiedStackDataBits": 5_120_133,
            "finalOccupiedStackDataBits": checkpoints[-1]["measuredStackBits"],
            "complete896StackMatchesOriginalFinishedWords": True,
            "originalSerializedRowPreserved": True,
            "opcodeCounts": {k: int(final[k]) for k in CATS},
            "checkpointCount": len(checkpoints),
            "checkpoints": checkpoints,
            "wallSeconds": float(perf["WALL"].removesuffix("s")),
            "maxProcessRSSKb": int(perf["MAX_RSS_KB"].removesuffix("kB"))
        },
        "semantics": {
            "kernelCheckedUniversalRunOne": True,
            "kernelCheckedDirectTableAllFuel": True,
            "kernelCheckedOriginalTraceReplay": True,
            "kernelCheckedCachedOriginalFinishedWordsEquality": True,
            "standardAxiomsOnly": ["propext", "Classical.choice", "Quot.sound"],
            "hostMeterUniversalProof": False,
            "hostMeterFullStateReferenceAt8M": True
        },
        "evidence": {
            "fullRawLog": path.name,
            "fullRawLogSHA256": hashlib.sha256(raw).hexdigest(),
            "baselineLog": baseline_path.name,
            "baselineLogSHA256": hashlib.sha256(baseline_path.read_bytes()).hexdigest(),
        },
        "notEstablished": [
            "entire original NativeLeafPreparation.command in one original compiled table",
            "full query loop, HighQueryProgram or SAT counting",
            "general subexponential runtime proof",
            "proof of ETH refutation",
            "physical TM2 elapsed runtime or exact primitive tape cost",
            "kernel proof of full host instrumentation loop",
            "universal compiler equivalence for independent native code assembly linker",
        ],
    }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=pathlib.Path, default=HERE/"aftercode-original-complete.raw.txt")
    parser.add_argument("--baseline", type=pathlib.Path, default=HERE/"fast-meter-8m-audit.raw.txt")
    parser.add_argument("--out", type=pathlib.Path, default=HERE/"aftercode-original-complete-results.json")
    args = parser.parse_args()
    result = parse(args.log, args.baseline)
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print("ORIGINAL_AFTERCODE_COMPLETE_LOG_VERIFIED exactHaltSteps=290560512 exactZeroBits=5120003 full896StorePass=true")

if __name__ == "__main__":
    main()
