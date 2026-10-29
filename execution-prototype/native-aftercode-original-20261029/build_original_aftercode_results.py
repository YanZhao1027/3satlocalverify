#!/usr/bin/env python3
"""Parse original-source Lean runtime evidence, fail closed on omissions.

The upstream command used by the runner is the actual StructuredCalls.compiled
afterCode; neither this parser nor offline CI execute or verify the Lean kernel.
"""
import argparse
import hashlib
import json
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
STEPS_PATTERN = re.compile(
    r"^DIRECT_ORIGINAL_PROGRESS chunk=(\d+) steps=(\d+) halted=(\w+) "
    r"sourcePC=\(some (\d+)\) zeroWordBits=(\d+) peakDataBits=(\d+) "
    r"longestStack=(\d+) push=(\d+) pop=(\d+) peek=(\d+) "
    r"branch=(\d+) goto=(\d+) set=(\d+) copy=(\d+) "
    r"bitLogic=(\d+) halt=(\d+) chunkMs=(\d+)$"
)
CATEGORIES = ("push", "pop", "peek", "branch", "goto", "set", "copy", "bitLogic", "halt")


def field(line, name):
    match = re.search(r"\b" + re.escape(name) + r"=(\w+)", line)
    if not match:
        raise ValueError(f"Missing field {name} in {line[:120]!r}")
    return match.group(1)


def one_line(lines, prefix):
    matching = [line for line in lines if line.startswith(prefix)]
    if len(matching) != 1:
        raise ValueError(f"Expected one {prefix!r} line; got {len(matching)}")
    return matching[0]


def generate(raw_path, semantics_path):
    raw_bytes = raw_path.read_bytes()
    lines = raw_bytes.decode("utf-8").splitlines()
    compiler = one_line(lines, "DIRECT_ORIGINAL_COMPILER ")
    success = one_line(lines, "DIRECT_ORIGINAL_ALL_OPCODES_MATCH ")
    incoming = one_line(lines, "DIRECT_ORIGINAL_INPUT ")
    terminal = one_line(lines, "DIRECT_ORIGINAL_RESULT ")
    proc = one_line(lines, "WALL=")
    assert int(field(compiler, "sourceLabels")) == 119
    assert int(field(compiler, "originalTableSize")) == 119
    assert int(field(compiler, "independentTableSize")) == 119
    assert int(field(compiler, "originalEntry")) == 1
    assert int(field(success, "labels")) == 119
    assert field(incoming, "sourceRowBits") == "13"
    assert field(incoming, "theoreticalZeroWordBits") == "5120003"
    assert field(incoming, "initialDataBits") == "126"
    rows = []
    for line in lines:
        if not line.startswith("DIRECT_ORIGINAL_PROGRESS"):
            continue
        m = STEPS_PATTERN.fullmatch(line)
        if not m:
            raise ValueError("Malformed step line: " + line[:200])
        captures = m.groups()
        d = dict(zip(
            ("chunk", "sourceSteps", "halted", "pc", "zeroWordBits",
             "peakDataBits", "longestStack", *CATEGORIES, "chunkMs"),
            [int(x) if j != 2 else x == "true" for j, x in enumerate(captures)]
        ))
        rows.append(d)
    assert len(rows) == 8
    for ix, row in enumerate(rows):
        assert row["chunk"] == ix + 1
        assert row["sourceSteps"] == (ix + 1) * 1_000_000
        assert row["halted"] is False
        assert sum(row[k] for k in CATEGORIES) == row["sourceSteps"]
        if ix:
            assert row["zeroWordBits"] >= rows[ix - 1]["zeroWordBits"]
            assert row["peakDataBits"] >= rows[ix - 1]["peakDataBits"]
            for k in CATEGORIES:
                assert row[k] >= rows[ix - 1][k]
    assert rows[1]["zeroWordBits"] == 35238 and rows[1]["peakDataBits"] == 35368
    assert rows[3]["zeroWordBits"] == 70478 and rows[3]["peakDataBits"] == 70608
    assert rows[-1]["zeroWordBits"] == 140962
    assert rows[-1]["peakDataBits"] == 141092
    assert int(field(terminal, "steps")) == 8_000_000
    assert field(terminal, "halted") == "false"
    assert int(field(terminal, "currentBits")) == rows[-1]["zeroWordBits"]
    assert int(field(terminal, "targetBits")) == 5120003
    assert int(field(terminal, "maxDataBits")) == rows[-1]["peakDataBits"]
    for k in ("rowsPreserved", "allOpcodesMatch", "sourceFromUpstream"):
        assert field(terminal, k) == "true"
    assert field(proc, "EXIT") == "0"
    semantic = semantics_path.read_text().strip()
    assert re.search(r"^ORIGINAL_BITPROGRAM_COMPACT_STEP_DIFFERENTIAL_PASS cases=536 originalLabels=119 extraOpcodeCases=15 physicalRegisters=40 physicalStacks=896$", semantic, re.M)
    return {
        "date": "2026-10-29",
        "originalOpenAIMathCommit": "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a",
        "priorRepoCommit": "68b639ce72f70640fb506a7a77bea37601a89f56",
        "source": "OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled NativeLeafPreparation.afterCode 784 788",
        "input": "genuine nonempty 3-variable, 1-clause CNF; original native parameters/searches/serialization",
        "originalOpcodeTable": {"labels": 119, "entry": 1, "allOriginalAgainstFastMatched": True, "fullKernelCompilerEqualityTheorem": False},
        "independentInterpreter": {"testCasesAgainstOriginalExecInstr": 536, "programPositions": 119, "additionalSyntheticInstructions": 15, "fixtureVariants": 4, "universalKernelStepEquivalenceTheorem": False},
        "execution": {
            "command": "lean --run NativeFinishOriginalDirectRunner.lean 1000000 8",
            "sourceSteps": 8_000_000,
            "halted": False,
            "targetZeroWordBits": 5_120_003,
            "generatedZeroWordBits": rows[-1]["zeroWordBits"],
            "peakOccupiedStackDataBits": rows[-1]["peakDataBits"],
            "sourceRow777Bits": 13,
            "sourceRow777Preserved": True,
            "allOpcodeCountsSumToSteps": True,
            "wallSeconds": float(field(proc, "WALL").replace("s", "")),
            "maxProcessRssKb": int(re.search(r"RSS_KB=(\d+)kB", proc).group(1)),
            "checkpoints": rows
        },
        "evidence": {
            "rawLogFile": raw_path.name,
            "rawLogSha256": hashlib.sha256(raw_bytes).hexdigest(),
            "semanticAuditFile": semantics_path.name,
            "semanticAuditSha256": hashlib.sha256(semantics_path.read_bytes()).hexdigest()
        },
        "notEstablished": [
            "full afterCode termination",
            "upstream whole NativeLeafPreparation semantic execution",
            "general #SAT / HighQuery end-to-end execution",
            "complete kernel proof of compact interpreter equivalence",
            "kernel theorem for full original-vs-fast opcode table equality",
            "subexponential runtime advantage or contradiction of ETH"
        ]
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", type=pathlib.Path, default=HERE / "aftercode-direct-original-8m-20261029.raw.txt")
    ap.add_argument("--semantics", type=pathlib.Path, default=HERE / "step-semantic-audit-20261029.raw.txt")
    ap.add_argument("--out", type=pathlib.Path, default=HERE / "original-aftercode-results.json")
    args = ap.parse_args()
    result = generate(args.log, args.semantics)
    args.out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print("ORIGINAL_SOURCE_AFTERCODE_RESULTS_PARSED sourceSteps=8000000 sourceCodeLabels=119")


if __name__ == "__main__":
    main()
