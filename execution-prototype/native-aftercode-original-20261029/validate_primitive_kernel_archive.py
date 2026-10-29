#!/usr/bin/env python3
"""Offline evidence validation only. Actual Lean proof checking is on Ubuntu."""
import hashlib
import json
from pathlib import Path
from verify_kernel_axioms import verify

HERE = Path(__file__).resolve().parent
FILES = {
    "interpreter": "kernel-axioms-interpreter-20261029.raw.txt",
    "trace": "kernel-axioms-fuel-20261029.raw.txt",
    "specialization": "kernel-axioms-aftercode-20261029.raw.txt"
}
RECORD = HERE / "primitive-kernel-results.json"


def make_record():
    content = {k: (HERE / v).read_text() for k, v in FILES.items()}
    count = verify(content)
    assert count == 8
    return {
        "date": "2026-10-29",
        "openaiMathUpstreamCommit": "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a",
        "leanToolchain": "4.34.1",
        "kind": "Lean kernel proof source/axiom audit and archived Ubuntu replay",
        "theoremAxiomsChecked": count,
        "allowedAxioms": ["propext", "Classical.choice", "Quot.sound"],
        "proofClaims": {
            "allPrimitiveInstructions": True,
            "allWellTypedBitProgramConfigurations": True,
            "allFiniteFuel": True,
            "allOriginalAfterCodeCompiledLabels": True,
            "directSourceTableExecutionProved": True
        },
        "limitations": {
            "fullNativeCodeAssemblyIndependentCompilerEquivalence": False,
            "runInstrumentedMetricsInterpreterEquivalence": False,
            "originalAfterCodeFullHalt": False,
            "entireHighQuerySATExecuted": False,
            "generalSubexponentialSATAdvantageVerified": False
        },
        "evidenceSha256": {
            key: hashlib.sha256((HERE / file).read_bytes()).hexdigest()
            for key, file in FILES.items()
        }
    }


def main():
    expected = make_record()
    recorded = json.loads(RECORD.read_text())
    assert recorded == expected, "Archived proof evidence or metadata changed"
    print("PRIMITIVE_KERNEL_OFFLINE_ARCHIVE_PASS theorems=8; complete-solver claims remain false")


if __name__ == "__main__":
    main()
