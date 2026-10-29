#!/usr/bin/env python3
"""Check raw Lean #print axioms evidence. Does not verify Lean itself."""
import argparse
import re
from pathlib import Path

THEOREMS = (
    ("interpreter", ("IndependentNativeCompactProof.runOne_exact",)),
    ("trace", (
        "IndependentNativeTraceProof.all_fuel_exact",
        "IndependentNativeTraceProof.bitStep_exact",
        "IndependentNativeTraceProof.sourceArray_is_ofFn",
        "IndependentNativeTraceProof.direct_table_fuel_exact"
    )),
    ("specialization", (
        "IndependentNativeAfterCodeCertificate.original_array_exact",
        "IndependentNativeAfterCodeCertificate.afterCode_direct_fuel_exact",
        "IndependentNativeAfterCodeCertificate.afterCode_one_step_exact"
    )),
)
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}


def verify(logs):
    checked = 0
    for group, names in THEOREMS:
        content = logs[group]
        declarations = re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]", content, re.S
        )
        observed = {name: [x.strip() for x in values.split(",") if x.strip()]
                    for name, values in declarations}
        if set(observed) != set(names) or len(declarations) != len(names):
            raise ValueError(f"{group}: unexpected proof audit declarations: {list(observed)}")
        for name, actual in observed.items():
            if set(actual) != PERMITTED or len(actual) != len(PERMITTED):
                raise ValueError(f"{name}: unsupported axiom dependency: {actual}")
            checked += 1
    return checked


def main():
    p = argparse.ArgumentParser()
    for key, _ in THEOREMS:
        p.add_argument("--" + key, type=Path, required=True)
    args = p.parse_args()
    files = {key: getattr(args, key).read_text() for key, _ in THEOREMS}
    total = verify(files)
    assert total == 8
    print("UNIVERSAL_KERNEL_AXIOM_AUDIT_PASS theorems=8 only=propext,Classical.choice,Quot.sound")


if __name__ == "__main__":
    main()
