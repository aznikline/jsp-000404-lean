#!/usr/bin/env python3
"""Necessary axiom gate; it does not replace statement-correspondence review."""

import argparse
import re
from pathlib import Path


def check(path):
    text = path.read_text()
    records = {}
    for name, raw in re.findall(r"^'([^']+)' depends on axioms: \[(.*?)\]$", text, re.M):
        records[name] = {axiom.strip() for axiom in raw.split(",") if axiom.strip()}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    required = {"Jsp404.sendov_lower", "Jsp404.sendov_upper"}
    missing = required - records.keys()
    invalid = {name: sorted(records[name] - allowed)
               for name in required & records.keys() if records[name] - allowed}
    if missing or invalid:
        print("REJECTED: original lower/upper root axiom gate.")
        for name in sorted(missing):
            print(name, "missing audit record")
        for name, axioms in sorted(invalid.items()):
            print(name, "unexpected axioms:", ", ".join(axioms))
        return 1
    print("PASSED: root axiom gate only; inspect exact original statement separately.")
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("audit_log", type=Path)
    args = parser.parse_args()
    raise SystemExit(check(args.audit_log))
