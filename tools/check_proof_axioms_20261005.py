#!/usr/bin/env python3
"""Check every requested declaration in the composed Lean axiom audit.

The verified mode excludes only the explicitly retained arbitrary-N root.
The root mode checks the original lower/upper pair and must currently fail.
The log must come from a successful source Lean invocation under trust=0.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ORIGINAL_ROOTS = {"Jsp404.sendov_lower", "Jsp404.sendov_upper"}


def check(audit: Path, log: Path, mode: str) -> bool:
    declarations = re.findall(r"^#print axioms (\S+)", audit.read_text(), re.M)
    assert len(set(declarations)) == len(declarations), "duplicate audit declaration"
    requested = [name for name in declarations if
                 (name in ORIGINAL_ROOTS if mode == "root" else
                  name != "Jsp404.sendov_lower")]
    assert requested, "empty declaration gate"
    text = log.read_text()
    groups = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    groups += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    observed: dict[str, list[set[str]]] = {}
    for name, group in groups:
        observed.setdefault(name, []).append({a.strip() for a in group.split(",") if a.strip()})
    failures = []
    axioms = {}
    for name in requested:
        found = observed.get(name, [])
        if len(found) != 1:
            failures.append({"declaration": name, "reason": "missing or repeated axiom report"})
            continue
        axioms[name] = sorted(found[0])
        unexpected = sorted(found[0] - ALLOWED)
        if unexpected:
            failures.append({"declaration": name, "unexpected_axioms": unexpected})
    if re.search(r"(^|\n).*\berror:", text):
        failures.append({"reason": "Lean error diagnostic in source audit log"})
    print(json.dumps({"status": "FAIL" if failures else "PASS", "mode": mode,
                      "declaration_count": len(requested), "allowed_axioms": sorted(ALLOWED),
                      "axioms": axioms, "failures": failures}, indent=2))
    return not failures


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path, default=ROOT / "verification/oct5-review/ProofAudit.lean")
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--mode", choices=("verified", "root"), default="verified")
    args = parser.parse_args()
    raise SystemExit(0 if check(args.audit, args.log, args.mode) else 1)
