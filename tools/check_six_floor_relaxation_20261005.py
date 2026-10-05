#!/usr/bin/env python3
"""Diagnostic: unbounded real strip with floors relaxed to {0,1} union [2,infinity).

This is a necessary relaxation, not an actual floor model or a Lean proof.
The exact strip checker is separate and must not be confused with this one.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import z3
import check_strong_four_rows_20261005 as source


def rational(model, expression):
    value = model.eval(expression, model_completion=True)
    return Fraction(value.numerator_as_long(), value.denominator_as_long())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wall-seconds", type=float, default=58)
    parser.add_argument("--case-timeout-ms", type=int, default=1500)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if not 0 < args.wall_seconds <= 58 or args.case_timeout_ms <= 0:
        parser.error("Use a positive bounded budget of at most 58 seconds")
    plan = source.orientations()
    report = {"diagnostic_only": True, "Lean_certificate": False,
              "n": "real >=4, unbounded", "floor_domain": "{0,1} union [2,infinity)",
              "exact_integer_floors": False, "point_realizability": "NOT_CLAIMED",
              "cases": []}
    start = time.monotonic()
    for mask, rows in plan:
        remaining = args.wall_seconds - (time.monotonic() - start)
        if remaining <= 0:
            break
        solver, n, delta, theta, chords, gaps, constraints = source.build(
            mask, rows, count_bound=True, minimum_n=4,
            quantized=True, threshold_three=True)
        floors = {}
        for i, c in source.DEFECTS.items():
            floors[i] = [z3.Real(f"relaxed_floor_{i}_{j}") for j in range(5)]
            for j, (g, q) in enumerate(zip(gaps[i], floors[i])):
                constraints[f"floor_{i}_{j}_domain"] = z3.Or(q == 0, q == 1, q >= 2)
                constraints[f"floor_{i}_{j}_interval"] = z3.And(g >= 0, q <= g, g < q + 1)
            constraints[f"floor_{i}_score"] = z3.Sum(
                [z3.If(q >= 1, q - 1, 0) for q in floors[i]]) == n - c
        # Build is fresh for each mask; every extra constraint is asserted.
        for name, expression in constraints.items():
            if name.startswith("floor_"):
                solver.add(expression)
        solver.set(timeout=min(args.case_timeout_ms, max(1, int(remaining * 1000))), random_seed=0)
        began = time.monotonic()
        status = solver.check()
        case = {"orientation": mask, "status": str(status),
                "seconds": round(time.monotonic() - began, 6)}
        if status == z3.sat:
            model = solver.model()
            checked = {name: z3.is_true(model.eval(expression, model_completion=True))
                       for name, expression in constraints.items()}
            if not all(checked.values()):
                raise RuntimeError(f"SAT model fails asserted formulas: {checked}")
            nv = rational(model, n)
            row_records = {}
            for i, c in source.DEFECTS.items():
                gs = [rational(model, g) for g in gaps[i]]
                qs = [rational(model, q) for q in floors[i]]
                assert all(q in (0, 1) or q >= 2 for q in qs)
                assert all(g >= 0 and q <= g < q + 1 for g, q in zip(gs, qs))
                assert sum(max(q - 1, 0) for q in qs) == nv - c
                raw_floors = [g.numerator // g.denominator for g in gs]
                row_records[i] = {"gaps": list(map(str, gs)),
                    "relaxed_floors": list(map(str, qs)), "actual_floors": raw_floors,
                    "actual_floor_defect": str(nv - sum(max(q - 1, 0) for q in raw_floors)),
                    "requested_defect": c}
            case["model"] = {"n": str(nv), "delta": str(rational(model, delta)),
                "theta": [str(rational(model, t)) for t in theta],
                "chords": {f"{i},{j}": str(rational(model, d)) for (i, j), d in chords.items()},
                "rows": row_records, "all_asserted_formulas_checked": True,
                "point_realizability": "NOT_CLAIMED"}
        elif status == z3.unknown:
            case["reason"] = solver.reason_unknown()
        report["cases"].append(case)
        print(json.dumps({k: v for k, v in case.items() if k != "model"}), flush=True)
        if status == z3.sat:
            break
    report["unvisited"] = [mask for mask, _ in plan[len(report["cases"]):]]
    report["counts"] = {key: sum(c["status"] == key for c in report["cases"])
                        for key in ("sat", "unsat", "unknown")}
    report["complete_exclusion"] = (not report["unvisited"] and
        report["counts"]["unsat"] == len(plan))
    report["elapsed_seconds"] = round(time.monotonic() - start, 6)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"counts": report["counts"], "unvisited": len(report["unvisited"]),
                      "complete_exclusion": report["complete_exclusion"]}), flush=True)


if __name__ == "__main__":
    main()
