#!/usr/bin/env python3
"""Bounded diagnostic of necessary scalar six-centre models, never a proof.

Every gap floor in the four specified rows is encoded exactly. A SAT result
is independently checked with rational arithmetic; planar realization is not
asserted. An incomplete or timed-out run cannot certify universal exclusion.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import time

import z3
import check_strong_four_rows_20261005 as necessary


def fraction(model, expression):
    value = model.eval(expression, model_completion=True)
    if z3.is_int_value(value):
        return Fraction(value.as_long())
    return Fraction(value.numerator_as_long(), value.denominator_as_long())


def exact_case(n_value, mask, rows):
    solver, n, delta, theta, chords, gaps, constraints = necessary.build(
        mask, rows, count_bound=True, minimum_n=4, fixed_n=n_value,
        quantized=True, threshold_three=True)
    floors = {}
    for i, c in necessary.DEFECTS.items():
        floors[i] = [z3.Int(f"floor_{i}_{j}") for j in range(5)]
        for j, (g, q) in enumerate(zip(gaps[i], floors[i])):
            solver.add(g >= 0, q >= 0, q <= g, g < q + 1)
        solver.add(z3.Sum([z3.If(q >= 1, q - 1, 0) for q in floors[i]]) == n - c)
    return solver, n, delta, theta, chords, gaps, floors


def independently_validate(model, n, delta, theta, chords, gaps, floors, mask):
    nv = fraction(model, n)
    de = fraction(model, delta)
    ts = [fraction(model, t) for t in theta]
    ds = {e: fraction(model, d) for e, d in chords.items()}
    checks = {
        "integer_strip": nv.denominator == 1 and 4 <= nv <= 24,
        "delta": Fraction(1, 2) <= de < 1,
        "theta": all(0 <= t <= de for t in ts) and all(a < b for a, b in zip(ts, ts[1:])),
        "corridors": all(ts[i] + 1 <= d <= nv + de - 1 + ts[j] for (i, j), d in ds.items()),
    }
    triangles = []
    for bit, (i, j, k) in enumerate(necessary.TRIPLES):
        x, y, z = ds[i, j], ds[i, k], ds[j, k]
        arms = [x + 1 <= z and x < y < z, z + 1 <= x and z < y < x]
        triangles.append(any(arms) if mask is None else arms[(mask >> bit) & 1])
    checks["all_triangles"] = all(triangles)
    row_records = {}
    for i, c in necessary.DEFECTS.items():
        ordered = sorted(ds[tuple(sorted((i, j)))] for j in range(5) if i != j)
        actual_gaps = [ordered[0] - ts[i]] + [b - a for a, b in zip(ordered, ordered[1:])] + [ts[i] + nv + de - ordered[-1]]
        solver_gaps = [fraction(model, g) for g in gaps[i]]
        actual_floors = [g.numerator // g.denominator for g in actual_gaps]
        solver_floors = [fraction(model, q) for q in floors[i]]
        score = sum(max(q - 1, 0) for q in actual_floors)
        checks[f"row_{i}"] = (
            solver_gaps == actual_gaps and sum(actual_gaps) == nv + de
            and all(g >= 0 for g in actual_gaps)
            and solver_floors == actual_floors and nv - score == c)
        row_records[i] = {"gaps": list(map(str, actual_gaps)), "floors": actual_floors,
                          "score": score, "defect": str(nv - score)}
    if not all(checks.values()):
        raise RuntimeError(f"Independent rational check failed: {checks}")
    return {"n": str(nv), "delta": str(de), "theta": list(map(str, ts)),
            "chords": {f"{i},{j}": str(v) for (i, j), v in ds.items()},
            "rows": row_records, "checks": checks,
            "point_realizability": "NOT_CLAIMED"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n-values", default="6,8,12,24")
    parser.add_argument("--wall-seconds", type=float, default=58)
    parser.add_argument("--case-timeout-ms", type=int, default=1500)
    parser.add_argument("--joint", action="store_true")
    parser.add_argument("--profile", choices=("between", "front", "back"), default="between")
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.profile == "front":
        necessary.DEFECTS = {0: 2, 1: 2, 2: 3, 3: 3, 4: 3}
    elif args.profile == "back":
        necessary.DEFECTS = {0: 3, 1: 3, 2: 3, 3: 2, 4: 2}
    ns = [int(v) for v in args.n_values.split(",")]
    if not ns or any(not 4 <= n <= 24 for n in ns):
        parser.error("Requested strips must lie in 4..24")
    if not 0 < args.wall_seconds <= 58 or args.case_timeout_ms <= 0:
        parser.error("Use a positive bounded budget of at most 58 seconds")
    orientations = [(None, None)] if args.joint else necessary.orientations()
    plan = [(n, mask, rows) for n in ns for mask, rows in orientations]
    report = {"diagnostic_only": True, "Lean_certificate": False,
              "exact_gap_floors": True, "point_realizability": "NOT_CLAIMED",
              "source_model": "SixModelCompression.ModelSix", "solver": z3.get_version_string(),
              "requested_n": ns, "profile": args.profile,
              "row_defects": necessary.DEFECTS, "cases": []}
    start = time.monotonic()
    for index, (nv, mask, rows) in enumerate(plan):
        remaining = args.wall_seconds - (time.monotonic() - start)
        if remaining <= 0:
            break
        solver, n, delta, theta, chords, gaps, floors = exact_case(nv, mask, rows)
        solver.set(timeout=min(args.case_timeout_ms, max(1, int(remaining * 1000))), random_seed=0)
        began = time.monotonic()
        status = solver.check()
        case = {"n": nv, "orientation": "joint" if mask is None else mask,
                "status": str(status), "seconds": round(time.monotonic() - began, 6)}
        if status == z3.sat:
            case["model"] = independently_validate(solver.model(), n, delta, theta, chords, gaps, floors, mask)
        elif status == z3.unknown:
            case["reason"] = solver.reason_unknown()
        report["cases"].append(case)
        print(json.dumps({k: v for k, v in case.items() if k != "model"}), flush=True)
        if status == z3.sat:
            break
    visited = len(report["cases"])
    report["unvisited"] = [{"n": nv, "orientation": "joint" if mask is None else mask}
                           for nv, mask, _ in plan[visited:]]
    counts = Counter(case["status"] for case in report["cases"])
    report["counts"] = {key: counts[key] for key in ("sat", "unsat", "unknown")}
    report["complete_exclusion"] = visited == len(plan) and counts["unsat"] == len(plan)
    report["elapsed_seconds"] = round(time.monotonic() - start, 6)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"counts": report["counts"], "unvisited": len(report["unvisited"]),
                      "complete_exclusion": report["complete_exclusion"]}), flush=True)


if __name__ == "__main__":
    main()
