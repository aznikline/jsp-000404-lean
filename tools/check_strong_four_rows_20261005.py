#!/usr/bin/env python3
"""Exact LRA diagnostics for strong anchored six-model row budgets.

This is a necessary real model, never a Lean proof.  The strip variable n is
real and unbounded above.  Only floors >=2 need geometric support: for a row
of defect c<n, a nonempty set of t<=c such gaps has total at least n-c+t.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import time

import z3

ROOT = Path(__file__).resolve().parents[1]
EDGES = list(itertools.combinations(range(5), 2))
TRIPLES = list(itertools.combinations(range(5), 3))
DEFECTS = {0: 2, 1: 3, 3: 3, 4: 2}


def orientations():
    out = []
    for mask in range(1024):
        closure = {e: set() for e in EDGES}
        for bit, (a, b, c) in enumerate(TRIPLES):
            x, y, z = (a, b), (a, c), (b, c)
            lo, mid, hi = (z, y, x) if (mask >> bit) & 1 else (x, y, z)
            closure[lo].add(mid)
            closure[mid].add(hi)
        while True:
            nxt = {a: closure[a] | set().union(*(closure[b] for b in closure[a]))
                   for a in EDGES}
            if nxt == closure:
                break
            closure = nxt
        if any(e in closure[e] for e in EDGES):
            continue
        rows = []
        for i in range(5):
            es = [tuple(sorted((i, j))) for j in range(5) if i != j]
            old = tuple(es)
            es.sort(key=lambda e: sum(e in closure[f] for f in old))
            assert all(es[b] in closure[es[a]] for a in range(4) for b in range(a + 1, 4))
            rows.append(es)
        out.append((mask, rows))
    assert len(out) == 62
    return out


def sorted_four(xs):
    xs = list(xs)
    for a, b in ((0, 1), (2, 3), (0, 2), (1, 3), (1, 2)):
        x, y = xs[a], xs[b]
        xs[a], xs[b] = z3.If(x <= y, x, y), z3.If(x <= y, y, x)
    return xs


def build(mask=None, rows=None, count_bound=False, minimum_n=4, fixed_n=None,
          quantized=False, threshold_three=False):
    n, delta = z3.Reals("n delta")
    period = n + delta
    theta = [z3.Real(f"theta{i}") for i in range(5)]
    chords = {e: z3.Real(f"d{e[0]}{e[1]}") for e in EDGES}
    constraints = {"n_lower": n >= minimum_n, "delta_lower": delta >= z3.RealVal("1/2"),
                   "delta_upper": delta < 1}
    if fixed_n is not None:
        constraints["n_fixed"] = n == fixed_n
    for i, t in enumerate(theta):
        constraints[f"theta{i}_lower"] = t >= 0
        constraints[f"theta{i}_upper"] = t <= delta
        if i < 4:
            constraints[f"theta{i}_strict"] = t < theta[i + 1]
    for (i, j), d in chords.items():
        constraints[f"corridor{i}{j}_lower"] = theta[i] + 1 <= d
        constraints[f"corridor{i}{j}_upper"] = d <= period - 1 + theta[j]
    for bit, (i, j, k) in enumerate(TRIPLES):
        x, y, z = chords[i, j], chords[i, k], chords[j, k]
        arms = [z3.And(x + 1 <= z, x < y, y < z),
                z3.And(z + 1 <= x, z < y, y < x)]
        constraints[f"triangle{i}{j}{k}"] = z3.Or(*arms) if mask is None else arms[(mask >> bit) & 1]
    row_gaps = {}
    for i, c in DEFECTS.items():
        xs = sorted_four(chords[tuple(sorted((i, j)))] for j in range(5) if i != j) if rows is None else [chords[e] for e in rows[i]]
        gaps = [xs[0] - theta[i]] + [xs[k + 1] - xs[k] for k in range(3)] + [theta[i] + period - xs[-1]]
        row_gaps[i] = gaps
        choices = [z3.And(*[gaps[k] >= 2 for k in subset],
                          z3.Sum([gaps[k] for k in subset]) >= n - c + size,
                          n >= c + size if count_bound else z3.BoolVal(True))
                   for size in range(1, c + 1)
                   for subset in itertools.combinations(range(5), size)]
        # A one-gap choice needs only g>=n-c+1 since n>c, which implies >=2
        # only for integer n.  Keep >=2 explicitly: actual n is natural and
        # actual large-gap floors are >=2 even in the stronger real relaxation.
        constraints[f"row{i}_strong_defect{c}"] = z3.Or(*choices)
        if quantized:
            actual_score = n - c
            large_count = z3.Sum([z3.If(g >= 2, 1, 0) for g in gaps])
            unit_count = z3.Sum([z3.If(g >= 1, 1, 0) for g in gaps])
            constraints[f"row{i}_each_gap_upper"] = z3.And(*[g < actual_score + 2 for g in gaps])
            constraints[f"row{i}_all_large_count"] = large_count <= actual_score
            constraints[f"row{i}_all_unit_count"] = unit_count <= c
            if threshold_three:
                constraints[f"row{i}_score_requires_threshold3"] = z3.Or(
                    *[g >= 3 for g in gaps], actual_score <= large_count)
    solver = z3.SolverFor("QF_LRA")
    solver.set(random_seed=0)
    for name, expression in constraints.items():
        solver.assert_and_track(expression, z3.Bool(name))
    return solver, n, delta, theta, chords, row_gaps, constraints


def val(model, expression):
    q = model.eval(expression, model_completion=True)
    return Fraction(q.numerator_as_long(), q.denominator_as_long())


def validated_snapshot(model, n, delta, theta, chords, gaps, mask, count_bound=False, minimum_n=4,
                       quantized=False, threshold_three=False):
    nv, de = val(model, n), val(model, delta)
    tv = [val(model, t) for t in theta]
    dv = {e: val(model, d) for e, d in chords.items()}
    checks = {"strip": nv >= minimum_n and Fraction(1, 2) <= de < 1,
              "theta": all(0 <= t <= de for t in tv) and all(tv[i] < tv[i + 1] for i in range(4)),
              "corridors": all(tv[i] + 1 <= d <= nv + de - 1 + tv[j] for (i, j), d in dv.items())}
    triangle_checks = []
    for bit, (i, j, k) in enumerate(TRIPLES):
        x, y, z = dv[i, j], dv[i, k], dv[j, k]
        arms = [x + 1 <= z and x < y < z, z + 1 <= x and z < y < x]
        triangle_checks.append(any(arms) if mask is None else arms[(mask >> bit) & 1])
    checks["triangles"] = all(triangle_checks)
    witnesses = {}
    for i, c in DEFECTS.items():
        gs = [val(model, g) for g in gaps[i]]
        feasible = [list(subset) for size in range(1, c + 1)
                    for subset in itertools.combinations(range(5), size)
                    if all(gs[k] >= 2 for k in subset) and sum(gs[k] for k in subset) >= nv - c + size
                    and (not count_bound or nv >= c + size)]
        checks[f"row{i}_strong_budget"] = bool(feasible)
        floors = [g.numerator // g.denominator for g in gs]
        floor_score = sum(max(q - 1, 0) for q in floors)
        witnesses[i] = {"gaps": list(map(str, gs)), "large_gap_subsets": feasible,
                        "actual_floors": floors, "actual_floor_score": floor_score,
                        "actual_floor_defect": str(nv - floor_score),
                        "requested_defect": c, "exact_defect_matches": nv - floor_score == c}
        if quantized:
            large_count = sum(g >= 2 for g in gs)
            checks[f"row{i}_quantized_bounds"] = (all(g < nv - c + 2 for g in gs) and
                large_count <= nv - c and sum(g >= 1 for g in gs) <= c)
            if threshold_three:
                checks[f"row{i}_threshold3"] = any(g >= 3 for g in gs) or nv - c <= large_count
    assert all(checks.values()), checks
    return {"n": str(nv), "delta": str(de), "theta": list(map(str, tv)),
            "chords": {f"{i},{j}": str(d) for (i, j), d in dv.items()},
            "rows": witnesses, "fraction_checks": checks,
            "point_realizability": "NOT_CLAIMED"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wall-seconds", type=float, default=58)
    parser.add_argument("--case-timeout-ms", type=int, default=2000)
    parser.add_argument("--count-bound", action="store_true")
    parser.add_argument("--minimum-n", type=int, default=4)
    parser.add_argument("--n-values", type=str, help="Comma-separated fixed natural strips.")
    parser.add_argument("--masks", type=str, help="Comma-separated orientation masks.")
    parser.add_argument("--quantized", action="store_true")
    parser.add_argument("--threshold-3", action="store_true")
    parser.add_argument("--report", type=Path, default=ROOT / "research/JSP404_STRONG_FOUR_ROWS_LRA_20261005.json")
    args = parser.parse_args()
    opts = orientations()
    if args.masks:
        requested = {int(m) for m in args.masks.split(",")}
        opts = [(m, rows) for m, rows in opts if m in requested]
    else:
        opts = [(None, None)] + opts
    ns = [int(v) for v in args.n_values.split(",")] if args.n_values else [None]
    plan = [(nv, mask, rows) for nv in ns for mask, rows in opts]
    report = {"diagnostic_only": True, "no_Lean_certificate": True, "solver": z3.get_version_string(),
              "n": f"real >={args.minimum_n}, unbounded", "delta": "1/2 <= delta < 1",
              "row_defects": DEFECTS, "large_gap_threshold": 2,
              "active_subset_totals": "n-c+t, 1<=t<=c", "cases": [], "unvisited": []}
    report["active_count_bound"] = "t <= n-c" if args.count_bound else "not encoded"
    report["fixed_n_values"] = ns
    report["all_gap_quantization"] = args.quantized
    report["threshold_three_cut"] = args.threshold_3
    start = time.monotonic()
    for index, (nv, mask, rows) in enumerate(plan):
        remaining = args.wall_seconds - (time.monotonic() - start)
        if remaining <= 0:
            report["unvisited"] = [{"n": v, "mask": m} for v, m, _ in plan[index:]]
            break
        solver, n, delta, theta, chords, gaps, constraints = build(
            mask, rows, args.count_bound, args.minimum_n, nv, args.quantized, args.threshold_3)
        solver.set(timeout=min(args.case_timeout_ms, max(1, int(remaining * 1000))))
        began = time.monotonic()
        status = solver.check()
        case = {"n": nv, "orientation": "joint" if mask is None else mask,
                "status": str(status), "seconds": round(time.monotonic() - began, 6)}
        if status == z3.unsat:
            case["unsat_core"] = [str(a) for a in solver.unsat_core()]
        elif status == z3.unknown:
            case["reason"] = solver.reason_unknown()
        else:
            case["model"] = validated_snapshot(solver.model(), n, delta, theta, chords, gaps, mask,
                                               args.count_bound, args.minimum_n,
                                               args.quantized, args.threshold_3)
        report["cases"].append(case)
        print(json.dumps({k: v for k, v in case.items() if k != "model"}), flush=True)
    report["elapsed_seconds"] = round(time.monotonic() - start, 6)
    report["counts"] = {s: sum(c["status"] == s for c in report["cases"]) for s in ("sat", "unsat", "unknown")}
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"counts": report["counts"], "unvisited": len(report["unvisited"]),
                      "elapsed_seconds": report["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    main()
