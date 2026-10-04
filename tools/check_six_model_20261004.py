#!/usr/bin/env python3
"""Diagnostic for the exact ModelSix necessary scalar constraints.

This solver is not trusted by Lean. SAT models are independently checked using
fractions; they are not claimed to have a planar realization. UNSAT and UNKNOWN
are diagnostics, not mathematical proofs.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path
import time

import z3


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "research/JSP404_SIX_MODEL_DIAGNOSTIC_20261004.json"
TIMEOUT_MS = 10000
WALL_SECONDS = 300


def as_fraction(value):
    return Fraction(value.numerator_as_long(), value.denominator_as_long())


def qstr(value):
    return str(value)


def sorted4(xs):
    xs = list(xs)
    for a, b in [(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]:
        x, y = xs[a], xs[b]
        xs[a] = z3.If(x <= y, x, y)
        xs[b] = z3.If(x <= y, y, x)
    return xs


def build(n, defects):
    s = z3.Solver()
    s.set(timeout=TIMEOUT_MS)
    delta = z3.Real("delta")
    theta = [z3.Real(f"theta_{i}") for i in range(5)]
    d = {(i, j): z3.Real(f"d_{i}_{j}") for i in range(5) for j in range(i + 1, 5)}
    chord = lambda i, j: d[tuple(sorted((i, j)))]
    s.add(delta >= z3.RealVal("1/2"), delta < 1)
    for t in theta:
        s.add(t >= 0, t <= delta)
    for i in range(4):
        s.add(theta[i] < theta[i + 1])
    for (i, j), x in d.items():
        s.add(theta[i] + 1 <= x, x <= n + delta - 1 + theta[j])
    for i, j, k in itertools.combinations(range(5), 3):
        x, y, z = chord(i, j), chord(i, k), chord(j, k)
        s.add(z3.Or(z3.And(x + 1 <= z, x < y, y < z),
                    z3.And(z + 1 <= x, z < y, y < x)))
    for i in range(5):
        xs = sorted4(chord(i, j) for j in range(5) if j != i)
        gaps = [xs[0] - theta[i]]
        gaps += [xs[k + 1] - xs[k] for k in range(3)]
        gaps += [theta[i] + n + delta - xs[-1]]
        floors = [z3.Int(f"q_{i}_{k}") for k in range(5)]
        for g, q in zip(gaps, floors):
            s.add(g >= 0, q >= 0, q <= n, q <= g, g < q + 1)
        score = z3.Sum([z3.If(q >= 1, q - 1, 0) for q in floors])
        s.add(score == n - defects[i])
    return s, delta, theta, d


def validate(n, defects, delta, theta, d):
    chord = lambda i, j: d[tuple(sorted((i, j)))]
    checks = {"n_at_least_3": n >= 3,
              "delta_high_range": Fraction(1, 2) <= delta < 1,
              "theta_bounds": all(0 <= t <= delta for t in theta),
              "theta_strict": all(theta[i] < theta[i + 1] for i in range(4)),
              "corridors": all(theta[i] + 1 <= x <= n + delta - 1 + theta[j]
                               for (i, j), x in d.items())}
    triangle_records = []
    for i, j, k in itertools.combinations(range(5), 3):
        x, y, z = chord(i, j), chord(i, k), chord(j, k)
        ok = (x + 1 <= z and x < y < z) or (z + 1 <= x and z < y < x)
        triangle_records.append({"indices": [i, j, k], "valid": ok})
    checks["all_triangles"] = all(r["valid"] for r in triangle_records)
    row_records = []
    for i in range(5):
        xs = sorted(chord(i, j) for j in range(5) if j != i)
        gaps = [xs[0] - theta[i]] + [xs[k + 1] - xs[k] for k in range(3)]
        gaps += [theta[i] + n + delta - xs[-1]]
        floors = [g.numerator // g.denominator for g in gaps]
        score = sum(max(q - 1, 0) for q in floors)
        valid = (all(g >= 0 for g in gaps) and
                 all(0 <= q <= n for q in floors) and n - score == defects[i])
        row_records.append({"row": i, "sorted_chords": list(map(qstr, xs)),
                            "gaps": list(map(qstr, gaps)), "floors": floors,
                            "score": score, "defect": n - score, "valid": valid})
    checks["all_rows"] = all(r["valid"] for r in row_records)
    return {"method": "Python Fraction exact arithmetic, independently recomputed floors",
            "checks": checks, "valid": all(checks.values()),
            "rows": row_records, "triangles": triangle_records}


def summarize(report):
    planned = {n: 3 * (1 + 3 * (min(n, 9) - 3)) for n in range(3, 25)}
    visited = Counter(c["n"] for c in report["cases"])
    status = Counter(c["status"] for c in report["cases"])
    report["coverage"] = {
        "planned_cases": sum(planned.values()), "visited_cases": len(report["cases"]),
        "unvisited_cases": sum(planned.values()) - len(report["cases"]),
        "status_counts": dict(status),
        "fully_visited_n": [n for n, count in planned.items() if visited[n] == count],
        "per_n": {str(n): {"planned": count, "visited": visited[n]} for n, count in planned.items()},
    }
    report["case_constraints"] = "BARE exact ModelSix; no post-deletion rigidity assumptions"
    report["enriched_deletion_clauses"] = {
        "tested": False,
        "reason": "No bare SAT witness was found within this bounded run; enrichment trigger did not occur.",
    }


def main():
    start = time.monotonic()
    source = (ROOT / "Jsp000404/SixModelCompression.lean").read_bytes()
    record = source.split(b"structure ModelSix", 1)[1].split(b"noncomputable def rowDefect", 1)[0]
    report = {
        "date": "2026-10-04", "z3_version": z3.get_version_string(),
        "model_source": "Jsp000404/SixModelCompression.lean",
        "model_source_sha256": hashlib.sha256(source).hexdigest(),
        "model_record_sha256": hashlib.sha256(record).hexdigest(),
        "scope": "Necessary scalar constraints only; no planar realization claim",
        "delta_range": "1/2 <= delta < 1", "timeout_ms_per_case": TIMEOUT_MS,
        "wall_limit_seconds": WALL_SECONDS, "cases": [], "first_sat": None,
    }
    stop = False
    for n in range(3, 25):
        for low_pair in [(0, 1), (3, 4), (0, 4)]:
            tail = [i for i in range(5) if i not in low_pair]
            profiles = [(None, 3)] + [(i, c) for c in range(4, min(n, 9) + 1) for i in tail]
            for deep, c in profiles:
                if time.monotonic() - start >= WALL_SECONDS:
                    stop = True
                    report["stop_reason"] = "wall_limit"
                    break
                defects = [2 if i in low_pair else (c if i == deep else 3) for i in range(5)]
                case = {"n": n, "low_ranks": list(low_pair), "deep_rank": deep,
                        "deep_defect": c, "defects": [1] + defects}
                s, delta, theta, d = build(n, defects)
                # Keep the per-case solver budget within the remaining wall budget.
                remaining_ms = int(1000 * (WALL_SECONDS - (time.monotonic() - start)))
                s.set(timeout=max(1, min(TIMEOUT_MS, remaining_ms)))
                before = time.monotonic()
                result = s.check()
                case["status"] = str(result).upper()
                case["seconds"] = round(time.monotonic() - before, 3)
                if result == z3.unknown:
                    case["reason_unknown"] = s.reason_unknown()
                report["cases"].append(case)
                print(json.dumps(case), flush=True)
                if result == z3.sat:
                    model = s.model()
                    dv = as_fraction(model.eval(delta))
                    tv = [as_fraction(model.eval(t)) for t in theta]
                    chords = {ij: as_fraction(model.eval(x)) for ij, x in d.items()}
                    exact = {"delta": qstr(dv), "theta": list(map(qstr, tv)),
                             "chords": {f"{i},{j}": qstr(x) for (i, j), x in chords.items()}}
                    validation = validate(n, defects, dv, tv, chords)
                    if not validation["valid"]:
                        raise AssertionError(validation)
                    report["first_sat"] = {"case": case, "model": exact,
                                           "validation": validation}
                    report["stop_reason"] = "first_sat"
                    stop = True
                    break
            if stop:
                break
        if stop:
            break
    report.setdefault("stop_reason", "all_requested_cases_exhausted")
    report["elapsed_seconds"] = round(time.monotonic() - start, 3)
    report["interpretation"] = (
        "A SAT witness invalidates only exclusion from these necessary scalar constraints. "
        "It is not an actual geometric counterexample. UNSAT/UNKNOWN solver results are not Lean proofs."
    )
    summarize(report)
    OUT.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"saved {OUT}", flush=True)


if __name__ == "__main__":
    main()
