#!/usr/bin/env python3
"""Emit ordinary Lean prefix/suffix certificates, without trusting an SMT result.

Only the seven orientations selected by the elementary three-gap terminal are
exported.  The other 55 orientations still require an integer certificate.
Generated proofs use the actual ModelSix row permutation and natural floors.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

TRIPLES = list(itertools.combinations(range(5), 3))
EDGES = list(itertools.combinations(range(5), 2))
BEGIN = "-- BEGIN GENERATED THREE-GAP CERTIFICATES"
END = "-- END GENERATED THREE-GAP CERTIFICATES"


def orientations():
    out = []
    for mask in range(1024):
        closure = {e: set() for e in EDGES}
        for bit, (a, b, c) in enumerate(TRIPLES):
            x, y, z = (a, b), (a, c), (b, c)
            low, mid, high = (z, y, x) if (mask >> bit) & 1 else (x, y, z)
            closure[low].add(mid)
            closure[mid].add(high)
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
            es.sort(key=lambda a: sum(a in closure[b] for b in old))
            assert all(es[b] in closure[es[a]] for a in range(4)
                       for b in range(a + 1, 4))
            rows.append(es)
        out.append((mask, rows))
    assert len(out) == 62
    return out


def chord(e):
    return f"M.d {e[0]} {e[1]}"


def lean_list(es):
    return "[" + ", ".join(chord(e) for e in es) + "]"


def permutation_term(raw, target):
    current = list(raw)
    terms = []
    for rank, desired in enumerate(target):
        j = current.index(desired)
        while j > rank:
            k = j - 1
            tail = lean_list(current[k + 2:])
            term = f"(List.Perm.swap ({chord(current[k + 1])}) ({chord(current[k])}) {tail})"
            for e in reversed(current[:k]):
                term = f"({term}.cons ({chord(e)}))"
            terms.append(term)
            current[k], current[k + 1] = current[k + 1], current[k]
            j -= 1
    assert current == list(target)
    if not terms:
        return f"List.Perm.refl {lean_list(raw)}"
    term = terms[0]
    for step in terms[1:]:
        term = f"({term}.trans {step})"
    return term


def selected():
    found = []
    for mask, rows in orientations():
        for i in (1, 3):
            neighbours = [e[0] if e[1] == i else e[1] for e in rows[i]]
            colours = ["L"] + ["L" if j < i else "R" for j in neighbours] + ["R"]
            forced = [j for j in range(5) if colours[j] != colours[j + 1]]
            if i == 1 and forced == [0, 1, 2] and neighbours[2] < neighbours[3]:
                found.append((mask, rows, i, neighbours, "prefix"))
                break
            if i == 3 and forced == [2, 3, 4] and neighbours[0] < neighbours[1]:
                found.append((mask, rows, i, neighbours, "suffix"))
                break
    return found


def emit_case(mask, rows, i, neighbours, kind):
    lines = [f"/-- Three-gap certificate for acyclic orientation {mask}. -/",
             f"theorem orientation_{mask}_impossible {{n : ℕ}} (M : ModelSix n)"]
    for bit, (a, b, c) in enumerate(TRIPLES):
        x, y, z = chord((a, b)), chord((a, c)), chord((b, c))
        lo, hi = (z, x) if (mask >> bit) & 1 else (x, z)
        lines.append(f"    (h{a}{b}{c} : {lo} + 1 ≤ {hi} ∧ {lo} < {y} ∧ {y} < {hi})")
    lines += [f"    (hdef : SixModelCompression.rowDefect M {i} = 3) : False := by"]
    for a, b, c in TRIPLES:
        lines.append(f"  obtain ⟨h{a}{b}{c}a, h{a}{b}{c}b, h{a}{b}{c}c⟩ := h{a}{b}{c}")
    for a, b in EDGES:
        lines.append(f"  obtain ⟨hc{a}{b}a, hc{a}{b}b⟩ := M.corridor {a} {b} (by decide)")
    for j in range(5):
        lines.append(f"  obtain ⟨ht{j}a, ht{j}b⟩ := M.theta_bounds {j}")
    lines.append("  have hdelta := M.hdelta.2")
    row = rows[i]
    values = [chord(e) for e in row]
    lines += [f"  have hsort : ({lean_list(row)} : List ℝ).Pairwise (· ≤ ·) := by",
              "    simp [List.pairwise_cons]", "    repeat' apply And.intro", "    all_goals linarith"]
    raw = [tuple(sorted((i, j))) for j in range(5) if i != j]
    lines += [f"  have hperm : (M.rowxs {i}).Perm {lean_list(row)} := by",
              f"    have hp := M.row_perm {i}"]
    symms = []
    for j in range(i):
        name = f"hs{j}"
        symms.append(name)
        lines.append(f"    have {name} : M.d {i} {j} = M.d {j} {i} := M.symm {i} {j} (by decide)")
    lines += [f"    have he : (((List.finRange 5).erase ({i} : Fin 5)).map (M.d {i})) =",
              f"        {lean_list(raw)} := by",
              f"      norm_num [List.finRange, List.ofFn_succ, {', '.join(symms)}]",
              "    rw [he] at hp", f"    exact hp.trans {permutation_term(raw, row)}",
              f"  have hrow : M.rowxs {i} = {lean_list(row)} :=",
              f"    hperm.eq_of_pairwise' (M.row_sorted {i}) hsort"]
    if kind == "prefix":
        goals = [("hfirst", f"M.theta {i} + 1 ≤ {values[0]}"),
                 ("hsecond", f"{values[0]} + 1 ≤ {values[1]}"),
                 ("hthird", f"{values[1]} + 1 ≤ {values[2]}"),
                 ("hshort", f"{values[2]} - M.theta {i} < (n : ℝ)")]
    else:
        goals = [("hfirst", f"{values[1]} + 1 ≤ {values[2]}"),
                 ("hsecond", f"{values[2]} + 1 ≤ {values[3]}"),
                 ("hthird", f"{values[3]} + 1 ≤ M.theta {i} + ((n : ℝ) + M.delta)"),
                 ("hshort", f"M.theta {i} + ((n : ℝ) + M.delta) - {values[1]} < (n : ℝ)")]
    lines += [f"  have {name} : {goal} := by linarith" for name, goal in goals]
    lines += [f"  exact model_{kind}_terminal M {i} ({values[0]}) ({values[1]})",
              f"    ({values[2]}) ({values[3]}) hrow hfirst hsecond hthird hdef hshort",
              f"#print axioms orientation_{mask}_impossible", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Replace the generated Lean section.")
    parser.add_argument("--receipt", type=Path, help="Write coverage metadata; compilation is separate.")
    args = parser.parse_args()
    cases = selected()
    block = BEGIN + "\n\n" + "\n".join(emit_case(*case) for case in cases) + "\n" + END
    root = Path(__file__).resolve().parents[1]
    source = root / "Jsp000404/FourRowCertificate.lean"
    if args.write:
        body = source.read_text()
        if BEGIN in body:
            body = body[:body.index(BEGIN)] + block + body[body.index(END) + len(END):]
        else:
            body = body.replace("end Jsp404.FourRowCertificate", block + "\n\nend Jsp404.FourRowCertificate")
        source.write_text(body)
    metadata = {"orientation_count": 62,
                "generated_masks": [c[0] for c in cases],
                "generated_count": len(cases), "remaining_count": 62 - len(cases),
                "certificate_scope": "actual ModelSix, all natural strips, one defect-three row",
                "external_solver_answer_used_as_premise": False,
                "kernel_verification": "must run lake env lean --trust=0 on the emitted source"}
    if args.receipt:
        args.receipt.write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, ensure_ascii=False))


if __name__ == "__main__":
    main()
