#!/usr/bin/env python3
"""Exact cyclic-row necessary-model diagnostics; never a proof certificate.

Five globally projection-ordered actual centres have ten shared projective
chords in [0, P), P = n + delta. Each ordered triangle has the middle cap
(unit separation), strict betweenness, and BOTH endpoint caps. A four-chord
row has FOUR actual cyclic gaps: three differences and P + min - max.
There is no artificial split at zero. Four specified rows have defect 2;
the fifth has defect >= 2. Natural floors and cell/support budgets are exact.

Reversing vertex indices leaves all chord values unchanged and swaps each
triangle's two orientations. It preserves each row's cyclic gaps and all
caps, including chord zero. Thus only fifth ranks 0, 1, 2 need be inspected;
this is index reversal, not the invalid map d -> P-d at zero.
"""
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import time
import z3

ROOT = Path(__file__).resolve().parents[1]
EDGES = list(itertools.combinations(range(5), 2))
TRIANGLES = list(itertools.combinations(range(5), 3))


def sorted_four(xs):
    xs = list(xs)
    for a, b in [(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]:
        lo, hi = z3.If(xs[a] <= xs[b], xs[a], xs[b]), z3.If(xs[a] <= xs[b], xs[b], xs[a])
        xs[a], xs[b] = lo, hi
    return xs


def build(n_value, fifth_rank, endpoint_caps=True, continuous_relaxation=False, upper_n=24,
          fifth_budget=True):
    solver = z3.SolverFor("QF_LRA" if continuous_relaxation else "QF_LIRA")
    solver.set(random_seed=0)
    n = (z3.Real if continuous_relaxation else z3.Int)("n")
    delta = z3.Real("delta")
    period = n + delta
    d = {ij: z3.Real(f"d_{ij[0]}_{ij[1]}") for ij in EDGES}
    get = lambda i, j: d[tuple(sorted((i, j)))]
    solver.add(n >= 3, delta >= 0, delta < z3.RealVal("1/2"))
    if upper_n is not None:
        solver.add(n <= upper_n)
    if n_value is not None:
        solver.add(n == n_value)
    for value in d.values():
        solver.add(value >= 0, value < period)
    for i, j, k in TRIANGLES:
        x, y, z = get(i, j), get(i, k), get(j, k)
        inc = z3.And(x + 1 <= z, x < y, y < z)
        dec = z3.And(z + 1 <= x, z < y, y < x)
        if endpoint_caps:
            inc = z3.And(inc, y-x <= period-1, z-y <= period-1)
            dec = z3.And(dec, y-z <= period-1, x-y <= period-1)
        solver.add(z3.Or(inc, dec))
    row_qs = {}
    for i in range(5):
        if i == fifth_rank and not fifth_budget:
            continue
        xs = sorted_four([get(i, j) for j in range(5) if i != j])
        gaps = [xs[k+1] - xs[k] for k in range(3)] + [period + xs[0] - xs[3]]
        qs = [(z3.Real if continuous_relaxation else z3.Int)(f"q_{i}_{k}") for k in range(4)]
        row_qs[i] = qs
        for gap, q in zip(gaps, qs):
            solver.add(gap >= 0, q >= 0, q <= n, q <= gap, gap < q+1)
            if continuous_relaxation:
                solver.add(z3.Or(q == 0, q >= 1))
        cells = z3.Sum(qs)
        support = z3.Sum([z3.If(q >= 1, 1, 0) for q in qs])
        solver.add(cells <= n)
        defect = support + n - cells
        solver.add(defect >= 2 if i == fifth_rank else defect == 2)
    return solver, n, delta, d, row_qs


def rational_value(model, expr):
    value = model.eval(expr, model_completion=True)
    if z3.is_int_value(value):
        return Fraction(value.as_long())
    return Fraction(value.numerator_as_long(), value.denominator_as_long())


def validate(model, n, delta, d, qs, fifth, endpoint_caps):
    nv = int(rational_value(model, n))
    de = rational_value(model, delta)
    period = nv + de
    chords = {ij: rational_value(model, x) for ij, x in d.items()}
    get = lambda i, j: chords[tuple(sorted((i, j)))]
    checks = {
        "strip": 3 <= nv <= 24 and 0 <= de < Fraction(1, 2),
        "chord_ranges": all(0 <= x < period for x in chords.values()),
        "all_three_triangle_caps": all(
            (x+1 <= z and x < y < z and (not endpoint_caps or (y-x <= period-1 and z-y <= period-1)))
            or (z+1 <= x and z < y < x and (not endpoint_caps or (y-z <= period-1 and x-y <= period-1)))
            for i, j, k in TRIANGLES
            for x, y, z in [(get(i, j), get(i, k), get(j, k))]
        ),
    }
    rows = []
    for i in range(5):
        xs = sorted(get(i, j) for j in range(5) if i != j)
        gaps = [xs[k+1]-xs[k] for k in range(3)] + [period+xs[0]-xs[3]]
        floors = [gap.numerator // gap.denominator for gap in gaps]
        supplied = [int(rational_value(model, q)) for q in qs[i]]
        cells = sum(floors)
        support = sum(q >= 1 for q in floors)
        defect = support + nv - cells
        checks[f"row_{i}_exact_floors_budget"] = supplied == floors and cells <= nv and (
            defect >= 2 if i == fifth else defect == 2)
        rows.append({"rank": i, "cyclic_gaps": list(map(str, gaps)), "floors": floors,
                     "cells": cells, "support": support, "defect": defect})
    assert all(checks.values()), checks
    return {"n": nv, "delta": str(de), "chords": {f"{i},{j}": str(x) for (i,j),x in chords.items()},
            "rows": rows, "checks": checks, "exact_fraction_validation": True,
            "point_realizability": "NOT_CHECKED"}


def emit_endpoint_terminal(fifth=0, strong=False):
    """Generate ordinary Lean branches for a strictly weaker LRA endpoint core."""
    n, delta = z3.Reals("n delta")
    p = n + delta
    d = {edge: z3.Real("d" + "".join(map(str,edge))) for edge in EDGES}
    solver = z3.SolverFor("QF_LRA")
    lines = ["import Jsp000404.GapDefectStructure", "", "namespace Jsp404.GlobalFiveLowEndpointTerminal", "",
             "def GapBudget (n p a b c d : ℝ) : Prop :=",
             "  n-1 ≤ b-a ∨ n-1 ≤ c-b ∨ n-1 ≤ d-c ∨ n-1 ≤ p+a-d ∨",
             "  (1 ≤ b-a ∧ 1 ≤ c-b ∧ n ≤ (b-a)+(c-b)) ∨",
             "  (1 ≤ b-a ∧ 1 ≤ d-c ∧ n ≤ (b-a)+(d-c)) ∨",
             "  (1 ≤ b-a ∧ 1 ≤ p+a-d ∧ n ≤ (b-a)+(p+a-d)) ∨",
             "  (1 ≤ c-b ∧ 1 ≤ d-c ∧ n ≤ (c-b)+(d-c)) ∨",
             "  (1 ≤ c-b ∧ 1 ≤ p+a-d ∧ n ≤ (c-b)+(p+a-d)) ∨",
             "  (1 ≤ d-c ∧ 1 ≤ p+a-d ∧ n ≤ (d-c)+(p+a-d))", "",
             "structure FiveModel (n delta : ℝ) where",
             "  hn : 3 ≤ n", "  hdelta : 0 ≤ delta ∧ delta < 1/2",
             "  d : Fin 5 → Fin 5 → ℝ", "  symm : ∀ i j, d i j = d j i",
             "  range : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < n+delta",
             "  triangle : ∀ i j k : Fin 5, i < j → j < k →",
             "    (d i j+1 ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧",
             "      d i k-d i j ≤ n+delta-1 ∧ d j k-d i k ≤ n+delta-1) ∨",
             "    (d j k+1 ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧",
             "      d i k-d j k ≤ n+delta-1 ∧ d i j-d i k ≤ n+delta-1)",
             "  budget : ∀ i : Fin 5, i ≠ 0 → ∀ a b c e : Fin 5,",
             "    [a,b,c,e].Perm ((List.finRange 5).erase i) →",
             "    d i a ≤ d i b → d i b ≤ d i c → d i c ≤ d i e →",
             "    GapBudget n (n+delta) (d i a) (d i b) (d i c) (d i e)", "",
             "set_option maxHeartbeats 32000000 in",
             "theorem endpoint_model_impossible {n delta : ℝ} (m : FiveModel n delta) : False := by",
             "  have hn := m.hn", "  obtain ⟨hdelta0, hdelta1⟩ := m.hdelta"]
    if strong:
        option_index=lines.index("set_option maxHeartbeats 32000000 in")
        shared="\n".join(lines[:option_index])
        shared=shared.replace("GlobalFiveLowEndpointTerminal","GlobalFiveLowTerminal")
        shared=shared.replace("(1 ≤ ","(2 ≤ ").replace("∧ 1 ≤ ","∧ 2 ≤ ")
        shared=shared.replace("structure FiveModel (n delta : ℝ) where","structure FiveModel (n delta : ℝ) (q : Fin 5) where")
        shared=shared.replace("i ≠ 0 →","i ≠ q →")
        shared += "end Jsp404.GlobalFiveLowTerminal\n"
        (ROOT/"Jsp000404/GlobalFiveLowStrongModel.lean").write_text(shared)
        lines=["import Jsp000404.GlobalFiveLowStrongModel", "", "namespace Jsp404.GlobalFiveLowTerminal", "",
               "set_option maxHeartbeats 32000000 in",
               f"theorem model_impossible_{fifth} {{n delta : ℝ}} (m : FiveModel n delta {fifth}) : False := by",
               "  have hn := m.hn", "  obtain ⟨hdelta0, hdelta1⟩ := m.hdelta"]
    stats = {"linarith_leaves":0, "triangle_nodes":0, "budget_nodes":0}
    all_names = []

    def track(name, expr):
        solver.assert_and_track(expr, z3.Bool(name))
        all_names.append(name)

    track("hn", n>=3)
    track("hdelta0", delta>=0)
    track("hdelta1", delta<z3.RealVal("1/2"))
    for (i,j),value in d.items():
        lines.append(f"  obtain ⟨h{i}{j}0, h{i}{j}1⟩ := m.range {i} {j} (by decide)")
        track(f"h{i}{j}0", value>=0)
        track(f"h{i}{j}1", value<p)
    for i,j in EDGES:
        lines.append(f"  have hc{j}{i} := m.symm {j} {i}")

    def leaf(indent):
        names = [str(x) for x in solver.unsat_core()]
        lines.append(" "*indent + "linarith only [" + ", ".join(names) + "]")
        stats["linarith_leaves"] += 1

    def row_orders(mask):
        adj={edge:set() for edge in EDGES}
        for index,(i,j,k) in enumerate(TRIANGLES):
            x,y,z=(i,j),(i,k),(j,k)
            lo,mi,hi=(z,y,x) if (mask>>index)&1 else (x,y,z)
            adj[lo].add(mi);adj[mi].add(hi)
        for _ in range(10):
            adj={a:set(bs).union(*(adj[b] for b in bs)) for a,bs in adj.items()}
        result={}
        for i in [j for j in range(5) if j!=fifth]:
            edges=[tuple(sorted((i,j))) for j in range(5) if j!=i]
            original=tuple(edges)
            edges.sort(key=lambda e:sum(e in adj[f] for f in original))
            assert all(edges[b] in adj[edges[a]] for a in range(4) for b in range(a+1,4))
            result[i]=edges
        return result

    def budget_dfs(left, rows, indent):
        if solver.check()==z3.unsat:
            leaf(indent);return
        if not left:
            raise AssertionError("SAT endpoint coarse row core")
        opts={}
        for i in left:
            xs=[d[e] for e in rows[i]]
            gs=[xs[k+1]-xs[k] for k in range(3)]+[p+xs[0]-xs[3]]
            threshold=2 if strong else 1
            opts[i]=[[g>=n-1] for g in gs]+[[gs[a]>=threshold,gs[b]>=threshold,gs[a]+gs[b]>=n] for a,b in itertools.combinations(range(4),2)]
        scores=[]
        for i in left:
            count=0
            for branch in opts[i]:
                solver.push();solver.add(*branch);count+=solver.check()!=z3.unsat;solver.pop()
            scores.append((count,i))
        i=min(scores)[1];stats["budget_nodes"]+=1
        neighbors=[b if a==i else a for a,b in rows[i]]
        lines.append(" "*indent+f"have hb{i} := m.budget {i} (by decide) "+" ".join(map(str,neighbors))+" (by decide)")
        for _ in range(3):lines.append(" "*(indent+2)+"(by linarith)")
        canon=[f"hc{i}{j}" for j in neighbors if j<i]
        if canon:lines.append(" "*indent+"simp only ["+", ".join(canon)+f"] at hb{i}")
        lines.append(" "*indent+f"rcases hb{i} with hbg{i} | hbg{i} | hbg{i} | hbg{i} |")
        lines.append(" "*(indent+2)+f"⟨hbg{i}a,hbg{i}b,hbg{i}c⟩ | ⟨hbg{i}a,hbg{i}b,hbg{i}c⟩ | ⟨hbg{i}a,hbg{i}b,hbg{i}c⟩ |")
        lines.append(" "*(indent+2)+f"⟨hbg{i}a,hbg{i}b,hbg{i}c⟩ | ⟨hbg{i}a,hbg{i}b,hbg{i}c⟩ | ⟨hbg{i}a,hbg{i}b,hbg{i}c⟩")
        for branch in opts[i]:
            solver.push();old_len=len(all_names)
            for idx,condition in enumerate(branch):track(f"hbg{i}" if len(branch)==1 else f"hbg{i}"+"abc"[idx],condition)
            lines.append(" "*indent+"·")
            budget_dfs([j for j in left if j!=i],rows,indent+2)
            solver.pop();del all_names[old_len:]

    def triangle_dfs(index, mask, indent):
        if solver.check()==z3.unsat:
            leaf(indent);return
        if index==10:
            budget_dfs([i for i in range(5) if i!=fifth],row_orders(mask),indent);return
        i,j,k=TRIANGLES[index];x,y,z=d[i,j],d[i,k],d[j,k]
        conditions=[[x+1<=z,x<y,y<z,y-x<=p-1,z-y<=p-1],
                    [z+1<=x,z<y,y<x,y-z<=p-1,x-y<=p-1]]
        names=[f"ht{i}{j}{k}"+letter for letter in "abcde"]
        pat="⟨"+",".join(names)+"⟩"
        lines.append(" "*indent+f"rcases m.triangle {i} {j} {k} (by decide) (by decide) with {pat} | {pat}")
        stats["triangle_nodes"]+=1
        for choice,condition in enumerate(conditions):
            solver.push();old_len=len(all_names)
            for name,expr in zip(names,condition):track(name,expr)
            lines.append(" "*indent+"·")
            triangle_dfs(index+1,mask|(choice<<index),indent+2)
            solver.pop();del all_names[old_len:]

    triangle_dfs(0,0,2)
    lines += ["", f"#print axioms model_impossible_{fifth}" if strong else "#print axioms endpoint_model_impossible",
              "end Jsp404.GlobalFiveLowTerminal" if strong else "end Jsp404.GlobalFiveLowEndpointTerminal", ""]
    source="\n".join(lines)
    target=ROOT/f"Jsp000404/GlobalFiveLowTerminal{fifth}.lean" if strong else ROOT/"Jsp000404/GlobalFiveLowEndpointTerminal.lean"
    target.write_text(source)
    print(json.dumps({**stats,"bytes":len(source.encode()),"lines":len(lines),"file":str(target)}),flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--wall-seconds", type=float, default=58)
    parser.add_argument("--case-timeout-ms", type=int, default=4000)
    parser.add_argument("--emit-endpoint-terminal", action="store_true")
    parser.add_argument("--emit-strong-terminal", action="store_true")
    args = parser.parse_args()
    if args.emit_endpoint_terminal:
        emit_endpoint_terminal()
        return
    if args.emit_strong_terminal:
        for fifth in range(3):emit_endpoint_terminal(fifth,True)
        return
    # First inspect the fully variable uniform range, then its low strips.
    plan = [(None, i, True) for i in range(3)] + [
        (n, i, True) for n in [3,4,5,6,9,24] for i in range(3)]
    report = {"date": "2026-10-05", "solver": z3.get_version_string(), "diagnostic_only": True,
              "no_Lean_certificate": True, "scope": "Global five-centre cyclic necessary angle/floor model",
              "n_range": [3,24], "delta_range": "0 <= delta < 1/2",
              "row_gap_count": 4, "fifth_defect": ">= 2", "other_four_defects": "= 2",
              "all_three_triangle_caps": True, "chord_zero_allowed": True,
              "reflection": "Vertex index reversal preserves chord values; fifth ranks 0..2 represent all five ranks",
              "cases": [], "unvisited": []}
    start = time.monotonic()
    for index, (nval, fifth, caps) in enumerate(plan):
        remaining = args.wall_seconds - (time.monotonic()-start)
        if remaining <= 0:
            report["unvisited"] = [{"n":n,"fifth_rank":i} for n,i,_ in plan[index:]]
            break
        solver, n, delta, d, qs = build(nval, fifth, caps)
        timeout = min(args.case_timeout_ms, max(1,int(remaining*1000)))
        solver.set(timeout=timeout)
        one_start = time.monotonic()
        status = solver.check()
        rec = {"n": nval, "fifth_rank": fifth, "status":str(status),
               "timeout_ms": timeout, "seconds":round(time.monotonic()-one_start,4)}
        if status == z3.unknown:
            rec["reason"] = solver.reason_unknown()
        elif status == z3.sat:
            rec["necessary_model"] = validate(solver.model(), n, delta, d, qs, fifth, caps)
        report["cases"].append(rec)
        print(json.dumps({k:v for k,v in rec.items() if k!="necessary_model"}), flush=True)
    for group, relaxed, bound in [("unbounded_n_controls",False,None), ("continuous_relaxation_controls",True,24)]:
        report[group]=[]
        for fifth in range(3):
            remaining=args.wall_seconds-(time.monotonic()-start)
            if remaining<=0:
                report["unvisited"].append({"group":group,"fifth_rank":fifth})
                continue
            solver,n,delta,d,qs=build(None,fifth,continuous_relaxation=relaxed,upper_n=bound)
            timeout=min(args.case_timeout_ms,max(1,int(remaining*1000)))
            solver.set(timeout=timeout)
            one_start=time.monotonic()
            status=solver.check()
            rec={"fifth_rank":fifth,"status":str(status),"timeout_ms":timeout,
                 "seconds":round(time.monotonic()-one_start,4),
                 "scope":"nonintegral active q >= 1 or q = 0; real n in [3,24]" if relaxed else "unbounded integer n >= 3"}
            if status==z3.unknown:rec["reason"]=solver.reason_unknown()
            if status==z3.sat and not relaxed:
                rec["necessary_model"]=validate(solver.model(),n,delta,d,qs,fifth,True)
            report[group].append(rec)
            print(json.dumps({"group":group,**{k:v for k,v in rec.items() if k!="necessary_model"}}),flush=True)
    report["elapsed_seconds"] = round(time.monotonic()-start,4)
    report["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report["interpretation"] = "SAT is only a validated necessary angular model, not actual points; UNSAT is not a Lean proof; UNKNOWN is unresolved."
    (ROOT/"research/JSP404_GLOBAL_FIVE_LOW_20261005.json").write_text(json.dumps(report,indent=2)+"\n")


if __name__ == "__main__":
    main()
