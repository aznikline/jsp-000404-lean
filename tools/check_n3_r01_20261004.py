#!/usr/bin/env python3
"""Exact necessary-condition diagnostic for the remaining n=3 HIGH R1/R0.

This is not a point-realizability test and not a Lean proof.  UNSAT can
suggest a geometric leaf; SAT is only a rational angular countermodel.
Actual minimality is represented by preserving every survivor's row score
after deleting each zero-score tail.  All seven cases have a 10s solver cap.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import time

import z3


def sorting_network(values):
    """Fixed insertion network; each comparator uses exact LRA conditionals."""
    out = list(values)
    for top in range(1, len(out)):
        for j in range(top, 0, -1):
            a, b = out[j - 1], out[j]
            out[j - 1] = z3.If(a <= b, a, b)
            out[j] = z3.If(a <= b, b, a)
    return out


def row_gaps(theta, period, chords):
    row = sorting_network(chords)
    return [row[0] - theta] + [b - a for a, b in zip(row, row[1:])] + [
        theta + period - row[-1]
    ]


def row_score_condition(gaps, is_low):
    if not is_low:
        return z3.And(*[z3.And(0 < g, g < 2) for g in gaps])
    return z3.Or(*[
        z3.And(*[
            z3.And(2 <= g, g < 3) if j == big else z3.And(0 < g, g < 2)
            for j, g in enumerate(gaps)
        ])
        for big in range(len(gaps))
    ])


def exact_fraction(model, expr):
    value = model.eval(expr, model_completion=True)
    assert z3.is_rational_value(value), value
    return Fraction(value.numerator_as_long(), value.denominator_as_long())


def fraction_row(theta, period, chords):
    row = sorted(chords)
    gaps = [row[0] - theta] + [b - a for a, b in zip(row, row[1:])] + [
        theta + period - row[-1]
    ]
    return row, gaps


def validate_model(theta, period, chords, low):
    m = len(theta)
    delta = period - 3
    checks = {"strip": Fraction(1, 2) <= delta < 1,
              "theta_window": 0 <= theta[0] and theta[-1] <= delta,
              "theta_order": all(a < b for a, b in zip(theta, theta[1:]))}
    get = lambda i, j: chords[min(i, j), max(i, j)]
    checks["corridors"] = all(theta[i] + 1 <= get(i, j) <= period - 1 + theta[j]
                              for i, j in itertools.combinations(range(m), 2))
    checks["all_triangle_constraints"] = all(
        (get(i, j) + 1 <= get(j, k) and get(i, j) < get(i, k) < get(j, k)) or
        (get(j, k) + 1 <= get(i, j) and get(j, k) < get(i, k) < get(i, j))
        for i, j, k in itertools.combinations(range(m), 3))
    rows = {}
    deleted = {}
    def checked_row(i, survivor_set):
        order, gaps = fraction_row(theta[i], period,
                                  [get(i, j) for j in survivor_set if i != j])
        score = sum(max(g.numerator // g.denominator - 1, 0) for g in gaps)
        return {"order": list(map(str, order)), "gaps": list(map(str, gaps)),
                "score": score, "expected_score": int(i == low),
                "positive_gaps": all(g > 0 for g in gaps)}
    for i in range(m):
        rows[str(i)] = checked_row(i, range(m))
    checks["original_row_scores"] = all(r["score"] == r["expected_score"]
                                         and r["positive_gaps"] for r in rows.values())
    for q in range(m):
        if q == low:
            continue
        survivors = [i for i in range(m) if i != q]
        deleted[str(q)] = {str(i): checked_row(i, survivors) for i in survivors}
    checks["all_tail_deleted_survivor_scores"] = all(
        r["score"] == r["expected_score"] and r["positive_gaps"]
        for case in deleted.values() for r in case.values())
    # Anchor's largest wrap gap always has floor exactly 3 in this theta window.
    checks["anchor_score_2_original_and_after_all_tail_deletions"] = all(
        sum(max(g.numerator // g.denominator - 1, 0) for g in
            [b-a for a,b in zip(selected, selected[1:])] +
            [period + selected[0] - selected[-1]]) == 2
        for selected in [theta] + [[theta[i] for i in range(m) if i != q]
                                   for q in range(m) if q != low])
    assert all(checks.values()), checks
    return {"validated_exactly_with_Fraction": True, "checks": checks,
            "period": str(period), "delta": str(delta),
            "theta": list(map(str, theta)),
            "chords": {f"{i},{j}": str(v) for (i,j),v in chords.items()},
            "original_rows": rows, "after_tail_deletions": deleted,
            "geometric_point_realizability": "NOT_CHECKED"}


def run_case(m, low, timeout_ms, mode="minimality", shrink=False):
    case = f"R1_low_rank_{low}" if low is not None else "R0"
    delta = z3.Real(f"{case}_delta")
    period = 3 + delta
    theta = [z3.Real(f"{case}_theta_{i}") for i in range(m)]
    chords = {(i,j): z3.Real(f"{case}_d_{i}_{j}")
              for i,j in itertools.combinations(range(m), 2)}
    get = lambda i,j: chords[min(i,j),max(i,j)]
    conditions = {}
    conditions["theta_window"] = z3.And(delta >= z3.RealVal("1/2"), delta < 1,
        0 <= theta[0], theta[-1] <= delta,
        *[a < b for a,b in zip(theta,theta[1:])])
    for i,j in itertools.combinations(range(m),2):
        conditions[f"corridor_{i}_{j}"] = z3.And(theta[i]+1 <= get(i,j),
                                                   get(i,j) <= period-1+theta[j])
    for i,j,k in itertools.combinations(range(m),3):
        conditions[f"triangle_{i}_{j}_{k}"] = z3.Or(
            z3.And(get(i,j)+1 <= get(j,k), get(i,j)<get(i,k), get(i,k)<get(j,k)),
            z3.And(get(j,k)+1 <= get(i,j), get(j,k)<get(i,k), get(i,k)<get(i,j)))
    for i in range(m):
        conditions[f"original_row_{i}"] = row_score_condition(
            row_gaps(theta[i],period,[get(i,j) for j in range(m) if j != i]),i==low)
    for q in range(m):
        if q == low:
            continue
        for i in range(m):
            if i == q:
                continue
            conditions[f"delete_{q}_survivor_{i}"] = row_score_condition(
                row_gaps(theta[i],period,[get(i,j) for j in range(m)
                                         if j != i and j != q]),i==low)
    if mode == "geometry":
        conditions = {k:v for k,v in conditions.items()
                      if not k.startswith(("original_row_", "delete_"))}
    elif mode == "original_rows":
        conditions = {k:v for k,v in conditions.items() if not k.startswith("delete_")}
    elif mode == "positive_row":
        conditions = {k:v for k,v in conditions.items()
                      if not k.startswith(("original_row_", "delete_"))}
        conditions[f"positive_row_{low}"] = z3.Or(*[
            g >= 2 for g in row_gaps(theta[low],period,
                                     [get(low,j) for j in range(m) if j != low])])
    solver = z3.SolverFor("QF_LRA")
    solver.set(timeout=timeout_ms, random_seed=0)
    for name, expr in conditions.items():
        solver.assert_and_track(expr,z3.Bool(name))
    start = time.monotonic()
    status = solver.check()
    record = {"case": case, "total_centres": m+1, "low_rank": low,
              "constraints_mode": mode,
              "constraints_tracked": len(conditions), "status": str(status),
              "elapsed_seconds": round(time.monotonic()-start,4),
              "timeout_ms": timeout_ms}
    if status == z3.sat:
        model = solver.model()
        if mode == "minimality":
            record["angular_model"] = validate_model(
                [exact_fraction(model,t) for t in theta], exact_fraction(model,period),
                {ij:exact_fraction(model,v) for ij,v in chords.items()},low)
        else:
            record["angular_model"] = {
                "theta": [str(exact_fraction(model,t)) for t in theta],
                "period": str(exact_fraction(model,period)),
                "chords": {f"{i},{j}": str(exact_fraction(model,v))
                           for (i,j),v in chords.items()},
                "claim_limit": "SAT only for the weaker stated constraints"}
    elif status == z3.unsat:
        record["unsat_core"] = [str(c) for c in solver.unsat_core()]
        record["proof_status"] = "SMT_DIAGNOSTIC_ONLY_NOT_LEAN"
        if shrink:
            core = list(record["unsat_core"])
            shrink_start = time.monotonic()
            for name in list(core):
                candidate = [k for k in core if k != name]
                smaller = z3.SolverFor("QF_LRA")
                smaller.set(timeout=1000, random_seed=0)
                smaller.add(*[conditions[k] for k in candidate])
                if smaller.check() == z3.unsat:
                    core = candidate
            record["greedy_reduced_unsat_core"] = core
            record["core_reduction_seconds"] = round(time.monotonic()-shrink_start,4)
    else:
        record["reason_unknown"] = solver.reason_unknown()
    print(json.dumps({k:v for k,v in record.items() if k!="angular_model"}),flush=True)
    return record


def regenerate_six_terminal(terminal_path):
    """Emit ordinary Lean proofs; external SMT only chooses linear fact subsets.

    The existing prefix through SixModel/gapScore_zero_of_small is retained.
    Each generated arithmetic statement is checked by Lean, not imported from
    an external solver. All 20 triangle directions are exhaustively split.
    """
    m=6;l=z3.Real('l');p=z3.Real('p');t=[z3.Real(f't{i}') for i in range(m)];d={(i,j):z3.Real(f'd{i}{j}') for i,j in itertools.combinations(range(m),2)}
    b=[l>0,3*l<=p,p<4*l,t[0]>=0,t[-1]<=p-3*l]+[t[i]<t[i+1] for i in range(m-1)]
    for i,j in itertools.combinations(range(m),2):b += [t[i]+l<=d[i,j],d[i,j]<=p-l+t[j]]
    tr=[]
    for i,j,k in itertools.combinations(range(m),3):tr.append(((i,j,k),[[d[i,j]+l<=d[j,k],d[i,j]<d[i,k],d[i,k]<d[j,k]],[d[j,k]+l<=d[i,j],d[j,k]<d[i,k],d[i,k]<d[i,j]]]))
    s=z3.SolverFor('QF_LRA');s.add(*b);nodes=uns=sat=0;start=time.monotonic()
    names=['hlam','hp0','hp1','ht0','ht5']+[f'ht{i}{i+1}' for i in range(5)]
    for ii,jj in itertools.combinations(range(6),2):names += [f'hc{ii}{jj}a',f'hc{ii}{jj}b']
    factstack=list(zip(names,b))
    def core_for(neg=None):
     k=z3.SolverFor('QF_LRA')
     for nm, expr in factstack:k.assert_and_track(expr,z3.Bool('proof_'+nm))
     if neg is not None:k.add(neg)
     assert k.check()==z3.unsat
     return [str(x)[6:] for x in k.unsat_core()]
    def only_core(neg=None):return 'linarith only ['+', '.join(core_for(neg))+']'

    lines=['set_option maxHeartbeats 20000000 in','theorem six_model_rows_zero (m : SixModel) (i : Fin 6) :','    linearGapScore m.lam (m.t i) (m.t i + m.p) (m.rowxs i) = 0 := by','  have hlam := m.hlam','  have hp0 := m.hp.1','  have hp1 := m.hp.2','  have ht0 := m.ht0','  have ht5 := m.ht5']
    for i in range(5):lines.append(f'  have ht{i}{i+1} := m.ht (show ({i} : Fin 6) < {i+1} from by decide)')
    for i,j in itertools.combinations(range(6),2):lines.append(f'  obtain ⟨hc{i}{j}a, hc{i}{j}b⟩ := m.hcor {i} {j} (by decide)')
    def D(i,j):return d[min(i,j),max(i,j)]
    def dc(i,j):return f'm.d {min(i,j)} {max(i,j)}'
    def leafproof(indent):
     nonlocal sat
     sat+=1
     model=s.model()
     lines.append(' '*indent+'fin_cases i')
     for r in range(6):
      partners=sorted([j for j in range(6) if j!=r],key=lambda j:float(model.eval(D(r,j)).as_fraction()))
      xs=[D(r,j) for j in partners]
      gaps=[xs[0]-t[r]]+[v-u for u,v in zip(xs,xs[1:])]+[t[r]+p-xs[-1]]
      for g in gaps:
       s.push();s.add(g>=2*l)
       assert s.check()==z3.unsat,(r,partners,g)
       s.pop()
      q=' '*(indent+2)
      lines.append(' '*indent+'·')
      lines.append(q+f'change linearGapScore m.lam (m.t {r}) (m.t {r} + m.p) (m.rowxs {r}) = 0')
      idx=', '.join(map(str,partners))
      lines.append(q+f'have hpidx : (((List.finRange 6).erase ({r} : Fin 6))).Perm')
      lines.append(q+f'    ([{idx}] : List (Fin 6)) := by decide')
      lines.append(q+f'have hperm := (m.row_perm {r}).trans (hpidx.map (m.d {r}))')
      vals=', '.join(f'm.d {r} {j}' for j in partners)
      lines.append(q+f'change (m.rowxs {r}).Perm [{vals}] at hperm')
      for j in partners:
       if j<r:lines.append(q+f'rw [m.symm {r} {j} (by decide)] at hperm')
      lines.append(q+'have heq := hperm.eq_of_pairwise\' (m.row_sorted _) (by')
      lines.append(q+'  simp only [List.pairwise_cons, List.mem_cons,')
      lines.append(q+'    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]')
      ordcore=set()
      for xx,yy in itertools.combinations(xs,2):ordcore.update(core_for(xx>yy))
      lines.append(q+"  (repeat' constructor) <;> linarith only ["+', '.join(sorted(ordcore))+'])')
      lines.append(q+'rw [heq]')
      lines.append(q+'simp only [linearGapScore]')
      for j,g in enumerate(gaps):
       lines.append(q+'rw [gapScore_zero_of_small m.hlam (by '+only_core(g<0)+') (by '+only_core(g>=2*l)+')]')
      lines.append(q+'try norm_num')
    def rec(a,indent):
     nonlocal nodes,uns
     nodes+=1
     if s.check()==z3.unsat:
      uns+=1;lines.append(' '*indent+'exfalso; '+only_core());return
     if a==len(tr):leafproof(indent);return
     (i,j,k), branches=tr[a]
     lines.append(' '*indent+f'rcases m.htr {i} {j} {k} (by decide) (by decide) with')
     lines.append(' '*indent+f'  ⟨h{i}{j}{k}a, h{i}{j}{k}b, h{i}{j}{k}c⟩ | ⟨h{i}{j}{k}a, h{i}{j}{k}b, h{i}{j}{k}c⟩')
     for branch in branches:
      s.push();s.add(*branch)
      factstack.extend(zip([f'h{i}{j}{k}a',f'h{i}{j}{k}b',f'h{i}{j}{k}c'],branch))
      lines.append(' '*indent+'·');rec(a+1,indent+2)
      del factstack[-3:]
      s.pop()
    rec(0,2)
    lines+=['','#print axioms six_model_rows_zero','end Jsp404.N3R01Terminal','']
    path=terminal_path;src=path.read_text();src=src.split('set_option maxHeartbeats 20000000 in')[0];path.write_text(src+'\n'.join(lines))
    print({'nodes':nodes,'infeasible_linear_leaves':uns,'feasible_orientation_patterns':sat,'lines':len(lines),'generation_seconds':time.monotonic()-start})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--regenerate-six-lean", action="store_true")
    parser.add_argument("--timeout-ms",type=int,default=10000)
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parents[1]/
                        "research/JSP404_N3_R01_DIAGNOSTIC_20261004.json")
    args = parser.parse_args()
    if args.regenerate_six_lean:
        regenerate_six_terminal(Path(__file__).resolve().parents[1]/"Jsp000404/N3R01Terminal.lean")
        return
    records = []
    start = time.monotonic()
    for low in range(6):
        records.append(run_case(6,low,args.timeout_ms,shrink=True))
    records.append(run_case(7,None,args.timeout_ms,shrink=True))
    controls = [run_case(6,None,args.timeout_ms,mode="geometry",shrink=True),
                run_case(7,None,args.timeout_ms,mode="geometry",shrink=True)]
    for low in range(6):
        controls.append(run_case(6,low,args.timeout_ms,mode="original_rows",shrink=True))
    for low in range(6):
        controls.append(run_case(6,low,args.timeout_ms,mode="positive_row",shrink=True))
    result = {"date": "2026-10-04", "z3_version": z3.get_version_string(),
              "kind": "EXACT_RATIONAL_NECESSARY_ANGULAR_CONDITIONS",
              "normalization": "lambda=1, period=3+delta, 1/2 <= delta < 1",
              "minimality": "every score-zero tail deletion preserves all survivor scores",
              "claim_limit": "No claim of Lean proof or actual point counterexample",
              "elapsed_seconds": round(time.monotonic()-start,4), "cases": records,
              "weaker_constraints_controls": controls}
    args.output.write_text(json.dumps(result,indent=2)+"\n")


if __name__ == "__main__":
    main()
