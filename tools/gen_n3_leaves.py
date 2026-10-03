#!/usr/bin/env python3
"""Generate the leaf-closure core of Jsp000404/R2SixCentreN3.lean.

Reads leaf_min_cores.json (z3-verified minimal unsat cores of each
(row-rank, chord-permutation, big-gap-position) leaf under the relaxed
LRA model: 0 <= delta < 1, chords ordered by <=, gaps >= 0).  Each leaf
is replayed kernel-checkably: rcases the 24-way chord permutation, the
5-way big-gap signature, the minimal triple-constraint set, then
linarith over corridor / theta-order / gap bounds.
"""
import itertools, json, os, sys

P = 5
ROWS = [0, 1, 3, 4]
CHORDS = {r: [j for j in range(P) if j != r] for r in ROWS}
# survivor leaves (from joint analysis): row0 A,B,C ; row4 X,Y,Z
SURV = {0: [((0,1,2,3),4), ((0,1,3,2),2), ((1,0,3,2),0)],
        4: [((0,1,2,3),0), ((1,0,2,3),2), ((1,0,3,2),4)]}
JOINT_CORES = {
    ("A","X"): [],
    ("A","Y"): ["(0, 1, 4)"],
    ("A","Z"): ["(0, 1, 4)"],
    ("B","X"): ["(0, 3, 4)"],
    ("B","Y"): ["(0, 1, 4)"],
    ("B","Z"): ["(0, 3, 4)"],
    ("C","X"): ["(0, 3, 4)"],
    ("C","Y"): ["(0, 1, 4)"],
    ("C","Z"): ["(0, 1, 4)"],
}
L0 = {"A": ((0,1,2,3),4), "B": ((0,1,3,2),2), "C": ((1,0,3,2),0)}
L4 = {"X": ((0,1,2,3),0), "Y": ((1,0,2,3),2), "Z": ((1,0,3,2),4)}

def dn(i, j):
    return f"m.d {min(i,j)} {max(i,j)}"

def chord_list(r):
    return [dn(r, j) for j in CHORDS[r]]

def gaps5(r, cv):
    """gap expressions for row r with r_k = cv[k] (cv = chord terms in order)."""
    return [f"({cv[0]} - m.t {r})",
            f"({cv[1]} - {cv[0]})",
            f"({cv[2]} - {cv[1]})",
            f"({cv[3]} - {cv[2]})",
            f"(m.t {r} + m.p - {cv[3]})"]

def gap_conj(r, cv, gpos, lam="m.lam"):
    """the conjunction for 'gap gpos is the big one'."""
    gs = gaps5(r, cv)
    parts = []
    for k in range(5):
        if k == gpos:
            parts += [f"2 * {lam} <= {gs[k]}", f"{gs[k]} < 3 * {lam}"]
        else:
            parts.append(f"{gs[k]} < 2 * {lam}")
    # index order matches RowSig's per-disjunct atom order
    return parts

def bounds_conj(r):
    return [f"m.t {r} <= x0", "x0 <= x1", "x1 <= x2", "x2 <= x3",
            f"x3 <= m.t {r} + m.p"]

def leaf_close(core):
    """tactic line closing an UNSAT leaf given its minimal trip core."""
    if not core:
        return "linarith"
    parts = []
    for t in core:
        a,b,c = (int(x) for x in t.strip("()").split(","))
        parts.append(f"rcases m.htr {a} {b} {c} (by decide) (by decide) "
                     "with h | h")
    parts.append("linarith")
    return " <;> ".join(parts)

def gen_perm4_cases():
    """Emit perm4_cases: [w,x,y,z] ~ [a,b,c,d] -> 24-way Or (lex order)."""
    disj = []
    for p in itertools.permutations(range(4)):
        t = "abcd"
        conj = " ∧ ".join(f"{v} = {t[p[k]]}" for k, v in enumerate("wxyz"))
        disj.append(f"({conj})")
    stmt = ("theorem perm4_cases {a b c d w x y z : ℝ}\n"
            "    (h : List.Perm [w, x, y, z] [a, b, c, d]) :\n    "
            + " ∨\n    ".join(disj) + " := by\n")
    body = []
    body.append("  have hw : w ∈ ([a, b, c, d] : List ℝ) := h.subset (by simp)")
    body.append("  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw")
    body.append("  rcases hw with h | h | h | h")
    # case w = a: tail permutes [b,c,d]; w = b: swap; w=c,d: perm_middle
    tailcfg = [
        ("a", "b", "c", "d", "List.Perm.cons_inv h"),
        ("b", "a", "c", "d",
         "List.Perm.cons_inv (h.trans (List.Perm.swap a b [c, d]).symm)"),
        ("c", "a", "b", "d",
         "List.Perm.cons_inv (h.trans (List.perm_middle (a := c) "
         "(l₁ := [a, b]) (l₂ := [d])))"),
        ("d", "a", "b", "c",
         "List.Perm.cons_inv (h.trans (List.perm_middle (a := d) "
         "(l₁ := [a, b, c]) (l₂ := [])))"),
    ]
    for i, (xv, a1, b1, c1, inv) in enumerate(tailcfg):
        body.append("  · subst w")
        body.append(f"    have h' := {inv}")
        body.append(f"    rcases perm3_cases h' with "
                    "h | h | h | h | h | h")
        # the 6 sub-cases of perm3_cases in its declared order:
        subperms = [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]
        # disjunct index in the 24: position of σ0 = index of xv in "abcd"=i
        # each sub-perm maps (x,y,z) to (t'[j0], t'[j1], t'[j2]) where t'=[a1,b1,c1]
        for sp in subperms:
            t2 = [a1, b1, c1]
            tgt = [i] + [  # full σ tuple
                {"a":0,"b":1,"c":2,"d":3}[t2[j]] for j in sp]
            # find its rank among itertools order
            rank = list(itertools.permutations(range(4))).index(tuple(tgt))
            orpath = []
            r = rank
            # Or.inr chains: disjunct k -> k times Or.inr then final term
            if r == 23:
                orstr = "⟨rfl, h.1, h.2.1, h.2.2⟩"
                for _ in range(23):
                    orstr = f"Or.inr ({orstr})"
            else:
                orstr = "Or.inl ⟨rfl, h.1, h.2.1, h.2.2⟩"
                for _ in range(r):
                    orstr = f"Or.inr ({orstr})"
            body.append(f"    · exact {orstr}")
    return stmt + "\n".join(body) + "\n"

def gen_row(rowi, mincores):
    cv_sorted = chord_list(rowi)
    clist = "[" + ", ".join(cv_sorted) + "]"
    surv = SURV.get(rowi, [])
    out = []
    out.append(f"theorem n3_row{rowi} (m : N3Model) {{x0 x1 x2 x3 : ℝ}}")
    out.append(f"    (hp : List.Perm [x0, x1, x2, x3] {clist})")
    out.append(f"    (hs : RowSig m.lam m.p (m.t {rowi}) x0 x1 x2 x3) :")
    if surv:
        disj = []
        for (perm, gpos) in surv:
            cv = [cv_sorted[perm[k]] for k in range(4)]
            parts = ([f"x0 = {cv[0]}", f"x1 = {cv[1]}", f"x2 = {cv[2]}",
                      f"x3 = {cv[3]}"] + bounds_conj(rowi) +
                     gap_conj(rowi, cv, gpos))
            disj.append("(" + " ∧\n        ".join(parts) + ")")
        out.append("    " + " ∨\n      ".join(disj) + " := by")
    else:
        out.append("    False := by")
    out.append("  obtain ⟨hb0, hb1, hb2, hb3, hb4, hg⟩ := hs")
    for i in range(P):
        for j in range(i+1, P):
            out.append(f"  have hc{i}{j} := m.hcor {i} {j} (by decide)")
    out.append("  obtain ⟨hplo, hphi⟩ := m.hp")
    out.append("  have hlam := m.hlam")
    out.append("  have ht0b := m.ht0")
    out.append("  have ht4b := m.ht4")
    for i in range(P):
        for j in range(i+1, P):
            out.append(f"  have ht{i}{j} : m.t {i} < m.t {j} := m.ht (by decide)")
    out.append("  rcases perm4_cases hp with " + " | ".join(["h"]*24))
    for pidx, perm in enumerate(itertools.permutations(range(4))):
        cv = [cv_sorted[perm[k]] for k in range(4)]
        out.append("  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h")
        out.append("    rcases hg with hg | hg | hg | hg | hg")
        for gpos in range(5):
            key = f"{perm}:{gpos}"
            core = mincores[str(rowi)][key]
            if core == 'SAT':
                # survivor leaf: export the disjunct
                which = surv.index((perm, gpos))
                tup = "⟨rfl, rfl, rfl, rfl, hb0, hb1, hb2, hb3, hb4, hg⟩"
                if which == len(surv) - 1:
                    orpre = "Or.inr (" * which + tup + ")" * which
                else:
                    orpre = ("Or.inr (" * which + "Or.inl " + tup
                             + ")" * which)
                out.append(f"    · exact {orpre}")
            else:
                out.append(f"    · exfalso\n      {leaf_close(core)}")
    return "\n".join(out) + "\n"

def gen_between():
    out = []
    out.append("theorem n3_between (m : N3Model) {x0 x1 x2 x3 y0 y1 y2 y3 : ℝ}")
    out.append("    (hp0 : List.Perm [x0, x1, x2, x3] "
               "[m.d 0 1, m.d 0 2, m.d 0 3, m.d 0 4])")
    out.append("    (hs0 : RowSig m.lam m.p (m.t 0) x0 x1 x2 x3)")
    out.append("    (hp4 : List.Perm [y0, y1, y2, y3] "
               "[m.d 0 4, m.d 1 4, m.d 2 4, m.d 3 4])")
    out.append("    (hs4 : RowSig m.lam m.p (m.t 4) y0 y1 y2 y3) :")
    out.append("    False := by")
    out.append("  have s0 := n3_row0 m hp0 hs0")
    out.append("  have s4 := n3_row4 m hp4 hs4")
    for i in range(P):
        for j in range(i+1, P):
            out.append(f"  have hc{i}{j} := m.hcor {i} {j} (by decide)")
    out.append("  obtain ⟨hplo, hphi⟩ := m.hp")
    out.append("  have hlam := m.hlam")
    out.append("  have ht0b := m.ht0")
    out.append("  have ht4b := m.ht4")
    for i in range(P):
        for j in range(i+1, P):
            out.append(f"  have ht{i}{j} : m.t {i} < m.t {j} := m.ht (by decide)")
    out.append("  rcases s0 with h0 | h0 | h0 <;> rcases s4 with h4 | h4 | h4")
    cases = [("A","X"),("A","Y"),("A","Z"),("B","X"),("B","Y"),("B","Z"),
             ("C","X"),("C","Y"),("C","Z")]
    for nm0, nm4 in cases:
        out.append("  · obtain ⟨e0, e1, e2, e3, sb0, sb1, sb2, sb3, sb4, "
                   "ga0, ga1, ga2, ga3, ga4⟩ := h0")
        out.append("    obtain ⟨f0, f1, f2, f3, tb0, tb1, tb2, tb3, tb4, "
                   "gb0, gb1, gb2, gb3, gb4⟩ := h4")
        out.append("    subst e0 e1 e2 e3 f0 f1 f2 f3")
        core = JOINT_CORES[(nm0, nm4)]
        if not core:
            out.append("    linarith")
        else:
            parts = []
            for t in core:
                a,b,c = (int(x) for x in t.strip("()").split(","))
                parts.append(f"rcases m.htr {a} {b} {c} (by decide) (by decide) "
                             "with h | h")
            parts.append("linarith")
            out.append("    " + " <;> ".join(parts))
    return "\n".join(out) + "\n"

def main():
    mincores = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'n3_leaf_min_cores.json')))
    sys.stdout.write(gen_perm4_cases())
    for r in ROWS:
        sys.stdout.write("\n" + gen_row(r, mincores))
    sys.stdout.write("\n" + gen_between())

if __name__ == "__main__":
    main()
