#!/usr/bin/env python3
"""Generate Jsp000404/R2SixCentreN4.lean — multiset-fact leaf closure for
the n=4 six-centre R2 over-capacity case.

Inputs (produced by tools/n4_dump_cores.py + nb refinement):
  tools/n4_cores.json    — per-(cert,sig-combo) tracked unsat cores
  tools/n4_nb_sets.json  — minimal nb-instantiation chord sets per pair-E
"""
import itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
CORES = json.load(open(os.path.join(HERE, 'n4_cores.json')))
try:
    NBSETS = json.load(open(os.path.join(HERE, 'n4_nb_sets.json')))
except FileNotFoundError:
    NBSETS = {c: {} for c in CORES}

def dn(i, j):
    return f"(m.d {min(i,j)} {max(i,j)})"

def chords(r):
    return [dn(r, j) for j in range(5) if j != r]

MEDPAIR = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
PAIR12 = [(a, b) for a in range(4) for b in range(4) if a != b]
PERM3 = list(itertools.permutations(range(4), 3))
DJ = []
for _a in range(4):
    for _b in range(4):
        if _a == _b: continue
        _rest = [q for q in range(4) if q not in (_a, _b)]
        for (_u, _v) in itertools.permutations(_rest, 2):
            DJ.append((_a, _b, _u, _v))

def opick(i, n, T):
    """term proving disjunct i of a right-nested n-way Or."""
    s = f"({T})" if i == n - 1 else f"(Or.inl ({T}))"
    for _ in range(i):
        s = f"(Or.inr {s})"
    return s

# ---------------- positional signature text ----------------
def pos_gap(k):
    return ["x0 - tl", "x1 - x0", "x2 - x1", "x3 - x2", "tl + p - x3"][k]

def pos_disj(big, lo, hi):
    parts = []
    for k in range(5):
        g = f"({pos_gap(k)})"
        if k in big:
            parts += [f"{lo} * lam <= {g}", f"{g} < {hi} * lam"]
        else:
            parts.append(f"{g} < 2 * lam")
    return " ∧ ".join(parts)

def sig2_pos_disj(c):
    if isinstance(c, tuple): return pos_disj(list(c), 2, 3)
    if c < 5: return pos_disj([c], 3, 4)
    return pos_disj(list(MEDPAIR[c-5]), 2, 3)

def sig1_pos_disj(c):
    return pos_disj([c], 2, 3)

# ---------------- MSig bundle text ----------------
def E_or4(f):
    return "(" + " ∨ ".join(f(c) for c in ['c0','c1','c2','c3']) + ")"

def pairOr(lo, hi, strict=True):
    ds = []
    rel = "<" if strict else "≤"
    for (a, b) in PAIR12:
        x, y = f"c{a}", f"c{b}"
        conj = [f"{x} {rel} {y}"]
        if lo is not None: conj.append(f"{lo} * lam ≤ {y} - {x}")
        if hi is not None: conj.append(f"{y} - {x} < {hi} * lam")
        conj.append(f"(∀ z ∈ [c0, c1, c2, c3], z ≤ {x} ∨ {y} ≤ z)")
        ds.append("(" + " ∧ ".join(conj) + ")")
    return "(" + " ∨\n        ".join(ds) + ")"

def big2Or():
    chains = []
    for (a, b, c) in PERM3:
        x, y, z = f"c{a}", f"c{b}", f"c{c}"
        chains.append(
            f"({x} < {y} ∧ {y} < {z} ∧ "
            f"2 * lam ≤ {y} - {x} ∧ {y} - {x} < 3 * lam ∧ "
            f"(∀ w ∈ [c0, c1, c2, c3], w ≤ {x} ∨ {y} ≤ w) ∧ "
            f"2 * lam ≤ {z} - {y} ∧ {z} - {y} < 3 * lam ∧ "
            f"(∀ w ∈ [c0, c1, c2, c3], w ≤ {y} ∨ {z} ≤ w))")
    disj = []
    for (a, b, u, v) in DJ:
        x, y, uu, vv = f"c{a}", f"c{b}", f"c{u}", f"c{v}"
        disj.append(
            f"({x} < {y} ∧ 2 * lam ≤ {y} - {x} ∧ {y} - {x} < 3 * lam ∧ "
            f"(∀ w ∈ [c0, c1, c2, c3], w ≤ {x} ∨ {y} ≤ w) ∧ "
            f"{uu} < {vv} ∧ 2 * lam ≤ {vv} - {uu} ∧ {vv} - {uu} < 3 * lam ∧ "
            f"(∀ w ∈ [c0, c1, c2, c3], w ≤ {uu} ∨ {vv} ≤ w) ∧ "
            f"({y} ≤ {uu} ∨ {vv} ≤ {x}))")
    return ("((" + " ∨\n          ".join(chains) + ") ∨\n      (" +
            " ∨\n          ".join(disj) + "))")

def msig_conjuncts(kind, k):
    """ordered (tag, prop) — mirrors tools/n4_model.sig_case."""
    out = []
    def elo(v): out.append(('elo', f"(∀ z ∈ [c0, c1, c2, c3], {v} * lam ≤ z - tl)"))
    def ehi(v): out.append(('ehi', f"(∀ z ∈ [c0, c1, c2, c3], {v} * lam ≤ tl + p - z)"))
    def span(B): out.append(('sp', f"(∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < {B} * lam)"))
    def emin(v): out.append(('emin', E_or4(lambda c: f"{c} - tl < {v} * lam")))
    def emax(v): out.append(('emax', E_or4(lambda c: f"tl + p - {c} < {v} * lam")))
    def cpair(lo, hi): out.append(('bigk', pairOr(lo, hi)))
    if kind == 'hi':
        if k == 0: elo(3); span(6); emin(4); emax(2)
        elif k == 4: ehi(3); span(6); emax(4); emin(2)
        else: cpair(3, 4); span(8); emin(2); emax(2)
    elif kind == 'med':
        if k == 0: elo(2); span(6); emin(3); emax(2)
        elif k == 4: ehi(2); span(6); emax(3); emin(2)
        else: cpair(2, 3); span(7); emin(2); emax(2)
    else:
        a, b = k
        intern = [q for q in (a, b) if q in (1, 2, 3)]
        if 0 in (a, b): elo(2); emin(3)
        else: emin(2)
        if 4 in (a, b): ehi(2); emax(3)
        else: emax(2)
        m = len(intern)
        if m == 1: cpair(2, 3)
        elif m == 2:
            out.append(('big2', big2Or()))
            out.append(('sml', pairOr(None, 2, strict=False)))
        span(m + 6)
    return out

# ---------------- helpers ----------------
HELPERS = r'''
theorem mem4or {u x0 x1 x2 x3 : ℝ} (h : u ∈ [x0, x1, x2, x3]) :
    u = x0 ∨ u = x1 ∨ u = x2 ∨ u = x3 := by
  simpa using h

/-- A value occurring twice in a 4-list occupies an ordered pair of slots. -/
theorem two_slots {v c0 c1 c2 c3 : ℝ} (h : 2 ≤ List.count v [c0, c1, c2, c3]) :
    (c0 = v ∧ c1 = v) ∨ (c0 = v ∧ c2 = v) ∨ (c0 = v ∧ c3 = v) ∨
    (c1 = v ∧ c2 = v) ∨ (c1 = v ∧ c3 = v) ∨ (c2 = v ∧ c3 = v) := by
  classical
  by_cases h0 : c0 = v <;> by_cases h1 : c1 = v <;> by_cases h2 : c2 = v <;>
    by_cases h3 : c3 = v <;> simp_all [List.count]
'''

def nb_have(name, i, j, ind, bullet=False):
    """lines proving `have name : ∀ z ∈ [c0..c3], z ≤ c_i ∨ c_j ≤ z`;
    ind = column of `have`; bullet=True prepends `· ` two cols left."""
    head = (" " * (ind - 2) + "· " if bullet else " " * ind)
    return [f"{head}have {name} : ∀ z ∈ [c0, c1, c2, c3], z ≤ c{i} ∨ c{j} ≤ z := by",
            " " * (ind + 2) + "intro z hz",
            " " * (ind + 2) + "rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>",
            " " * (ind + 4) + "first | exact Or.inl (by linarith) | exact Or.inr (by linarith)"]

SLOTS6 = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

def cnt_block(xa, xb, heqsrc, ind):
    """equal-values corner prologue. `ind` = column of the leading `·`;
    caller emits the six `two_slots` bullets at ind + 2 columns."""
    i2 = ind + "  "
    return [f"{ind}· have heq : {xa} = {xb} := {heqsrc}",
            f"{i2}have hcnt : 2 ≤ List.count {xb} [c0, c1, c2, c3] := by",
            f"{i2}  rw [← hp.count_eq {xb}]",
            f"{i2}  by_cases e0 : x0 = {xb} <;> by_cases e1 : x1 = {xb} <;>",
            f"{i2}    by_cases e2 : x2 = {xb} <;> by_cases e3 : x3 = {xb} <;>",
            f"{i2}    simp_all [List.count]",
            f"{i2}rcases two_slots hcnt with h | h | h | h | h | h"]

def sml_pair_disj(a, b):
    """sml disjunct term for equal-value slots (a,b)."""
    return ("⟨by linarith, by linarith, "
            "(fun z hz => (le_total z c" + str(a) + ").elim "
            "(fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩")

def conv_pair(lo, hi, gk):
    """pair-witness conv proof for a strict gap at position gk ∈ {1,2,3}."""
    xa, xb = f"x{gk-1}", f"x{gk}"
    lines = [f"    have hm1 := mem4or (hp.subset (show {xa} ∈ [x0, x1, x2, x3] by simp))",
             f"    have hm2 := mem4or (hp.subset (show {xb} ∈ [x0, x1, x2, x3] by simp))",
             "    rcases hm1 with h1 | h1 | h1 | h1"]
    for i in range(4):
        lines.append("    · rcases hm2 with h2 | h2 | h2 | h2")
        for j in range(4):
            if i == j:
                lines.append("      · exfalso; linarith")
                continue
            idx = PAIR12.index((i, j))
            parts = ["by linarith"]
            if lo is not None: parts.append("by linarith")
            if hi is not None: parts.append("by linarith")
            parts.append("hnb")
            tup = "⟨" + ", ".join(parts) + "⟩"
            lines += nb_have("hnb", i, j, 8, bullet=True)
            lines.append(f"        exact {opick(idx, 12, tup)}")
    return "\n".join(lines)

def conv_sml(gk):
    """non-strict small-gap pair witness; i==j corner via count."""
    xa, xb = f"x{gk-1}", f"x{gk}"
    lines = [f"    have hm1 := mem4or (hp.subset (show {xa} ∈ [x0, x1, x2, x3] by simp))",
             f"    have hm2 := mem4or (hp.subset (show {xb} ∈ [x0, x1, x2, x3] by simp))",
             "    rcases hm1 with h1 | h1 | h1 | h1"]
    for i in range(4):
        lines.append("    · rcases hm2 with h2 | h2 | h2 | h2")
        for j in range(4):
            if i == j:
                lines += cnt_block(xa, xb, "h1.trans h2.symm", "      ")
                for (a, b) in SLOTS6:
                    idx = PAIR12.index((a, b))
                    lines.append(f"        · exact {opick(idx, 12, sml_pair_disj(a, b))}")
                continue
            idx = PAIR12.index((i, j))
            lines += nb_have("hnb", i, j, 8, bullet=True)
            lines.append(f"        exact {opick(idx, 12, '⟨by linarith, by linarith, hnb⟩')}")
    return "\n".join(lines)

def conv_big2(a, b):
    """two internal medium gaps: chain witness (adjacent) or disjoint pairs."""
    if b == a + 1:
        xa, xy, xz = f"x{a-1}", f"x{a}", f"x{a+1}"
        lines = [f"    have hm1 := mem4or (hp.subset (show {xa} ∈ [x0, x1, x2, x3] by simp))",
                 f"    have hm2 := mem4or (hp.subset (show {xy} ∈ [x0, x1, x2, x3] by simp))",
                 f"    have hm3 := mem4or (hp.subset (show {xz} ∈ [x0, x1, x2, x3] by simp))",
                 "    rcases hm1 with h1 | h1 | h1 | h1"]
        for i in range(4):
            lines.append("    · rcases hm2 with h2 | h2 | h2 | h2")
            for j in range(4):
                lines.append("      · rcases hm3 with h3 | h3 | h3 | h3")
                for k in range(4):
                    if len({i, j, k}) < 3:
                        lines.append("        · exfalso; linarith")
                        continue
                    idx = PERM3.index((i, j, k))
                    lines += nb_have("hnbA", i, j, 10, bullet=True)
                    lines += nb_have("hnbB", j, k, 10)
                    tup = ("⟨by linarith, by linarith, by linarith, by linarith, hnbA, "
                           "by linarith, by linarith, hnbB⟩")
                    lines.append(f"          exact Or.inl {opick(idx, 24, tup)}")
        return "\n".join(lines)
    # disjoint pairs: positions (a-1,a),(b-1,b)
    pos = [a - 1, a, b - 1, b]
    lines = []
    for q, p in enumerate(pos):
        lines.append(f"    have hm{q+1} := mem4or (hp.subset (show x{p} ∈ [x0, x1, x2, x3] by simp))")
    lines.append("    rcases hm1 with h1 | h1 | h1 | h1")
    for i in range(4):
        lines.append("    · rcases hm2 with h2 | h2 | h2 | h2")
        for j in range(4):
            lines.append("      · rcases hm3 with h3 | h3 | h3 | h3")
            for k in range(4):
                lines.append("        · rcases hm4 with h4 | h4 | h4 | h4")
                for l in range(4):
                    if len({i, j, k, l}) == 4:
                        idx = DJ.index((i, j, k, l))
                        lines += nb_have("hnbA", i, j, 12, bullet=True)
                        lines += nb_have("hnbB", k, l, 12)
                        tup = ("⟨by linarith, by linarith, by linarith, hnbA, "
                               "by linarith, by linarith, by linarith, hnbB, "
                               "Or.inl (by linarith)⟩")
                        lines.append(f"            exact Or.inr {opick(idx, 24, tup)}")
                    elif j == k:
                        # equal middle values x_a = x_{b-1}: second v-slot via count
                        lines += cnt_block(f"x{a}", f"x{b-1}", "h2.trans h3.symm", "          ")
                        for (p, q) in SLOTS6:
                            opts = []
                            for (pp, qq) in [(p, q), (q, p)]:
                                if len({i, pp, qq, l}) == 4:
                                    idx = DJ.index((i, pp, qq, l))
                                    opts.append((pp, qq, idx))
                            if not opts:
                                lines.append("            · exfalso; linarith")
                                continue
                            lines.append("            · obtain ⟨hvp, hvq⟩ := h")
                            for oi, (pp, qq, idx) in enumerate(opts):
                                lines += nb_have(f"hnbA{oi}", i, pp, 14)
                                lines += nb_have(f"hnbB{oi}", qq, l, 14)
                            alts = []
                            for oi, (pp, qq, idx) in enumerate(opts):
                                tup = ("⟨by linarith, by linarith, by linarith, hnbA" + str(oi) +
                                       ", by linarith, by linarith, by linarith, hnbB" + str(oi) +
                                       ", Or.inl (by linarith)⟩")
                                alts.append(f"exact Or.inr {opick(idx, 24, tup)}")
                            alts.append("exfalso; linarith")
                            lines.append("              first | " + " | ".join(alts))
                    else:
                        lines.append("          · exfalso; linarith")
    return "\n".join(lines)

def conv_proof(tag, kind, k):
    """proof-script lines for one MSig conjunct (inside a `·` bullet)."""
    if tag == 'elo':
        return """    intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith"""
    if tag == 'ehi':
        return """    intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith"""
    if tag == 'sp':
        return """    intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith"""
    if tag == 'emin':
        lines = ["    have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))",
                 "    rcases hm with h | h | h | h"]
        for i in range(4):
            lines.append(f"    · exact {opick(i, 4, 'by linarith')}")
        return "\n".join(lines)
    if tag == 'emax':
        lines = ["    have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))",
                 "    rcases hm with h | h | h | h"]
        for i in range(4):
            lines.append(f"    · exact {opick(i, 4, 'by linarith')}")
        return "\n".join(lines)
    if tag == 'bigk':
        lo = 3 if kind == 'hi' else 2
        hi = 4 if kind == 'hi' else 3
        gk = k if kind != 'medpair' else (k[0] if k[0] in (1,2,3) else k[1])
        return conv_pair(lo, hi, gk)
    if tag == 'big2':
        return conv_big2(*k)
    if tag == 'sml':
        third = ({1,2,3} - set(k)).pop()
        return conv_sml(third)
    raise RuntimeError(tag)

# ---------------- conversion lemma emission ----------------
def sig_decl(kind, k):
    name = f"MSig1_{k}" if kind == 'sig1' else (f"MSig2_{k}" if not isinstance(k, tuple) else f"MSig2_{k[0]}_{k[1]}")
    if kind == 'sig1': kind2, kk = 'med', k
    elif isinstance(k, tuple): kind2, kk = 'medpair', k
    else: kind2, kk = 'hi', k
    cs = msig_conjuncts(kind2, kk)
    body = " ∧\n    ".join(t for _, t in cs)
    return f"abbrev {name} (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=\n    {body}"


def nconj(flat):
    # top-level conjunction count of "a ∧ b ∧ ..." (flat, parens only around atoms)
    import re
    return flat.count(" ∧ ") + 1

def conv_lemma(kind, k):
    """generate msigX_of_pos_* theorem."""
    name = f"MSig1_{k}" if kind == 'sig1' else (f"MSig2_{k}" if not isinstance(k, tuple) else f"MSig2_{k[0]}_{k[1]}")
    if kind == 'sig1':
        kind2, kk, nm = 'med', k, f"msig1_{k}_of_pos"
        cs = msig_conjuncts('med', k)
        hsn = "hs"
        hsprop = sig1_pos_disj(k)
    elif isinstance(k, tuple):
        kind2, nm = 'medpair', f"msig2_{k[0]}_{k[1]}_of_pos"
        cs = msig_conjuncts('medpair', k)
        hsn, hsprop = "hs", sig2_pos_disj(k)
    else:
        kind2, nm = 'hi', f"msig2_{k}_of_pos"
        cs = msig_conjuncts('hi', k)
        hsn, hsprop = "hs", sig2_pos_disj(k)
    parts = [f"theorem {nm} {{lam p tl : ℝ}} (hl : 0 < lam)",
             "    {x0 x1 x2 x3 : ℝ}",
             "    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)",
             f"    ({hsn} : {hsprop})",
             "    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :",
             f"    {name} lam p tl c0 c1 c2 c3 := by",
             "  classical",
             "  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord",
             "  obtain ⟨" + ", ".join(f"hg{q}" for q in range(nconj(hsprop))) + "⟩ := hs",
             "  refine ⟨" + ", ".join("?_" for _ in cs) + "⟩"]
    for tag, _prop in cs:
        pf = conv_proof(tag, kind2, k)
        ls = pf.split("\n")
        parts.append("  · " + ls[0].strip())
        parts += ls[1:]
    txt = "\n".join(parts)
    if kind2 == 'medpair':
        txt = "set_option maxHeartbeats 8000000 in\n" + txt
    return txt

# ---------------- positional RowSig ----------------
def rowsig_pos_def():
    ds1 = [sig1_pos_disj(c) for c in range(5)]
    ds2 = [sig2_pos_disj(c) for c in range(5)] + [sig2_pos_disj(p) for p in MEDPAIR]
    d1 = " ∨\n    ".join(f"({d})" for d in ds1)
    d2 = " ∨\n    ".join(f"({d})" for d in ds2)
    return (f"abbrev RowSig1 (lam p tl : ℝ) (x0 x1 x2 x3 : ℝ) : Prop :=\n    {d1}\n\n"
            f"abbrev RowSig2 (lam p tl : ℝ) (x0 x1 x2 x3 : ℝ) : Prop :=\n    {d2}")

# ---------------- leaf theorems ----------------
# cert -> (spec rows+kind, has em)
CERTS = {
 'pair_A':    ([(1,'s2'),(3,'s1')], False),
 'pair_B':    ([(1,'s1'),(3,'s2')], False),
 'triple_A':  ([(1,'s2'),(2,'s1'),(4,'s1')], False),
 'triple_B':  ([(0,'s1'),(2,'s1'),(3,'s2')], False),
 'pair04_em': ([(0,'s2'),(4,'s2')], True),
}
TAG = {'pair_A':'pA','pair_B':'pB','triple_A':'tA','triple_B':'tB','pair04_em':'pE'}

def msig_name(kind, c):
    if kind == 's1': return f"MSig1_{c}"
    if c < 5: return f"MSig2_{c}"
    a, b = MEDPAIR[c - 5]
    return f"MSig2_{a}_{b}"

def case_of(kind, c):
    if kind == 's1': return ('med', c)
    if c < 5: return ('hi', c)
    return ('medpair', MEDPAIR[c - 5])

def leaf_name(cert, key):
    return "n4l_" + TAG[cert] + "_" + "_".join(str(s) for s in key)

EM_DISJ = "(m.t 0 + m.p - m.lam < m.d 0 1) ∨ (m.t 0 + m.p - m.lam < m.d 0 2) ∨\n" \
          "      (m.t 0 + m.p - m.lam < m.d 0 3) ∨ (m.d 1 4 < m.t 4 + m.lam) ∨\n" \
          "      (m.d 2 4 < m.t 4 + m.lam) ∨ (m.d 3 4 < m.t 4 + m.lam)"

def leaf_theorem(cert, keystr, core):
    spec, hasem = CERTS[cert]
    key = tuple(int(v) for v in keystr.split(','))
    hyps = []
    for i, (r, kind) in enumerate(spec):
        ch = chords(r)
        hyps.append(f"(h{r} : {msig_name(kind, key[i])} m.lam m.p (m.t {r}) "
                    f"{ch[0]} {ch[1]} {ch[2]} {ch[3]})")
    if hasem:
        hyps.append(f"(hem : {EM_DISJ})")
    parts = [f"theorem {leaf_name(cert, key)} (m : N4Model)",
             "    " + "\n    ".join(hyps) + " : False := by"]
    tree_lines, used = emit_cases(cert, keystr, core, spec, hasem, indent="  ")
    # model fact haves — only those the terminal cores actually use
    parts.append("  have hlam := m.hlam")
    if 'hplo' in used or 'hphi' in used:
        parts.append("  obtain ⟨hplo, hphi⟩ := m.hp")
    if 'ht0b' in used:
        parts.append("  have ht0b := m.ht0")
    if 'ht4b' in used:
        parts.append("  have ht4b := m.ht4")
    for i in range(5):
        for j in range(i + 1, 5):
            if f'hc{i}{j}' in used:
                parts.append(f"  have hc{i}{j} := m.hcor {i} {j} (by decide)")
    for i in range(4):
        if f'ht{i}{i+1}' in used:
            parts.append(f"  have ht{i}{i+1} : m.t {i} < m.t {i+1} := m.ht (by decide)")
    # destructure row bundles — named conjuncts the tree splits or cores use,
    # `_` placeholders for the rest (order must match the And-structure)
    def tree_or_names(nd, acc):
        if nd[0] == 'node':
            typ, r, _name, _meta = nd[2]
            if typ in ('emin', 'emax', 'bigk', 'sml', 'big2'):
                acc.add((r, typ))
            for k in nd[3]:
                tree_or_names(k, acc)
    ornames = set()
    tree_or_names(TREES[cert][keystr], ornames)
    for i, (r, kind) in enumerate(spec):
        kind2, kk = case_of(kind, key[i])
        tags = [t for t, _ in msig_conjuncts(kind2, kk)]
        wanted = [t if (r, t) in ornames or
                  (t == 'elo' and any(n.startswith(f'u{r}e') for n in used)) or
                  (t == 'ehi' and any(n.startswith(f'u{r}h') for n in used)) or
                  (t == 'sp' and any(n.startswith(f'u{r}s') for n in used))
                  else '_' for t in tags]
        if any(w != '_' for w in wanted):
            parts.append(f"  obtain ⟨{', '.join(f'h{r}{t}' if t != '_' else '_' for t in wanted)}⟩ := h{r}")
    # U instantiations — only those in cores
    for i, (r, kind) in enumerate(spec):
        kind2, kk = case_of(kind, key[i])
        ch = chords(r)
        tags = {t for t, _ in msig_conjuncts(kind2, kk)}
        if 'elo' in tags:
            for ci in range(4):
                if f'u{r}e{ci}' in used:
                    parts.append(f"  have u{r}e{ci} := h{r}elo {ch[ci]} (by simp)")
        if 'ehi' in tags:
            for ci in range(4):
                if f'u{r}h{ci}' in used:
                    parts.append(f"  have u{r}h{ci} := h{r}ehi {ch[ci]} (by simp)")
        if 'sp' in tags:
            for ci in range(4):
                for cj in range(4):
                    if ci != cj and f'u{r}s{ci}{cj}' in used:
                        parts.append(f"  have u{r}s{ci}{cj} := h{r}sp {ch[ci]} (by simp) {ch[cj]} (by simp)")
    parts += tree_lines
    txt = "\n".join(parts)
    n = count_nodes(TREES[cert][keystr])
    if n > 1500:
        hb = max(1600000, n * 4000)
        txt = f"set_option maxHeartbeats {hb} in\n" + txt
    return txt

def count_nodes(tr):
    if tr[0] in ('term', 'FAIL'):
        return 1
    return 1 + sum(count_nodes(k) for k in tr[3])

def chain_for(e, r, spec, nbdict, base):
    """tactic-chain fragment destructing E-fact e (of row r) uniformly."""
    if e == 'em':
        return "rcases hem with hem | hem | hem | hem | hem | hem"
    tag = e[3:]
    hyp = f"h{r}{tag}"
    ch = chords(r)
    zs = nbdict.get(f"{r}_{tag}", [0, 1, 2, 3])
    if tag in ('emin', 'emax'):
        return f"rcases {hyp} with {e}c | {e}c | {e}c | {e}c"
    if tag in ('bigk', 'sml'):
        ncomp = 4 if tag == 'bigk' else 3
        seg = f"rcases {hyp} with " + " | ".join([f"{e}c"] * 12)
        seg += f" <;> obtain ⟨{', '.join(f'{e}p{j}' for j in range(ncomp))}⟩ := {e}c"
        for zi, z in enumerate(zs):
            seg += f" <;> rcases {e}p{ncomp-1} {ch[z]} (by simp) with {e}z{zi} | {e}z{zi}"
        return seg
    raise RuntimeError(f"chain_for: {e}")

# ---------------- explicit decision-tree leaf bodies ----------------
TREES = json.load(open(os.path.join(HERE, 'n4_leaf_trees.json')))

def emit_cases(cert, keystr, core, spec, hasem, indent):
    """Emit the leaf body as an explicit `·`-bullet decision tree with
    terminal `linarith only [...]`, extracted by tools/n4_extract_trees.py.
    Returns (lines, used_ground_names)."""
    tree = TREES[cert][keystr]
    if tree[0] == 'FAIL':
        raise RuntimeError(f'extract FAIL {cert} {keystr}')
    nodeinfo = {}
    used = set()
    def collect(nd):
        if nd[0] == 'node':
            nodeinfo[nd[1]] = nd[2]
            for k in nd[3]:
                collect(k)
        elif nd[0] == 'term':
            used.update(nd[1])
    collect(tree)

    def core_names(core):
        out = {'hlam'}
        for nm in core:
            if nm.startswith('N'):
                n = int(nm[1:])
                typ, r, _name, _meta = nodeinfo[n]
                if typ == 'bigk':
                    out |= {f'p{n}_{i}' for i in range(4)}
                elif typ == 'sml':
                    out |= {f'p{n}_{i}' for i in range(3)}
                elif typ == 'big2':
                    out |= {f'p{n}_{i}' for i in range(8)}
                else:
                    out.add(f'h{n}')
            else:
                out.add(nm)
        return sorted(out)

    def emit(nd, ind):
        pad = ' ' * ind
        if nd[0] == 'term':
            return [f"{pad}linarith only [{', '.join(core_names(nd[1]))}]"]
        node, info, kids = nd[1], nd[2], nd[3]
        typ, r, _name, meta = info
        lines = []
        if typ == 'tr':
            i, j, k = r
            lines.append(f"{pad}rcases m.htr {i} {j} {k} (by decide) (by decide) "
                         f"with h{node} | h{node}")
        elif typ in ('emin', 'emax'):
            lines.append(f"{pad}rcases h{r}{typ} with h{node} | h{node} | h{node} | h{node}")
        elif typ == 'em':
            lines.append(f"{pad}rcases hem with " + " | ".join([f"h{node}"] * 6))
        elif typ in ('bigk', 'sml'):
            ncomp = 4 if typ == 'bigk' else 3
            lines.append(f"{pad}rcases h{r}{typ} with " + " | ".join([f"h{node}c"] * 12))
            for kid in kids:
                lines.append(f"{pad}· obtain ⟨{', '.join(f'p{node}_{i}' for i in range(ncomp))}⟩"
                             f" := h{node}c")
                lines += emit(kid, ind + 2)
            return lines
        elif typ == 'big2':
            lines.append(f"{pad}rcases h{r}big2 with h{node}b | h{node}b")
            for half in range(2):
                ncomp = 8 if half == 0 else 9
                lines.append(f"{pad}· rcases h{node}b with " + " | ".join([f"h{node}c"] * 24))
                for kid in kids[half * 24:(half + 1) * 24]:
                    lines.append(f"{' ' * (ind + 2)}· obtain "
                                 f"⟨{', '.join(f'p{node}_{i}' for i in range(ncomp))}⟩ := h{node}c")
                    lines += emit(kid, ind + 4)
            return lines
        elif typ == 'nbz':
            pnd, comp, z = meta
            ch = chords(r)[z]
            lines.append(f"{pad}rcases p{pnd}_{comp} {ch} (by simp) with h{node} | h{node}")
        elif typ == 'sep':
            pnd, comp = meta
            lines.append(f"{pad}rcases p{pnd}_{comp} with h{node} | h{node}")
        for kid in kids:
            kl = emit(kid, ind + 2)
            lines.append(f"{pad}· {kl[0].strip()}")
            lines += kl[1:]
        return lines

    lines = emit(tree, len(indent))
    ground_used = {'hlam'} | {n for n in used if not n.startswith('N')}
    return lines, ground_used

# ---------------- certificate assembly ----------------
def conv_nm(kind2, kk):
    if kind2 == 'med': return f"msig1_{kk}_of_pos"
    if kind2 == 'hi': return f"msig2_{kk}_of_pos"
    return f"msig2_{kk[0]}_{kk[1]}_of_pos"

def cert_theorem(cert):
    spec, hasem = CERTS[cert]
    params = []
    for r, kind in spec:
        ch = chords(r)
        rs = 'RowSig2' if kind == 's2' else 'RowSig1'
        params += [
            f"    {{x{r}0 x{r}1 x{r}2 x{r}3 : ℝ}}",
            f"    (ho{r} : m.t {r} ≤ x{r}0 ∧ x{r}0 ≤ x{r}1 ∧ x{r}1 ≤ x{r}2 ∧ "
            f"x{r}2 ≤ x{r}3 ∧ x{r}3 ≤ m.t {r} + m.p)",
            f"    (hs{r} : {rs} m.lam m.p (m.t {r}) x{r}0 x{r}1 x{r}2 x{r}3)",
            f"    (hp{r} : List.Perm [x{r}0, x{r}1, x{r}2, x{r}3] "
            f"[{ch[0]}, {ch[1]}, {ch[2]}, {ch[3]}])"]
    if hasem:
        params.append(f"    (hem : {EM_DISJ})")
    lines = [f"theorem n4cert_{cert} (m : N4Model)"] + params + ["    : False := by"]

    def rec(i, key, ind):
        r, kind = spec[i]
        n = 15 if kind == 's2' else 5
        out = [ind + f"rcases hs{r} with " + " | ".join([f"s{r}"] * n)]
        for c in range(n):
            key2 = key + [c]
            if i == len(spec) - 1:
                ln = leaf_name(cert, tuple(key2))
                args = []
                for j, (rr, kk) in enumerate(spec):
                    kind2, kk2 = case_of(kk, key2[j])
                    args.append(f"({conv_nm(kind2, kk2)} m.hlam ho{rr} s{rr} hp{rr})")
                call = f"exact {ln} m " + " ".join(args)
                if hasem:
                    call += " hem"
                out.append(ind + f"· {call}")
            else:
                sub = rec(i + 1, key2, ind + "  ")
                out.append(ind + "· " + sub[0].strip())
                out += sub[1:]
        return out

    lines += rec(0, [], "  ")
    return "\n".join(lines)


# ---------------- assembly ----------------
def emit_header():
    return '''import Mathlib

set_option maxHeartbeats 1600000

namespace R2N4

open List

/-- **Scalar model of the `n = 4` six-centre terminal geometry.** -/
structure N4Model where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 4 * lam <= p ∧ p < 5 * lam
  t : Fin 5 → ℝ
  ht : StrictMono t
  ht0 : 0 <= t 0
  ht4 : t 4 <= p - 4 * lam
  d : Fin 5 → Fin 5 → ℝ
  hcor : ∀ i j : Fin 5, i < j →
    t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin 5, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)
''' + rowsig_pos_def()

LEAF_FILES = {
    'pair_A':    ['N4LeavesPA'],
    'pair_B':    ['N4LeavesPB1', 'N4LeavesPB2'],
    'triple_A':  ['N4LeavesTA1', 'N4LeavesTA2', 'N4LeavesTA3', 'N4LeavesTA4'],
    'triple_B':  [f'N4LeavesTB{i}' for i in range(1, 13)],
    'pair04_em': ['N4LeavesPE1', 'N4LeavesPE2'],
}

def main():
    outdir = 'Jsp000404'
    # ---- shared definitions ----
    chunks = [emit_header(), HELPERS]
    for c in range(5):
        chunks.append(sig_decl('sig1', c))
    for c in range(5):
        chunks.append(sig_decl('sig2', c))
    for (a, b) in MEDPAIR:
        chunks.append(sig_decl('sig2', (a, b)))
    for c in range(5):
        chunks.append(conv_lemma('sig1', c))
    for c in range(5):
        chunks.append(conv_lemma('sig2', c))
    for (a, b) in MEDPAIR:
        chunks.append(conv_lemma('sig2', (a, b)))
    _write(f'{outdir}/N4Defs.lean', chunks)
    # ---- leaf files, bucketed by node budget ----
    leaf_modules = []
    for cert, files in LEAF_FILES.items():
        m = CORES[cert]
        items = sorted(m.items(),
                       key=lambda kv: count_nodes(TREES[cert][kv[0]]), reverse=True)
        buckets = [{'nodes': 0, 'ks': []} for _ in files]
        for kstr, core in items:
            if core == 'SAT':
                raise RuntimeError(f'SAT leaf {cert} {kstr}')
            b = min(buckets, key=lambda b: b['nodes'])
            b['ks'].append(kstr)
            b['nodes'] += count_nodes(TREES[cert][kstr])
        for fname, b in zip(files, buckets):
            body = [f"import Jsp000404.N4Defs\n\nnamespace R2N4\n"]
            for kstr in sorted(b['ks'], key=lambda s: tuple(int(v) for v in s.split(','))):
                body.append(leaf_theorem(cert, kstr, CORES[cert][kstr]))
            _write(f'{outdir}/{fname}.lean', body)
            leaf_modules.append(f'Jsp000404.{fname}')
    # ---- certificate assembly ----
    body = ["import " + "\nimport ".join(sorted(set(leaf_modules))) + "\n\nnamespace R2N4\n"]
    for cert in CERTS:
        body.append(cert_theorem(cert))
    _write(f'{outdir}/R2SixCentreN4.lean', body)

def _write(path, chunks):
    txt = "\n\n".join(chunks) + "\n\nend R2N4\n"
    with open(path, 'w') as f:
        f.write(txt)
    print('wrote', path, len(txt.splitlines()), 'lines')

if __name__ == '__main__':
    main(*sys.argv[1:])
