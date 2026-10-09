#!/usr/bin/env python3
"""Generate Jsp000404/S7Defs.lean — S7/S8 model, row signatures,
canonical (quotiented) multiset signatures and converters.

Canonical s2 classes (per tools/s7_canon.py):
  H_L  : hi gap at index 0          -> elo(3), emin(4), emax(2)
  H_I  : hi gap internal            -> cpair(3,4), emin(2), emax(2)
  H_R  : hi gap at last             -> ehi(3), emax(4), emin(2)
  M_LI : medpair {0, internal}      -> elo(2), emin(3), emax(2), cpair(2,3)
  M_LR : medpair {0, last}          -> elo(2), emin(3), ehi(2), emax(3)
  M_II : medpair both internal      -> corridor-excluded (span < 4*lam)
  M_IR : medpair {internal, last}   -> emin(2), ehi(2), emax(3), cpair(2,3)
Canonical s1 classes:
  L_0  : med gap at 0     -> elo(2), emin(3), emax(2)
  L_I  : med gap internal -> cpair(2,3), emin(2), emax(2)
  L_R  : med gap at last  -> ehi(2), emax(3), emin(2)

cpair enumerates ALL ordered pairs (incl. diagonal): N^2 arms,
matching the Python model's `for x in S for y in S` order.
"""
import itertools, os

HERE = os.path.dirname(os.path.abspath(__file__))


def cslist(N):
    return "[" + ", ".join(f"c{i}" for i in range(N)) + "]"


def xslist(N):
    return "[" + ", ".join(f"x{i}" for i in range(N)) + "]"


def pos_gap(k, N):
    if k == 0:
        return "x0 - tl"
    if k == N:
        return f"tl + p - x{N - 1}"
    return f"x{k} - x{k - 1}"


def pos_disj(big, lo, hi, N):
    parts = []
    for k in range(N + 1):
        g = f"({pos_gap(k, N)})"
        if k in big:
            parts += [f"{lo} * lam <= {g}", f"{g} < {hi} * lam"]
        else:
            parts.append(f"{g} < 2 * lam")
    return " ∧ ".join(parts)


def medpairs(N):
    return list(itertools.combinations(range(N + 1), 2))


def sig2_pos_disj(c, N):
    if c <= N:
        return pos_disj([c], 3, 4, N)
    return pos_disj(list(medpairs(N)[c - N - 1]), 2, 3, N)


def sig1_pos_disj(c, N):
    return pos_disj([c], 2, 3, N)


def opick(i, n, T):
    s = f"({T})" if i == n - 1 else f"(Or.inl ({T}))"
    for _ in range(i):
        s = f"(Or.inr {s})"
    return s


def E_or(f, N):
    return "(" + " ∨ ".join(f(f"c{i}") for i in range(N)) + ")"


def pairOr(lo, hi, N):
    ds = []
    for a in range(N):
        for b in range(N):
            x, y = f"c{a}", f"c{b}"
            conj = [f"{x} < {y}",
                    f"{lo} * lam ≤ {y} - {x}",
                    f"{y} - {x} < {hi} * lam",
                    f"(∀ z ∈ {cslist(N)}, z ≤ {x} ∨ {y} ≤ z)"]
            ds.append("(" + " ∧ ".join(conj) + ")")
    return "(" + " ∨\n        ".join(ds) + ")"


# ---------------- canonical MSig declarations ----------------
def comp_prop(tag, arg, N):
    if tag == 'elo':
        return f"(∀ z ∈ {cslist(N)}, {arg} * lam ≤ z - tl)"
    if tag == 'ehi':
        return f"(∀ z ∈ {cslist(N)}, {arg} * lam ≤ tl + p - z)"
    if tag == 'emin':
        return E_or(lambda c: f"{c} - tl < {arg} * lam", N)
    if tag == 'emax':
        return E_or(lambda c: f"tl + p - {c} < {arg} * lam", N)
    if tag == 'bigk':
        return pairOr(arg[0], arg[1], N)
    raise RuntimeError(tag)


def canon_comps(cls):
    """ordered (tag, arg) list mirroring s7_canon.gap_sig_case."""
    return {
        'H_L':  [('elo', 3), ('emin', 4), ('emax', 2)],
        'H_I':  [('bigk', (3, 4)), ('emin', 2), ('emax', 2)],
        'H_R':  [('ehi', 3), ('emax', 4), ('emin', 2)],
        'M_LI': [('elo', 2), ('emin', 3), ('emax', 2), ('bigk', (2, 3))],
        'M_LR': [('elo', 2), ('emin', 3), ('ehi', 2), ('emax', 3)],
        'M_IR': [('emin', 2), ('ehi', 2), ('emax', 3), ('bigk', (2, 3))],
        'L_0':  [('elo', 2), ('emin', 3), ('emax', 2)],
        'L_I':  [('bigk', (2, 3)), ('emin', 2), ('emax', 2)],
        'L_R':  [('ehi', 2), ('emax', 3), ('emin', 2)],
    }[cls]


CANON2 = ['H_L', 'H_I', 'H_R', 'M_LI', 'M_LR', 'M_IR']
CANON1 = ['L_0', 'L_I', 'L_R']


def csig_decl(cls, kind, N, P):
    name = f"CMSig{kind}_{P}_{cls}"
    args = "(lam p tl " + " ".join(f"c{i}" for i in range(N)) + " : ℝ)"
    body = " ∧\n    ".join(comp_prop(t, a, N) for t, a in canon_comps(cls))
    return f"abbrev {name} {args} : Prop :=\n    {body}"


# ---------------- conversion proofs ----------------
def nb_have(name, i, j, ind, N, bullet=False):
    head = (" " * (ind - 2) + "· " if bullet else " " * ind)
    return [f"{head}have {name} : ∀ z ∈ {cslist(N)}, z ≤ c{i} ∨ c{j} ≤ z := by",
            " " * (ind + 2) + "intro z hz",
            " " * (ind + 2) + f"rcases (mem{N}or (hp.symm.subset hz)) with "
            + " | ".join(["hz'"] * N) + " <;>",
            " " * (ind + 4) + "first | exact Or.inl (by linarith) | "
            "exact Or.inr (by linarith)"]


def conv_pair(gk, lo, hi, N):
    """witness pair for strict internal gap gk (1 <= gk <= N-1)."""
    xa, xb = f"x{gk - 1}", f"x{gk}"
    xs = xslist(N)
    lines = [f"    have hm1 := mem{N}or (hp.subset "
             f"(show {xa} ∈ {xs} by simp))",
             f"    have hm2 := mem{N}or (hp.subset "
             f"(show {xb} ∈ {xs} by simp))",
             "    rcases hm1 with " + " | ".join(["h1"] * N)]
    for i in range(N):
        lines.append("    · rcases hm2 with " + " | ".join(["h2"] * N))
        for j in range(N):
            if i == j:
                lines.append("      · exfalso; linarith")
                continue
            idx = i * N + j
            tup = "⟨by linarith, by linarith, by linarith, hnb⟩"
            lines += nb_have("hnb", i, j, 8, N, bullet=True)
            lines.append(f"        exact {opick(idx, N * N, tup)}")
    return "\n".join(lines)


def conv_comp(tag, arg, gk, N):
    """proof script for one canonical component, inside a `·` bullet."""
    xs = xslist(N)
    if tag in ('elo', 'ehi'):
        return ("    intro z hz\n"
                f"    rcases (mem{N}or (hp.symm.subset hz)) with "
                + " | ".join(["rfl"] * N) + " <;>\n"
                "      linarith")
    if tag == 'emin':
        lines = [f"    have hm := mem{N}or (hp.subset "
                 f"(show x0 ∈ {xs} by simp))",
                 "    rcases hm with " + " | ".join(["h"] * N)]
        for i in range(N):
            lines.append(f"    · exact {opick(i, N, 'by linarith')}")
        return "\n".join(lines)
    if tag == 'emax':
        lines = [f"    have hm := mem{N}or (hp.subset "
                 f"(show x{N - 1} ∈ {xs} by simp))",
                 "    rcases hm with " + " | ".join(["h"] * N)]
        for i in range(N):
            lines.append(f"    · exact {opick(i, N, 'by linarith')}")
        return "\n".join(lines)
    if tag == 'bigk':
        lo, hi = arg
        return conv_pair(gk, lo, hi, N)
    raise RuntimeError(tag)


def nconj(s):
    return s.count(" ∧ ") + 1


def hord_prop(N):
    chain = ["tl ≤ x0"]
    for i in range(1, N):
        chain.append(f"x{i - 1} ≤ x{i}")
    chain.append(f"x{N - 1} ≤ tl + p")
    return " ∧ ".join(chain)


def pair_gk(pair):
    a, b = pair
    return a if a != 0 else b


def canon2_of_pos(P, N, c):
    last = N
    if c <= N:
        if c == 0:
            return ('H_L', c)
        if c == last:
            return ('H_R', c)
        return ('H_I', c)
    a, b = medpairs(N)[c - N - 1]
    if 0 in (a, b):
        return ('M_LI', (a, b)) if last not in (a, b) else ('M_LR', (a, b))
    if last in (a, b):
        return ('M_IR', (a, b))
    return ('M_II', (a, b))


def canon1_of_pos(N, c):
    if c == 0:
        return ('L_0', c)
    if c == N:
        return ('L_R', c)
    return ('L_I', c)


def conv_lemma(cls, kind, c, gk, hsprop, N, P):
    """per-positional-case lemma producing the canonical MSig."""
    name = f"CMSig{kind}_{P}_{cls}"
    nm = f"msig{kind}_{P}_{cls}_of_pos_{c}"
    cs = canon_comps(cls)
    xs = " ".join(f"x{i}" for i in range(N))
    cs_args = " ".join(f"c{i}" for i in range(N))
    parts = [f"theorem {nm} {{lam p tl : ℝ}} (hl : 0 < lam)",
             f"    {{{xs} : ℝ}}",
             f"    (hord : {hord_prop(N)})",
             f"    (hs : {hsprop})",
             f"    {{{' '.join(f'c{i}' for i in range(N))} : ℝ}} "
             f"(hp : List.Perm {xslist(N)} {cslist(N)}) :",
             f"    {name} lam p tl {cs_args} := by",
             "  classical",
             "  obtain ⟨" + ", ".join(f"hb{q}" for q in range(N + 1))
             + "⟩ := hord",
             "  obtain ⟨" + ", ".join(f"hg{q}" for q in range(nconj(hsprop)))
             + "⟩ := hs",
             "  refine ⟨" + ", ".join("?_" for _ in cs) + "⟩"]
    for tag, arg in cs:
        pf = conv_comp(tag, arg, gk, N)
        ls = pf.split("\n")
        parts.append("  · " + ls[0].strip())
        parts += ls[1:]
    txt = "\n".join(parts)
    if nconj(hsprop) > 10:
        txt = "set_option maxHeartbeats 4000000 in\n" + txt
    return txt


# ---------------- positional RowSig + family converters ----------------
def rowsig_defs(N, P):
    ds1 = [sig1_pos_disj(c, N) for c in range(N + 1)]
    ds2 = [sig2_pos_disj(c, N) for c in range(N + 1)] + \
        [pos_disj(list(pr), 2, 3, N) for pr in medpairs(N)]
    d1 = " ∨\n    ".join(f"({d})" for d in ds1)
    d2 = " ∨\n    ".join(f"({d})" for d in ds2)
    xs = " ".join(f"x{i}" for i in range(N))
    return (f"abbrev RowSig1_{P} (lam p tl : ℝ) ({xs} : ℝ) : Prop :=\n"
            f"    {d1}\n\n"
            f"abbrev RowSig2_{P} (lam p tl : ℝ) ({xs} : ℝ) : Prop :=\n"
            f"    {d2}")


def fam_lemma_s2(N, P):
    xs = " ".join(f"x{i}" for i in range(N))
    cs = " ".join(f"c{i}" for i in range(N))
    ncase = (N + 1) + len(medpairs(N))
    tgt = " ∨\n    ".join(f"CMSig2_{P}_{cls} lam p tl {cs}"
                          for cls in CANON2)
    lines = [f"theorem msig2_{P}_canon_of_pos {{lam p tl : ℝ}} (hl : 0 < lam)",
             f"    {{{xs} : ℝ}}",
             f"    (hord : {hord_prop(N)})",
             f"    (hs : RowSig2_{P} lam p tl {xs})",
             f"    {{{' '.join(f'c{i}' for i in range(N))} : ℝ}}",
             f"    (hp : List.Perm {xslist(N)} {cslist(N)})",
             f"    (hsp : ∀ z ∈ {cslist(N)}, lam ≤ z ∧ z < 5 * lam) :",
             f"    {tgt} := by",
             "  rcases hs with " + " | ".join(["s"] * ncase)]
    for c in range(ncase):
        cls, info = canon2_of_pos(P, N, c)
        if cls == 'M_II':
            a, b = info
            ng = nconj(pos_disj([a, b], 2, 3, N))
            lines += [
                "  · exfalso",
                "    obtain ⟨" + ", ".join(f"hg{q}" for q in range(ng))
                + "⟩ := s",
                "    obtain ⟨hAl, hAu⟩ := hsp x" + str(a - 1) +
                " (hp.subset (by simp))",
                "    obtain ⟨hBl, hBu⟩ := hsp x" + str(b) +
                " (hp.subset (by simp))",
                "    linarith"]
            continue
        idx = CANON2.index(cls)
        nm = f"msig2_{P}_{cls}_of_pos_{c}"
        lines.append(f"  · exact {opick(idx, 6, f'{nm} hl hord s hp')}")
    return "\n".join(lines)


def fam_lemma_s1(N, P):
    xs = " ".join(f"x{i}" for i in range(N))
    cs = " ".join(f"c{i}" for i in range(N))
    ncase = N + 1
    tgt = " ∨\n    ".join(f"CMSig1_{P}_{cls} lam p tl {cs}"
                          for cls in CANON1)
    lines = [f"theorem msig1_{P}_canon_of_pos {{lam p tl : ℝ}} (hl : 0 < lam)",
             f"    {{{xs} : ℝ}}",
             f"    (hord : {hord_prop(N)})",
             f"    (hs : RowSig1_{P} lam p tl {xs})",
             f"    {{{' '.join(f'c{i}' for i in range(N))} : ℝ}}",
             f"    (hp : List.Perm {xslist(N)} {cslist(N)}) :",
             f"    {tgt} := by",
             "  rcases hs with " + " | ".join(["s"] * ncase)]
    for c in range(ncase):
        cls, _ = canon1_of_pos(N, c)
        idx = CANON1.index(cls)
        nm = f"msig1_{P}_{cls}_of_pos_{c}"
        lines.append(f"  · exact {opick(idx, 3, f'{nm} hl hord s hp')}")
    return "\n".join(lines)


# ---------------- helpers ----------------
def helpers(N):
    mem = " ∨ ".join(f"u = x{i}" for i in range(N))
    return f'''
theorem mem{N}or {{u {" ".join(f"x{i}" for i in range(N))} : ℝ}}
    (h : u ∈ {xslist(N)}) :
    {mem} := by
  simpa using h
'''


def model_decl(N, P):
    """N = non-anchor vertices = chords-per-row + ... wait: rows have
    N-1 chords? No — here N is the number of non-anchor points = t arity.
    Rows carry N-1+1 = N chords? Rows have (points-1)=N-1 chords...
    Keep this simple: called with N = #non-anchor points."""
    return f'''/-- **Scalar model of the `n = 4` {P}-centre terminal geometry
(`{P}` centres = anchor + {N} non-anchor vertices).** -/
structure N{P}Model where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 4 * lam <= p ∧ p < 5 * lam
  t : Fin {N} → ℝ
  ht : StrictMono t
  ht0 : 0 <= t 0
  ht{N - 1} : t {N - 1} <= p - 4 * lam
  d : Fin {N} → Fin {N} → ℝ
  hcor : ∀ i j : Fin {N}, i < j →
    t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin {N}, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)

theorem n{P}_chord_bounds (m : N{P}Model) {{i j : Fin {N}}} (hij : i < j) :
    m.lam ≤ m.d i j ∧ m.d i j < 5 * m.lam := by
  obtain ⟨hb1, hb2⟩ := m.hcor i j hij
  obtain ⟨hplo, hphi⟩ := m.hp
  have h0 : m.t 0 ≤ m.t i := m.ht.monotone (Fin.zero_le _)
  have h5 : m.t j ≤ m.t {N - 1} := m.ht.monotone (Fin.le_last j)
  have h0b := m.ht0
  have h5b := m.ht{N - 1}
  constructor <;> linarith
'''


# ---------------- emission ----------------
def emit_family(N, P):
    """N = chords per row = #non-anchor - 1;  P = #centres = #non-anchor+1."""
    chunks = [model_decl(N + 1, P), helpers(N), rowsig_defs(N, P)]
    for cls in CANON2:
        chunks.append(csig_decl(cls, 2, N, P))
    for cls in CANON1:
        chunks.append(csig_decl(cls, 1, N, P))
    n2 = (N + 1) + len(medpairs(N))
    for c in range(n2):
        cls, info = canon2_of_pos(P, N, c)
        if cls == 'M_II':
            continue
        if c <= N:
            hsprop, gk = sig2_pos_disj(c, N), c
        else:
            pr = info
            hsprop = pos_disj(list(pr), 2, 3, N)
            gk = pair_gk(pr) if cls != 'M_LR' else 0
        chunks.append(conv_lemma(cls, 2, c, gk, hsprop, N, P))
    for c in range(N + 1):
        cls, _ = canon1_of_pos(N, c)
        chunks.append(conv_lemma(cls, 1, c, c, sig1_pos_disj(c, N), N, P))
    chunks.append(fam_lemma_s2(N, P))
    chunks.append(fam_lemma_s1(N, P))
    return chunks


def main():
    chunks = ["""import Mathlib

set_option maxHeartbeats 1600000

namespace R2N4

open List
"""]
    chunks += emit_family(5, 7)
    chunks += emit_family(6, 8)
    txt = "\n\n".join(chunks) + "\n\nend R2N4\n"
    path = os.path.join(HERE, '..', 'Jsp000404', 'S7Defs.lean')
    with open(path, 'w') as f:
        f.write(txt)
    print('wrote', path, len(txt.splitlines()), 'lines')


if __name__ == '__main__':
    main()
