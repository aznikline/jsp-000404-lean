#!/usr/bin/env python3
"""Lean-side signature structure shared by gen_r1_defs / gen_r1_leaves.

Mirror of r1_msig.msig_ors as Lean Prop text over a model m, row r.
Chord list cs{T}_{r} m is a literal list [m.d a b, ...] (a<b, a,b!=r).

Each signature-or is described by a record:
  kind:  'bot' single | 'gap' single | 'ordis' (or of subsigs)
  arms:  list of arm descriptors for emission.
Arm descriptor:
  ('gap', ci, lo, hi) : R1Gap applied to chord index ci
  ('bot', lo, hi)     : R1Bot
  ('pair', ...)       : And of two ors (pat pairs)
"""
import itertools


def chord_vars(P, r):
    """[(a,b)] a<b, a,b != r — the chord index pairs of row r."""
    out = []
    for j in range(P):
        if j == r:
            continue
        out.append((min(r, j), max(r, j)))
    return out


def dn(pair):
    return f"(m.d {pair[0]} {pair[1]})"


def cs_list(P, r):
    return "[" + ", ".join(dn(pr) for pr in chord_vars(P, r)) + "]"


def gap_pred(P, r, pred_idx):
    """pred_idx -1 = bottom; else chord position in chord_vars."""
    if pred_idx == -1:
        return None
    return chord_vars(P, r)[pred_idx]


def rgap(lo, hi, ci, P, r):
    """Lean text: gap after chord ci in [lo,hi)."""
    cs = cs_list(P, r)
    if ci is None:
        return (f"(R1Bot m.lam m.p (m.t {r}) {lo} {hi} {cs})")
    x = dn(chord_vars(P, r)[ci])
    return (f"(R1Gap m.lam m.p (m.t {r}) {lo} {hi} {x} {cs})")


def sig_components(P, r, kind):
    """Ordered list of signature-Or components, each = list of arms.
    Each arm = list of 'subsig' entries (a conjunction arm):
      ('gap', lo, hi, ci)  ci=None -> R1Bot else R1Gap at chord index ci
    An arm with >1 entry is an And (pat-pairs)."""
    n = P - 1                      # chords per row
    preds = [-1] + list(range(n))  # bottom first
    comps = []
    if kind == 's0':
        for p in preds:
            comps.append([[('gap', 0, 2, p)]])
    elif kind == 's1':
        comps.append([[('gap', 2, 3, p)] for p in preds])          # ex
        for p in preds:                                            # g
            comps.append([[('gap', 0, 2, p)], [('gap', 2, 3, p)]])
        for x, y in itertools.combinations(preds, 2):              # b2
            comps.append([[('gap', 0, 2, x)], [('gap', 0, 2, y)]])
    elif kind == 's2':
        for p in preds:                                            # g
            comps.append([[('gap', 0, 2, p)], [('gap', 2, 3, p)],
                          [('gap', 3, 4, p)]])
        for x, y, u in itertools.combinations(preds, 3):           # b2
            comps.append([[('gap', 0, 2, x)], [('gap', 0, 2, y)],
                          [('gap', 0, 2, u)]])
        for x, y in itertools.combinations(preds, 2):              # b3
            comps.append([[('gap', 0, 3, x)], [('gap', 0, 3, y)]])
        comps.append([                                            # ex
            [('or2', p)] for p in preds])
        comps.append([                                            # pat
            *[[('gap', 3, 4, p)] for p in preds],
            *[[('or2', x), ('or2', y)]
              for x, y in itertools.combinations(preds, 2)]])
    else:
        raise ValueError(kind)
    return comps


def or2_lean(lo_hi_pred, P, r):
    """('or2', p) = gap_p in [2,3) or [3,4)."""
    _, p = lo_hi_pred
    return f"({rgap(2, 3, p, P, r)} ∨ {rgap(3, 4, p, P, r)})"


def arm_lean(arm, P, r):
    parts = []
    for e in arm:
        if e[0] == 'gap':
            _, lo, hi, ci = e
            parts.append(rgap(lo, hi, ci, P, r))
        elif e[0] == 'or2':
            parts.append(or2_lean(e, P, r))
        else:
            raise ValueError(e)
    if len(parts) == 1:
        return parts[0]
    return "(" + " ∧ ".join(parts) + ")"


def comp_lean(comp, P, r):
    arms = [arm_lean(a, P, r) for a in comp]
    if len(arms) == 1:
        return arms[0]
    return "(" + " ∨ ".join(arms) + ")"


def sig_lean(P, r, kind):
    """Full signature Prop = right-nested And of comp_lean items."""
    comps = sig_components(P, r, kind)
    txt = " ∧\n    ".join(comp_lean(c, P, r) for c in comps)
    return txt


def n_comps(P, kind):
    return len(sig_components(P, 0, kind))
