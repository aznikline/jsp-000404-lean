#!/usr/bin/env python3
"""Generate Jsp000404/S7Leaves*.lean, S8Leaves*.lean, S7S8Certs.lean
from tools/s7_leaf_trees_lin.json (pure-linear terminals, dual-solver
extractor).

Tree -> Lean:
  'node' tr       : rcases m.htr i j k (by decide) (by decide) with hN | hN
  'node' emin/emax: rcases h{r}{tag} with hN | ... (N arms)
  'node' bigk     : rcases h{r}bigk with hNc | ... (N^2 arms incl diagonal)
                    each arm: obtain <pN_0, pN_1, pN_2, pN_3> := hNc
  'node' nbz      : rcases p{pnd}_{ci} (chord) (by simp) with hN | hN
  'term'          : linarith only [...]

Subtrees larger than BUDGET nodes are hoisted into `private theorem`s
taking (m, the row MSig bundles, the ancestor arm hypotheses).
"""
import itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
_SNAP = os.path.join(HERE, 's7_leaf_trees_snap.json')
TREES = json.load(open(_SNAP if os.path.exists(_SNAP)
                    else os.path.join(HERE, 's7_leaf_trees_lin.json')))

CANON2 = ['H_L', 'H_I', 'H_R', 'M_LI', 'M_LR', 'M_IR']
CANON1 = ['L_0', 'L_I', 'L_R']
COMPS = {
    'H_L':  [('elo', 3), ('emin', 4), ('emax', 2)],
    'H_I':  [('bigk', (3, 4)), ('emin', 2), ('emax', 2)],
    'H_R':  [('ehi', 3), ('emax', 4), ('emin', 2)],
    'M_LI': [('elo', 2), ('emin', 3), ('emax', 2), ('bigk', (2, 3))],
    'M_LR': [('elo', 2), ('emin', 3), ('ehi', 2), ('emax', 3)],
    'M_IR': [('emin', 2), ('ehi', 2), ('emax', 3), ('bigk', (2, 3))],
    'L_0':  [('elo', 2), ('emin', 3), ('emax', 2)],
    'L_I':  [('bigk', (2, 3)), ('emin', 2), ('emax', 2)],
    'L_R':  [('ehi', 2), ('emax', 3), ('emin', 2)],
}

CERTS = {
    's7_AA2': dict(P=7, spec=[(0, 's2'), (1, 's2'), (2, 's1')]),
    's7_AA3': dict(P=7, spec=[(0, 's2'), (1, 's2'), (3, 's1')]),
    's7_AA4': dict(P=7, spec=[(0, 's2'), (1, 's2'), (4, 's1')]),
    's7_AA5': dict(P=7, spec=[(0, 's2'), (1, 's2'), (5, 's1')]),
    's7_AB0': dict(P=7, spec=[(4, 's2'), (5, 's2'), (0, 's1')]),
    's7_AB1': dict(P=7, spec=[(4, 's2'), (5, 's2'), (1, 's1')]),
    's7_AB2': dict(P=7, spec=[(4, 's2'), (5, 's2'), (2, 's1')]),
    's7_AB3': dict(P=7, spec=[(4, 's2'), (5, 's2'), (3, 's1')]),
    's7_BT1': dict(P=7, spec=[(0, 's2'), (5, 's2'), (1, 's1')]),
    's7_BT2': dict(P=7, spec=[(0, 's2'), (5, 's2'), (2, 's1')]),
    's7_BT3': dict(P=7, spec=[(0, 's2'), (5, 's2'), (3, 's1')]),
    's7_BT4': dict(P=7, spec=[(0, 's2'), (5, 's2'), (4, 's1')]),
    's8_AA':  dict(P=8, spec=[(0, 's2'), (1, 's2')]),
    's8_BT':  dict(P=8, spec=[(0, 's2'), (6, 's2')]),
    's8_AB':  dict(P=8, spec=[(5, 's2'), (6, 's2')]),
}
TAG = {'s7_AA2': 'sAA2', 's7_AA3': 'sAA3', 's7_AA4': 'sAA4',
       's7_AA5': 'sAA5', 's7_AB0': 'sAB0', 's7_AB1': 'sAB1',
       's7_AB2': 'sAB2', 's7_AB3': 'sAB3', 's7_BT1': 'sBT1',
       's7_BT2': 'sBT2', 's7_BT3': 'sBT3', 's7_BT4': 'sBT4',
       's8_AA': 'sAA8', 's8_BT': 'sBT8', 's8_AB': 'sAB8'}

BUDGET = 2500  # max nodes per hoisted subtheorem


def dn(i, j):
    return f"(m.d {min(i, j)} {max(i, j)})"


def chords(P, r):
    """N = P-1 non-anchor points; row r's chord list (P-2 elements)."""
    return [dn(r, j) for j in range(P - 1) if j != r]


def cls_index(kind, cls):
    return (CANON2 if kind == 's2' else CANON1).index(cls)


def leaf_name(cert, key):
    ks = key.split(',')
    return f"n{CERTS[cert]['P']}l_{TAG[cert]}_" + "_".join(ks)


def count_nodes(tr):
    if tr[0] in ('term', 'FAIL', 'OVER', 'NEEDS_SPLIT'):
        return 1
    return 1 + sum(count_nodes(k) for k in tr[3])


# ---------- prop text for arm hypotheses ----------
def tr_prop(ijk, di):
    i, j, k = ijk
    if di == 0:
        return (f"(m.d {i} {j} + m.lam ≤ m.d {j} {k} ∧ "
                f"m.d {i} {j} < m.d {i} {k} ∧ m.d {i} {k} < m.d {j} {k})")
    return (f"(m.d {j} {k} + m.lam ≤ m.d {i} {j} ∧ "
            f"m.d {j} {k} < m.d {i} {k} ∧ m.d {i} {k} < m.d {i} {j})")


def cs_list(P, r):
    return "[" + ", ".join(chords(P, r)) + "]"


def bigk_prop(P, r, cls, di):
    n = P - 2
    a, b = di // n, di % n
    lo, hi = dict(COMPS[cls])['bigk']
    ch = chords(P, r)
    x, y = ch[a], ch[b]
    return (f"({x} < {y} ∧ {lo} * m.lam ≤ {y} - {x} ∧ "
            f"{y} - {x} < {hi} * m.lam ∧ "
            f"(∀ z ∈ {cs_list(P, r)}, z ≤ {x} ∨ {y} ≤ z))")


def e_prop(P, r, cls, tag, di):
    ch = chords(P, r)[di]
    v = dict(COMPS[cls])[tag]
    if tag == 'emin':
        return f"({ch} - m.t {r} < {v} * m.lam)"
    return f"(m.t {r} + m.p - {ch} < {v} * m.lam)"


def nbz_prop(P, r, cls, meta, di):
    pnd, pdi, ci, z = meta
    n = P - 2
    a, b = pdi // n, pdi % n
    ch = chords(P, r)
    x, y, zz = ch[a], ch[b], ch[z]
    if di == 0:
        return f"({zz} ≤ {x})"
    return f"({y} ≤ {zz})"


# ---------- emitter ----------
class LeafEmit:
    def __init__(self, cert, key):
        self.cert = cert
        self.key = key
        self.P = CERTS[cert]['P']
        self.spec = CERTS[cert]['spec']
        self.n = self.P - 2
        self.combo = key.split(',')
        self.cls = list(self.combo)
        self.tree = TREES[cert][key]
        self.nodeinfo = {}
        self.collect(self.tree)
        self.subs = []
        self.sub_ctr = itertools.count()

    def collect(self, nd):
        if nd[0] == 'node':
            self.nodeinfo[nd[1]] = nd[2]
            for k in nd[3]:
                self.collect(k)

    def row_cls(self, r):
        for (rr, kk), c in zip(self.spec, self.cls):
            if rr == r:
                return c
        raise KeyError(r)

    def core_names(self, core):
        out = {'hlam'}
        for nm in core:
            if nm.startswith('N'):
                base, _, ci = nm.partition('c')
                n = int(base[1:])
                typ, r, _name, _meta = self.nodeinfo[n]
                if typ == 'bigk':
                    out.add(f'p{n}_{ci}')
                else:
                    out.add(f'h{n}')
            elif nm == 'htPb':
                out.add(f'ht{self.P - 2}b')
            else:
                out.add(nm)
        return sorted(out)

    def arm_prop(self, and_, di):
        typ, r, name, meta = self.nodeinfo[and_]
        if typ == 'tr':
            return tr_prop(r, di)
        if typ in ('emin', 'emax'):
            return e_prop(self.P, r, self.row_cls(r), typ, di)
        if typ == 'bigk':
            return bigk_prop(self.P, r, self.row_cls(r), di)
        if typ == 'nbz':
            return nbz_prop(self.P, r, self.row_cls(r), meta, di)
        raise RuntimeError(typ)

    def used_names(self, nd, acc):
        if nd[0] == 'term':
            acc.update(nd[1])
        elif nd[0] == 'node':
            for k in nd[3]:
                self.used_names(k, acc)

    def split_tags(self, nd, acc):
        if nd[0] == 'node':
            typ, r, _n, _m = nd[2]
            if typ in ('emin', 'emax', 'bigk'):
                acc.add((r, typ))
            for k in nd[3]:
                self.split_tags(k, acc)

    def ground_haves(self, used):
        P = self.P
        out = ["  have hlam := m.hlam"]
        if 'hplo' in used or 'hphi' in used:
            out.append("  obtain ⟨hplo, hphi⟩ := m.hp")
        if 'ht0b' in used:
            out.append("  have ht0b := m.ht0")
        if 'htPb' in used:
            out.append(f"  have ht{P - 2}b := m.ht{P - 2}")
        for i in range(P - 1):
            for j in range(i + 1, P - 1):
                if f'hc{i}{j}' in used:
                    out.append(
                        f"  have hc{i}{j} := m.hcor {i} {j} (by decide)")
        for i in range(P - 2):
            if f'ht{i}{i + 1}' in used:
                out.append(f"  have ht{i}{i + 1} : m.t {i} < m.t {i + 1}"
                           f" := m.ht (by decide)")
        return out

    def obtain_lines(self, used, ornames):
        # Non-consuming projections: deeper hoisted calls still need hb{r}.
        out = []
        for (r, kind) in self.spec:
            cls = self.row_cls(r)
            tags = [t for t, _ in COMPS[cls]]
            k = len(tags)
            for i, t in enumerate(tags):
                need = (r, t) in ornames or \
                    (t in ('elo', 'ehi') and
                     any(nm.startswith(f'u{r}{t}') for nm in used))
                if not need:
                    continue
                proj = '.'.join(['2'] * i + ['1']) if i < k - 1 \
                    else '.'.join(['2'] * (k - 1))
                out.append(f"  have h{r}{t} := hb{r}.{proj}")
        return out

    def u_entries(self, cls):
        """U list in append order: each elo/ehi call adds n entries."""
        seq = []
        for tag, _a in COMPS[cls]:
            if tag in ('elo', 'ehi'):
                seq += [(tag, i) for i in range(self.n)]
        return seq

    def u_lines(self, used):
        out = []
        for (r, kind) in self.spec:
            cls = self.row_cls(r)
            ch = chords(self.P, r)
            for gi, (tag, ci) in enumerate(self.u_entries(cls)):
                nm = f'u{r}{tag}{gi}'
                if nm in used:
                    out.append(f"  have {nm} := h{r}{tag} "
                               f"{ch[ci]} (by simp)")
        return out

    def emit(self, nd, ind, anc):
        pad = ' ' * ind
        if nd[0] == 'term':
            return [f"{pad}linarith only "
                    f"[{', '.join(self.core_names(nd[1]))}]"]
        node, info, kids = nd[1], nd[2], nd[3]
        typ, r, name, meta = info
        if ind > 2 and count_nodes(nd) > BUDGET:
            return [self.hoist(nd, ind, anc)]
        lines = []
        if typ == 'tr':
            i, j, k = r
            lines.append(f"{pad}rcases m.htr {i} {j} {k} (by decide) "
                         f"(by decide) with h{node} | h{node}")
        elif typ in ('emin', 'emax'):
            arms = " | ".join([f"h{node}"] * self.n)
            lines.append(f"{pad}rcases h{r}{typ} with {arms}")
        elif typ == 'bigk':
            arms = " | ".join([f"h{node}c"] * (self.n * self.n))
            lines.append(f"{pad}rcases h{r}bigk with {arms}")
            for di, kid in enumerate(kids):
                lines.append(
                    f"{pad}· obtain "
                    f"⟨{', '.join(f'p{node}_{j}' for j in range(4))}⟩"
                    f" := h{node}c")
                lines += self.emit(kid, ind + 2, anc + [(node, 'bigk', di)])
            return lines
        elif typ == 'nbz':
            pnd, pdi, ci, z = meta
            ch = chords(self.P, r)[z]
            lines.append(f"{pad}rcases p{pnd}_{ci} {ch} (by simp) "
                         f"with h{node} | h{node}")
        else:
            raise RuntimeError(typ)
        for di, kid in enumerate(kids):
            kl = self.emit(kid, ind + 2, anc + [(node, typ, di)])
            lines.append(f"{pad}· {kl[0].strip()}")
            lines += kl[1:]
        return lines

    def hoist(self, nd, ind, anc):
        pad = ' ' * ind
        sid = next(self.sub_ctr)
        lname = f"{leaf_name(self.cert, self.key)}_s{sid}"
        used = set()
        self.used_names(nd, used)
        ornames = set()
        self.split_tags(nd, ornames)
        sig = [f"private theorem {lname} (m : N{self.P}Model)"]
        for (r, kind) in self.spec:
            cls = self.row_cls(r)
            cs = " ".join(chords(self.P, r))
            sig.append(f"    (hb{r} : CMSig{kind[1]}_{self.P}_{cls} "
                       f"m.lam m.p (m.t {r}) {cs})")
        for (and_, typ, di) in anc:
            sig.append(f"    (hg{and_} : {self.arm_prop(and_, di)})")
        callargs = " ".join(
            ['m'] + [f"hb{r}" for r, _ in self.spec]
            + [f"h{and_}c" if typ == 'bigk' else f"h{and_}"
               for (and_, typ, di) in anc])
        body = [" : False := by"]
        body += self.ground_haves(used)
        # destructure MSig bundles BEFORE aliasing arm hyps: an ancestor
        # node id may numerically equal a row index, and `have h{r}` would
        # shadow the bundle.
        body += self.obtain_lines(used, ornames)
        body += self.u_lines(used)
        for (and_, typ, di) in anc:
            if typ == 'bigk':
                body.append(f"  have h{and_}c := hg{and_}")
                body.append(
                    f"  obtain "
                    f"⟨{', '.join(f'p{and_}_{j}' for j in range(4))}⟩"
                    f" := h{and_}c")
            else:
                body.append(f"  have h{and_} := hg{and_}")
        body += self.emit(nd, 2, anc)
        subtxt = "\n".join(sig) + "\n" + "\n".join(body)
        n = count_nodes(nd)
        if n > 1500:
            subtxt = (f"set_option maxHeartbeats "
                      f"{max(1600000, n * 2000)} in\n" + subtxt)
        self.subs.append(subtxt)
        return f"{pad}exact {lname} {callargs}"


def emit_leaf(cert, key):
    le = LeafEmit(cert, key)
    P = le.P
    sig = [f"theorem {leaf_name(cert, key)} (m : N{P}Model)"]
    for (r, kind), c in zip(le.spec, le.combo):
        cls = le.row_cls(r)
        cs = " ".join(chords(P, r))
        sig.append(f"    (hb{r} : CMSig{kind[1]}_{P}_{cls} "
                   f"m.lam m.p (m.t {r}) {cs})")
    used = set()
    le.used_names(le.tree, used)
    ornames = set()
    le.split_tags(le.tree, ornames)
    body = ["    : False := by"]
    body += le.ground_haves(used)
    body += le.obtain_lines(used, ornames)
    body += le.u_lines(used)
    body += le.emit(le.tree, 2, [])
    main = "\n".join(sig) + "\n" + "\n".join(body)
    n = count_nodes(le.tree)
    if n > 1500:
        main = (f"set_option maxHeartbeats "
                f"{max(1600000, n * 2000)} in\n" + main)
    if le.subs:
        main = "\n\n".join(le.subs) + "\n\n" + main
    return main


# ---------------- cert dispatch ----------------
def hord_prop(P, r):
    n = P - 2
    chain = [f"m.t {r} ≤ x{r}0"]
    for i in range(1, n):
        chain.append(f"x{r}{i - 1} ≤ x{r}{i}")
    chain.append(f"x{r}{n - 1} ≤ m.t {r} + m.p")
    return " ∧ ".join(chain)


def hsp_proof(P, r):
    n = P - 2
    chs = cs_list(P, r)
    return [f"  have hsp{r} : ∀ z ∈ {chs}, m.lam ≤ z ∧ z < 5 * m.lam :=",
            "    fun z hz => by",
            f"      rcases (mem{n}or hz) with " +
            " | ".join(["rfl"] * n) + " <;>",
            f"        exact n{P}_chord_bounds m (by decide)"]


def cert_theorem(cert):
    P = CERTS[cert]['P']
    spec = CERTS[cert]['spec']
    n = P - 2
    params = []
    for r, kind in spec:
        chs = ", ".join(chords(P, r))
        xs = " ".join(f"x{r}{i}" for i in range(n))
        rs = f"RowSig{kind[1]}_{P}"
        params += [
            f"    {{{xs} : ℝ}}",
            f"    (ho{r} : {hord_prop(P, r)})",
            f"    (hs{r} : {rs} m.lam m.p (m.t {r}) {xs})",
            f"    (hp{r} : List.Perm [{', '.join(f'x{r}{i}' for i in range(n))}] "
            f"{cs_list(P, r)})"]
    lines = [f"theorem s{P}cert_{cert[3:]} (m : N{P}Model)"] + params + \
        ["    : False := by"]
    for r, kind in spec:
        lines += hsp_proof(P, r)
    # nested canonical rcases
    def rec(i, prefix, ind):
        r, kind = spec[i]
        k = '2' if kind == 's2' else '1'
        narm = 6 if kind == 's2' else 3
        conv = f"msig{k}_{P}_canon_of_pos m.hlam ho{r} hs{r} hp{r}"
        if kind == 's2':
            conv += f" hsp{r}"
        lines = [ind + f"rcases {conv} with " + " | ".join([f"c{r}"] * narm)]
        order = CANON2 if kind == 's2' else CANON1
        for ci, cls in enumerate(order):
            key2 = prefix + [cls]
            if i == len(spec) - 1:
                ln = leaf_name(cert, ','.join(key2))
                call = f"exact {ln} m " + " ".join(
                    f"c{rr}" for rr, _ in spec)
                lines.append(ind + f"· {call}")
            else:
                sub = rec(i + 1, key2, ind + "  ")
                lines.append(ind + "· " + sub[0].strip())
                lines += sub[1:]
        return lines
    lines += rec(0, [], "  ")
    return "\n".join(lines)


# ---------------- driver ----------------
def main(which=None):
    outdir = os.path.join(HERE, '..', 'Jsp000404')
    mods = []
    for cert in CERTS:
        if which and cert != which:
            continue
        if cert not in TREES:
            continue  # trees not yet extracted
        P = CERTS[cert]['P']
        m = TREES[cert]
        items = sorted(m.items(), key=lambda kv: count_nodes(kv[1]),
                       reverse=True)
        # bucket into files ~6000 nodes each
        buckets, cur, curn = [], [], 0
        for kstr, tr in items:
            if curn > 6000 and cur:
                buckets.append(cur)
                cur, curn = [], 0
            cur.append(kstr)
            curn += count_nodes(tr)
        if cur:
            buckets.append(cur)
        for bi, ks in enumerate(buckets):
            body = ["import Jsp000404.S7Defs\n\n"
                    "set_option maxHeartbeats 1600000\n\n"
                    "namespace R2N4\n"]
            for kstr in sorted(ks):
                body.append(emit_leaf(cert, kstr))
            fname = f"S{P}Leaves{TAG[cert]}_{bi}"
            path = os.path.join(outdir, fname + '.lean')
            with open(path, 'w') as f:
                f.write("\n\n".join(body) + "\n\nend R2N4\n")
            mods.append(f'Jsp000404.{fname}')
            print('wrote', fname, os.path.getsize(path))
    if not which:
        # per-family aggregators so S7/S8 extraction build independently
        for pref, out in (('s7', 'S7Certs.lean'), ('s8', 'S8Certs.lean')):
            fam = [c for c in CERTS
                   if c.startswith(pref) and c in TREES]
            fmods = [m for m in mods
                     if f'.S{pref[1].upper()}Leaves' in m]
            body = ["import " + "\nimport ".join(sorted(fmods)) +
                    "\n\nnamespace R2N4\n"]
            for cert in fam:
                body.append(cert_theorem(cert))
            path = os.path.join(outdir, out)
            with open(path, 'w') as f:
                f.write("\n\n".join(body) + "\n\nend R2N4\n")
            print('wrote', out, os.path.getsize(path))


if __name__ == '__main__':
    main(*(sys.argv[1:] or [None]))
