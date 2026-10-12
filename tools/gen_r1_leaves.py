#!/usr/bin/env python3
"""Generate Jsp000404/R1Leaves*.lean + R1Certs.lean from
tools/r1_trees.json (reduced-key -> tree) + tools/r1_map.json
(full spec+combo -> reduced key) + tools/r1_specs.json.

Port of gen_s7_leaves.py.  Differences:
  * leaf theorems are emitted per REDUCED (core-row) problem;
    the cert dispatcher destructures every spec row's CMSig bundle
    into its canonical class and calls the reduced leaf.
  * P = #centres (7..11); model N{P}Model lives in S7Defs (P<=8)
    or R1Defs (P>=9).
"""
import itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
_TSNAP = os.environ.get('R1_TREES', os.path.join(HERE, 'r1_trees.json'))
_FSNAP = os.environ.get('R1_MAP', os.path.join(HERE, 'r1_map.json'))
# Lazily-initialized snapshots: preflight only needs specs+map and must
# run BEFORE the ~22MB trees JSON is loaded.
_TREES = None
_FMAP = None
_SPECS = None


def load_trees():
    global _TREES
    if _TREES is None:
        _TREES = json.load(open(_TSNAP))
    return _TREES


def load_fmap():
    global _FMAP
    if _FMAP is None:
        _FMAP = json.load(open(_FSNAP))
    return _FMAP


def load_specs():
    global _SPECS
    if _SPECS is None:
        _SPECS = json.load(open(os.path.join(HERE, 'r1_specs.json')))
    return _SPECS

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
BUDGET = 2500
DEFS_MOD = {7: 'S7Defs', 8: 'S7Defs', 9: 'R1Defs', 10: 'R1Defs',
            11: 'R1Defs'}


def dn(i, j):
    return f"(m.d {min(i, j)} {max(i, j)})"


def chords(P, r):
    """row r's chord list over N = P-2 chord vars."""
    return [dn(r, j) for j in range(P - 1) if j != r]


def parse_rkey(rkey):
    """'P{p}|{k}@{r},...|{cls},...' -> (centres, [(r,kind)], [cls]).

    The rkey's P is the extraction size (#t-positions); the Lean model
    N{centres}Model has centres = positions + 1."""
    ppart, spart, cpart = rkey.split('|')
    P = int(ppart[1:]) + 1
    spec = [(int(r), k) for k, r in
            (x.split('@') for x in spart.split(','))]
    return P, spec, cpart.split(',')


def count_nodes(tr):
    if tr[0] in ('term', 'FAIL', 'OVER', 'NEEDS_SPLIT', 'NONUNSAT'):
        return 1
    return 1 + sum(count_nodes(k) for k in tr[3])


# registry: reduced-key -> short leaf name
REG = {}


def leaf_name(rkey):
    if rkey not in REG:
        P, spec, combo = parse_rkey(rkey)
        REG[rkey] = (f"r1l{P}_" +
                     "_".join(f'{k[1]}{r}' for r, k in spec)
                     + "_" + "_".join(combo))
    return REG[rkey]


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
    def __init__(self, rkey):
        self.P, self.spec, self.cls = parse_rkey(rkey)
        self.n = self.P - 2
        self.tree = load_trees()[rkey]
        self.nodeinfo = {}
        self.collect(self.tree)
        self.subs = []
        self.sub_ctr = itertools.count()
        self.rkey = rkey

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
            projs = ['1', '2.1', '2.2.1', '2.2.2']
            for di, kid in enumerate(kids):
                lines.append(f"{pad}· have p{node}_0 := h{node}c.1")
                for j in (1, 2, 3):
                    lines.append(
                        f"{pad}  have p{node}_{j} := "
                        f"h{node}c.{projs[j]}")
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
        lname = f"{leaf_name(self.rkey)}_s{sid}"
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
        body += self.obtain_lines(used, ornames)
        body += self.u_lines(used)
        for (and_, typ, di) in anc:
            if typ == 'bigk':
                body.append(f"  have h{and_}c := hg{and_}")
                for j, proj in enumerate(['1', '2.1', '2.2.1', '2.2.2']):
                    body.append(
                        f"  have p{and_}_{j} := h{and_}c.{proj}")
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


def emit_leaf(rkey):
    le = LeafEmit(rkey)
    P = le.P
    sig = [f"theorem {leaf_name(rkey)} (m : N{P}Model)"]
    for (r, kind), c in zip(le.spec, le.cls):
        cs = " ".join(chords(P, r))
        sig.append(f"    (hb{r} : CMSig{kind[1]}_{P}_{c} "
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


def cert_name(speckey_):
    return ('r1cert_' + speckey_.replace('|', '_')
            .replace(',', '_').replace('@', 'a').replace('s', 's'))


def cert_theorem(speckey_, P, spec):
    """theorem for one full spec: per-row sig -> class dispatch -> leaf."""
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
    cname = cert_name(speckey_)
    lines = [f"theorem {cname} (m : N{P}Model)"] + params + \
        ["    : False := by"]
    for r, kind in spec:
        lines += hsp_proof(P, r)

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
                fk = speckey_ + '|' + ','.join(key2)
                tgt = load_fmap().get(fk)
                if tgt is None or tgt.startswith('NONUNSAT'):
                    raise RuntimeError(f"UNMAPPED {fk}")
                ln = leaf_name(tgt)
                PP, rspec, _ = parse_rkey(tgt)
                call = (f"exact {ln} m " + " ".join(
                    f"c{rr}" for rr, _ in rspec))
                lines.append(ind + f"· {call}")
            else:
                sub = rec(i + 1, key2, ind + "  ")
                lines.append(ind + "· " + sub[0].strip())
                lines += sub[1:]
        return lines
    lines += rec(0, [], "  ")
    return "\n".join(lines)


def speckey(prof, spec):
    return (prof + '|' + ','.join(f'{k}@{r}' for k, r in
                                  ((x[1], x[0]) for x in spec)))


def required_keys(speckey_, spec):
    """Yield every full map key `speckey_|c1,c2,...`: the cartesian
    product over rows of CANON2 ('s2' rows) / CANON1 ('s1' rows), in the
    same traversal order as cert_theorem's rec()."""
    orders = [CANON2 if kind == 's2' else CANON1 for _r, kind in spec]
    for combo in itertools.product(*orders):
        yield speckey_ + '|' + ','.join(combo)


def preflight(specs, fmap):
    """Check every (prof, P, spec) against the map.  A spec is COMPLETE
    iff all its required keys exist in fmap and none maps to a
    'NONUNSAT'-prefixed target.  Returns (complete_specs, missing) where
    missing maps speckey -> list of missing/NONUNSAT full keys."""
    complete_specs = []
    missing = {}
    for prof, P, spec in specs:
        sk = speckey(prof, spec)
        bad = [fk for fk in required_keys(sk, spec)
               if fmap.get(fk) is None or fmap[fk].startswith('NONUNSAT')]
        if bad:
            missing[sk] = bad
        else:
            complete_specs.append((prof, P, spec))
    return complete_specs, missing


# ---------------- driver ----------------
def main():
    argv = sys.argv[1:]
    allow_partial = '--allow-partial' in argv
    only = set(a for a in argv if not a.startswith('--'))
    outdir = os.path.join(HERE, '..', 'Jsp000404')
    # unique specs per profile
    allspecs = []
    for prof, profspecs in load_specs().items():
        if only and prof not in only:
            continue
        P = {'T1': 7, 'T2': 7, 'T3': 8, 'T4': 9, 'T5': 10,
             'T6': 11}[prof]
        seen = set()
        for v in profspecs.values():
            if not v:
                continue
            st = tuple(tuple(x) for x in v)
            if st in seen:
                continue
            seen.add(st)
            allspecs.append((prof, P, [list(x) for x in st]))
    # ---- preflight on specs+map only, BEFORE the 22MB trees load and
    # before any output file is written ----
    complete_specs, missing = preflight(allspecs, load_fmap())
    nmiss = sum(len(v) for v in missing.values())
    if missing and not allow_partial:
        print(f"preflight FAIL: {len(missing)} incomplete spec(s), "
              f"{nmiss} missing/NONUNSAT map keys", file=sys.stderr)
        shown = 0
        for sk in sorted(missing):
            for fk in missing[sk]:
                if shown >= 20:
                    break
                print(f"  {fk}", file=sys.stderr)
                shown += 1
            if shown >= 20:
                break
        sys.exit(2)
    if allow_partial:
        manifest = {
            'emitted': [speckey(prof, spec)
                        for prof, _P, spec in complete_specs],
            'skipped': [{'speckey': sk, 'missing_count': len(ks)}
                        for sk, ks in sorted(missing.items())],
        }
        mpath = os.path.join(HERE, 'r1_emit_manifest.json')
        with open(mpath, 'w') as f:
            json.dump(manifest, f, indent=1)
        print(f"preflight: emitting {len(complete_specs)} complete "
              f"spec(s), skipping {len(missing)} incomplete "
              f"({nmiss} missing keys); manifest -> {mpath}",
              flush=True)
    emit_specs = complete_specs
    # leaf files: bucket reduced trees by P then by size
    okP = {p for prof, p, _ in emit_specs}
    byP = {}
    for rkey, tr in load_trees().items():
        if only:
            P_, _, _ = parse_rkey(rkey)
            if P_ not in okP:
                continue
        if tr[0] == 'NONUNSAT':
            continue
        P, _, _ = parse_rkey(rkey)
        byP.setdefault(P, []).append((rkey, tr))
    mods = []
    for P, items in sorted(byP.items()):
        items.sort(key=lambda kv: count_nodes(kv[1]), reverse=True)
        buckets, cur, curn = [], [], 0
        for kstr, tr in items:
            n = count_nodes(tr)
            if curn > 8000 and cur:
                buckets.append(cur)
                cur, curn = [], 0
            cur.append(kstr)
            curn += n
        if cur:
            buckets.append(cur)
        for bi, ks in enumerate(buckets):
            body = [f"import Jsp000404.{DEFS_MOD[P]}\n\n"
                    "set_option maxHeartbeats 1600000\n\n"
                    "namespace R2N4\n"]
            for kstr in sorted(ks):
                try:
                    body.append(emit_leaf(kstr))
                except Exception as e:
                    body.append(f"-- EMIT FAIL {kstr}: {e}")
                    print('EMIT FAIL', kstr, e, flush=True)
            fname = f"R1LeavesN{P}_{bi}"
            path = os.path.join(outdir, fname + '.lean')
            with open(path, 'w') as f:
                f.write("\n\n".join(body) + "\n\nend R2N4\n")
            mods.append((P, f'Jsp000404.{fname}'))
            print('wrote', fname, os.path.getsize(path), flush=True)
    # cert aggregator per profile
    for prof, P, spec in emit_specs:
        sk = speckey(prof, spec)
        fmods = [m for PP, m in mods if PP == P]
        body = [f"import Jsp000404.{DEFS_MOD[P]}"] + \
            [f"import {m}" for m in sorted(fmods)] + \
            ["\nnamespace R2N4\n"]
        body.append(cert_theorem(sk, P, spec))
        fname = f"R1Cert{prof}_" + \
            "_".join(f'{k[1]}{r}' for r, k in spec)
        path = os.path.join(outdir, fname + '.lean')
        with open(path, 'w') as f:
            f.write("\n\n".join(body) + "\n\nend R2N4\n")
        print('wrote', fname, os.path.getsize(path), flush=True)


if __name__ == '__main__':
    main()
