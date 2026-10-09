"""Structural audit of extracted trees (no arithmetic, no UNSAT checks).

Checks per Lead's spec:
  - exact canonical key coverage per cert (no missing/dup/extra)
  - no FAIL/OVER/NEEDS_SPLIT/SAT/UNKNOWN anywhere in a tree
  - every split node: kid count/order matches the source Or arity
    (tr:2, emin/emax: arity, bigk: (P-1)^2 incl. diagonal, nbz: 2)
  - every terminal's N-id references a strict ancestor node
  - nbz nodes carry provenance emitmeta (parent_di, comp_idx, z_slot)
  - cpair arm count = (P-1)^2 — diagonal arms present
"""
import json, os, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s7_canon import build, sig2_of_class, sig1_of_class, CANON1_ORDER
from s7_extract_trees import CERTS, CASES2

TREES = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     's7_leaf_trees_lin.json')


def expected_keys(cert):
    P, spec = CERTS[cert]
    kinds = [k for _, k in spec]
    return {','.join(c) for c in itertools.product(
        *[CASES2 if k == 's2' else CANON1_ORDER for k in kinds])}


def audit():
    data = json.load(open(TREES))
    errs = []
    stats = {'certs': 0, 'combos': 0, 'nodes': 0, 'terms': 0,
             'nbz_nodes': 0, 'bad_status': 0}
    for cert, (P, spec) in CERTS.items():
        if cert not in data:
            errs.append(f'{cert}: MISSING cert')
            continue
        m = data[cert]
        want = expected_keys(cert)
        got = set(m.keys())
        if got != want:
            errs.append(f'{cert}: key mismatch '
                        f'missing={len(want-got)} extra={len(got-want)}')
            continue
        stats['certs'] += 1
        delta, t, d, D, p, base, trips = build(P)
        kinds = dict(spec)
        for key, tr in m.items():
            stats['combos'] += 1
            combo = key.split(',')
            # rebuild or arity table for this combo
            arity = {}
            for (r, kind), c in zip(spec, combo):
                S = [D(r, j) for j in range(P) if j != r]
                fn = sig2_of_class if kind == 's2' else sig1_of_class
                U, E = fn(P, t[r], S, p, c)
                for ei, (tag, e) in enumerate(E):
                    arity[f'E{r}_{tag}{ei}'] = (
                        len(e.children()) if __import__('z3').is_or(e)
                        else 1)
            for ij, tre in trips.items():
                arity[f'tr{ij[0]}{ij[1]}{ij[2]}'] = len(tre.children())
            # DFS audit
            anc = set()
            stack = [(tr, anc)]
            while stack:
                node, ancestors = stack.pop()
                if not isinstance(node, list) or not node:
                    errs.append(f'{cert}/{key}: malformed node {node!r}')
                    continue
                tag = node[0]
                if tag == 'term':
                    stats['terms'] += 1
                    for nm in node[1]:
                        if nm.startswith('N'):
                            base_nm = nm.split('c')[0]
                            if base_nm not in ancestors:
                                errs.append(
                                    f'{cert}/{key}: term ref {nm} '
                                    f'not an ancestor')
                    continue
                if tag != 'node':
                    errs.append(f'{cert}/{key}: bad status {tag}')
                    stats['bad_status'] += 1
                    continue
                stats['nodes'] += 1
                nd, emit, kids = node[1], node[2], node[3]
                typ, r, orname, emitmeta = emit
                if typ == 'nbz':
                    stats['nbz_nodes'] += 1
                    if emitmeta is None or len(emitmeta) != 4:
                        errs.append(f'{cert}/{key}: nbz bad provenance '
                                    f'{emitmeta}')
                    else:
                        pnd, _di, _ci, _z = emitmeta
                        if f'N{pnd}' not in ancestors:
                            errs.append(f'{cert}/{key}: nbz src N{pnd} '
                                        f'not an ancestor')
                    if len(kids) != 2:
                        errs.append(f'{cert}/{key}: nbz arity {len(kids)}')
                else:
                    want_arity = arity.get(orname)
                    if want_arity is None:
                        errs.append(f'{cert}/{key}: unknown or {orname}')
                    elif len(kids) != want_arity:
                        errs.append(f'{cert}/{key}: {orname} arity '
                                    f'{len(kids)} != {want_arity}')
                for k in kids:
                    stack.append((k, ancestors | {f'N{nd}'}))
    print(f'audited {stats["certs"]} certs, {stats["combos"]} combos, '
          f'{stats["nodes"]} split-nodes, {stats["terms"]} terms, '
          f'{stats["nbz_nodes"]} nbz-nodes')
    if errs:
        print(f'{len(errs)} ERRORS')
        for e in errs[:50]:
            print(' ', e)
    else:
        print('STRUCTURAL AUDIT: PASS')


if __name__ == '__main__':
    audit()
