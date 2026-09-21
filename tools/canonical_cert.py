"""Canonicalize & cluster Farkas certificates for min-delta skeletons.

For each skeleton (via skeleton_enum) whose float-LP min delta equals
the target, run the exact Fraction LP, extract the Farkas certificate,
verify it, then canonicalize under vertex relabeling (S4) and cluster.

Usage: python3 canonical_cert.py k0 k1 k2 k3 [target] [max_skel]
  e.g.   python3 canonical_cert.py 3 2 2 1 0.5
"""
import sys, json, re, time
sys.path.insert(0, '.')
from itertools import permutations
import remainder_check as rc
import seidel_lp
import skeleton_enum as sen

DELTA = rc.DELTA
CONST = rc.CONST
n = 4

def lp_min_delta_f(ineqs):
    present = sorted({v for q in ineqs for v in q.a if v != CONST},
                     key=str)
    if DELTA not in present:
        present.append(DELTA)
    idx = {v: t for t, v in enumerate(present)}
    nv = len(present)
    cons = []
    for q in ineqs:
        a = [float(q.a.get(v, 0)) for v in present]
        b = float(q.b) - float(q.a.get(CONST, 0))
        cons.append((a, b))
    obj = [0.0] * nv
    obj[idx[DELTA]] = -1.0
    bounds = [(0.0, 1.0)] * nv
    r = seidel_lp.lp_max(nv, cons, obj, bounds)
    if r[0] == 'infeasible':
        return ('infeasible', None)
    if r[0] == 'unbounded':
        return ('unbounded', None)
    return ('bounded', -r[1])

def parse_desc(desc):
    if desc.startswith('V') and 'Σgap' in desc:
        return ('fan', int(desc[1]))
    if desc.startswith('Δ'):
        m = re.match(r'Δ\((\d+), (\d+), (\d+)\)', desc)
        return ('tri', tuple(int(x) for x in m.groups()))
    m = re.match(r'∠(\d)(\d)(\d)≤π−λ', desc)
    if m:
        return ('ang',) + tuple(int(x) for x in m.groups())
    m = re.match(r'r(\d)(\d)≥0', desc)
    if m:
        return ('rnn', int(m[1]), int(m[2]))
    m = re.match(r'r(\d)(\d)≤1', desc)
    if m:
        return ('rle', int(m[1]), int(m[2]))
    m = re.match(r'g(\d)(\d)≥0', desc)
    if m:
        return ('gnn', int(m[1]), int(m[2]))
    return ('other', desc)

PERMS = list(permutations(range(4)))

def apply_perm(tok, p):
    ty = tok[0]
    if ty == 'fan':
        return ('fan', p[tok[1]])
    if ty == 'tri':
        return ('tri', tuple(sorted(p[x] for x in tok[1])))
    if ty == 'ang':
        return ('ang', p[tok[1]], p[tok[2]], p[tok[3]])
    if ty in ('rnn', 'rle', 'gnn'):
        return (ty, p[tok[1]], tok[2])
    return tok

def canon(toks):
    best = None
    for p in PERMS:
        cand = tuple(sorted((apply_perm(t, p), w)
                            for t, w in toks))
        if best is None or cand < best:
            best = cand
    return best

def main():
    ks = tuple(int(x) for x in sys.argv[1:5]) or (3, 2, 2, 1)
    target = float(sys.argv[5]) if len(sys.argv) > 5 else 0.5
    max_skel = int(sys.argv[6]) if len(sys.argv) > 6 else 10**9
    VV = sen.build_VV(ks, n)
    sigvars, sig = sen.build_signatures(VV)
    t0 = time.time()
    total = kept = 0
    clusters = {}
    fails = []
    for sol, idxs, sigkey in sen.gen_cases(ks, n, VV, sigvars, sig):
        total += 1
        if total > max_skel:
            break
        rc.ORIG.clear()
        b = rc.build_case(sol, n, 'A')
        if b is None:
            continue
        ineqs, eqs = b
        ineqs = rc.substitute(eqs, ineqs)
        st = lp_min_delta_f(ineqs)
        if st[0] != 'bounded' or abs(st[1] - target) > 1e-9:
            continue
        kept += 1
        res = rc.lp_min_delta(ineqs)
        if res[0] != 'bounded':
            fails.append(('exact-disagree', idxs, st, res[:2]))
            continue
        cert = rc.extract_cert(ineqs, res[2])
        if cert is None:
            fails.append(('cert-none', idxs))
            continue
        W, combo = cert
        if (combo.get(DELTA, 0) != -1 or
                any(v < 0 for k, v in combo.items()
                    if k not in (CONST, DELTA))):
            fails.append(('bad-combo', idxs,
                          {str(k): str(v)
                           for k, v in combo.items()}))
            continue
        toks = []
        for cid, w in W.items():
            if w == 0:
                continue
            toks.append((parse_desc(rc.ORIG[cid][0]), str(w)))
        key = canon(toks)
        cl = clusters.setdefault(key, {'count': 0, 'reps': []})
        cl['count'] += 1
        if len(cl['reps']) < 2:
            cl['reps'].append({
                'idxs': idxs, 'sig': sigkey, 'toks': toks,
                'lo': str(combo.get(CONST, 0)),
                'combo': {str(k): str(v)
                          for k, v in combo.items()}})
        if kept % 50 == 0:
            print(f'  {kept} kept / {total} leaves, '
                  f'{len(clusters)} clusters, '
                  f'{time.time()-t0:.0f}s', flush=True)
    print(f'\nkept={kept} / leaves={total} '
          f'clusters={len(clusters)} fails={len(fails)} '
          f'time={time.time()-t0:.0f}s')
    for f in fails[:10]:
        print('  FAIL', f)
    ranked = sorted(clusters.items(),
                    key=lambda kv: -kv[1]['count'])
    out = []
    for i, (key, cl) in enumerate(ranked):
        ang = sum(1 for t, w in key if t[0] == 'ang')
        fan = sum(1 for t, w in key if t[0] == 'fan')
        tri = sum(1 for t, w in key if t[0] == 'tri')
        nn = sum(1 for t, w in key
                 if t[0] in ('rnn', 'gnn'))
        print(f'cluster {i}: count={cl["count"]} '
              f'fan={fan} tri={tri} ang={ang} nonneg={nn} '
              f'size={len(key)}')
        out.append({'rank': i, 'count': cl['count'],
                    'key': [[list(t), w] for t, w in key],
                    'reps': cl['reps']})
    fn = f'cert_clusters_ks{"".join(map(str, ks))}_{target}.json'
    with open(fn, 'w') as f:
        json.dump(out, f, indent=1)
    print(f'-> {fn}')

if __name__ == '__main__':
    main()
