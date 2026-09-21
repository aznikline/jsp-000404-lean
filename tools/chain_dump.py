"""Unified chain representation for every mapped MUS core.

For each MUS core: rebuild restricted case, extract exact Farkas
certificate, then reconstruct the chain topology purely from the
equality weights — no LP solving beyond the certificate itself:

  * eq nodes (fans + triangles) with cert weight w_e
  * each node's signed r-support  {var: w_e * coeff}
  * adjacency: two eq-nodes share an r-var whose residual
    contributions cancel (sum = 0) -> telescoping edge
  * path = greedy ordering of the eq-node graph
  * charged = lower-bound ineqs (a_i<=0, no delta)
  * capped  = cap ineqs (a_i>=0, a_delta<=0)
  * free    = leftover nonnegative P terms

Emits per-instance record with profile deficits, vertex weights,
residual params, and selector features.  Goal: find a deterministic
profile+skeleton -> chain rule (DebtSelection candidate).

Usage: python3 chain_dump.py [s4|s5]
"""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
import residual_map as rm

def parse_ang(desc):
    """'∠102≤π−λ' -> (1,0,2); '∠024≥0' -> (0,2,4)."""
    s = desc.split('≤')[0].split('≥')[0][1:]
    return tuple(int(c) for c in s)

def parse_fan(desc):
    return int(desc[1])

def parse_tri(desc):
    s = desc.split('Σ')[0]
    s = s[s.index('(') + 1:s.index(')')]
    return tuple(int(c) for c in s.split(', '))

def chain_structure(E, W, DELTA, CONST):
    """Reconstruct chain topology from certificate weights."""
    eqs, ineqs = [], []
    for cid, w in W.items():
        desc, form, is_eq = E.orig(cid)
        supp = {k: w * v for k, v in form.items()
                if k is not DELTA and k is not CONST and v}
        if is_eq:
            kind = 'fan' if desc.startswith('V') else 'tri'
            eqs.append({'desc': desc, 'kind': kind, 'w': str(w),
                        'supp': supp,
                        'vtx': (parse_fan(desc) if kind == 'fan'
                                else parse_tri(desc))})
        else:
            ineqs.append({'desc': desc, 'w': str(w),
                          'form': form})

    # adjacency: shared r-var with cancelling signed contribution
    adj = {i: {} for i in range(len(eqs))}
    for i in range(len(eqs)):
        for j in range(i + 1, len(eqs)):
            shared = []
            for v, ci in eqs[i]['supp'].items():
                if v in eqs[j]['supp'] and ci + eqs[j]['supp'][v] == 0:
                    shared.append(str(v))
            if shared:
                adj[i][j] = adj[j][i] = sorted(shared)

    # greedy path order (fans are endpoints when degree 1);
    # visited set guards against cycles in the support graph
    fans = [i for i, e in enumerate(eqs) if e['kind'] == 'fan']
    path = []
    visited = set()
    start = fans[0] if fans else 0
    cur, prev = start, None
    while cur is not None and cur not in visited:
        path.append(cur)
        visited.add(cur)
        nxt = [j for j in adj[cur] if j != prev and
               j not in visited]
        prev, cur = cur, (nxt[0] if nxt else None)
    reachable = len(path) == len(eqs)

    # residual bookkeeping
    charged, capped, nn = [], [], []
    for it in ineqs:
        f = it['form']
        ad = f.get(DELTA, F(0))
        rp = {k: v for k, v in f.items()
              if k is not DELTA and k is not CONST}
        if rp and all(v <= 0 for v in rp.values()) and ad == 0:
            charged.append(it)
        elif rp and all(v >= 0 for v in rp.values()) and ad <= 0:
            capped.append(it)
        else:
            nn.append(it)
    return {'eqs': eqs, 'ineqs': ineqs,
            'adj': {str(i): {str(j): s for j, s in a.items()}
                    for i, a in adj.items()},
            'path': path, 'path_covers': reachable,
            'charged': [c['desc'] for c in charged],
            'capped': [c['desc'] for c in capped],
            'other_ineq': [c['desc'] for c in nn]}

def profile_info(ks, n):
    d = [(n - 1) - k for k in ks]
    W = sum(F(1, 2 ** x) for x in d)
    return {'ks': list(ks), 'deficits': d,
            'W': str(W), 'excess': str(W - 2)}

def record(E, sol, ks, n, core_descs, tag, idxs):
    out = rm.core_restricted_cert(E, sol, n, core_descs)
    if out is None or out[1] is None:
        return {'tag': tag, 'verdict': 'lp-fail'}
    lo, W = out
    res = rm.analyze(E, W, E.DELTA, E.CONST)
    ch = chain_structure(E, W, E.DELTA, E.CONST)
    d = [(n - 1) - k for k in ks]
    feats = {
        'eq_vertices': sorted({v for e in ch['eqs'] for v in
                               ([e['vtx']] if e['kind'] == 'fan'
                                else e['vtx'])}),
        'fan_endpoints': [e['vtx'] for e in ch['eqs']
                          if e['kind'] == 'fan'],
        'triangles': [e['vtx'] for e in ch['eqs']
                      if e['kind'] == 'tri'],
        'charged_angles': [parse_ang(c) for c in ch['charged']],
        'capped_angles': [parse_ang(c) for c in ch['capped']],
    }
    feats['d_at_fans'] = [d[v] for v in feats['fan_endpoints']]
    feats['d_at_tri_verts'] = sorted({d[v] for t in feats['triangles']
                                    for v in t})
    return {'tag': tag, 'idxs': idxs, 'profile': profile_info(ks, n),
            'qs': [list(sol[v]['qs']) for v in range(len(sol))],
            'mus': sorted(core_descs), 'residual': res,
            'chain': {k: v for k, v in ch.items()
                      if k not in ('eqs', 'adj', 'ineqs')},
            'eqs': [{**e, 'supp': {str(k): str(v)
                                   for k, v in e['supp'].items()}}
                    for e in ch['eqs']],
            'adj': ch['adj'], 'features': feats,
            'verdict': res.get('verdict')}

def run_s4():
    import skeleton_enum as sen
    E = rm.load_s4()
    n = 4
    data = json.load(open('mus_clusters_ks3221_0.5.json'))
    ks = (3, 2, 2, 1)
    VV = sen.build_VV(ks, n)
    out = []
    for cl in data:
        rep = cl['reps'][0]
        sol = [VV[v][rep['idxs'][v]] for v in range(4)]
        out.append(record(E, sol, ks, n, rep['descs'],
                          f"s4c{cl['rank']}", rep['idxs']))
    json.dump(out, open('chain_dump_s4.json', 'w'), indent=1)
    print(f"s4: {len(out)} records -> chain_dump_s4.json")

def run_s5():
    import generic_enum as ge
    E = rm.load_g()
    n, s = 5, 5
    detail = json.load(open('residual_map_s5.json'))
    vv_cache = {}
    out = []
    for rec in detail:
        fn = rec['file']
        if fn not in vv_cache:
            ks = json.load(open(fn))['ks']
            vv_cache[fn] = (ks, ge.build_VV(ks, n, s))
        ks, VV = vv_cache[fn]
        idxs = rec['idxs']
        sol = [VV[v][idxs[v]] for v in range(s)]
        out.append(record(E, sol, ks, n, rec['mus'],
                          f"{fn}:{rec['idxs']}", idxs))
    json.dump(out, open('chain_dump_s5.json', 'w'), indent=1)
    print(f"s5: {len(out)} records -> chain_dump_s5.json")

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 's5':
        run_s5()
    else:
        run_s4()
