"""Stratified winning-gadget families over allbad_dump records.

For each pair pattern and a bounded sample, try gadget families in
order and report which hits bound >= 1:

  block  : inequality-only charge-cap (eval_ext.block_gadgets)
  pure   : pure cap
  strip  : fans+links grammar evaluated by eval_ext.eval_chain2,
           enumerated by increasing (|links|,|fans|) with early stop.

Reports the FIRST-hitting family + the gadget shape for strips.
"""
import sys, json, itertools, collections, time
sys.path.insert(0, '.')
from fractions import Fraction as F
import generic_enum as ge
import link_graph as lg
import eval_ext as ex
from allbad_dump import PROFILES, N, S


def rebuild(rec, look):
    sol = []
    for v, vd in enumerate(rec['vdata']):
        key = (tuple(vd['order']),
               tuple(sorted((int(k), b) for k, b in vd['bits'].items())),
               tuple(vd['qs']))
        sol.append(look[v][key])
    return sol


def staged(ctx, max_links=3):
    """Return (family, result) for first bound>=1 gadget."""
    r = lg.pure_gadget(ctx)
    if r is not None and r['bound'] >= 1:
        return 'pure', r
    bg = ex.block_gadgets(ctx)
    if bg is not None and bg[0] >= F(1):
        return 'block', {'v': bg[1]}
    fas = [{}]
    for v in range(S):
        for f in (1, -1):
            fas.append({v: f})
    fas2 = list(fas)
    for v1 in range(S):
        for v2 in range(v1 + 1, S):
            for f1 in (1, -1):
                for f2 in (1, -1):
                    fas2.append({v1: f1, v2: f2})
    for nl in range(0, max_links + 1):
        fansets = fas if nl >= 1 else fas2
        for h in range(S):
            outer = [v for v in range(S) if v != h]
            links1 = [(a, b, sg)
                      for a, b in itertools.combinations(outer, 2)
                      for sg in (1, -1)]
            linksets = [[]] if nl == 0 else \
                [list(p) for p in itertools.combinations(links1, nl)]
            for ed in linksets:
                for fa in fansets:
                    res = ex.eval_chain2(ctx, h, ed, fa)
                    if res is not None and res['bound'] >= 1:
                        return f'strip_L{nl}F{len(fa)}', res
    return 'none', None


def main():
    fn = sys.argv[1] if len(sys.argv) > 1 else 'allbad_dump.json'
    per = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    ks = (3, 3, 2, 2)
    VV = ge.build_VV(list(ks), N, S)
    look = [{(vv['order'], tuple(sorted(vv['bits'].items())), vv['qs']): vv
            for vv in VV[v]} for v in range(S)]
    recs = json.load(open(fn))
    bypat = collections.defaultdict(list)
    for r in recs:
        p = r['pairs'][0]
        bypat[(p['slot_i'], p['slot_j'])].append(r)
    t0 = time.time()
    for pat, rs in sorted(bypat.items()):
        tally = collections.Counter()
        shapes = collections.Counter()
        for r in rs[:per]:
            sol = rebuild(r, look)
            ctx = lg.Ctx(sol, N, S)
            fam, res = staged(ctx)
            tally[fam] += 1
            if res is not None and fam.startswith('strip'):
                shapes[(tuple(sorted(res['fans'].items())),
                        tuple(tuple(e) for e in res['edges']),
                        res['pivot'])] += 1
        print(f'{pat} (n={len(rs)}, sampled {min(per,len(rs))}): '
              f'{dict(tally)}  [{time.time()-t0:.0f}s]', flush=True)
        for k, c in shapes.most_common(8):
            print(f'      {c:4d} {k}')


if __name__ == '__main__':
    main()
