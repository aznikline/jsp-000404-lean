"""Single-profile adversarial scan driver (for parallel sharding).

Usage: gc_one.py n s d0 d1 ... d{s-1} [leaf_cap] [max_sigs] [per_sig]
"""
import sys, json, time
sys.path.insert(0, '.')
import generic_cegis as gc

def main():
    n = int(sys.argv[1]); s = int(sys.argv[2])
    d = [int(x) for x in sys.argv[3:3 + s]]
    leaf_cap = int(sys.argv[3 + s]) if len(sys.argv) > 3 + s else 80000
    max_sigs = int(sys.argv[4 + s]) if len(sys.argv) > 4 + s else 100000
    per_sig = int(sys.argv[5 + s]) if len(sys.argv) > 5 + s else 150
    ks = [n - 1 - x for x in d]
    W = sum(2.0 ** (-x) for x in d)
    t0 = time.time()
    res = gc.scan_profile(ks, n, s, 0.5, leaf_cap, max_sigs,
                          per_sig=per_sig)
    md = res['min_delta']
    md_rep = ('INFEASIBLE_LT_1' if md is None or md >= 1 - 1e-9
              else md)
    cex = res['cex'] is not None
    out = dict(deficit=d, ks=ks, W=W, cex=cex,
               cex_witness=res['cex'], min_delta=md,
               leaves=res['leaves'], sigs=res['sigs'],
               boundary=res['boundary'])
    tag = 'COUNTEREXAMPLE' if cex else 'killed'
    print(f'd={tuple(d)} k={tuple(ks)} W={W:.3f}: {tag} '
          f'delta_min={md_rep} leaves={res["leaves"]} '
          f'sigs={res["sigs"]} boundary={len(res["boundary"])} '
          f'({time.time()-t0:.0f}s)')
    fn = 'gc_' + '_'.join(map(str, d)) + f'_n{n}s{s}.json'
    with open(fn, 'w') as f:
        json.dump(out, f, indent=1, default=str)

if __name__ == '__main__':
    main()
