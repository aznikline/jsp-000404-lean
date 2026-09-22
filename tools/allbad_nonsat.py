"""Non-saturated-vertex angle structure in all-bad skeletons.

For each record: at each non-saturated vertex x, list its three angle
expressions (comp?, arc gaps, q_arc).  A comp arc with small q_arc is
chargeable (gain 1-q_arc > 0); a direct arc with q_arc >= n is a pure
cap.  Correlate with the bad-pair slot pattern and which vertex the
conjectured strip would use.
"""
import sys, json, itertools, collections
sys.path.insert(0, '.')

N = S = 4


def ang_of(vd):
    """angles at a vertex from vdata: list (a,b,comp,arc,q)."""
    order = vd['order']
    bits = vd['bits']
    qs = vd['qs']
    pos = {d: t for t, d in enumerate(order)}
    out = []
    for a, b in itertools.combinations(order, 2):
        lo, hi = sorted((pos[a], pos[b]))
        arc = tuple(range(lo, hi))
        q = sum(qs[g] for g in arc)
        comp = bits[str(a)] != bits[str(b)] \
            if isinstance(next(iter(bits)), str) else bits[a] != bits[b]
        out.append((a, b, comp, arc, q))
    return out, pos


def main():
    fn = sys.argv[1] if len(sys.argv) > 1 else 'allbad_dump.json'
    recs = json.load(open(fn))
    # per non-sat vertex: does it have charge (comp,q=0) or pure(dir,q>=n)?
    tally = collections.Counter()
    # joint structure: (#vertices with pure, #with charge)
    joint = collections.Counter()
    bypat = collections.defaultdict(collections.Counter)
    for r in recs:
        sat = set(r['sat'])
        nonsat = [v for v in range(S) if v not in sat]
        feats = []
        for v in nonsat:
            ang, pos = ang_of(r['vdata'][v])
            has_charge = any(c and q == 0 for _, _, c, _, q in ang)
            has_pure = any((not c) and q >= N for _, _, c, _, q in ang)
            # weaker charge: comp arc with q_arc <= 1
            has_charge1 = any(c and q <= 1 for _, _, c, _, q in ang)
            feats.append((v, has_pure, has_charge, has_charge1))
        n_pure = sum(f[1] for f in feats)
        n_charge = sum(f[2] for f in feats)
        n_charge1 = sum(f[3] for f in feats)
        joint[(n_pure, n_charge, n_charge1)] += 1
        p = r['pairs'][0]
        bypat[(p['slot_i'], p['slot_j'])][
            (n_pure > 0, n_charge > 0)] += 1
        if n_pure == 0 and n_charge == 0:
            tally['NOLOCAL'] += 1
            if tally['NOLOCAL'] <= 10:
                print('NOLOCAL', r['idxs'], r['pairs'],
                      [r['vdata'][v] for v in nonsat])
    print('records:', len(recs))
    print('(n_pure, n_charge, n_charge_q<=1) joint:', dict(joint))
    print('by slot pattern (has_pure, has_charge):')
    for k in sorted(bypat):
        print('   ', k, dict(bypat[k]))


if __name__ == '__main__':
    main()
