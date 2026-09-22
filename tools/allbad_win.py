"""Winning-gadget analysis over allbad_dump.json records.

Rebuilds each recorded all-bad skeleton and computes the first
sufficient gadget in the enriched grammar (block/pure/strip).
Aggregates by pair pattern: for strips, where the fans sit, which
vertices carry charges/caps.
"""
import sys, json, itertools, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
import link_graph as lg
import eval_ext as ex
from allbad_dump import winning, N, S


def rebuild(rec):
    sol = []
    for vd in rec['vdata']:
        sol.append({'order': tuple(vd['order']),
                    'bits': {int(k): b for k, b in vd['bits'].items()},
                    'qs': tuple(vd['qs'])})
    return sol


def main():
    fn = sys.argv[1] if len(sys.argv) > 1 else 'allbad_dump.json'
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    recs = json.load(open(fn))
    bypat = collections.defaultdict(list)
    for r in recs:
        p = r['pairs'][0]
        bypat[(p['mode_i'], p['slot_i'], p['mode_j'], p['slot_j'])].append(r)
    out = {}
    for pat, rs in sorted(bypat.items()):
        tally = collections.Counter()
        samples = []
        for r in rs[:cap]:
            sol = rebuild(r)
            ctx = lg.Ctx(sol, N, S)
            kind, win = winning(ctx)
            key = [kind]
            if kind == 'strip':
                key += [tuple(sorted(win['fans'].items())),
                        tuple(tuple(e) for e in win['edges']),
                        win['pivot']]
            elif kind == 'block':
                key += [win['v']]
            elif kind == 'pure':
                key += [tuple(c[0] for c in win['caps'])]
            tally[str(key)] += 1
            if len(samples) < 3:
                samples.append({'idxs': r['idxs'], 'kind': kind,
                                'win': win})
        out[str(pat)] = {'n': len(rs), 'tally': dict(tally),
                         'samples': samples}
        print(f'{pat}: n={len(rs)}')
        for k, c in tally.most_common(12):
            print(f'    {c:5d}  {k}')
    with open('allbad_win.json', 'w') as f:
        json.dump(out, f, indent=1, default=str)
    print('wrote allbad_win.json')


if __name__ == '__main__':
    main()
