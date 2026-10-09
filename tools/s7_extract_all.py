"""Full extraction: cores + best order + pure-linear trees, 540 combos."""
import json, os, sys, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s7_extract_trees import *

OUT = os.path.join(HERE, 's7_leaf_trees_lin.json')
BAD = ('FAIL', 'OVER', 'NEEDS_SPLIT', 'SAT', 'UNKNOWN')
out = {}
if os.path.exists(OUT):
    out = json.load(open(OUT))


def tree_ok(tr):
    """Completed tree: list, no bad status at any depth."""
    if not isinstance(tr, list) or not tr:
        return False
    if tr[0] == 'term':
        return isinstance(tr[1], list)
    if tr[0] == 'node':
        return all(tree_ok(k) for k in tr[3])
    return tr[0] not in BAD


jobs = []
for cert, (P, spec) in CERTS.items():
    kinds = [k for _, k in spec]
    for combo in itertools.product(
            *[CASES2 if k == 's2' else CANON1_ORDER for k in kinds]):
        key = ','.join(combo)
        if cert in out and key in out[cert] and tree_ok(out[cert][key]):
            continue
        jobs.append((cert, P, spec, combo, key))

print(f'{len(jobs)} combos to extract', flush=True)
t0 = time.time()
for idx, (cert, P, spec, combo, key) in enumerate(jobs):
    t1 = time.time()
    st, core = leaf_core(P, spec, combo)
    if st != 'UNSAT':
        print(f'!!! {st}', cert, key, flush=True)
        out.setdefault(cert, {})[key] = st
        continue
    bo = best_order(P, spec, combo, core)
    tree = build_tree(P, spec, combo, bo[2])
    n = count_nodes(tree)
    out.setdefault(cert, {})[key] = tree
    print(f'{idx+1}/{len(jobs)} {cert} {key} core={len(core)} '
          f'mode={bo[1]} nodes={n} terms={count_terms(tree)} '
          f'{time.time()-t1:.0f}s cum={time.time()-t0:.0f}s', flush=True)
    if (idx + 1) % 25 == 0:
        json.dump(out, open(OUT, 'w'))
        print('  checkpoint', flush=True)
json.dump(out, open(OUT, 'w'))
print('DONE', time.time() - t0, flush=True)
