"""Full extraction: cores + best order + trees for all 540 canonical combos."""
import json, os, sys, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from s7_extract_trees import *

OUT = os.path.join(HERE, 's7_leaf_trees.json')
out = {}
if os.path.exists(OUT):
    out = json.load(open(OUT))

jobs = []
for cert, (P, spec) in CERTS.items():
    kinds = [k for _, k in spec]
    for combo in itertools.product(
            *[CASES2N if k == 's2' else CASES1N for k in kinds]):
        key = ','.join(combo)
        if cert in out and key in out[cert] and out[cert][key][0] != 'FAIL':
            continue
        jobs.append((cert, P, spec, combo, key))

print(f'{len(jobs)} combos to extract', flush=True)
t0 = time.time()
for idx, (cert, P, spec, combo, key) in enumerate(jobs):
    t1 = time.time()
    core = leaf_core(P, spec, combo)
    if core == 'SAT':
        print('!!! SAT', cert, key, flush=True)
        out.setdefault(cert, {})[key] = 'SAT'
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
