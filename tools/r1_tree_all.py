#!/usr/bin/env python3
"""Batch tree extraction for R1 terminal specs (canon-class method,
core-subproblem dedupe).

For each unique minimal spec in tools/r1_specs.json:
  - enumerate canon class-combos (6 s2-classes x 3 s1-classes per row)
  - leaf_core UNSAT check per combo
  - reduce to the CORE-ROW sub-spec + sub-combo; cache trees by the
    reduced problem (shared across specs and combos)
  - save:  tools/r1_trees.json   reduced-key -> tree
           tools/r1_map.json     '<speckey>|<combo>' -> reduced-key
           tools/r1_trees.log
"""
import sys, os, json, time, itertools, re


def dump(obj, path):
    tmp = path + '.tmp'
    json.dump(obj, open(tmp, 'w'))
    os.replace(tmp, path)

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from s7_extract_trees import (leaf_env, leaf_core, build_tree,
                              count_nodes, CASES2)
from s7_canon import CANON1_ORDER

PROFILES = {'T1': 6, 'T2': 6, 'T3': 7, 'T4': 8, 'T5': 9, 'T6': 10}
TREES_OUT = os.path.join(HERE, 'r1_trees.json')
MAP_OUT = os.path.join(HERE, 'r1_map.json')
LOG = os.path.join(HERE, 'r1_trees.log')
BUDGET = 2_000_000

ROWRE = re.compile(r'[uE](\d+)')


def speckey(prof, spec):
    return (prof + '|' + ','.join(f'{k}@{r}' for r, k in spec))


def core_rows(core):
    return sorted({int(m.group(1)) for n in core
                   for m in [ROWRE.match(n)] if m})


def tree_for(P, spec, combo):
    """Build a tree for (spec, combo); returns (status, tree, nodes)."""
    st, core = leaf_core(P, spec, combo)
    if st != 'UNSAT':
        return st, None, 0
    ornames = sorted(n for n in core if n.startswith('tr')
                     or n.startswith('E'))
    ornames.sort(key=lambda n: (not n.startswith('tr'), n))
    tr = build_tree(P, spec, combo, ornames, budget_nodes=BUDGET)
    return tr[0], tr, count_nodes(tr)


def main():
    only = set(sys.argv[1:])
    specs = json.load(open(os.path.join(HERE, 'r1_specs.json')))
    trees, fmap = {}, {}
    if os.path.exists(TREES_OUT):
        trees = json.load(open(TREES_OUT))
    if os.path.exists(MAP_OUT):
        fmap = json.load(open(MAP_OUT))
    log = open(LOG, 'a')

    for prof, profspecs in specs.items():
        if only and prof not in only:
            continue
        P = PROFILES[prof]
        uniq = sorted({tuple(tuple(x) for x in v)
                       for v in profspecs.values() if v})
        for spec_t in uniq:
            spec = [list(x) for x in spec_t]
            sk = speckey(prof, spec)
            per_row = [CASES2 if k == 's2' else CANON1_ORDER
                       for _, k in spec]
            combos = list(itertools.product(*per_row))
            t0 = time.time()
            n_new = n_cached = n_nodes = 0
            for combo in combos:
                ck = sk + '|' + ','.join(combo)
                if ck in fmap:
                    n_cached += 1
                    continue
                st, core = leaf_core(P, spec, combo)
                if st != 'UNSAT':
                    fmap[ck] = 'NONUNSAT:' + st
                    continue
                rows = core_rows(core)
                rspec = [[r, k] for r, k in spec if r in rows]
                rcombo = [cls for (r, _), cls in zip(spec, combo)
                          if r in rows]
                rkey = (f'P{P}|'
                        + ','.join(f'{k}@{r}' for r, k in rspec)
                        + '|' + ','.join(rcombo))
                fmap[ck] = rkey
                if rkey in trees:
                    continue
                rst, tr, nn = tree_for(P, rspec, rcombo)
                if tr is not None:
                    trees[rkey] = tr
                    n_nodes += nn
                    n_new += 1
                else:
                    trees[rkey] = ['NONUNSAT', rst]
                    fmap[ck] = 'NONUNSAT:' + rst
                if n_new % 30 == 0:
                    dump(trees, TREES_OUT)
                    dump(fmap, MAP_OUT)
            dump(trees, TREES_OUT)
            dump(fmap, MAP_OUT)
            msg = (f'{sk}: {len(combos)} combos newtrees+{n_new} '
                   f'nodes+{n_nodes} ({time.time()-t0:.0f}s)')
            print(msg, flush=True)
            log.write(msg + '\n'); log.flush()
    dump(trees, TREES_OUT)
    dump(fmap, MAP_OUT)
    print('done', flush=True)


if __name__ == '__main__':
    main()
