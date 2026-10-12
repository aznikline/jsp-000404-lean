#!/usr/bin/env python3
"""Preflight tests for gen_r1_leaves.

Uses only small fake specs/fmap dicts -- never reads the real
r1_specs.json / r1_map.json / r1_trees.json snapshots.  Run:

    python3 tools/test_gen_r1_leaves_preflight.py
"""
import inspect
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import gen_r1_leaves as g

RESULTS = []


def check(name, cond, detail=""):
    RESULTS.append((name, bool(cond), detail))


# fake spec: one 's2' row (6 classes) + one 's1' row (3 classes)
SPEC = [[0, 's2'], [2, 's1']]
PROF, P = 'TX', 7
SK = g.speckey(PROF, SPEC)
ALL_KEYS = list(g.required_keys(SK, SPEC))
GOOD_RKEY = 'P6|s2@0,s1@2|H_L,L_0'


def full_fmap():
    return {fk: GOOD_RKEY for fk in ALL_KEYS}


# sanity: key shape and count (6 * 3 = 18, CANON2 outer / CANON1 inner)
check('required_keys count', len(ALL_KEYS) == 18, str(len(ALL_KEYS)))
check('required_keys order',
      ALL_KEYS[0] == SK + '|H_L,L_0' and
      ALL_KEYS[-1] == SK + '|M_IR,L_R',
      f'{ALL_KEYS[0]} .. {ALL_KEYS[-1]}')
check('required_keys all share speckey prefix',
      all(k.startswith(SK + '|') for k in ALL_KEYS))

# (d) preflight signature takes exactly (specs, fmap) -- no trees arg
sig = inspect.signature(g.preflight)
check('preflight signature is (specs, fmap)',
      list(sig.parameters) == ['specs', 'fmap'],
      str(sig))


def boom():
    raise AssertionError('load_trees must not be called by preflight')


_orig_load_trees = g.load_trees
g.load_trees = boom  # preflight must never touch the trees snapshot
try:
    # (c) fully-mapped spec is complete
    complete, missing = g.preflight([(PROF, P, SPEC)], full_fmap())
    check('fully-mapped spec complete',
          complete == [(PROF, P, SPEC)] and missing == {},
          f'complete={complete} missing={missing}')

    # (a) one missing key -> incomplete, key listed
    fm = full_fmap()
    victim = ALL_KEYS[7]
    del fm[victim]
    complete, missing = g.preflight([(PROF, P, SPEC)], fm)
    check('one missing key -> incomplete',
          complete == [] and missing.get(SK) == [victim],
          f'missing={missing}')

    # (b) NONUNSAT-valued key counts as missing
    fm = full_fmap()
    fm[ALL_KEYS[3]] = 'NONUNSAT:whatever'
    complete, missing = g.preflight([(PROF, P, SPEC)], fm)
    check('NONUNSAT value counts as missing',
          complete == [] and missing.get(SK) == [ALL_KEYS[3]],
          f'missing={missing}')

    # mixed batch: complete + incomplete specs coexist
    SPEC2 = [[1, 's1']]
    SK2 = g.speckey(PROF, SPEC2)
    KEYS2 = list(g.required_keys(SK2, SPEC2))
    check('s1-only spec has 3 keys', len(KEYS2) == 3, str(KEYS2))
    fm = full_fmap()
    fm.update({k: GOOD_RKEY for k in KEYS2[:-1]})  # last key absent
    complete, missing = g.preflight(
        [(PROF, P, SPEC), (PROF, P, SPEC2)], fm)
    check('mixed batch partitions correctly',
          complete == [(PROF, P, SPEC)] and
          missing.get(SK2) == [KEYS2[-1]],
          f'complete={complete} missing={missing}')
finally:
    g.load_trees = _orig_load_trees

# ---- summary ----
npass = sum(1 for _n, ok, _d in RESULTS if ok)
for name, ok, detail in RESULTS:
    print(f"{'PASS' if ok else 'FAIL'}  {name}"
          + ('' if ok else f'  [{detail}]'))
print(f"{npass}/{len(RESULTS)} checks passed")
sys.exit(0 if npass == len(RESULTS) else 1)
