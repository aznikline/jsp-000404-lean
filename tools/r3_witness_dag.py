#!/usr/bin/env python3
"""Finite combinatorial enumeration of *canonical-witness* ShortWitness
DAG classes for the five-point R=3 profile.

Profile (SatChart Fin 4, anchor v defect 1):
    P,Q,R : rowDefect = 2     ("low" rows)
    H     : rowDefect >= 3    ("high" row)

Vertices {P,Q,R,H}.  A directed labeled edge X -F-> Y means: row X's
FIRST end gap is short and its head chord is the chord X->Y
(`short_first_gap_gives_lower`).  X -L-> Y is the mirrored last-gap
statement (`short_last_gap_gives_higher`).  Canonical witnesses are
functional: each row has at most one F-target and at most one L-target.

Consequences proved in the Lean development, encoded mechanically:

  * Every ShortWitness strictly lowers psi
    (`shortWitness_projection_lt`): the digraph must be acyclic;
    equivalently a linear order psi with psi target < psi source on
    every edge exists (`shortWitness_no_cycle`).
  * F-edge X->Y  => theta Y < theta X.
    L-edge X->Y  => theta X < theta Y.
    The theta constraints (a strict relation, not necessarily an order
    on all pairs) must themselves be acyclic.
  * A low row with an outgoing edge has a short end; a low row with no
    outgoing edge has both end gaps >= lam ("END_BIG sink").
  * `exists_short_end_of_three_defect_two`: not all three low rows sink.
    Strengthened empirically (r3_sink_tests.py, n=3..6, 0 SAT leaves):
    at most ONE low row is END_BIG -- encode as: <=1 low sink.
  * `five_point_receiver_indegree_le_one`: indegree(H) <= 1.
  * `defect_two_row_not_receive_both`: incoming labels at a low receiver
    are uniform (all F or all L).
  * `psi_min_row_ends_big`: the psi-min vertex is a sink.  Every finite
    DAG has a sink; the proof branches on whether psi-min is H or low.
    If psi-min is a low row it is a Type II sink whose three chord
    directions sit in a window of width <= pi - n*lam
    (`row_span_le_delta_of_defect_two_ends`).
  * `first_witness_of_min_defect_two_high` /
    `last_witness_of_max_defect_two_high`: an F-edge of the theta-min
    low row (resp. L-edge of the theta-max low row) lands on a
    defect>=3 vertex, i.e. H.  Implied by theta consistency alone; kept
    as an audit check.
  * Type split (`rowDefect_eq_two_type`): defect-2 = Type I (rowBig=1)
    or Type II (rowBig=2).
      - sink => Type II.
      - Type II emits at most one side (two short ends would force its
        big gaps into adjacent interior positions {1,2}, excluded by
        `five_point_no_adjacent_big`).
      - `type_I_first_receiver_is_first_short` /
        `type_I_last_receiver_is_last_short`: a Type I receiver of an
        F-edge emits an F-edge; of an L-edge emits an L-edge.
      - `type_II_first_receiver_trichotomy` /
        `type_II_last_receiver_trichotomy`: a Type II receiver either
        emits an edge (either side) or is a signatured END_BIG sink:
            SIG_A (received F): floor(first/lam)=1, floor(last/lam)=n-1
            SIG_B (received L): floor(first/lam)=n-1, floor(last/lam)=1

Classes are canonicalised under the S_3 relabelling of {P,Q,R}.
theta/psi orders are NOT class data -- each class additionally records
one consistent (theta,psi) sample pair for auditability.

Outputs: R3_DAG_CLASSES.json, R3_DAG_REPORT.md.
Discovery/audit tool only -- not the Lean proof.
"""

from itertools import permutations, product, combinations
import json
import sys

LOW = ('P', 'Q', 'R')
H = 'H'
V = LOW + (H,)

LOW_PERMS = list(permutations(LOW))


def is_acyclic(rel):
    """rel: set of ordered pairs (a,b) meaning a<b.  Strict-order
    acyclicity check on 4 vertices."""
    reach = {v: set() for v in V}
    for a, b in rel:
        reach[a].add(b)
    # transitive closure
    for _ in range(4):
        for a in V:
            reach[a] |= {c for b in list(reach[a]) for c in reach[b]}
    return all(v not in reach[v] for v in V)


def theta_relation(edges):
    """Strict theta constraints: F x->y gives theta_y < theta_x;
    L x->y gives theta_x < theta_y."""
    rel = set()
    for (x, y), l in edges.items():
        if l == 'F':
            rel.add((y, x))      # y < x
        else:
            rel.add((x, y))      # x < y
    return rel


def theta_min_low(edges):
    """Low vertices that can be theta-minimal among lows under some
    consistent theta order.  Returns None if inconsistent."""
    rel = theta_relation(edges)
    if not is_acyclic(rel):
        return None
    reach = {v: set() for v in V}
    for a, b in rel:
        reach[a].add(b)
    for _ in range(4):
        for a in V:
            reach[a] |= {c for b in list(reach[a]) for c in reach[b]}
    # v can be theta-min low iff no other low vertex is forced below it
    return [v for v in LOW
            if not any(u in reach[v] for u in LOW if u != v)]


def sample_orders(edges):
    """One concrete (theta, psi) order pair consistent with the edges,
    for audit.  Returns (theta_order_low_first, psi_order_low_first)
    or None."""
    trel = theta_relation(edges)
    prel = {(y, x) for (x, y) in edges}   # psi_y < psi_x
    for tp in permutations(V):
        tr = {v: i for i, v in enumerate(tp)}
        if all(tr[a] < tr[b] for a, b in trel):
            for pp in permutations(V):
                prr = {v: i for i, v in enumerate(pp)}
                if all(prr[a] < prr[b] for a, b in prel):
                    return list(tp), list(pp)
    return None


def canon(edges, types):
    """Canonical key under S_3 relabelling of the three low rows."""
    best = None
    for sigma in LOW_PERMS:
        mp = dict(zip(LOW, sigma))
        mp[H] = H
        es = tuple(sorted((mp[a], mp[b], l) for (a, b), l in edges.items()))
        ty = tuple(types[mp[v]] for v in LOW)
        key = (es, ty)
        if best is None or key < best:
            best = key
    return best


def valid(edges, types):
    """Mechanical DAG-level constraints.  Returns derived dict or None."""
    if not edges:
        return None
    if not is_acyclic({(b, a) for (a, b) in edges}):
        return None                       # digraph acyclic (psi descent)
    if not is_acyclic(theta_relation(edges)):
        return None                       # theta consistency
    out_e = {v: [] for v in V}
    in_e = {v: [] for v in V}
    for (a, b), l in edges.items():
        out_e[a].append((b, l))
        in_e[b].append((a, l))
    if len(in_e[H]) > 1:
        return None                       # indegree(H) <= 1
    sinks = [v for v in LOW if not out_e[v]]
    if len(sinks) >= 2:
        return None                       # two END_BIG defect-2 rows
                                          # impossible (r3_sink_tests:
                                          # 0 SAT leaves, n=3..6)
    for v in LOW:
        labs = {l for _, l in in_e[v]}
        if len(labs) > 1:
            return None                   # not_receive_both
        if not out_e[v] and types[v] != 'II':
            return None                   # sink => Type II
        if types[v] == 'II':
            if len({l for _, l in out_e[v]}) > 1:
                return None               # Type II one side only
        if in_e[v]:
            lab = in_e[v][0][1]
            outs = {l for _, l in out_e[v]}
            if types[v] == 'I' and lab not in outs:
                return None               # Type I propagates same side
    return derive(edges, types)


def derive(edges, types):
    out_e = {v: [] for v in V}
    in_e = {v: [] for v in V}
    for (a, b), l in edges.items():
        out_e[a].append((b, l))
        in_e[b].append((a, l))
    sinks = [v for v in V if not out_e[v]]
    low_sinks = [v for v in LOW if not out_e[v]]
    sigs = {}
    for v in LOW:
        if in_e[v] and not out_e[v]:
            sigs[v] = 'SIG_A' if in_e[v][0][1] == 'F' else 'SIG_B'
    # psi-min can be any digraph sink
    psi_min_opts = sinks
    # theta extremal facts: F-edge from a possible theta-min low row must
    # land on H; symmetric for L.
    ext_notes = []
    tmins = theta_min_low(edges)
    if tmins is not None:
        for v in tmins:
            for b, l in out_e[v]:
                if l == 'F' and b != H:
                    ext_notes.append(
                        f'VIOLATION? {v} F->{b} while theta-min-able')
    return dict(out_e=out_e, in_e=in_e, sinks=low_sinks,
                all_sinks=sinks, sigs=sigs, psi_min_opts=psi_min_opts,
                h_indeg=len(in_e[H]), theta_min_low_opts=tmins)


def family(edges, types, d):
    parts = []
    parts.append('IND1' if d['h_indeg'] == 1 else 'IND0')
    parts.append('SINK' + ''.join(sorted(d['sinks']))
                 if d['sinks'] else 'SINK0')
    if H in d['all_sinks']:
        parts.append('HSINK')
    ll = sorted((a, b, l) for (a, b), l in edges.items()
                if a in LOW and b in LOW)
    parts.append('LL:' + ','.join(f'{a}{l}{b}' for a, b, l in ll)
                 if ll else 'NO_LL')
    lh = sorted((a, l) for (a, b), l in edges.items()
                if a in LOW and b == H)
    if lh:
        parts.append('LH:' + ','.join(f'{a}{l}' for a, l in lh))
    hl = sorted((b, l) for (a, b), l in edges.items()
                if a == H and b in LOW)
    if hl:
        parts.append('HL:' + ','.join(f'{b}{l}' for b, l in hl))
    parts.append('T' + ''.join(types[v] for v in LOW))
    if d['sigs']:
        parts.append('SIG:' + ','.join(
            f'{v}{s}' for v, s in sorted(d['sigs'].items())))
    return '|'.join(parts)


def main():
    seen = {}
    total_raw = 0
    # per-source functional choices: (F-target, L-target) in {None}+V\{x}
    src_opts = {x: [(f, l) for f in [None] + [y for y in V if y != x]
                    for l in [None] + [y for y in V if y != x]]
                for x in V}
    for pick in product(*[src_opts[x] for x in V]):
        edges = {}
        for x, (f, l) in zip(V, pick):
            if f is not None:
                edges[(x, f)] = 'F'
            if l is not None:
                edges[(x, l)] = 'L'
        if not edges:
            continue
        if sum(1 for (a, b) in edges if b == H) > 1:
            continue
        low_sinks = [v for v in LOW
                     if not any(a == v for a, _ in edges)]
        if len(low_sinks) >= 2:
            continue   # two defect-2 END_BIG rows impossible
                       # (r3_sink_tests.py: 0 SAT leaves, n=3..6)
        if not is_acyclic({(b, a) for (a, b) in edges}):
            continue
        if not is_acyclic(theta_relation(edges)):
            continue
        inlab = {v: set() for v in LOW}
        for (a, b), l in edges.items():
            if b in LOW:
                inlab[b].add(l)
        if any(len(s) > 1 for s in inlab.values()):
            continue
        for tcombo in product(['I', 'II'], repeat=3):
            types = dict(zip(LOW, tcombo))
            if any(types[v] != 'II' for v in low_sinks):
                continue
            ok = True
            for v in LOW:
                outs = {l for (a, _), l in edges.items() if a == v}
                if types[v] == 'II' and len(outs) > 1:
                    ok = False
                    break
                if inlab[v]:
                    lab = next(iter(inlab[v]))
                    if types[v] == 'I' and lab not in outs:
                        ok = False
                        break
            if not ok:
                continue
            total_raw += 1
            key = canon(edges, types)
            seen[key] = seen.get(key, 0) + 1

    classes = []
    for i, key in enumerate(sorted(seen)):
        es, ty = key
        edges = {(a, b): l for a, b, l in es}
        types = dict(zip(LOW, ty))
        d = derive(edges, types)
        th, ps = sample_orders(edges)
        classes.append(dict(
            id=f'R3C{i:03d}',
            edges=[f'{a}-[{l}]->{b}' for a, b, l in es],
            sides={f'{a}->{b}': l for a, b, l in es},
            types=types,
            sinks=d['sinks'],
            sink_signatures=d['sigs'],
            h_indegree=d['h_indeg'],
            all_sink_vertices=d['all_sinks'],
            psi_min_candidates=d['psi_min_opts'],
            theta_min_low_candidates=d['theta_min_low_opts'],
            sample_theta_order=th,
            sample_psi_order=ps,
            instances=seen[key],
            family=family(edges, types, d)))

    with open('R3_DAG_CLASSES.json', 'w') as f:
        json.dump(classes, f, indent=1)

    families = {}
    for c in classes:
        families.setdefault(c['family'], []).append(c['id'])
    agg0 = sum(1 for c in classes if c['h_indegree'] == 0)
    agg1 = sum(1 for c in classes if c['h_indegree'] == 1)

    rep = ['# R3 ShortWitness DAG classes\n',
           f'Canonical classes (mod S3): {len(classes)}',
           f'- indegree(H)=0: {agg0}',
           f'- indegree(H)=1: {agg1}',
           f'- distinct families: {len(families)}\n',
           '## Families\n']
    for fam, ids in sorted(families.items()):
        rep.append(f'- `{fam}` : {len(ids)} class(es)')
    rep.append('\n## Classes\n')
    for c in classes:
        rep.append(f"### {c['id']}")
        rep.append(f"ID={c['id']}")
        rep.append(f"EDGES={c['edges']}")
        rep.append(f"SIDES={c['sides']}")
        rep.append(f"TYPES={c['types']}")
        rep.append(f"SINKS={c['sinks']}")
        rep.append(f"SINK_SIGNATURES={c['sink_signatures']}")
        rep.append(f"H_INDEGREE={c['h_indegree']}")
        rep.append(f"ALL_SINK_VERTICES={c['all_sink_vertices']}")
        rep.append(f"PSI_MIN_CANDIDATES={c['psi_min_candidates']}")
        rep.append(f"THETA_MIN_LOW_CANDIDATES="
                   f"{c['theta_min_low_candidates']}")
        rep.append(f"SAMPLE_THETA_ORDER={c['sample_theta_order']}")
        rep.append(f"SAMPLE_PSI_ORDER={c['sample_psi_order']}")
        rep.append(f"INSTANCES={c['instances']}")
        rep.append(f"FAMILY={c['family']}")
        rep.append('')
    with open('R3_DAG_REPORT.md', 'w') as f:
        f.write('\n'.join(rep))
    print(f'raw instances={total_raw} canonical classes={len(classes)} '
          f'(indeg0={agg0} indeg1={agg1}) families={len(families)}')


if __name__ == '__main__':
    sys.exit(main())
