#!/usr/bin/env python3
"""Bounded exact eleven-point HIGH necessary-angle-model diagnostic.

The strict DBM implementation is copied from the audited nine-point exporter.
Bounds are half-integers plus a strict bit (packed as 4*bound-strict);
addition ORs strictness and every path retains its original-atom bitset.

55 upper chords, 165 ordered triangles, 0<=d<4; both endpoint absolute
angle differences are <3. Each middle angle supplies separation >=1 and
strict chord betweenness. There are no positive/floor/NoSat/deletion inputs.
No Lean source, certificate, cache, compilation or proof claim is generated.
An abstract feasible angular model is not a planar point counterexample.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import time
INF=10**9
ROOT=Path(__file__).resolve().parents[1]

class FeasibleDBM(Exception):
    def __init__(self, dbm):
        self.dbm=dbm
        super().__init__("complete consistent orientation")

def plus(a, b):
    return a + b + ((a & 1) & (b & 1))


class DBM:
    def __init__(self, size, costs=None, proofs=None):
        self.size = size
        self.costs = costs if costs is not None else [[0 if a == b else INF for b in range(size)] for a in range(size)]
        self.proofs = proofs if proofs is not None else [[0] * size for _ in range(size)]

    def copy(self):
        return DBM(self.size, [r[:] for r in self.costs], [r[:] for r in self.proofs])

    def immediate_cycle(self, edge):
        u, v, w, atom = edge
        back = self.costs[v][u]
        if back != INF and plus(back, w) < 0:
            return self.proofs[v][u] | (1 << atom)
        return None

    def add(self, edge):
        u, v, w, atom = edge
        costs, proofs, size = self.costs, self.proofs, self.size
        if costs[u][v] <= w:
            return None
        cycle = self.immediate_cycle(edge)
        if cycle is not None:
            return cycle
        # Distances to u and from v cannot improve through the new edge in a
        # consistent graph.  Capture them before the O(V^2) closure update.
        incoming = [(a, costs[a][u], proofs[a][u]) for a in range(size) if costs[a][u] != INF]
        outgoing = [(b, costs[v][b], proofs[v][b]) for b in range(size) if costs[v][b] != INF]
        bit = 1 << atom
        for a, ca, pa in incoming:
            aw = plus(ca, w)
            ap = pa | bit
            row, prow = costs[a], proofs[a]
            for b, cb, pb in outgoing:
                candidate = plus(aw, cb)
                if candidate < row[b]:
                    row[b] = candidate
                    prow[b] = ap | pb
        return None


class Search:
    def __init__(self, n, wall_seconds, max_nodes, ordering):
        self.n, self.wall_seconds, self.max_nodes = n, wall_seconds, max_nodes
        self.ordering = ordering
        self.chords = list(itertools.combinations(range(n), 2))
        self.variables = {e: i + 1 for i, e in enumerate(self.chords)}
        self.triples = list(itertools.combinations(range(n), 3))
        self.atoms, self.base, self.arms = [], [], []
        self.stats = {"nodes": 0, "leaves": 0, "max_depth": 0,
                      "forced_splits": 0, "branch_splits": 0,
                      "largest_cycle_core": 0, "closure_updates": 0,
                      "redundant_triangles_removed": 0, "terminal_states": 0}
        self.started = time.monotonic()
        for i, j in self.chords:
            v = self.variables[i, j]
            self.base.append(self.edge(v, 0, 0, f"hd{i}{j}a"))
            self.base.append(self.edge(0, v, 15, f"hd{i}{j}b"))
        for i, j, k in self.triples:
            x, y, z = self.variables[i, j], self.variables[i, k], self.variables[j, k]
            # Both endpoint absolute-difference caps hold in either triangle
            # arm.  Derive them once in ordinary Lean and add them up front;
            # they must not be delayed until that triangle's orientation split.
            for u, v, suffix in ((x, y, "xy"), (y, x, "yx"),
                                 (y, z, "yz"), (z, y, "zy")):
                self.base.append(self.edge(u, v, 11, f"hc{i}{j}{k}{suffix}"))
            arms = []
            for low, high in ((x, z), (z, x)):
                names = [f"htr{i}{j}{k}{s}" for s in "abcde"]
                # x_v-x_u bound: high->low -1, middle->low <0,
                # high->middle <0, low->middle <3, middle->high <3.
                arms.append([self.edge(high, low, -4, names[0]),
                             self.edge(y, low, -1, names[1]),
                             self.edge(high, y, -1, names[2])])
            self.arms.append(arms)

    def edge(self, u, v, weight, name):
        idx = len(self.atoms)
        self.atoms.append({"from": u, "to": v, "packed_bound": weight, "name": name})
        return u, v, weight, idx

    def check_budget(self):
        if self.stats["nodes"] >= self.max_nodes:
            raise TimeoutError("node budget exhausted")
        if time.monotonic() - self.started >= self.wall_seconds:
            raise TimeoutError("wall budget exhausted")

    def trial(self, dbm, edges):
        child = dbm.copy()
        for edge in edges:
            self.stats["closure_updates"] += 1
            cycle = child.add(edge)
            if cycle is not None:
                return None, cycle
        return child, None

    def leaf(self, core):
        self.stats["leaves"] += 1
        self.stats["largest_cycle_core"] = max(self.stats["largest_cycle_core"], core.bit_count())
        return {"core": core}

    def rank(self, dbm, idx):
        i, j, k = self.triples[idx]
        x, y, z = self.variables[i, j], self.variables[i, k], self.variables[j, k]
        if self.ordering == "span":
            return k - i, j - i, idx
        # Tight outer-chord difference intervals are the cheapest unit splits.
        width = plus(dbm.costs[x][z], dbm.costs[z][x])
        return width, k - i, j - i, idx

    def tree(self, dbm, pending, depth=0):
        self.check_budget()
        self.stats["nodes"] += 1
        self.stats["max_depth"] = max(self.stats["max_depth"], depth)
        # If the current closed DBM entails one whole arm, this triangle adds
        # no constraint or provenance.  Discard it without a Lean split: every
        # later negative-cycle proof uses only the already selected atoms.
        live = []
        for idx in pending:
            entailed = any(all(dbm.costs[u][v] <= weight for u, v, weight, _ in arm)
                          for arm in self.arms[idx])
            if entailed:
                self.stats["redundant_triangles_removed"] += 1
            else:
                live.append(idx)
        pending = tuple(live)
        if not pending:
            raise FeasibleDBM(dbm)
        # Cheap negative-cycle checks find forced triangle arms without copying
        # or computing closure for all candidate orientations.
        chosen = None
        arm_trials = None
        for idx in pending:
            quick = [next((cycle for e in arm if (cycle := dbm.immediate_cycle(e)) is not None), None)
                     for arm in self.arms[idx]]
            if any(c is not None for c in quick):
                chosen = idx
                arm_trials = [(None, cycle) if cycle is not None else self.trial(dbm, arm)
                              for arm, cycle in zip(self.arms[idx], quick)]
                self.stats["forced_splits"] += 1
                break
        if chosen is None:
            chosen = min(pending, key=lambda idx: self.rank(dbm, idx))
            arm_trials = [self.trial(dbm, arm) for arm in self.arms[chosen]]
            self.stats["branch_splits"] += 1
        remaining = tuple(idx for idx in pending if idx != chosen)
        if all(cycle is not None for _, cycle in arm_trials):
            self.stats["terminal_states"] += 1
        children = [self.leaf(cycle) if cycle is not None else self.tree(child, remaining, depth + 1)
                    for child, cycle in arm_trials]
        return {"triple": chosen, "children": children}

    def run(self):
        dbm = DBM(len(self.chords) + 1)
        for edge in self.base:
            assert dbm.add(edge) is None
        try:
            tree = self.tree(dbm, tuple(range(len(self.triples))))
            result = "complete_unsat_tree"
            reason = None
        except FeasibleDBM as exc:
            tree, result, reason = None, "abstract_necessary_model_sat", None
            self.feasible_dbm = exc.dbm
        except TimeoutError as exc:
            tree, result, reason = None, "budget_incomplete", str(exc)
        return tree, {"diagnostic_only_until_kernel_checked": True,
                      "points": self.n, "variables": len(self.chords) + 1,
                      "triples": len(self.triples), "result": result, "reason": reason,
                      "exact_arithmetic": "half-integer bound plus strict bit; no epsilon",
                      "normalized_range": "0 <= d < 4",
                      "normalized_endpoint_caps": "both endpoint absolute differences < 3",
                      "positive_row_assumptions": False,
                      "ordering": self.ordering,
                      "budget_seconds": self.wall_seconds, "budget_nodes": self.max_nodes,
                      "elapsed_seconds": round(time.monotonic() - self.started, 6),
                      **self.stats}


def exact_model(search, dbm):
    # All half-integral positive cycle sums are >=1/2; a common rational
    # epsilon below 1/(2V) satisfies every finite strict edge simultaneously.
    size=dbm.size
    epsilon=Fraction(1,8*(size+1))
    dist=[Fraction(0) for _ in range(size)]
    edges=[]
    for u in range(size):
        for v in range(size):
            w=dbm.costs[u][v]
            if w==INF:continue
            strict=w&1
            bound=Fraction(w+strict,4)-epsilon*strict
            edges.append((u,v,bound))
    for _ in range(size):
        changed=False
        for u,v,w in edges:
            if dist[v]>dist[u]+w:
                dist[v]=dist[u]+w;changed=True
        if not changed:break
    else:
        raise AssertionError("rational strict-bound witness relaxation failed")
    x=[v-dist[0] for v in dist]
    get=lambda i,j:x[search.variables[tuple(sorted((i,j)))]]
    checks={"nonnegative_lower_and_strict_upper":all(0<=get(i,j)<4 for i,j in search.chords),
            "all_165_full_triangle_conditions":all(
                (get(i,j)+1<=get(j,k) and get(i,j)<get(i,k)<get(j,k) and
                 get(i,k)-get(i,j)<3 and get(j,k)-get(i,k)<3) or
                (get(j,k)+1<=get(i,j) and get(j,k)<get(i,k)<get(i,j) and
                 get(i,k)-get(j,k)<3 and get(i,j)-get(i,k)<3)
                for i,j,k in search.triples)}
    assert all(checks.values()),checks
    return {"validated_exactly_with_Fraction":True,"checks":checks,
            "epsilon_for_witness_only":str(epsilon),
            "chords":{f"{i},{j}":str(get(i,j)) for i,j in search.chords},
            "actual_planar_realizability":"NOT_CHECKED"}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wall-seconds",type=float,default=50.)
    parser.add_argument("--max-nodes",type=int,default=200000)
    parser.add_argument("--ordering",choices=("span","tight"),default="tight")
    args=parser.parse_args()
    if not 0<args.wall_seconds<=50:parser.error("wall budget must lie in (0,50] to leave room below the 55s total limit")
    if not 0<args.max_nodes<=200000:parser.error("nodes must lie in (0,200000]")
    search=Search(11,args.wall_seconds,args.max_nodes,args.ordering)
    tree,report=search.run()
    report.update({"diagnostic_only":True,"no_Lean_certificate":True,
                   "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "provenance":"negative-cycle core retains the original atom bitset",
                   "chord_variables":len(search.chords),"zero_reference_vertices":1,
                   "kernel_verification":"NOT_RUN", "Lean_source_generated":False})
    if report["result"]=="abstract_necessary_model_sat":
        report["angular_witness"]=exact_model(search,search.feasible_dbm)
    report["elapsed_total_seconds"]=round(time.monotonic()-search.started,6)
    if tree is not None:
        report["tree_not_persisted"]=True
    (ROOT/"research/JSP404_ELEVEN_DBM_DIAGNOSTIC_20261005.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report),flush=True)
if __name__=="__main__":main()
