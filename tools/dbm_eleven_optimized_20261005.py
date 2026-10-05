#!/usr/bin/env python3
"""Bounded, exact eleven-point necessary-angle-model diagnostic.

The frozen diagnostic supplies the complete original atom set.  Only its
execution is changed: native exact closure with atom-bitset provenance,
in-place forced saturation, and memoization of completed UNSAT states.
No mathematical constraint is removed or weakened; no Lean source is emitted.
"""
from __future__ import annotations

import argparse
import ctypes as C
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

import dbm_eleven_diagnostic_20261005 as audited

ROOT = Path(__file__).resolve().parents[1]
SIZE, BLOCKS = 56, 28
INF = audited.INF

NATIVE_SOURCE = r"""
#include <stdint.h>
#include <string.h>
#define N 56
#define B 28
#define INF 1000000000
typedef struct {
  int32_t costs[N*N];
  uint64_t proofs[N*N*B];
} DBM;
static inline int plus(int a,int b) { return a+b+((a&1)&(b&1)); }
static inline uint64_t *proof(DBM *d,int a,int b) {
  return d->proofs+(a*N+b)*B;
}
int immediate(DBM *d,int u,int v,int w,int atom,uint64_t *core) {
  int back=d->costs[v*N+u];
  if(back==INF || plus(back,w)>=0) return 0;
  memcpy(core,proof(d,v,u),B*sizeof(uint64_t));
  core[atom/64]|=((uint64_t)1)<<(atom%64);
  return 1;
}
int add(DBM *d,int u,int v,int w,int atom,uint64_t *core) {
  if(d->costs[u*N+v]<=w) return 0;
  if(immediate(d,u,v,w,atom,core)) return 1;
  int inc[N],out[N];
  uint64_t ip[N*B],op[N*B];
  for(int a=0;a<N;a++) {
    inc[a]=d->costs[a*N+u]; out[a]=d->costs[v*N+a];
    memcpy(ip+a*B,proof(d,a,u),B*sizeof(uint64_t));
    memcpy(op+a*B,proof(d,v,a),B*sizeof(uint64_t));
  }
  for(int a=0;a<N;a++) {
    if(inc[a]==INF) continue;
    int aw=plus(inc[a],w);
    for(int b=0;b<N;b++) {
      if(out[b]==INF) continue;
      int candidate=plus(aw,out[b]);
      if(candidate>=d->costs[a*N+b]) continue;
      d->costs[a*N+b]=candidate;
      uint64_t *p=proof(d,a,b);
      for(int k=0;k<B;k++) p[k]=ip[a*B+k]|op[b*B+k];
      p[atom/64]|=((uint64_t)1)<<(atom%64);
    }
  }
  return 0;
}
/* Entire arms remain present.  Test entailment or single-edge refutation. */
int scan(DBM *d,int *pending,int length,int *xs,int *ys,int *zs,
         int *newlength,int *mask,int *removed) {
  int chosen=-1, chosenmask=0, lengthout=0, discarded=0;
  for(int p=0;p<length;p++) {
    int t=pending[p],x=xs[t],y=ys[t],z=zs[t];
    int32_t *c=d->costs;
    int e0=c[z*N+x]<=-4 && c[y*N+x]<=-1 && c[z*N+y]<=-1;
    int e1=c[x*N+z]<=-4 && c[y*N+z]<=-1 && c[x*N+y]<=-1;
    if(e0 || e1) { discarded++; continue; }
    pending[lengthout++]=t;
    int q0=c[x*N+z]<4 || c[x*N+y]<=0 || c[y*N+z]<=0;
    int q1=c[z*N+x]<4 || c[z*N+y]<=0 || c[y*N+x]<=0;
    int qmask=q0+2*q1;
    if(qmask && (chosen<0 || qmask==3)) {
      chosen=t; chosenmask=qmask;
    }
  }
  *newlength=lengthout; *mask=chosenmask; *removed=discarded;
  return chosen;
}
int rank(DBM *d,int *pending,int length,int *xs,int *zs,int *span,int *left) {
  int best=-1,bw=INF,bs=INF,bl=INF;
  for(int p=0;p<length;p++) {
    int t=pending[p],x=xs[t],z=zs[t];
    int width=plus(d->costs[x*N+z],d->costs[z*N+x]);
    if(width<bw || (width==bw && (span[t]<bs ||
       (span[t]==bs && (left[t]<bl || (left[t]==bl && t<best)))))) {
      best=t; bw=width; bs=span[t]; bl=left[t];
    }
  }
  return best;
}
int key(DBM *d,uint8_t *out) {
  for(int k=0;k<N*N;k++) {
    if(d->costs[k]<-15 || d->costs[k]>15) return 0;
    out[k]=(uint8_t)(d->costs[k]+16);
  }
  return 1;
}
"""


class NativeData(C.Structure):
    _fields_ = [("costs", C.c_int32 * (SIZE * SIZE)),
                ("proofs", C.c_uint64 * (SIZE * SIZE * BLOCKS))]


def build_native(directory):
    source, library = Path(directory) / "dbm.c", Path(directory) / "dbm.so"
    source.write_text(NATIVE_SOURCE)
    result = subprocess.run(["clang", "-O3", "-shared", "-fPIC", str(source),
                             "-o", str(library)], capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stderr)
    lib = C.CDLL(str(library))
    pointer = C.POINTER(NativeData)
    coreptr = C.POINTER(C.c_uint64)
    for name in ("add", "immediate"):
        getattr(lib, name).argtypes = [pointer, C.c_int, C.c_int, C.c_int, C.c_int, coreptr]
        getattr(lib, name).restype = C.c_int
    intptr = C.POINTER(C.c_int)
    lib.scan.argtypes = [pointer, intptr, C.c_int, intptr, intptr, intptr,
                         intptr, intptr, intptr]
    lib.scan.restype = C.c_int
    lib.rank.argtypes = [pointer, intptr, C.c_int, intptr, intptr, intptr, intptr]
    lib.rank.restype = C.c_int
    lib.key.argtypes = [pointer, C.POINTER(C.c_uint8)]
    lib.key.restype = C.c_int
    return lib


class NativeDBM:
    def __init__(self, lib, data=None):
        self.lib, self.data = lib, data if data is not None else NativeData()
        self.size = SIZE
        if data is None:
            for a in range(SIZE):
                for b in range(SIZE):
                    self.data.costs[a * SIZE + b] = 0 if a == b else INF
        self.core = (C.c_uint64 * BLOCKS)()

    def copy(self):
        data = NativeData()
        C.memmove(C.byref(data), C.byref(self.data), C.sizeof(data))
        return NativeDBM(self.lib, data)

    def call(self, name, edge):
        if not getattr(self.lib, name)(C.byref(self.data), *edge, self.core):
            return None
        return sum(int(b) << (64 * k) for k, b in enumerate(self.core))

    def add(self, edge):
        return self.call("add", edge)

    def immediate_cycle(self, edge):
        return self.call("immediate", edge)

    @property
    def costs(self):
        return [list(self.data.costs[a * SIZE:(a + 1) * SIZE]) for a in range(SIZE)]

    def key(self, pending):
        # All distances are finite, bounded by the unchanged range atoms.
        # Costs plus remaining triangle IDs determine the complete future CSP.
        packed = (C.c_uint8 * (SIZE * SIZE))()
        valid = self.lib.key(C.byref(self.data), packed)
        assert valid, "consistent costs left [-15,15]"
        return (bytes(packed), tuple(pending))


@dataclass(frozen=True)
class Counts:
    splits: int
    leaves: int
    depth: int


class Search(audited.Search):
    def __init__(self, lib, seconds, max_nodes, memo_limit, progress_seconds):
        super().__init__(11, seconds, max_nodes, "tight")
        assert len(self.atoms) <= 64 * BLOCKS
        self.lib, self.memo, self.memo_limit = lib, {}, memo_limit
        self.progress_seconds, self.last_progress = progress_seconds, self.started
        self.stats.update({"saturated_entries": 0, "memo_hits": 0,
                           "memo_stored_states": 0, "matrix_copies": 0,
                           "forced_survivor_additions": 0})
        items = [(self.variables[i, j], self.variables[i, k], self.variables[j, k],
                  k - i, j - i) for i, j, k in self.triples]
        self.xs, self.ys, self.zs, self.spans, self.lefts = [
            (C.c_int * len(items))(*(r[q] for r in items)) for q in range(5)]
        self.frontier = []
        self.validation = self.validate_native()
        self.started = time.monotonic()
        self.last_progress = self.started

    def validate_native(self):
        """Compare exact costs and every retained atom bit against frozen Python."""
        import random
        py, native = audited.DBM(SIZE), NativeDBM(self.lib)
        rng = random.Random(20261005)
        checks = 0
        edges = self.base + [e for arms in self.arms for e in rng.choice(arms)]
        for edge in edges:
            p, q = py.add(edge), native.add(edge)
            assert p == q, ("cycle", edge, p, q)
            assert py.costs == native.costs, ("costs", edge)
            for a in range(SIZE):
                for b in range(SIZE):
                    offset = (a * SIZE + b) * BLOCKS
                    bits = sum(int(native.data.proofs[offset + k]) << (64 * k)
                               for k in range(BLOCKS))
                    assert bits == py.proofs[a][b], ("provenance", edge, a, b)
            checks += 1
            if p is not None:
                break
        # Scan/rank involve derived strict thresholds; compare them independently.
        for _ in range(20):
            p = rng.sample(range(len(self.triples)), rng.randint(1, 165))
            live, chosen, mask, removed = self.scan(native, p)
            expected_live = [t for t in p if not any(
                all(py.costs[u][v] <= w for u, v, w, _ in arm)
                for arm in self.arms[t])]
            assert live == expected_live
            if chosen >= 0:
                expected_mask = sum((1 << q) for q, arm in enumerate(self.arms[chosen])
                                    if any(py.immediate_cycle(e) is not None for e in arm))
                assert mask == expected_mask
            else:
                assert not any(py.immediate_cycle(e) is not None
                               for t in live for arm in self.arms[t] for e in arm)
                if live:
                    assert self.rank_native(native, live) == min(live, key=lambda t:self.rank(py,t))
        return {"frozen_python_costs_and_atom_provenance_match": True,
                "edge_updates_compared": checks, "scan_rank_comparisons": 20}

    def scan(self, dbm, pending):
        ids = (C.c_int * len(pending))(*pending)
        length, mask, removed = C.c_int(), C.c_int(), C.c_int()
        chosen = self.lib.scan(C.byref(dbm.data), ids, len(pending),
                               self.xs, self.ys, self.zs, C.byref(length),
                               C.byref(mask), C.byref(removed))
        return list(ids[:length.value]), chosen, mask.value, removed.value

    def rank_native(self, dbm, pending):
        ids = (C.c_int * len(pending))(*pending)
        return self.lib.rank(C.byref(dbm.data), ids, len(pending),
                             self.xs, self.zs, self.spans, self.lefts)

    def tick(self, depth):
        self.check_budget()
        self.stats["nodes"] += 1
        self.stats["max_depth"] = max(self.stats["max_depth"], depth)
        now = time.monotonic()
        if now - self.last_progress >= self.progress_seconds:
            self.last_progress = now
            print(json.dumps({"progress": True, "elapsed_seconds": round(now-self.started,3),
                              **self.stats}), flush=True)

    def note_cycle(self, core):
        assert core is not None
        self.stats["leaves"] += 1
        self.stats["largest_cycle_core"] = max(self.stats["largest_cycle_core"],core.bit_count())

    def add_arm(self, dbm, arm):
        for e in arm:
            self.stats["closure_updates"] += 1
            core = dbm.add(e)
            if core is not None:
                return core
        return None

    def tree(self, dbm, pending, depth=0):
        self.stats["saturated_entries"] += 1
        forced = 0
        while True:
            self.tick(depth + forced)
            pending, chosen, mask, removed = self.scan(dbm, pending)
            self.stats["redundant_triangles_removed"] += removed
            if not pending:
                raise audited.FeasibleDBM(dbm)
            if chosen < 0:
                break
            self.stats["forced_splits"] += 1
            remaining = [t for t in pending if t != chosen]
            rejected = []
            for q, arm in enumerate(self.arms[chosen]):
                if mask & (1 << q):
                    core = next(c for e in arm if (c := dbm.immediate_cycle(e)) is not None)
                    self.note_cycle(core)
                    rejected.append(q)
            if len(rejected) == 2:
                self.stats["terminal_states"] += 1
                return Counts(forced + 1, forced + 2, forced + 1)
            survivor = 1 - rejected[0]
            self.stats["forced_survivor_additions"] += 1
            core = self.add_arm(dbm, self.arms[chosen][survivor])
            if core is not None:
                self.note_cycle(core)
                self.stats["terminal_states"] += 1
                return Counts(forced + 1, forced + 2, forced + 1)
            forced += 1
            pending = remaining
        key = dbm.key(pending)
        cached = self.memo.get(key)
        if cached is not None:
            self.stats["memo_hits"] += 1
            return Counts(forced + cached.splits, forced + cached.leaves, forced + cached.depth)
        chosen = self.rank_native(dbm, pending)
        self.stats["branch_splits"] += 1
        remaining = [t for t in pending if t != chosen]
        children = []
        self.frontier.append({"triple": chosen, "child": 0, "remaining": len(remaining)})
        try:
            for q, arm in enumerate(self.arms[chosen]):
                self.frontier[-1]["child"] = q
                self.check_budget()
                child = dbm.copy()
                self.stats["matrix_copies"] += 1
                core = self.add_arm(child, arm)
                if core is not None:
                    self.note_cycle(core)
                    children.append(Counts(0, 1, 0))
                else:
                    children.append(self.tree(child, remaining, depth + forced + 1))
        except (TimeoutError, audited.FeasibleDBM):
            raise
        else:
            self.frontier.pop()
        subtree = Counts(1+sum(c.splits for c in children),
                         sum(c.leaves for c in children), 1+max(c.depth for c in children))
        if len(self.memo) < self.memo_limit:
            self.memo[key] = subtree
            self.stats["memo_stored_states"] = len(self.memo)
        return Counts(forced + subtree.splits, forced + subtree.leaves, forced + subtree.depth)

    def run(self):
        dbm = NativeDBM(self.lib)
        for e in self.base:
            core = dbm.add(e)
            assert core is None
        counts = None
        try:
            counts = self.tree(dbm, list(range(len(self.triples))))
            result, reason = "complete_unsat_state_search", None
        except audited.FeasibleDBM as exc:
            result, reason = "abstract_necessary_model_sat", None
            self.feasible_dbm = exc.dbm
        except TimeoutError as exc:
            result, reason = "budget_incomplete", str(exc)
        report = {"diagnostic_only_until_kernel_checked": True,
                  "points": 11, "variables": SIZE, "chord_variables": 55, "triples": 165,
                  "result": result, "reason": reason,
                  "budget_seconds": self.wall_seconds, "budget_nodes": self.max_nodes,
                  "elapsed_search_seconds": round(time.monotonic()-self.started,6),
                  "exact_arithmetic": "half-integer bound plus strict bit; plus(a,b)=a+b+((a&1)&(b&1))",
                  "normalized_range": "0 <= d < 4",
                  "normalized_endpoint_caps": "both endpoint absolute differences < 3",
                  "triangle_arms": "outer difference >= 1, middle strictly between outer chords",
                  "positive_row_assumptions": False, "floor_assumptions": False,
                  "deleted_hypotheses": False, "atom_count": len(self.atoms),
                  "optimization": "native exact closure; original-atom bitsets; in-place forced saturation; completed UNSAT state memo",
                  "validation": self.validation, "ordering": "tight",
                  "memo_key": "complete exact cost matrix and remaining triangle IDs; proofs not reused",
                  "memo_max_states": self.memo_limit,
                  "provenance": "every directly found negative-cycle core retains original atom bitset",
                  "kernel_verification": "NOT_RUN", "Lean_source_generated": False,
                  "no_Lean_certificate": True,
                  "memo_certificate_limitation": "cached state UNSAT decisions require fresh provenance or Lean transport before proof export",
                  "remaining_frontier_at_budget": self.frontier,
                  **self.stats}
        if counts is not None:
            assert counts.leaves == counts.splits+1
            report["expanded_tree_counts"] = {"split_nodes": counts.splits,
                                              "negative_cycle_leaves": counts.leaves,
                                              "maximum_split_depth": counts.depth,
                                              "certificate_tree_persisted": False}
        else:
            report["total_tree_size_estimate"] = "UNAVAILABLE: unfinished deterministic DFS provides no rigorous extrapolation"
        return report


def main():
    if not __debug__:
        raise RuntimeError("diagnostic self-validation requires Python assertions enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wall-seconds", type=float, default=180.)
    parser.add_argument("--max-nodes", type=int, default=600000)
    parser.add_argument("--memo-limit", type=int, default=60000)
    parser.add_argument("--progress-seconds", type=float, default=20.)
    args = parser.parse_args()
    if not 0 < args.wall_seconds <= 180: parser.error("wall budget must be in (0,180]")
    if not 0 < args.max_nodes <= 600000: parser.error("node budget must be in (0,600000]")
    if not 0 <= args.memo_limit <= 60000: parser.error("memo limit must be in [0,60000]")
    began = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="jsp404_eleven_dbm_") as directory:
        lib = build_native(directory)
        search = Search(lib, args.wall_seconds, args.max_nodes, args.memo_limit, args.progress_seconds)
        setup_seconds = time.monotonic() - began
        search.wall_seconds = max(0.001, args.wall_seconds - setup_seconds - 0.1)
        report = search.run()
        if report["result"] == "abstract_necessary_model_sat":
            report["angular_witness"] = audited.exact_model(search, search.feasible_dbm)
        report["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        report["frozen_atom_source_sha256"] = hashlib.sha256(Path(audited.__file__).read_bytes()).hexdigest()
        report["native_source_sha256"] = hashlib.sha256(NATIVE_SOURCE.encode()).hexdigest()
        report["requested_total_budget_seconds"] = args.wall_seconds
        report["setup_validation_seconds"] = round(setup_seconds, 6)
        report["elapsed_total_seconds"] = round(time.monotonic()-began,6)
        path = ROOT / "research/JSP404_ELEVEN_DBM_OPTIMIZED_20261005.json"
        path.write_text(json.dumps(report,indent=2)+"\n")
        print(json.dumps(report),flush=True)


if __name__ == "__main__":
    main()
