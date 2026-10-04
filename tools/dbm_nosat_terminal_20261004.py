#!/usr/bin/env python3
"""Exact strict DBM search for the bare nine-point LOW triangle terminal.

Bounds are half-integers paired with strictness, packed as 4*bound-strict.
Addition ORs strictness.  No floating epsilon or external solver is used.
A complete search may emit ordinary Lean branching and linarith; the DBM
answer itself is never a theorem premise.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import itertools
import json
import pickle
import re
import subprocess
import time
from pathlib import Path

INF = 10**9
ROOT = Path(__file__).resolve().parents[1]


def verify_shards(report_path, jobs, resume=False, memory_limit_gib=6):
    """Compile every generated source under trust=0 and audit the final root.

    Actual Lean oleans are produced for imports.  No Lake trace or compiler
    receipt is forged; whole-project Lake verification remains independent.
    """
    report = json.loads(report_path.read_text())
    count = report["generated_proof_sources"]["private_proof_shards"]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    previous = report.get("kernel_verification", {}) if resume else {}
    kept = []
    for result in previous.get("completed_shards", []):
        source = ROOT / "Jsp000404" / f"{result['module']}.lean"
        if (result["status"] == "PASS" and result["exit_code"] == 0 and
            set(result["axioms"]) <= allowed and Path(result["olean"]).exists() and
            hashlib.sha256(source.read_bytes()).hexdigest() == result["source_sha256"]):
            kept.append(result)
    done_numbers = {result["number"] for result in kept}
    pending = iter(i for i in range(count) if i not in done_numbers)
    verification = {"status": "RUNNING", "trust_level": 0, "maximum_parallel_jobs": jobs,
                    "expected_shards": count, "completed_shards": kept,
                    "failed_shards": [], "root": "NOT_RUN",
                    "resumed_verified_shards": len(kept),
                    "own_lean_rss_limit_gib": memory_limit_gib,
                    "maximum_observed_parallel_jobs": 0,
                    "maximum_observed_own_lean_rss_bytes": 0}
    report["kernel_verification"] = verification
    started = time.monotonic()
    prior_elapsed = previous.get("elapsed_seconds", 0)
    nominal_rss = int(1.7 * 1024**3)
    limit_rss = memory_limit_gib * 1024**3
    def swap_used():
        output = subprocess.check_output(["sysctl", "-n", "vm.swapusage"], text=True)
        match = re.search(r"used\s*=\s*([\d.]+)([MG])", output)
        return int(float(match.group(1)) * (1024**2 if match.group(2) == "M" else 1024**3)) if match else 0
    initial_swap = swap_used()
    verification["initial_system_swap_used_bytes"] = initial_swap
    verification["swap_growth_throttled_to_two_jobs"] = False
    def own_rss(numbers):
        output = subprocess.check_output(["ps", "-axo", "rss,command"], text=True)
        total, seen = 0, set()
        for line in output.splitlines():
            fields = line.strip().split(maxsplit=1)
            if len(fields) != 2 or not fields[0].isdigit():
                continue
            command = fields[1]
            if command.split(maxsplit=1)[0].rsplit("/", 1)[-1] != "lean":
                continue
            match = re.search(r"NoSatNineDBMShard(\d+)\.lean", command)
            if match and int(match.group(1)) in numbers:
                total += int(fields[0]) * 1024
                seen.add(int(match.group(1)))
        verification["maximum_observed_own_lean_rss_bytes"] = max(
            total, verification["maximum_observed_own_lean_rss_bytes"])
        return total + nominal_rss * (len(numbers) - len(seen))
    def save():
        verification["elapsed_seconds"] = round(prior_elapsed + time.monotonic() - started, 3)
        report_path.write_text(json.dumps(report, indent=2) + "\n")
    def compile_one(number):
        module = f"NoSatNineDBMShard{number:03d}" if isinstance(number, int) else number
        source = ROOT / "Jsp000404" / f"{module}.lean"
        output = ROOT / ".lake/build/lib/lean/Jsp000404" / f"{module}.olean"
        log = Path("/tmp") / f"jsp404_{module}_trust0_20261004.log"
        began = time.monotonic()
        with log.open("w") as handle:
            result = subprocess.run(["lake", "env", "lean", "--trust=0", "-o", str(output), str(source)],
                                    cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT)
        content = log.read_text()
        axiom_groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", content, re.S)
        axioms = sorted({x.strip() for group in axiom_groups for x in group.split(",") if x.strip()})
        passed = result.returncode == 0 and bool(axiom_groups) and set(axioms) <= allowed
        return {"module": module, "number": number, "exit_code": result.returncode,
                "status": "PASS" if passed else "FAIL", "axioms": axioms,
                "seconds": round(time.monotonic() - began, 3), "log": str(log),
                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "olean": str(output) if passed else None}
    save()
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {}
        def dispatch():
            current_swap = swap_used()
            if current_swap > initial_swap + 256 * 1024**2:
                verification["swap_growth_throttled_to_two_jobs"] = True
            active_limit = min(jobs, 2) if verification["swap_growth_throttled_to_two_jobs"] else jobs
            while len(futures) < active_limit:
                if own_rss(set(futures.values())) + nominal_rss > limit_rss:
                    break
                number = next(pending, None)
                if number is None:
                    break
                futures[executor.submit(compile_one, number)] = number
                verification["maximum_observed_parallel_jobs"] = max(
                    len(futures), verification["maximum_observed_parallel_jobs"])
        dispatch()
        while futures:
            done, _ = wait(futures, return_when=FIRST_COMPLETED)
            for future in done:
                number = futures.pop(future)
                result = future.result()
                if result["status"] == "PASS":
                    verification["completed_shards"].append(result)
                else:
                    verification["failed_shards"].append(result)
                save()
                print(json.dumps({"shard": number, "status": result["status"],
                                  "seconds": result["seconds"],
                                  "complete": len(verification["completed_shards"]), "of": count}), flush=True)
                if verification["failed_shards"]:
                    continue
                dispatch()
    if len(verification["completed_shards"]) == count and not verification["failed_shards"]:
        verification["root"] = compile_one("NoSatNineDBMTerminal")
        verification["status"] = verification["root"]["status"]
        if verification["status"] == "PASS":
            report["diagnostic_only_until_kernel_checked"] = False
            report["generated_proof_sources"]["kernel_verification"] = "PASS"
    else:
        verification["status"] = "FAIL"
    save()
    print(json.dumps({"kernel_status": verification["status"],
                      "completed_shards": len(verification["completed_shards"]),
                      "root": verification["root"], "elapsed_seconds": verification["elapsed_seconds"]}), flush=True)
    return verification["status"] == "PASS"


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
            self.base.append(self.edge(0, v, 13, f"hd{i}{j}b"))
        for i, j, k in self.triples:
            x, y, z = self.variables[i, j], self.variables[i, k], self.variables[j, k]
            # Both endpoint absolute-difference caps hold in either triangle
            # arm.  Derive them once in ordinary Lean and add them up front;
            # they must not be delayed until that triangle's orientation split.
            for u, v, suffix in ((x, y, "xy"), (y, x, "yx"),
                                 (y, z, "yz"), (z, y, "zy")):
                self.base.append(self.edge(u, v, 9, f"hc{i}{j}{k}{suffix}"))
            arms = []
            for low, high in ((x, z), (z, x)):
                names = [f"htr{i}{j}{k}{s}" for s in "abcde"]
                # x_v-x_u bound: high->low -1, middle->low <0,
                # high->middle <0, low->middle <5/2, middle->high <5/2.
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
            raise ValueError("a complete consistent orientation was reached")
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
        except (TimeoutError, ValueError) as exc:
            tree, result, reason = None, "incomplete", str(exc)
        return tree, {"diagnostic_only_until_kernel_checked": True,
                      "points": self.n, "variables": len(self.chords) + 1,
                      "triples": len(self.triples), "result": result, "reason": reason,
                      "exact_arithmetic": "half-integer bound plus strict bit; no epsilon",
                      "normalized_range": "0 <= d < 7/2",
                      "normalized_endpoint_caps": "both endpoint differences < 5/2",
                      "positive_row_assumptions": False,
                      "ordering": self.ordering,
                      "budget_seconds": self.wall_seconds, "budget_nodes": self.max_nodes,
                      "elapsed_seconds": round(time.monotonic() - self.started, 6),
                      **self.stats}

    def emit_tree(self, tree, indent=2):
        if "core" in tree:
            names = sorted({a["name"] for i, a in enumerate(self.atoms) if tree["core"] & (1 << i)})
            return [" " * indent + "linarith only [hlam, " + ", ".join(names) + "]"]
        i, j, k = self.triples[tree["triple"]]
        names = [f"htr{i}{j}{k}{s}" for s in "abcde"]
        raw_names = names[:3] + ["_", "_"]
        pat = "⟨" + ", ".join(raw_names) + "⟩"
        prefix = " " * indent
        lines = [prefix + f"rcases m.htr {i} {j} {k} (by decide) (by decide) with",
                 prefix + "  " + pat + " | " + pat]
        for arm, child in enumerate(tree["children"]):
            lines.append(prefix + "·")
            lines += self.emit_tree(child, indent + 2)
        return lines

    def emit_lean(self, tree, path):
        n = self.n
        header = f'''import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Exact DBM search only selects a finite ordinary Lean branch tree. Every
leaf is checked by linarith and the kernel; no diagnostic result is trusted. -/
namespace Jsp404.NoSatNineDBMTerminal

structure NineModel (lam p : ℝ) where
  hlam : 0 < lam
  hp : 2*p < 7*lam
  d : Fin {n} → Fin {n} → ℝ
  hrange : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < p
  htr : ∀ i j k : Fin {n}, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ p-lam ∧ d j k-d i k ≤ p-lam) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ p-lam ∧ d i j-d i k ≤ p-lam)

private theorem endpoint_caps {{lam p : ℝ}} (m : NineModel lam p)
    (i j k : Fin {n}) (hij : i < j) (hjk : j < k) :
    m.d i k-m.d i j < (5/2 : ℝ)*lam ∧
    m.d i j-m.d i k < (5/2 : ℝ)*lam ∧
    m.d j k-m.d i k < (5/2 : ℝ)*lam ∧
    m.d i k-m.d j k < (5/2 : ℝ)*lam := by
  have hp := m.hp
  have hlam := m.hlam
  rcases m.htr i j k hij hjk with h | h
  all_goals rcases h with ⟨ha, hb, hc, hd, he⟩
  all_goals repeat' apply And.intro
  all_goals linarith

set_option maxHeartbeats 64000000 in
theorem nine_model_impossible {{lam p : ℝ}} (m : NineModel lam p) : False := by
  have hlam := m.hlam
  have hp := m.hp
'''
        setup = []
        for i, j in self.chords:
            setup += [f"  obtain ⟨hd{i}{j}a, hd{i}{j}braw⟩ := m.hrange {i} {j} (by decide)",
                      f"  have hd{i}{j}b : m.d {i} {j} < (7/2 : ℝ)*lam := by",
                      f"    linarith only [hd{i}{j}braw, hp]"]
        for i, j, k in self.triples:
            setup.append(f"  obtain ⟨hc{i}{j}{k}xy, hc{i}{j}{k}yx, hc{i}{j}{k}yz, hc{i}{j}{k}zy⟩ := endpoint_caps m {i} {j} {k} (by decide) (by decide)")
        source = header + "\n".join(setup + self.emit_tree(tree)) + "\n\n#print axioms nine_model_impossible\nend Jsp404.NoSatNineDBMTerminal\n"
        path.write_text(source)
        return len(source.splitlines())

    def atom_type(self, idx):
        atom = self.atoms[idx]
        u, v, bound = atom["from"], atom["to"], atom["packed_bound"]
        def value(vertex):
            if vertex == 0:
                return "(0 : ℝ)"
            i, j = self.chords[vertex - 1]
            return f"m.d {i} {j}"
        if bound == 0 and v == 0:
            return f"0 ≤ {value(u)}"
        if bound == -4:
            return f"{value(v)} + lam ≤ {value(u)}"
        if bound == -1:
            return f"{value(v)} < {value(u)}"
        if bound == 13 and u == 0:
            return f"{value(v)} < (7/2 : ℝ)*lam"
        if bound == 9:
            return f"{value(v)} - {value(u)} < (5/2 : ℝ)*lam"
        raise ValueError((idx, atom))

    def model_source(self):
        return f'''import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Necessary bare LOW triangle model.  Period and both endpoint angle
caps are retained.  No positive row, floor, deletion or saturation premise. -/
namespace Jsp404.NoSatNineDBMTerminal

structure NineModel (lam p : ℝ) where
  hlam : 0 < lam
  hp : 2*p < 7*lam
  d : Fin {self.n} → Fin {self.n} → ℝ
  hrange : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < p
  htr : ∀ i j k : Fin {self.n}, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ p-lam ∧ d j k-d i k ≤ p-lam) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ p-lam ∧ d i j-d i k ≤ p-lam)

theorem endpoint_caps {{lam p : ℝ}} (m : NineModel lam p)
    (i j k : Fin {self.n}) (hij : i < j) (hjk : j < k) :
    m.d i k-m.d i j < (5/2 : ℝ)*lam ∧
    m.d i j-m.d i k < (5/2 : ℝ)*lam ∧
    m.d j k-m.d i k < (5/2 : ℝ)*lam ∧
    m.d i k-m.d j k < (5/2 : ℝ)*lam := by
  have hp := m.hp
  have hlam := m.hlam
  rcases m.htr i j k hij hjk with h | h
  all_goals rcases h with ⟨ha, hb, hc, hd, he⟩
  all_goals repeat' apply And.intro
  all_goals linarith

#print axioms endpoint_caps
end Jsp404.NoSatNineDBMTerminal
'''

    def setup_lines(self, needed_names=None):
        lines = ["  have hlam := m.hlam", "  have hp := m.hp"]
        for i, j in self.chords:
            if needed_names is not None and not ({f"hd{i}{j}a", f"hd{i}{j}b"} & needed_names):
                continue
            if needed_names is not None and f"hd{i}{j}b" not in needed_names:
                lines.append(f"  have hd{i}{j}a := (m.hrange {i} {j} (by decide)).1")
                continue
            lines += [f"  obtain ⟨hd{i}{j}a, hd{i}{j}braw⟩ := m.hrange {i} {j} (by decide)",
                      f"  have hd{i}{j}b : m.d {i} {j} < (7/2 : ℝ)*lam := by",
                      f"    linarith only [hd{i}{j}braw, hp]"]
        for i, j, k in self.triples:
            names = {f"hc{i}{j}{k}{s}" for s in ("xy", "yx", "yz", "zy")}
            if needed_names is not None and not (names & needed_names):
                continue
            lines.append(f"  obtain ⟨hc{i}{j}{k}xy, hc{i}{j}{k}yx, hc{i}{j}{k}yz, hc{i}{j}{k}zy⟩ := endpoint_caps m {i} {j} {k} (by decide) (by decide)")
        return lines

    def emit_shards(self, tree, directory, split_depth, max_checks=0,
                    prune_base=False, preserve_prefix_count=0):
        shards = []
        emitted = []
        subtree_checks = {}
        def count_checks(node):
            count = 1 if "core" in node else sum(count_checks(c) for c in node["children"])
            subtree_checks[id(node)] = count
            return count
        count_checks(tree)
        def leaf_lines(node, indent):
            return self.emit_tree(node, indent)
        def render(node, active, binary_depth, indent=2, allow_shards=True):
            if "core" in node:
                return leaf_lines(node, indent)
            split_here = (subtree_checks[id(node)] <= max_checks if max_checks
                          else binary_depth >= split_depth)
            if allow_shards and split_here:
                number = len(shards)
                shards.append((node, active))
                args = " ".join(self.atoms[a]["name"] for a in active)
                return [" " * indent + f"exact shard_{number:03d} m " + args]
            prefix = " " * indent
            idx = node["triple"]
            i, j, k = self.triples[idx]
            pattern = "⟨" + ", ".join(f"htr{i}{j}{k}{s}" for s in "abc") + ", _, _⟩"
            c0, c1 = node["children"]
            dead = 0 if "core" in c0 else (1 if "core" in c1 else None)
            if dead is not None and "core" not in node["children"][1 - dead]:
                winner = 1 - dead
                method = "resolve_left" if dead == 0 else "resolve_right"
                force_name = f"hforced{i}{j}{k}"
                lines = [prefix + f"have {force_name} := (m.htr {i} {j} {k} (by decide) (by decide)).{method} (by",
                         prefix + f"  rintro {pattern}"]
                lines += leaf_lines(node["children"][dead], indent + 2)
                lines[-1] += ")"
                lines.append(prefix + f"obtain {pattern} := {force_name}")
                winning_atoms = tuple(e[3] for e in self.arms[idx][winner])
                return lines + render(node["children"][winner], active + winning_atoms,
                                      binary_depth, indent, allow_shards)
            lines = [prefix + f"rcases m.htr {i} {j} {k} (by decide) (by decide) with",
                     prefix + "  " + pattern + " | " + pattern]
            for arm, child in enumerate(node["children"]):
                lines.append(prefix + "·")
                atoms = tuple(e[3] for e in self.arms[idx][arm])
                lines += render(child, active + atoms, binary_depth + 1, indent + 2, allow_shards)
            return lines

        def needed(body):
            names = set()
            for line in body:
                match = re.search(r"linarith only \[([^\]]*)\]", line)
                if match:
                    names.update(x.strip() for x in match.group(1).split(","))
            return names if prune_base else None
        root_body = render(tree, (), 0)
        root_proof = self.setup_lines(needed(root_body)) + root_body
        model_path = directory / "NoSatNineDBMModel.lean"
        model_text = self.model_source()
        if not model_path.exists() or model_path.read_text() != model_text:
            model_path.write_text(model_text)
        emitted.append(model_path)
        shard_sizes = []
        for number, (subtree, active) in enumerate(shards):
            name = f"shard_{number:03d}"
            prems = [f"    ({self.atoms[a]['name']} : {self.atom_type(a)})" for a in active]
            proof_name = f"proof_{name}"
            thm = ["set_option maxHeartbeats 32000000 in",
                   f"private theorem {proof_name} {{lam p : ℝ}} (m : NineModel lam p)"]
            body = render(subtree, active, 0, allow_shards=False)
            thm += prems + ["    : False := by"] + self.setup_lines(needed(body)) + body
            public = [f"theorem {name} {{lam p : ℝ}} (m : NineModel lam p)"] + prems
            public += ["    : False :=", f"  {proof_name} m " + " ".join(self.atoms[a]["name"] for a in active)]
            source = "import Jsp000404.NoSatNineDBMModel\n\nnamespace Jsp404.NoSatNineDBMTerminal\n\n"
            source += "\n".join(thm) + "\n\n" + "\n".join(public)
            source += f"\n\n#print axioms {name}\nend Jsp404.NoSatNineDBMTerminal\n"
            path = directory / f"NoSatNineDBMShard{number:03d}.lean"
            if number >= preserve_prefix_count:
                path.write_text(source)
            else:
                source = path.read_text()
            emitted.append(path)
            shard_sizes.append({"number": number, "lines": len(source.splitlines()),
                                "bytes": len(source.encode()), "incoming_hypotheses": len(active)})
        root_source = "\n".join(f"import Jsp000404.NoSatNineDBMShard{i:03d}" for i in range(len(shards)))
        root_source += "\n\nnamespace Jsp404.NoSatNineDBMTerminal\n\n"
        root_source += "set_option maxHeartbeats 32000000 in\ntheorem nine_model_impossible {lam p : ℝ} (m : NineModel lam p) : False := by\n"
        root_source += "\n".join(root_proof)
        root_source += "\n\n#print axioms nine_model_impossible\nend Jsp404.NoSatNineDBMTerminal\n"
        root_path = directory / "NoSatNineDBMTerminal.lean"
        root_path.write_text(root_source)
        emitted.append(root_path)
        return {"private_proof_shards": len(shards), "shards": shard_sizes,
                "total_source_lines": sum(len(p.read_text().splitlines()) for p in emitted),
                "total_source_bytes": sum(p.stat().st_size for p in emitted),
                "root_source_lines": len(root_source.splitlines()),
                "kernel_verification": "NOT_RUN", "binary_split_depth": split_depth,
                "maximum_negative_cycle_checks_per_shard": max_checks or None,
                "setup_pruned_to_actual_leaf_references": prune_base,
                "preserved_prefix_shards": preserve_prefix_count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--points", type=int, default=9)
    parser.add_argument("--wall-seconds", type=float, default=60)
    parser.add_argument("--max-nodes", type=int, default=10000)
    parser.add_argument("--ordering", choices=("span", "tight"), default="span")
    parser.add_argument("--report", type=Path, default=ROOT / "research/JSP404_NOSAT_NINE_DBM_20261004.json")
    parser.add_argument("--emit-lean", type=Path)
    parser.add_argument("--tree-cache", type=Path,
                        help="Save a complete tree locally for later proof emission; no proof claim.")
    parser.add_argument("--from-cache", type=Path, help="Use a complete locally generated tree cache.")
    parser.add_argument("--emit-shards", type=Path)
    parser.add_argument("--shard-depth", type=int, default=5)
    parser.add_argument("--shard-max-checks", type=int, default=0)
    parser.add_argument("--prune-base", action="store_true")
    parser.add_argument("--preserve-prefix-count", type=int, default=0)
    parser.add_argument("--verify-shards", action="store_true")
    parser.add_argument("--verify-jobs", type=int, choices=(1, 2, 3, 4), default=2)
    parser.add_argument("--resume-verification", action="store_true")
    parser.add_argument("--memory-limit-gib", type=float, default=6)
    args = parser.parse_args()
    if args.verify_shards:
        raise SystemExit(0 if verify_shards(args.report, args.verify_jobs,
                                         args.resume_verification, args.memory_limit_gib) else 1)
    search = Search(args.points, args.wall_seconds, args.max_nodes, args.ordering)
    if args.from_cache:
        with args.from_cache.open("rb") as source:
            cached = pickle.load(source)
        assert cached["points"] == search.n and cached["atoms"] == search.atoms
        tree, report = cached["tree"], dict(cached["report"])
    else:
        tree, report = search.run()
    if args.tree_cache and tree is not None:
        with args.tree_cache.open("wb") as output:
            pickle.dump({"points": search.n, "tree": tree, "atoms": search.atoms,
                         "triples": search.triples, "report": report}, output)
        report["complete_tree_cache"] = str(args.tree_cache)
    if args.emit_shards and tree is not None:
        report["generated_proof_sources"] = search.emit_shards(tree, args.emit_shards, args.shard_depth,
                                                             args.shard_max_checks, args.prune_base,
                                                             args.preserve_prefix_count)
    if args.emit_lean and tree is not None:
        report["lean_source_lines"] = search.emit_lean(tree, args.emit_lean)
        report["lean_source"] = str(args.emit_lean)
        report["kernel_verification"] = "NOT_RUN"
    elif args.emit_lean:
        report["lean_source_emitted"] = False
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))


if __name__ == "__main__":
    main()
