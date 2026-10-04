#!/usr/bin/env python3
"""Produce genuine Lake leanArts for the frozen kernel-verified nine-point proof.

Each Lake invocation builds one target.  Model first, then at most three
independent shards, then terminal.  No Lake trace or metadata is fabricated.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
from pathlib import Path
import re
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[1]
GIB = 1024**3


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def swap_used():
    output = subprocess.check_output(["sysctl", "-n", "vm.swapusage"], text=True)
    match = re.search(r"used\s*=\s*([\d.]+)([MG])", output)
    return int(float(match.group(1)) * (1024**2 if match.group(2) == "M" else GIB)) if match else 0


def build(jobs, rss_gib, resume):
    kernel = json.loads((ROOT / "research/JSP404_NOSAT_NINE_DBM_CERTIFICATE_20261004.json").read_text())
    checked = kernel["kernel_verification"]
    assert checked["status"] == "PASS" and len(checked["completed_shards"]) == 268
    expected = {x["module"]: x["source_sha256"] for x in checked["completed_shards"] + [checked["root"]]}
    expected["NoSatNineDBMModel"] = kernel["final_source_receipt"]["model_sha256"]
    for module, digest in expected.items():
        assert sha(ROOT / "Jsp000404" / f"{module}.lean") == digest, module
    receipt_path = ROOT / "research/JSP404_NINE_LAKE_ARTIFACT_RECEIPT_20261005.json"
    logs = ROOT / "verification/nine-lake-20261005"
    logs.mkdir(parents=True, exist_ok=True)
    prior = json.loads(receipt_path.read_text()) if resume and receipt_path.exists() else {}
    retained = [x for x in prior.get("targets", []) if x["status"] == "PASS" and
                x["source_sha256"] == expected.get(x["module"])]
    report = {"status": "RUNNING", "verification": "real lake build per target",
              "package_lean_options": {"autoImplicit": False},
              "maximum_parallel_lake_targets": jobs, "own_lean_rss_limit_gib": rss_gib,
              "kernel_source_receipt": "research/JSP404_NOSAT_NINE_DBM_CERTIFICATE_20261004.json",
              "targets": retained, "failures": [], "scope": "Model, 268 shards, terminal",
              "root_and_actual_consumers_not_built": True,
              "maximum_observed_own_lean_rss_bytes": 0, "maximum_observed_parallel_targets": 0,
              "swap_growth_throttled_to_two": False}
    began = time.monotonic()
    initial_swap = swap_used()
    active = {}
    lock = threading.Lock()
    def save():
        report["elapsed_seconds"] = round(time.monotonic() - began, 3)
        receipt_path.write_text(json.dumps(report, indent=2) + "\n")
    def rss():
        output = subprocess.check_output(["ps", "-axo", "pid,ppid,rss,command"], text=True)
        processes = {}
        for line in output.splitlines():
            parts = line.strip().split(maxsplit=3)
            if len(parts) == 4 and all(x.isdigit() for x in parts[:3]):
                processes[int(parts[0])] = (int(parts[1]), int(parts[2]) * 1024, parts[3])
        with lock:
            roots = set(active.values())
        total, matched_roots = 0, set()
        for pid, (_, size, command) in processes.items():
            if command.split(maxsplit=1)[0].rsplit("/", 1)[-1] != "lean":
                continue
            cursor, visited = pid, set()
            while cursor in processes and cursor not in visited:
                if cursor in roots:
                    total += size
                    matched_roots.add(cursor)
                    break
                visited.add(cursor)
                cursor = processes[cursor][0]
        report["maximum_observed_own_lean_rss_bytes"] = max(
            total, report["maximum_observed_own_lean_rss_bytes"])
        return total + max(0, len(roots) - len(matched_roots)) * int(1.7 * GIB)
    def one(module):
        source = ROOT / "Jsp000404" / f"{module}.lean"
        if sha(source) != expected[module]:
            return {"module": module, "status": "FAIL", "reason": "frozen source hash changed"}
        log = logs / f"{module}.txt"
        started = time.monotonic()
        with log.open("w") as output:
            process = subprocess.Popen(["lake", "build", f"Jsp000404.{module}"], cwd=ROOT,
                                       stdout=output, stderr=subprocess.STDOUT)
            with lock:
                active[module] = process.pid
            try:
                code = process.wait()
            finally:
                with lock:
                    active.pop(module, None)
        unchanged = sha(source) == expected[module]
        content = log.read_text()
        own_axioms = re.findall(r"'Jsp404\.NoSatNineDBMTerminal\.[^']+' depends on axioms:\s*\[([^\]]*)\]", content, re.S)
        ax = sorted({a.strip() for group in own_axioms for a in group.split(",") if a.strip()})
        ok = code == 0 and unchanged and set(ax) <= {"propext", "Classical.choice", "Quot.sound"}
        return {"module": module, "status": "PASS" if ok else "FAIL", "exit_code": code,
                "source_sha256": sha(source), "source_hash_matches_kernel": unchanged,
                "seconds": round(time.monotonic() - started, 3), "log": str(log),
                "reported_nine_point_axioms": ax,
                "olean": str(ROOT / ".lake/build/lib/lean/Jsp000404" / f"{module}.olean")}
    def record(result):
        report["targets" if result["status"] == "PASS" else "failures"].append(result)
        save()
        print(json.dumps({"target": result["module"], "status": result["status"],
                          "seconds": result.get("seconds"), "completed": len(report["targets"]),
                          "of": 270}), flush=True)
    save()
    model = one("NoSatNineDBMModel")
    report["targets"] = [x for x in report["targets"] if x["module"] != "NoSatNineDBMModel"]
    record(model)
    if model["status"] != "PASS":
        report["status"] = "FAIL"
        save()
        return False
    done = {x["module"] for x in report["targets"]}
    pending = iter(f"NoSatNineDBMShard{i:03d}" for i in range(268)
                   if f"NoSatNineDBMShard{i:03d}" not in done)
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {}
        def dispatch():
            if swap_used() > initial_swap + 256 * 1024**2:
                report["swap_growth_throttled_to_two"] = True
            maximum = min(jobs, 2) if report["swap_growth_throttled_to_two"] else jobs
            while len(futures) < maximum and not report["failures"]:
                effective = max(rss(), len(futures) * int(1.7 * GIB))
                if effective + int(1.7 * GIB) > rss_gib * GIB:
                    break
                module = next(pending, None)
                if module is None:
                    break
                futures[executor.submit(one, module)] = module
                report["maximum_observed_parallel_targets"] = max(
                    len(futures), report["maximum_observed_parallel_targets"])
        dispatch()
        while futures:
            finished, _ = wait(futures, return_when=FIRST_COMPLETED)
            for future in finished:
                futures.pop(future)
                record(future.result())
            dispatch()
    if not report["failures"]:
        root = one("NoSatNineDBMTerminal")
        report["targets"] = [x for x in report["targets"] if x["module"] != "NoSatNineDBMTerminal"]
        record(root)
    report["status"] = "PASS" if len(report["targets"]) == 270 and not report["failures"] else "FAIL"
    save()
    print(json.dumps({"lake_artifacts_status": report["status"],
                      "verified_targets": len(report["targets"]),
                      "elapsed_seconds": report["elapsed_seconds"]}), flush=True)
    return report["status"] == "PASS"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, choices=(1, 2, 3), default=3)
    parser.add_argument("--own-rss-gib", type=float, default=6)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    raise SystemExit(0 if build(args.jobs, args.own_rss_gib, args.resume) else 1)
