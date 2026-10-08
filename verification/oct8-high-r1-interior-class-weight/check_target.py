#!/usr/bin/env python3
"""Prepare by default; compile only one explicitly leased candidate at a time.

This wrapper never edits Lean sources, imports, audit selections or Git.
The preparation plan and source snapshots are not proof receipts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import runpy
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {'weighted': {'module': 'Jsp000404.ActualHighR1InteriorClassWeight', 'source': 'Jsp000404/ActualHighR1InteriorClassWeight.lean', 'initial_sha256': '7977f5db7227230afa0f3a5fa47e119690bdb69de9fad347dc471d085e384e37', 'selected': ['Jsp404.ActualHighR1InteriorClassWeight.exists_actual_high_r1_interior_class_weight'], 'scope': 'Original positive HIGH4 cap20 minimum Model, actual SAT v and score-two a, and an original score-one interior p internally supply card7/potential22, real three-class geometry and original weights sum20/each>=4/SAT>=8/each<=12/SAT-free<=8. No caller potential, gains, partition, weights or LOW half-scale premise. No apex exclusion or R1 capacity claim.', 'source_owner': 'uniform_complete_oct6b'}}
PROTECTED = {'Jsp000404/ActualHighR1PositiveCriticalProfile.lean': 'c1b25f9a8f17eba30c61768c4637c8a8bfd776ace741c73f4df0a134073cc6d2', 'Jsp000404/ActualHighR1HeavyEndpoint.lean': 'ae4d9aa67003638117c32ef19ecf294192a714e18d2e501b42086cfed62e6802', 'Jsp000404/ActualN4R2Capacity.lean': '8f50d099413f1489591203162145b54142a041ee2a46be06cafe9a6d72dba901', 'Jsp000404/ActualInteriorOnePartition.lean': 'e47fc2302bcd1129d883210552fe9af3b2daf89d9499041fa5f5f6e417abb053', 'Jsp000404/ActualF18ClassWeight.lean': '6b27bf26bcc615cee3fe39d21bb333b299204ada005aa8691b48f71a3b318818', 'Jsp000404/ActualMinimalBandCounterexample.lean': '6fbf73008515e37dcbab3f83973d252cf7c9635a954a0e1c7484000fb61a0915'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as out:
        out.write(data)


def json_bytes(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def check_protected():
    observed = {path: sha(ROOT / path) for path in PROTECTED}
    assert observed == PROTECTED, "A frozen true parent changed; stop without editing it"
    return observed


def selected_from_source(source):
    text = source.decode()
    assert not re.search(r"\b(sorry|admit|native_decide|axiom|newaxiom)\b", text)
    namespace = re.search(r"^namespace\s+(\S+)", text, re.M).group(1)
    return [name if name.startswith("Jsp404.") else namespace + "." + name
            for name in re.findall(r"^#print axioms\s+(\S+)", text, re.M)]


def compiler_rows():
    raw = subprocess.check_output(["ps", "-A", "-o", "pid=,ppid=,rss=,comm="], text=True)
    rows = []
    for line in raw.splitlines():
        fields = line.strip().split(None, 3)
        if len(fields) == 4 and fields[3].rsplit("/", 1)[-1] in {"lean", "lake"}:
            rows.append({"pid": int(fields[0]), "kind": fields[3].rsplit("/", 1)[-1]})
    return rows


def prepare():
    check_protected()
    rows = []
    for key, config in TARGETS.items():
        path = ROOT / config["source"]
        source = path.read_bytes()
        assert hashlib.sha256(source).hexdigest() == config["initial_sha256"]
        assert selected_from_source(source) == config["selected"]
        snapshot = HERE / "initial-sources" / (key + ".lean")
        if snapshot.exists():
            assert snapshot.read_bytes() == source, "Do not overwrite an initial candidate"
        else:
            write_new(snapshot, source)
        rows.append({"key": key, **config,
                     "bytes": len(source), "lines": len(source.splitlines()),
                     "initial_snapshot": str(snapshot.relative_to(ROOT)),
                     "initial_snapshot_sha256": sha(snapshot)})
    plan = {"status": "PREPARED_SOURCE_ONLY_NO_LEAN", "Lean_launched": False,
            "included_in_public_gate": False, "included_in_2677": False,
            "root_resource_grant_required_for_execute": True,
            "source_edits_authorized_by_this_plan": False,
            "stage_order": ["strict trust=0", "genuine normal target build"],
            "global_max_Lean_processes": 1, "rss_cap_gib": 8, "seconds_per_stage": 180,
            "maximum_candidate_attempts_per_target": 3,
            "runner": str(Path(__file__).relative_to(ROOT)), "runner_sha256": sha(Path(__file__)),
            "protected_true_parent_sources": PROTECTED, "targets_in_order": rows,
            "failure_policy": "Preserve exact source and raw stdout; stop after failure. Mathematical gaps or repairs over one minute must return the lease to Root. No source edits are performed by this wrapper."}
    dest = HERE / "initial-plan.json"
    payload = json_bytes(plan)
    if dest.exists():
        assert dest.read_bytes() == payload, "Do not overwrite a prepared plan"
    else:
        write_new(dest, payload)
    print(json.dumps({"status": plan["status"], "plan": str(dest.relative_to(ROOT)),
                      "plan_sha256": sha(dest), "selected_counts": {k: len(v["selected"]) for k, v in TARGETS.items()},
                      "Lean_launched": False}), flush=True)


def execute(args):
    assert args.root_lease.strip(), "A fresh explicit Root lease is required"
    config = TARGETS[args.target]
    source_path = ROOT / config["source"]
    expected = args.candidate_sha or config["initial_sha256"]
    if expected != config["initial_sha256"]:
        assert args.repair_approval.strip(), "A changed candidate needs explicit Root API-repair approval"
    assert sha(source_path) == expected
    source = source_path.read_bytes()
    assert selected_from_source(source) == config["selected"]
    check_protected()
    assert not compiler_rows(), "An existing global Lean/Lake process holds the resource"
    directory = HERE / args.target
    directory.mkdir(exist_ok=True)
    attempt = 1
    while (directory / f"attempt{attempt:02d}-receipt.json").exists():
        attempt += 1
    assert attempt <= 3, "The three-candidate bound is exhausted; return to Root"
    receipt_path = directory / f"attempt{attempt:02d}-receipt.json"
    receipt = {"status": "RUNNING", "module": config["module"], "scope": config["scope"],
               "source": config["source"], "source_sha256": expected,
               "initial_source_sha256": config["initial_sha256"], "selected_declarations": config["selected"],
               "root_lease": args.root_lease, "Root_API_repair_approval": args.repair_approval or None,
               "runner": str(Path(__file__).relative_to(ROOT)), "runner_sha256": sha(Path(__file__)),
               "candidate_attempt": attempt, "concurrency": 1, "rss_cap_gib": 8,
               "time_cap_seconds": 180, "included_in_public_gate": False,
               "protected_true_parent_sources": check_protected(), "results": []}
    write_new(receipt_path, json_bytes(receipt))
    rss_tree = runpy.run_path(str(ROOT / "tools/check_six_symbolic_kernel_20261005.py"))["rss_tree"]
    artifact = ROOT / ".lake/build/lib/lean" / Path(config["source"]).with_suffix(".olean")
    for stage in ("strict", "normal"):
        assert not compiler_rows(), "Global compiler guard before dispatch"
        check_protected()
        assert sha(source_path) == expected
        snapshot = directory / f"attempt{attempt:02d}-{stage}.source.lean"
        log = directory / f"attempt{attempt:02d}-{stage}.stdout.txt"
        write_new(snapshot, source)
        command = (["lake", "env", "lean", "--trust=0", "-DautoImplicit=false", "-M8192",
                    "-o", str(artifact), str(source_path)] if stage == "strict" else
                   ["lake", "build", config["module"]])
        started, peak, global_max, stop = time.monotonic(), 0, 0, None
        with log.open("xb") as out:
            process = subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            print(json.dumps({"stage": stage, "module": config["module"], "pid": process.pid,
                              "candidate_attempt": attempt}), flush=True)
            while process.poll() is None:
                rss, _, _ = rss_tree(process.pid)
                peak = max(peak, rss)
                count = sum(row["kind"] == "lean" for row in compiler_rows())
                global_max = max(global_max, count)
                if rss >= 8 * 1024 ** 2 or time.monotonic() - started > 180 or count > 1:
                    stop = ("RSS_CAP" if rss >= 8 * 1024 ** 2 else
                            "GLOBAL_LEAN_CONCURRENCY" if count > 1 else "TIME_CAP")
                    os.killpg(process.pid, signal.SIGINT)
                    break
                time.sleep(.1)
            try:
                process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                stop = stop or "EXIT_TIMEOUT"
        raw = log.read_text(errors="replace")
        axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw))
        for name in re.findall(r"'([^']+)' does not depend on any axioms", raw):
            axioms[name] = ""
        observed = {name: axioms.get(name) for name in config["selected"]}
        own_built = bool(re.search(r"Built\s+" + re.escape(config["module"]) + r"(?:\s|$)", raw))
        parents = {path: sha(ROOT / path) for path in PROTECTED}
        success = (process.returncode == 0 and stop is None and global_max <= 1
                   and sha(source_path) == expected and parents == PROTECTED and artifact.is_file()
                   and all(value is not None and set(value.replace(",", " ").split()) <= STANDARD
                           for value in observed.values())
                   and (stage != "normal" or own_built and "Build completed successfully" in raw))
        row = {"stage": stage, "status": "PASS" if success else "NOT_PROVED",
               "command": command, "exit_code": process.returncode, "resource_stop": stop,
               "seconds": time.monotonic() - started, "peak_tree_rss_kib": peak,
               "global_max_Lean_processes": global_max, "source_sha256_after": sha(source_path),
               "source_snapshot": str(snapshot.relative_to(ROOT)), "source_snapshot_sha256": sha(snapshot),
               "log": str(log.relative_to(ROOT)), "log_sha256": sha(log),
               "protected_true_parent_sources_after": parents, "selected_axioms": observed,
               "own_target_built": own_built if stage == "normal" else None,
               "artifact_sha256": sha(artifact) if artifact.is_file() else None,
               "own_warnings": [line for line in raw.splitlines()
                                if config["source"] + ":" in line and "warning:" in line]}
        receipt["results"].append(row)
        receipt["status"] = "RUNNING" if success else "NOT_PROVED"
        receipt_path.write_bytes(json_bytes(receipt))
        print(json.dumps({key: row[key] for key in ("stage", "status", "exit_code", "resource_stop",
                         "seconds", "peak_tree_rss_kib", "global_max_Lean_processes", "selected_axioms",
                         "own_target_built", "own_warnings")}), flush=True)
        if not success:
            print("\n".join(line for line in raw.splitlines()
                            if "error:" in line or "error(" in line)[-5000:], flush=True)
            return 1
    receipt["status"] = "SCOPED_PASS_TWO_REAL_STAGES"
    receipt["all_dispatched_processes_exited"] = not compiler_rows()
    receipt_path.write_bytes(json_bytes(receipt))
    print(json.dumps({"status": receipt["status"], "receipt": str(receipt_path.relative_to(ROOT)),
                      "receipt_sha256": sha(receipt_path), "source_sha256": expected}), flush=True)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--execute", action="store_true")
    parser.add_argument("--target", choices=TARGETS)
    parser.add_argument("--root-lease", default="")
    parser.add_argument("--candidate-sha")
    parser.add_argument("--repair-approval", default="")
    args = parser.parse_args()
    if not args.execute:
        prepare()
        return 0
    assert args.target, "Choose one independently leased target"
    return execute(args)


if __name__ == "__main__":
    raise SystemExit(main())
