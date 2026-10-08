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
TARGETS = {'soundness': {'module': 'Jsp000404.SevenLowerReplaySoundness', 'source': 'Jsp000404/SevenLowerReplaySoundness.lean', 'initial_sha256': 'be05c0beffc94ffa422b73974cda2617d4467a82130dfcd46d22d8bfbe13499c', 'selected': ['Jsp404.SevenLowerReplaySoundness.rowsChecked_rowxs_eq', 'Jsp404.SevenLowerReplaySoundness.selectedLower_sound', 'Jsp404.SevenLowerReplaySoundness.decode_sound', 'Jsp404.SevenLowerReplaySoundness.cycleCheck_sound', 'Jsp404.SevenLowerReplaySoundness.check_sound', 'Jsp404.SevenLowerReplaySoundness.checked_root_impossible'], 'scope': 'GenericModel6 strip4 actual interpretation and fuel-recursive cover for the fixed lower-only DAG checker. Literal row orders are internally derived from complete label checks and selected actual triangle arms. Selected profiles are supplied by actual floor accounting. A data-specific root Boolean check remains required; this module asserts no supplied DAG or seven-point terminal has passed. No HIGH/gauge/upper-floor/row4-score or external solver premise.', 'source_owner': 'uniform_complete_oct6b'}}
PROTECTED = {'Jsp000404/SevenLowerReplay.lean': '2c302a294adaddfda76de0252cb5b3f70b5898683ba0c0809cc12eefde8d6440', 'Jsp000404/SevenWeakFloorProfiles.lean': '00594754a3bc67325bceb937179be9d27015e8c82e91f60346b7c2e2559e23f3', 'Jsp000404/N4R2SharedCycleChecker.lean': '395bb55ec39ef93e80832922402d1055fe63ec103157c557ef683d8d27dc708f', 'Jsp000404/N4R2ThinReplay.lean': '9102b5b08044b80240969bad86d710ab458b566243d1c4be04fd4a0e0eba5e41', 'Jsp000404/SatScalarModel.lean': '143fef4b435a544df7750d860ea43f55aa18e2d963d4e01535c414f9a6068e0a', '.lake/packages/mathlib/Mathlib/Data/List/OfFn.lean': 'e14a87415ad8baf04439924697192e596e5d4730506ed54448c3d8b4b6fb1be2', '.lake/packages/mathlib/Mathlib/Order/Fin/Basic.lean': '048735aef17ef89d37cd55ed9dd2b1168848377379c45c4a2a49c2336ff5109b'}


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
            "included_in_public_gate": False, "included_in_2695": False,
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
