#!/usr/bin/env python3
"""One formally allocated WordCatalog target; no other targets are dispatched."""
from pathlib import Path
import hashlib
import json
import os
import re
import runpy
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'Jsp000404/SixOuterWordCatalogComplete.lean'
MODULE = 'Jsp000404.SixOuterWordCatalogComplete'
EXPECTED = 'b42de2205e22c27067842de8ec43f733e289f0df5ffcd4137d49b4e9b0d846b3'
OUTPUT = ROOT / 'research/JSP404_SIX_OUTER_WORD_CATALOG_RECEIPT_20261008.json'
LOGS = Path(__file__).parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def active_compilers():
    rows = subprocess.check_output(['ps', '-A', '-o', 'pid=,ppid=,rss=,comm='], text=True)
    return [line.strip() for line in rows.splitlines()
            if line.strip().split()[-1].rsplit('/', 1)[-1] in ('lean', 'lake')]


def main():
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == EXPECTED
    text = source.decode()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|newaxiom)\b', text)
    namespace = re.search(r'^namespace\s+(\S+)', text, re.M).group(1)
    selected = [name if name.startswith('Jsp404.') else namespace + '.' + name
                for name in re.findall(r'^#print axioms\s+(\S+)', text, re.M)]
    rss_tree = runpy.run_path(str(ROOT / 'tools/check_six_symbolic_kernel_20261005.py'))['rss_tree']
    artifact = ROOT / '.lake/build/lib/lean/Jsp000404/SixOuterWordCatalogComplete.olean'
    assert not OUTPUT.exists(), 'Do not overwrite an existing receipt'
    receipt = {'status': 'RUNNING', 'module': MODULE,
               'source': str(SOURCE.relative_to(ROOT)), 'source_sha256': EXPECTED,
               'scope': 'Actual GenericModel5 n4 word coverage in 62 masks; no HIGH or floor-profile premise. No exclusion or original lower theorem is certified.',
               'selected_declarations': selected, 'concurrency': 1, 'rss_cap_gib': 8,
               'time_cap_seconds': 180, 'runner': str(Path(__file__).relative_to(ROOT)),
               'runner_sha256': sha(Path(__file__)), 'results': []}
    for stage in ('strict', 'normal'):
        assert not active_compilers(), 'Global Lean/Lake guard found an active compiler before dispatch'
        assert sha(SOURCE) == EXPECTED
        index = 1
        while (LOGS / f'{stage}-attempt{index:02d}.txt').exists():
            index += 1
        log = LOGS / f'{stage}-attempt{index:02d}.txt'
        snapshot = LOGS / f'{stage}-attempt{index:02d}.source.lean'
        snapshot.write_bytes(source)
        command = (['lake', 'env', 'lean', '--trust=0', '-DautoImplicit=false', '-M8192',
                    '-o', str(artifact), str(SOURCE)] if stage == 'strict' else
                   ['lake', 'build', MODULE])
        started, peak, stop = time.monotonic(), 0, None
        with log.open('w') as out:
            process = subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            while process.poll() is None:
                rss, _, _ = rss_tree(process.pid)
                peak = max(peak, rss)
                if rss >= 8 * 1024 ** 2 or time.monotonic() - started > 180:
                    stop = 'RSS_CAP' if rss >= 8 * 1024 ** 2 else 'TIME_CAP'
                    os.killpg(process.pid, signal.SIGINT)
                    break
                time.sleep(.1)
            try:
                process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                stop = stop or 'EXIT_TIMEOUT'
        raw = log.read_text()
        axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw))
        for name in re.findall(r"'([^']+)' does not depend on any axioms", raw):
            axioms[name] = ''
        observed = {name: axioms.get(name) for name in selected}
        own_built = bool(re.search(r'Built\s+' + re.escape(MODULE) + r'(?:\s|$)', raw))
        success = (process.returncode == 0 and stop is None and 'error:' not in raw
                   and sha(SOURCE) == EXPECTED and artifact.is_file()
                   and all(value is not None and set(value.replace(',', ' ').split()) <= STANDARD
                           for value in observed.values())
                   and (stage != 'normal' or own_built and 'Build completed successfully' in raw))
        row = {'stage': stage, 'attempt': index, 'status': 'PASS' if success else 'NOT_PROVED',
               'source_sha256': EXPECTED, 'command': command, 'exit_code': process.returncode,
               'resource_stop': stop, 'seconds': time.monotonic() - started,
               'peak_tree_rss_kib': peak, 'rss_cap_gib': 8,
               'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
               'source_snapshot': str(snapshot.relative_to(ROOT)), 'source_snapshot_sha256': sha(snapshot),
               'selected_axioms': observed, 'own_target_built': own_built if stage == 'normal' else None,
               'all_replayed_axioms': axioms,
               'artifact_sha256': sha(artifact) if artifact.is_file() else None,
               'own_warnings': [line for line in raw.splitlines()
                                if str(SOURCE.relative_to(ROOT)) + ':' in line and 'warning:' in line]}
        receipt['results'].append(row)
        receipt['status'] = 'RUNNING' if success else 'NOT_PROVED'
        OUTPUT.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps(row), flush=True)
        if not success:
            print(raw[-12000:], flush=True)
            return 1
    receipt['status'] = 'SCOPED_PASS_SIX_OUTER_WORD_CATALOG_STRICT_AND_GENUINE_NORMAL'
    receipt['all_dispatched_processes_exited'] = not active_compilers()
    OUTPUT.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'receipt': str(OUTPUT.relative_to(ROOT)),
                      'receipt_sha256': sha(OUTPUT), 'source_sha256': EXPECTED}), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
