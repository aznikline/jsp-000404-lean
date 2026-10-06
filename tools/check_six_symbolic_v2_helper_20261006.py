#!/usr/bin/env python3
"""Real single-process strict and normal checks for the thin V2 budget helpers."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import time
from check_six_symbolic_kernel_20261005 import rss_tree, STANDARD

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--helper', choices=('active', 'unit'), default='unit')
    args = parser.parse_args()
    stem = 'SixSymbolicActiveCountBound' if args.helper == 'active' else 'SixSymbolicUnitEndCountBound'
    names = ('active_count_le_defect',) if args.helper == 'active' else (
        'unit_gap_score_lower', 'unit_first_active_count_le_one', 'unit_last_active_count_le_one')
    expected = {'Jsp404.SixExactFloorKernel.' + name for name in names}
    source = ROOT / f'Jsp000404/{stem}.lean'
    artifact = ROOT / f'.lake/build/lib/lean/Jsp000404/{stem}.olean'
    logs = ROOT / f'verification/six-symbolic-v2-{args.helper}-20261006'
    logs.mkdir(exist_ok=True)
    path = ROOT / f'research/JSP404_SIX_SYMBOLIC_V2_{args.helper.upper()}_HELPER_RECEIPT_20261006.json'
    receipt = {'status': 'RUNNING', 'source': str(source.relative_to(ROOT)),
               'source_sha256': sha(source), 'concurrency': 1, 'rss_cap_gib': 6, 'results': []}
    for stage in ('strict', 'normal'):
        command = (['lake', 'env', 'lean', '--trust=0', '-DautoImplicit=false',
                    '-o', str(artifact), str(source)] if stage == 'strict' else
                   ['lake', 'build', f'Jsp000404.{stem}'])
        log = logs / f'{stage}.txt'
        start, peak, stop = time.monotonic(), 0, None
        with log.open('w') as output:
            proc = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
            while proc.poll() is None:
                rss, rows, own = rss_tree(proc.pid)
                peak = max(peak, rss)
                if rss >= 6 * 1024 ** 2 or time.monotonic() - start > 90:
                    stop = 'RSS_CAP' if rss >= 6 * 1024 ** 2 else 'TIME_CAP'
                    for pid, parent, memory in rows:
                        if pid in own and not any(pp == pid for cc, pp, rr in rows):
                            subprocess.run(['kill', '-INT', str(pid)], check=False)
                    break
                time.sleep(.1)
            proc.wait(timeout=20)
        output = log.read_text()
        all_axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
        selected = {name: ax for name, ax in all_axioms.items() if name in expected}
        ok = (proc.returncode == 0 and stop is None and 'error:' not in output and
              set(selected) == expected and artifact.exists() and
              sha(source) == receipt['source_sha256'] and
              all(set(ax.replace(',', ' ').split()) <= STANDARD for ax in all_axioms.values()))
        result = {'stage': stage, 'status': 'PASS' if ok else 'NOT_PROVED', 'command': command,
                  'exit_code': proc.returncode, 'resource_stop': stop,
                  'seconds': time.monotonic() - start, 'peak_tree_rss_kib': peak,
                  'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
                  'axioms': selected, 'all_replayed_axioms': all_axioms,
                  'artifact_sha256': sha(artifact) if ok else None}
        receipt['results'].append(result)
        receipt['status'] = 'RUNNING' if ok else 'NOT_PROVED'
        path.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({k: result[k] for k in ('stage', 'status', 'seconds', 'peak_tree_rss_kib')}), flush=True)
        if not ok:
            raise RuntimeError('Thin helper did not pass; stopped')
    receipt['status'] = 'PASS'
    path.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
