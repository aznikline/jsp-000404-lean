#!/usr/bin/env python3
"""Actually check the all-direction terminal, with one 8 GiB process tree."""
from pathlib import Path
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
    manifest_path = ROOT / 'research/JSP404_SIX_SYMBOLIC_BETWEEN_TERMINAL_SOURCE_MANIFEST_20261006.json'
    manifest = json.loads(manifest_path.read_text())
    source = ROOT / manifest['source']
    assert sha(source) == manifest['source_sha256']
    assert len(manifest['typed_leaf_registry']) == 62
    for item in manifest['typed_leaf_registry'].values():
        assert sha(ROOT / item['source']) == item['source_sha256']
        assert sha(ROOT / item['freeze']) == item['freeze_sha256']
    artifact = ROOT / '.lake/build/lib/lean/Jsp000404/SixExactFloorKernelSymbolicBetweenTerminal.olean'
    logs = ROOT / 'verification/six-symbolic-between-terminal-20261006'
    logs.mkdir(exist_ok=True)
    path = ROOT / 'research/JSP404_SIX_SYMBOLIC_BETWEEN_TERMINAL_CHECK_RECEIPT_20261006.json'
    receipt = {'status': 'RUNNING', 'source_sha256': sha(source),
               'source_manifest': str(manifest_path.relative_to(ROOT)),
               'source_manifest_sha256': sha(manifest_path),
               'concurrency': 1, 'rss_cap_gib': 8, 'results': []}
    for stage in ('strict', 'normal'):
        command = (['lake', 'env', 'lean', '--trust=0', '-DautoImplicit=false',
                    '-o', str(artifact), str(source)] if stage == 'strict' else
                   ['lake', 'build', 'Jsp000404.SixExactFloorKernelSymbolicBetweenTerminal'])
        log = logs / f'{stage}.txt'
        start, peak, stop = time.monotonic(), 0, None
        with log.open('w') as output:
            proc = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
            while proc.poll() is None:
                rss, rows, own = rss_tree(proc.pid)
                peak = max(peak, rss)
                if rss >= 8 * 1024 ** 2 or time.monotonic() - start > 300:
                    stop = 'RSS_CAP' if rss >= 8 * 1024 ** 2 else 'TIME_CAP'
                    for pid, parent, memory in rows:
                        if pid in own and not any(pp == pid for cc, pp, rr in rows):
                            subprocess.run(['kill', '-INT', str(pid)], check=False)
                    break
                time.sleep(.1)
            proc.wait(timeout=20)
        text = log.read_text()
        axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
        name = manifest['public_theorem']
        ok = (proc.returncode == 0 and stop is None and 'error:' not in text and name in axioms and
              all(set(ax.replace(',', ' ').split()) <= STANDARD for ax in axioms.values()) and
              artifact.exists() and sha(source) == manifest['source_sha256'])
        result = {'stage': stage, 'status': 'PASS' if ok else 'NOT_PROVED',
                  'command': command, 'exit_code': proc.returncode, 'resource_stop': stop,
                  'seconds': time.monotonic() - start, 'peak_tree_rss_kib': peak,
                  'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
                  'public_axioms': axioms.get(name), 'all_replayed_axioms': axioms,
                  'artifact_sha256': sha(artifact) if ok else None}
        receipt['results'].append(result)
        receipt['status'] = 'RUNNING' if ok else 'NOT_PROVED'
        path.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({k: result[k] for k in ('stage', 'status', 'seconds', 'peak_tree_rss_kib')}), flush=True)
        if not ok:
            raise RuntimeError('Terminal check did not pass; stopped')
    receipt['status'] = 'PASS'
    path.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
