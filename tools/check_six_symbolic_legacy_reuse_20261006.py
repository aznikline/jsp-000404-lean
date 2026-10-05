#!/usr/bin/env python3
"""Single-process real kernel and Lake validation of seven legacy adapters."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import time
from check_six_symbolic_kernel_20261005 import STANDARD, rss_tree

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=float, default=180)
    parser.add_argument('--reconcile-existing-logs', action='store_true',
                        help='Re-audit captured real exits after a receipt-parser fix; no compilation.')
    args = parser.parse_args()
    manifest_path = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_SOURCE_MANIFEST_20261006.json'
    manifest = json.loads(manifest_path.read_text())
    source = ROOT / manifest['source']
    assert sha(source) == manifest['source_sha256']
    assert sha(ROOT / manifest['legacy_source']) == manifest['legacy_source_sha256']
    artifact = ROOT / '.lake/build/lib/lean/Jsp000404/SixSymbolicLegacyReuse.olean'
    module = manifest['module']
    log_dir = ROOT / 'verification/six-symbolic-legacy-reuse-20261006'
    log_dir.mkdir(exist_ok=True)
    receipt_path = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_CHECK_RECEIPT_20261006.json'
    expected = {d['new_theorem'] for d in manifest['declarations']}

    def audit_axioms(text):
        records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
        all_axioms = dict(records)
        selected = {name: ax for name, ax in records if name in expected}
        valid = (set(selected) == expected and
                 all(set(ax.replace(',', ' ').split()).issubset(STANDARD)
                     for ax in all_axioms.values()))
        return selected, all_axioms, valid

    if args.reconcile_existing_logs:
        receipt = json.loads(receipt_path.read_text())
        historical = ROOT / 'research/JSP404_SIX_SYMBOLIC_LEGACY_REUSE_INITIAL_RECEIPT_20261006.json'
        assert not historical.exists(), 'Reconciliation history already exists'
        historical.write_bytes(receipt_path.read_bytes())
        assert receipt['source_sha256'] == manifest['source_sha256']
        assert {r['stage'] for r in receipt['results']} == {'strict', 'normal'}
        for result in receipt['results']:
            assert result['exit_code'] == 0 and result['resource_stop'] is None
            log = ROOT / result['log']
            assert sha(log) == result['log_sha256']
            text = log.read_text()
            selected, all_axioms, valid = audit_axioms(text)
            assert valid and 'error:' not in text
            if result['stage'] == 'normal':
                assert 'Build completed successfully' in text
                result['artifact_sha256'] = sha(artifact)
            result['status'] = 'PASS'
            result['axioms'] = selected
            result['all_replayed_axioms'] = all_axioms
        receipt['status'] = 'PASS'
        receipt['receipt_reconciliation_only'] = True
        receipt['initial_receipt'] = str(historical.relative_to(ROOT))
        receipt['initial_receipt_sha256'] = sha(historical)
        receipt['reconciliation_reason'] = (
            'Normal Lake output replays dependency AX messages in addition to the seven selected exports; '
            'the original real compiler and Lake calls both exited zero. '
            'Require all seven selected names and validate every replayed axiom subset.')
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({'status': 'PASS', 'mode': 'CAPTURED_REAL_EXIT_LOG_RECONCILIATION',
                          'selected_exports': len(expected), 'additional_compiler_calls': 0}))
        return
    receipt = {
        'status': 'RUNNING', 'module': module, 'source_sha256': sha(source),
        'manifest': str(manifest_path.relative_to(ROOT)),
        'manifest_sha256': sha(manifest_path),
        'concurrency': 1, 'rss_cap_gib': 8, 'results': [],
    }
    for stage in ('strict', 'normal'):
        command = (['lake', 'env', 'lean', '--trust=0', '-DautoImplicit=false',
                    '-o', str(artifact), str(source)] if stage == 'strict' else
                   ['lake', 'build', module])
        log = log_dir / f'{stage}.txt'
        start, peak, stop = time.monotonic(), 0, None
        with log.open('w') as output:
            proc = subprocess.Popen(command, cwd=ROOT, stdout=output,
                                    stderr=subprocess.STDOUT)
            while proc.poll() is None:
                rss, rows, own = rss_tree(proc.pid)
                peak = max(peak, rss)
                if rss >= 8 * 1024 ** 2 or time.monotonic() - start > args.seconds:
                    stop = 'RSS_CAP' if rss >= 8 * 1024 ** 2 else 'TIME_CAP'
                    for pid, parent, memory in rows:
                        if pid in own and not any(pp == pid for cc, pp, rr in rows):
                            subprocess.run(['kill', '-INT', str(pid)], check=False)
                    break
                time.sleep(.1)
            proc.wait(timeout=20)
        text = log.read_text()
        selected, all_axioms, valid_axioms = audit_axioms(text)
        ok = (proc.returncode == 0 and stop is None and 'error:' not in text and
              artifact.exists() and valid_axioms and
              sha(source) == manifest['source_sha256'])
        result = {
            'stage': stage, 'status': 'PASS' if ok else 'NOT_PROVED',
            'command': command, 'exit_code': proc.returncode,
            'resource_stop': stop, 'seconds': time.monotonic() - start,
            'sampled_peak_tree_rss_kib': peak,
            'source_sha256': sha(source),
            'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
            'axioms': selected, 'all_replayed_axioms': all_axioms,
            'artifact_sha256': sha(artifact) if ok else None,
        }
        receipt['results'].append(result)
        receipt['status'] = 'RUNNING' if ok else 'NOT_PROVED'
        receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps({k: result[k] for k in ('stage', 'status', 'seconds',
                                                'sampled_peak_tree_rss_kib')}), flush=True)
        if not ok:
            raise RuntimeError(f'Legacy reuse {stage} did not pass; stopped')
    receipt['status'] = 'PASS'
    receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
