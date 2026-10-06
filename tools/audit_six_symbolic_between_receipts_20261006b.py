#!/usr/bin/env python3
"""Read-only audit of frozen all-62 proof sources and genuine compiler logs.

This audits existing evidence; it never compiles Lean or rewrites a PASS receipt.
The output is an independent audit, not a compiler completion claim.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

from audit_six_symbolic_between_coverage_20261006b import audit as audit_coverage

ROOT = Path(__file__).resolve().parents[1]
FINAL = 'research/JSP404_SIX_SYMBOLIC_BETWEEN_ALL62_FINAL_FREEZE_20261006.json'
HELPERS = 'research/JSP404_SIX_SYMBOLIC_V2_BUDGET_HELPERS_FREEZE_20261006.json'
FRESH = 'research/JSP404_SIX_SYMBOLIC_BETWEEN_FRESH_RECHECK_20261006b.json'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
AXIOMS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")


def read_json(path):
    return json.loads((ROOT / path).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit():
    final = read_json(FINAL)
    errors, checked, results = [], {}, []
    strict, normal, normal_targets = set(), set(), {}
    counts = Counter()

    def check_hash(path, digest, owner):
        path = str(path)
        key = (path, digest)
        if key in checked:
            return
        full = ROOT / path
        actual = sha(full) if full.is_file() else None
        checked[key] = actual
        if actual != digest:
            errors.append({'owner': owner, 'path': path, 'expected': digest,
                           'actual': actual, 'issue': 'missing file or SHA mismatch'})

    registry = final['typed_leaf_registry']
    assert len(registry) == 62
    for mask, item in registry.items():
        for path_key, hash_key in [('source', 'source_sha256'), ('freeze', 'freeze_sha256')]:
            check_hash(item[path_key], item[hash_key], f'mask {mask}')
    for path, digest in final['proof_source_hashes'].items():
        check_hash(path, digest, FINAL)

    manifest_path = final['source_manifest']
    manifest = read_json(manifest_path)
    for path_key, hash_key in [('source', 'source_sha256'), ('generator', 'generator_sha256'),
                               ('coverage_tree', 'coverage_tree_sha256')]:
        check_hash(manifest[path_key], manifest[hash_key], manifest_path)
    terminal_receipt = read_json(final['check_receipt'])
    check_hash(manifest_path, terminal_receipt['source_manifest_sha256'], final['check_receipt'])
    if registry != manifest['typed_leaf_registry']:
        errors.append({'issue': 'terminal and final registries differ'})

    freezes = sorted({item['freeze'] for item in registry.values()}) + [HELPERS]
    receipts = []
    for path in freezes:
        frozen = read_json(path)
        for key in ['source_hashes', 'helper_source_hashes', 'sources_frozen_for_first_checks',
                    'file_hashes']:
            for source, digest in frozen.get(key, {}).items():
                check_hash(source, digest, path)
        refs = frozen.get('receipts', {})
        if isinstance(refs, dict):
            for stage, item in refs.items():
                check_hash(item['path'], item['sha256'], path)
                receipts.append((item['path'], stage.lower()))
        else:
            receipts.extend((item, 'both') for item in refs)
        for key, stage in [('nat_receipt', 'nat'), ('actual_receipt', 'actual'),
                           ('normal_lake_receipt', 'normal'), ('strict_and_normal_receipt', 'both')]:
            if key in frozen:
                receipts.append((frozen[key], stage))
    receipts.append((final['check_receipt'], 'both'))
    if (ROOT / FRESH).is_file():
        receipts.append((FRESH, 'both'))

    for path, stage in receipts:
        receipt = read_json(path)
        if path == FRESH:
            check_hash(receipt['source_freeze'], receipt['source_freeze_sha256'], path)
            check_hash(receipt['script'], receipt['script_sha256'], path)
        if receipt.get('status') != 'PASS':
            errors.append({'path': path, 'issue': 'receipt not PASS'})
        rows = receipt.get('results', [])
        if receipt.get('expected_targets', len(rows)) != len(rows) or receipt.get('completed', len(rows)) != len(rows):
            errors.append({'path': path, 'issue': 'incomplete receipt'})
        for row in rows:
            command = row.get('command')
            if command is None and row.get('reused_real_probe_receipt'):
                probe_path = 'research/JSP404_SIX_SYMBOLIC_NAT_SHARD025_CAP6_PROBE_20261005.json'
                probe = read_json(probe_path)
                command = probe['command']
                check_hash(probe['source'], probe['source_sha256'], probe_path)
                if probe['status'] != 'PASS' or probe['exit_code'] != 0 or probe['resource_stop'] is not None:
                    errors.append({'path': probe_path, 'issue': 'invalid original strict probe'})
                original_log = Path(probe['log'])
                if original_log.is_file():
                    check_hash(str(original_log), row['log_sha256'], probe_path)
            if command is None:
                errors.append({'path': path, 'issue': 'missing compiler command'})
                continue
            default_module = (final['public_import'] if path == final['check_receipt'] else
                              'Jsp000404.SixSymbolicActiveCountBound' if 'ACTIVE_COUNT' in path else
                              'Jsp000404.SixSymbolicUnitEndCountBound' if 'UNIT_HELPER' in path else
                              'Jsp000404.SixSymbolicLegacyReuse')
            module = row.get('module', default_module)
            source = row.get('source', module.replace('.', '/') + '.lean')
            own_stage = row.get('stage', stage)
            if own_stage == 'both':
                own_stage = 'normal' if command[:2] == ['lake', 'build'] else 'strict'
            counts[own_stage] += 1
            if row.get('status') != 'PASS' or row.get('exit_code') != 0 or row.get('resource_stop') is not None:
                errors.append({'path': path, 'module': module, 'issue': 'compiler result not clean PASS'})
            if 'source_sha256' in row:
                check_hash(source, row['source_sha256'], path)
            if path == FRESH:
                check_hash(row['artifact'], row['artifact_sha256'], path)
            check_hash(row['log'], row['log_sha256'], path)
            text = (ROOT / row['log']).read_text()
            axioms = dict(AXIOMS.findall(text))
            if not axioms or 'error:' in text:
                errors.append({'path': path, 'module': module, 'issue': 'log lacks axioms or contains error'})
            for theorem, axioms_text in axioms.items():
                if not set(axioms_text.replace(',', ' ').split()) <= STANDARD:
                    errors.append({'path': path, 'theorem': theorem, 'issue': 'nonstandard axioms', 'axioms': axioms_text})
            if own_stage == 'normal':
                built = bool(re.search(r'\bBuilt ' + re.escape(module) + r'(?:\s|$)', text))
                if command != ['lake', 'build', module] or not built or 'Build completed successfully' not in text:
                    errors.append({'path': path, 'module': module, 'issue': 'normal target not genuinely built'})
                normal.add(source)
                artifact = '.lake/build/lib/lean/' + str(Path(source).with_suffix('.olean'))
                if row.get('artifact_sha256'):
                    check_hash(artifact, row['artifact_sha256'], path)
                normal_targets[module] = {'source': source, 'source_sha256': sha(ROOT / source),
                                          'receipt': path, 'log': row['log'], 'log_sha256': row['log_sha256'],
                                          'artifact_sha256': row.get('artifact_sha256'),
                                          'artifact': artifact,
                                          'artifact_matches_current_bytes': sha(ROOT / artifact) == row.get('artifact_sha256'),
                                          'own_target_built': built}
            else:
                if command[:3] != ['lake', 'env', 'lean'] or '--trust=0' not in command:
                    errors.append({'path': path, 'module': module, 'issue': 'strict check missing trust=0'})
                strict.add(source)
            peak = max([row.get(key, 0) for key in ['peak_tree_rss_kib', 'sampled_peak_tree_rss_kib',
                                                  'peak_sampled_tree_rss_kib']])
            if peak >= 8 * 1024 ** 2 or row.get('seconds', 0) <= 0:
                errors.append({'path': path, 'module': module, 'issue': 'resource evidence outside limits'})
            results.append({'receipt': path, 'module': module, 'source': source, 'stage': own_stage,
                            'log': row['log'], 'log_sha256': row['log_sha256'],
                            'axiom_declarations': len(axioms), 'peak_tree_rss_kib': peak})

    missing_strict = sorted(set(final['proof_source_hashes']) - strict)
    missing_normal = sorted(set(final['proof_source_hashes']) - normal)
    if missing_normal:
        errors.append({'issue': 'sources lack normal evidence', 'sources': missing_normal})
    if missing_strict and missing_strict != ['Jsp000404/SixExactFloorKernelSymbolicInterval.lean']:
        errors.append({'issue': 'unexpected sources lack strict command evidence', 'sources': missing_strict})
    coverage = audit_coverage()
    if coverage['status'] != 'PASS':
        errors.append({'issue': 'independent coverage audit did not pass'})
    declarations = []
    forbidden = []
    for path in final['proof_source_hashes']:
        text = (ROOT / path).read_text()
        for line, content in enumerate(text.splitlines(), 1):
            match = re.match(r'^#print axioms\s+(\S+)', content)
            if match:
                name = match[1]
                if not name.startswith('Jsp404.'):
                    name = 'Jsp404.SixExactFloorKernel.' + name
                declarations.append({'theorem': name, 'source': path, 'line': line})
        # Every frozen proof source uses this exact namespace. Token scan is
        # deliberately conservative: comments are scanned too.
        for token in ['sorry', 'admit', 'native_decide', 'axiom', 'newaxiom']:
            if re.search(r'\b' + token + r'\b', text):
                forbidden.append({'source': path, 'token': token})
    if forbidden:
        errors.append({'issue': 'forbidden proof source tokens', 'matches': forbidden})

    publication_files = set()
    for name in final['publish_files']:
        path = ROOT / name
        if path.is_dir():
            publication_files.update(str(item.relative_to(ROOT)) for item in path.rglob('*') if item.is_file())
        elif path.is_file():
            publication_files.add(name)
        else:
            errors.append({'path': name, 'issue': 'publication path missing'})
    publication_hashes = {path: sha(ROOT / path) for path in sorted(publication_files)}
    trailing_logs = [path for path in sorted(publication_files) if path.startswith('verification/')
                     and re.search(rb'[ \t]+\r?$', (ROOT / path).read_bytes(), re.M)]
    supplemental_files = [str(Path(__file__).resolve().relative_to(ROOT)),
                          'tools/audit_six_symbolic_between_coverage_20261006b.py',
                          'tools/recheck_six_symbolic_between_interval_20261006b.py']
    if (ROOT / FRESH).is_file():
        supplemental_files.extend(read_json(FRESH)['publish_files'])
    supplemental_hashes = {path: sha(ROOT / path) for path in sorted(set(supplemental_files))}

    return {'status': 'STATIC_AUDIT_PASS' if not errors and not missing_strict else
                     'STATIC_AUDIT_PASS_INTERVAL_STRICT_COMMAND_PENDING' if not errors else 'STATIC_AUDIT_FAILED',
            'scope': final['scope'], 'original_problem_complete': False,
            'final_freeze': FINAL, 'final_freeze_sha256': sha(ROOT / FINAL),
            'audit_script': str(Path(__file__).resolve().relative_to(ROOT)), 'audit_script_sha256': sha(Path(__file__)),
            'public_import': final['public_import'], 'public_theorem': final['public_theorem'],
            'registry_directions': sorted(map(int, registry)), 'case_freezes': freezes,
            'hash_checks': len(checked), 'receipt_count': len(receipts), 'stage_result_counts': dict(counts),
            'proof_sources': final['proof_source_hashes'], 'normal_reuse_targets': normal_targets,
            'missing_strict_command_evidence': missing_strict, 'missing_normal_evidence': missing_normal,
            'independent_coverage_audit': coverage,
            'raw_interval_strict_log': 'verification/SIX_SYMBOLIC_MIN_INTERVAL_KERNEL_20261006.txt',
            'raw_interval_strict_log_sha256': sha(ROOT / 'verification/SIX_SYMBOLIC_MIN_INTERVAL_KERNEL_20261006.txt'),
            'printed_axiom_declarations': declarations, 'results': results, 'errors': errors,
            'expanded_publication_file_hashes': publication_hashes,
            'supplemental_publication_file_hashes': supplemental_hashes,
            'stdout_trailing_whitespace_local_retention': {path: publication_hashes[path] for path in trailing_logs},
            'stdout_retention_rule': 'Keep original bytes and SHA locally; do not strip or rewrite existing PASS logs.',
            'limitations': ['This audit reads actual saved evidence and runs no Lean compiler.',
                            'Other imported repository theorems may contain sorry; this public proof uses only Std3 axioms.']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='research/JSP404_SIX_SYMBOLIC_BETWEEN_ALL62_INDEPENDENT_AUDIT_20261006b.json')
    args = parser.parse_args()
    result = audit()
    destination = ROOT / args.output
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ['status', 'hash_checks', 'receipt_count',
                                                'stage_result_counts', 'missing_strict_command_evidence', 'errors']}))
    if result['errors']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
