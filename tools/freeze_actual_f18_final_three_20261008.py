#!/usr/bin/env python3
"""Freeze existing genuine F18 final-three checks; never run a compiler or Git."""
from pathlib import Path
import gzip
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / 'verification/oct8-f18-final-three-batch'
OUTPUT = 'research/JSP404_ACTUAL_F18_COMPLETE_FINAL_BATCH_RECEIPT_20261008.json'
NOTE = 'research/JSP404_ACTUAL_F18_COMPLETE_FINAL_BATCH_VALIDATION_20261008.md'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
NAMES = ['ActualF18ThreeHeavyNoHO', 'ActualF18ThreeHeavy', 'ActualF18Complete']
HISTORY = ['research/JSP404_ACTUAL_F18_THREE_HEAVY_NO_HO_SOURCE_ONLY_OCT8.md',
           'research/JSP404_ACTUAL_F18_THREE_HEAVY_SOURCE_ONLY_20261008.json']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    assert not (ROOT / OUTPUT).exists(), 'Never replace a completed freeze receipt'
    files, records, selected, warnings = set(), {}, {}, []
    for path in ['verification/oct8-f18-final-three-batch/check_target.py',
                 'verification/oct8-f18-final-three-batch/precheck-source-freeze.json',
                 str(Path(__file__).resolve().relative_to(ROOT))] + HISTORY:
        assert (ROOT / path).is_file()
        files.add(path)
    candidates = json.loads((LOGS / 'precheck-source-freeze.json').read_text())
    for candidate in candidates['modules']:
        snapshot = candidate['candidate_snapshot']
        assert sha(ROOT / snapshot) == candidate['source_sha256']
        files.add(snapshot)
    for name in NAMES:
        source = 'Jsp000404/' + name + '.lean'
        text = (ROOT / source).read_text()
        digest = sha(ROOT / source)
        namespace = re.search(r'^namespace\s+(\S+)', text, re.M)[1]
        printed = [n if n.startswith('Jsp404.') else namespace + '.' + n
                   for n in re.findall(r'^#print axioms\s+(\S+)', text, re.M)]
        runs = []
        for path in sorted((LOGS / name).glob('run-attempt*.json')):
            record = json.loads(path.read_text())
            assert record['module'] == 'Jsp000404.' + name
            files.add(str(path.relative_to(ROOT)))
            for result in record['results']:
                assert sha(ROOT / result['log']) == result['log_sha256']
                assert sha(ROOT / result['source_snapshot']) == result['source_snapshot_sha256']
                assert result['source_snapshot_sha256'] == result['source_sha256']
                files.update([result['log'], result['source_snapshot']])
            runs.append(record)
        good = [r for r in runs if r['status'] == 'PASS_EXACT_SOURCE_STRICT_AND_GENUINE_NORMAL'
                and r['source_sha256'] == digest]
        assert len(good) == 1, ('Missing or repeated genuine successful target', name)
        passed = good[0]
        assert passed['selected_declarations'] == printed and len(printed) == 1
        assert [r['stage'] for r in passed['results']] == ['strict', 'normal']
        for result in passed['results']:
            assert result['status'] == 'PASS' and result['exit_code'] == 0
            assert result['resource_stop'] is None and result['source_sha256'] == digest
            assert set(result['selected_axioms']) == set(printed)
            for declaration, axes in result['selected_axioms'].items():
                assert axes is not None and set(axes.replace(',', ' ').split()) <= STANDARD
                selected[declaration] = sorted(set(axes.replace(',', ' ').split()))
            if result['stage'] == 'strict':
                assert '--trust=0' in result['command']
            else:
                assert result['command'] == ['lake', 'build', 'Jsp000404.' + name]
                assert result['own_target_built']
                raw = (ROOT / result['log']).read_text()
                assert 'Built Jsp000404.' + name in raw and 'Build completed successfully' in raw
            warnings.extend({'module': name, 'stage': result['stage'], 'line': line}
                            for line in result['own_warnings'])
        artifact = ROOT / '.lake/build/lib/lean/Jsp000404' / (name + '.olean')
        assert sha(artifact) == passed['results'][1]['artifact_sha256']
        files.add(source)
        records[name] = {'successful': passed, 'attempts': runs}
    assert len(selected) == 3
    for candidate in candidates['modules']:
        before = (ROOT / candidate['candidate_snapshot']).read_bytes()
        after = (ROOT / candidate['source']).read_bytes()
        if candidate['module'] == 'Jsp000404.ActualF18Complete':
            assert before.replace(b'False.elim (Finset.not_mem_empty q hqmem)',
                                  b'False.elim (by simpa using hqmem)') == after
        else:
            assert before == after
    note = ROOT / NOTE
    assert not note.exists()
    note.write_text('# Original F18 minimum-countermodel exclusion\n\n'
        'The three final modules passed actual trust-zero source checks and genuine target builds. '
        'The original cap16 minimum-countermodel in the strip-four LOW band cannot have potential18. '
        'Its actual Frame supplies the heavy count zero through three; all profile choices are internal. '
        'The three-heavy case uses genuine general cloud geometry after its separate local validation, '
        'an internally chosen interior-to-acute-heavy injection in the NoHO branch, and the actual full-hull '
        'turn budget ten in the HO branch. HO itself has only the legality baseline one. '
        'No subset Model or caller hull/type/window/budget is supplied.\n\n'
        'NoHO and ThreeHeavy passed in their initial versions. Complete first failed only because '
        '`Finset.not_mem_empty` is unavailable; the exact source and raw failed output remain retained. '
        'One equivalent empty-membership elimination was substituted, with no mathematical premise change. '
        'The successful Complete source retains one simp-suggestion warning in each mode. '
        'Historical SOURCE_ONLY notes are preserved as preparation history.\n\n'
        'This receipt does not establish the F17 branch, unconditional R2/high-band capacity, '
        'the original arbitrary-N lower theorem, or a complete prize submission.\n')
    files.add(NOTE)
    names_path = LOGS / 'selected-names-final.txt'
    assert not names_path.exists()
    names_path.write_text('\n'.join(sorted(selected)) + '\n')
    files.add(str(names_path.relative_to(ROOT)))
    archives = []
    for path in sorted(files):
        if path.endswith('.txt'):
            raw = (ROOT / path).read_bytes()
            if any(line.endswith((b' ', b'\t')) for line in raw.splitlines()):
                archived = path + '.gz'
                if (ROOT / archived).exists():
                    assert gzip.decompress((ROOT / archived).read_bytes()) == raw
                else:
                    (ROOT / archived).write_bytes(gzip.compress(raw, mtime=0))
                assert gzip.decompress((ROOT / archived).read_bytes()) == raw
                archives.append({'raw_path': path, 'raw_sha256': sha(ROOT / path),
                                 'published_gzip': archived, 'gzip_sha256': sha(ROOT / archived),
                                 'decompression_restores_exact_raw_bytes': True})
                files.remove(path)
                files.add(archived)
    for path in files:
        if path.endswith(('.lean', '.py', '.json', '.md', '.txt')):
            assert not any(line.endswith((b' ', b'\t'))
                           for line in (ROOT / path).read_bytes().splitlines()), path
    result = {'status': 'SCOPED_PASS_ACTUAL_F18_COMPLETE_MINIMUM_COUNTERMODEL_EXCLUSION',
              'original_problem_complete': False, 'modules': records,
              'selected_declarations': selected, 'selected_count': 3,
              'scope': 'ActualMinimalBandCounterexample.Model o e (pi/(4+1/2)) (pi/4) 16 (s+1) c lam; original potential18 is impossible. No caller heavy count in the final Complete theorem.',
              'source_api_repairs': ['Complete only: replace unavailable Finset.not_mem_empty with equivalent False.elim(by simpa using hqmem).'],
              'mathematical_premises_changed': False,
              'own_warning_occurrences': warnings,
              'lossless_stdout_archives': archives,
              'cloud_dependency': {'module': 'Jsp000404.DevinF18TwoHeavyApex',
                                   'source_sha256': sha(ROOT / 'Jsp000404/DevinF18TwoHeavyApex.lean'),
                                   'local_verification_recorded_separately': True},
              'historical_source_only_notes': HISTORY,
              'not_established_by_this_receipt': ['F17 contradiction', 'Unconditional R2/high-band capacity',
                                                'Original arbitrary-N lower theorem', 'Prize theorem'],
              'publication_file_whitelist': sorted(files | {OUTPUT}),
              'publication_file_sha256': {p: sha(ROOT / p) for p in sorted(files)}}
    (ROOT / OUTPUT).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'receipt': OUTPUT, 'sha256': sha(ROOT / OUTPUT),
                      'files': len(result['publication_file_whitelist']), 'selected': len(selected),
                      'own_warning_occurrences': len(warnings), 'lossless_archives': len(archives)}))


if __name__ == '__main__':
    main()
