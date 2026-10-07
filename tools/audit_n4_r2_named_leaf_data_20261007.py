#!/usr/bin/env python3
"""Independent source/data parity for named finite leaves; never a kernel proof."""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'research/JSP404_N4_R2_SHARED_REPLAY_SOURCE_MANIFEST_20261007.json'
REPORT = 'research/JSP404_N4_R2_PACKET_TAIL_COMPLETE_PAIRS_20261006.json'
OUTPUT = 'research/JSP404_N4_R2_NAMED_LEAF_SOURCE_PARITY_20261007.json'
TRIPLES = list(itertools.combinations(range(7), 3))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vector(items):
    return '![' + ', '.join(map(str, items)) + ']'


def main():
    manifest = json.loads((ROOT / MANIFEST).read_text())
    report = json.loads((ROOT / REPORT).read_text())
    assert manifest['report_sha256'] == sha(ROOT / REPORT)
    words = report['word_records']
    assert len(words) == 24698
    blocks, checked_ids, occurrences = [], [], 0
    for module, strategy in sorted(manifest.get('leaf_proof_strategies', {}).items()):
        if strategy != 'named per-word checks and balanced theorem-reference composition':
            continue
        source = module.replace('.', '/') + '.lean'
        text = (ROOT / source).read_text()
        assert sha(ROOT / source) == manifest['source_hashes'][source]
        data = manifest['leaf_local_cycle_maps'][module]
        start, count = data['start'], data['count']
        original_ids = data['original_cycle_ids']
        assert len(original_ids) == len(set(original_ids))
        local = {cid: index for index, cid in enumerate(original_ids)}
        references = set()

        def case_id(case):
            nonlocal occurrences
            assert case['status'] == 'DBM_EXCLUDED'
            assert len(case['cycle_ids']) == 1
            cid = case['cycle_ids'][0]
            references.add(cid)
            occurrences += 1
            return local[cid]

        def profiles(cases, optional):
            assert sorted(case['profile_id'] for case in cases) == list(range(28))
            indexed = {case['profile_id']: case for case in cases}
            result = []
            for p in range(28):
                case = indexed[p]
                if case['status'] == 'DBM_EXCLUDED':
                    value = case_id(case)
                    result.append(f'some {value}' if optional else str(value))
                else:
                    assert optional and case['status'] == 'WEAK_DBM_RESIDUAL'
                    assert not case['cycle_ids']
                    result.append('none')
            return vector(result)

        def leaf(word):
            stage = word['stage']
            if stage == 'TAIL_GEOMETRY':
                return f'.tail {case_id(word)}'
            if stage in ('LOW0_WEAK28', 'LOW6_WEAK28'):
                row = 0 if stage == 'LOW0_WEAK28' else 6
                return f'.low{row} ({profiles(word["profiles"], False)})'
            assert stage == 'TWO_LOW_RESIDUAL_PAIRS' and word['pair_cover_closed']
            table0 = profiles(word['low_profiles']['0'], True)
            table6 = profiles(word['low_profiles']['6'], True)
            expected = set(itertools.product(word['residual_profile0_ids'], word['residual_profile6_ids']))
            assert {(c['profile0_id'], c['profile6_id']) for c in word['pair_results']} == expected
            assert len(word['pair_results']) == len(expected)
            pair_values = [(c['profile0_id'], c['profile6_id'], case_id(c)) for c in word['pair_results']]
            expression = '0'
            for p0, p6, value in reversed(pair_values):
                expression = f'if p0 = {p0} ∧ p6 = {p6} then {value} else ({expression})'
            return f'.twoLow ({table0}) ({table6}) (fun p0 p6 => {expression})'

        for offset, word in enumerate(words[start:start + count]):
            neighbors = []
            for row in range(7):
                before = {j: set() for j in range(7) if j != row}
                for triple, bit in zip(TRIPLES, word['word']):
                    if row in triple:
                        u, v = sorted(set(triple) - {row})
                        first, second = (u, v) if bit == '0' else (v, u)
                        before[second].add(first)
                assert sorted(map(len, before.values())) == list(range(6))
                ordered = sorted(before, key=lambda j: len(before[j]))
                assert all(u in before[v] for k, u in enumerate(ordered) for v in ordered[k + 1:])
                neighbors.append(vector(ordered))
            name = f'namedLeaf{offset:03d}'
            expected = f'def {name} : LeafData := {{ rows := {vector(neighbors)}, proof := {leaf(word)} }}'
            assert expected in text, f'Named leaf source/data mismatch {module}:{offset}'
            theorem = (f'theorem {name}_checked :\n'
                       f'    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 {start + offset})) {name} = true :=\n'
                       '  by decide +kernel')
            assert theorem in text, f'Direct word theorem is missing {module}:{offset}'
            assert f'exact {name}_checked' in text
            checked_ids.append(start + offset)
        assert references == set(original_ids)
        assert len(re.findall(r'^def localCycle\d+ : Cycle where$', text, re.M)) == len(local)
        assert 'Array LeafData' not in text and 'decide (∀ j : Fin ' not in text
        assert 'import Jsp000404.N4R2CycleLibrary' not in text
        assert len(re.findall(r'^theorem namedLeaf\d+_checked :$', text, re.M)) == count
        blocks.append({'module': module, 'source': source, 'source_sha256': sha(ROOT / source),
                       'start': start, 'count': count, 'compact_local_cycles': len(local)})
    assert len(checked_ids) == len(set(checked_ids))
    result = {'status': 'STATIC_SOURCE_PARITY_PASS_NOT_LEAN_KERNEL', 'Lean_compiled': False,
              'kernel_all_words': False, 'blocks': blocks, 'named_word_checks_in_source': len(checked_ids),
              'case_cycle_occurrences_exact': occurrences,
              'source_manifest': MANIFEST, 'source_manifest_sha256': sha(ROOT / MANIFEST),
              'report': REPORT, 'report_sha256': sha(ROOT / REPORT),
              'audit_tool': str(Path(__file__).resolve().relative_to(ROOT)), 'audit_tool_sha256': sha(Path(__file__)),
              'not_claimed': ['Any listed theorem compiled', 'All24698 exclusions', 'Between terminal', 'Original lower theorem']}
    (ROOT / OUTPUT).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'blocks': len(blocks),
                      'named_words': len(checked_ids), 'case_cycle_occurrences': occurrences}))


if __name__ == '__main__':
    main()
