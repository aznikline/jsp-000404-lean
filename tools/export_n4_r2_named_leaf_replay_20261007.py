#!/usr/bin/env python3
"""Export named per-word checks and bounded composition of checked leaves.

No Lean is executed. This never treats Python audit results as kernel proof.
Only new owned files are written; completed replay sources are immutable.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
REPORT = 'research/JSP404_N4_R2_PACKET_TAIL_COMPLETE_PAIRS_20261006.json'
AUDIT = 'research/JSP404_N4_R2_SHARED_CYCLE_DATA_AUDIT_20261006b.json'
MANIFEST = 'research/JSP404_N4_R2_SHARED_REPLAY_SOURCE_MANIFEST_20261007.json'
CHECKPOINT = 'research/JSP404_N4_R2_SHARED_REPLAY_CHECKPOINT_20261007.json'
CYCLE_CHUNK = 256
LEAF_CHUNK = 128
TRIPLES = tuple(itertools.combinations(range(7), 3))
VERTICES = ['.zero'] + [f'.theta {i}' for i in range(7)] + [
    f'.distance {i} {j}' for i, j in itertools.combinations(range(7), 2)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vector(items):
    return '![' + ', '.join(map(str, items)) + ']'


def origin(name):
    if match := re.fullmatch(r'ht([0-6])([ab])', name):
        i, side = match.groups()
        return f'.theta{"Lower" if side == "a" else "Upper"} {i}'
    if match := re.fullmatch(r'ht([0-5])([1-6])', name):
        i, j = map(int, match.groups())
        assert j == i + 1
        return f'.thetaNext {i}'
    if match := re.fullmatch(r'hc([0-6])([0-6])([ab])', name):
        i, j, side = match.groups()
        assert int(i) < int(j)
        return f'.corridor{"Lower" if side == "a" else "Upper"} {i} {j}'
    if match := re.fullmatch(r'htr([0-6])([0-6])([0-6])([abc])', name):
        i, j, k = map(int, match.groups()[:3])
        part = 'abc'.index(match.group(4))
        return f'.triangle {TRIPLES.index((i, j, k))} {part}'
    if match := re.fullmatch(r'hgap([0-6])([0-6])(lower|upper)', name):
        i, k, side = match.groups()
        return f'.gap{side.title()} {i} {k}'
    raise ValueError(f'Invalid origin: {name}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--leaf-block', action='append', type=int,
                        help='Regenerate only selected unpassed leaf blocks; preserve other source bytes')
    args = parser.parse_args()
    if args.leaf_block is not None:
        assert args.leaf_block and all(0 <= number < 193 for number in args.leaf_block)
    report = json.loads((ROOT / REPORT).read_text())
    audit = json.loads((ROOT / AUDIT).read_text())
    assert audit['report_sha256'] == sha(ROOT / REPORT)
    assert audit['complete_words'] == 24698
    paths = audit['ordered_path_certificates']
    referenced = set()
    for word in report['word_records']:
        referenced.update(word.get('cycle_ids', []))
        for case in word.get('profiles', []):
            referenced.update(case['cycle_ids'])
        for cases in word.get('low_profiles', {}).values():
            for case in cases:
                referenced.update(case['cycle_ids'])
        for case in word.get('pair_results', []):
            referenced.update(case['cycle_ids'])
    cycle_ids = sorted(referenced)
    assert len(cycle_ids) == 20027
    ids = {cid: index for index, cid in enumerate(cycle_ids)}
    previous = json.loads((ROOT / MANIFEST).read_text()) if (ROOT / MANIFEST).exists() else {}
    frozen = json.loads((ROOT / CHECKPOINT).read_text()).get('passed_source_hashes', {}) if (ROOT / CHECKPOINT).exists() else {}
    source_hashes, modules, kinds = {}, [], {}

    def emit(module, content, kind):
        relative = module.replace('.', '/') + '.lean'
        target = ROOT / relative
        if target.exists() and target.read_text() != content:
            if relative in frozen:
                raise ValueError(f'Refusing to change completed kernel source {relative}')
            if sha(target) != previous.get('source_hashes', {}).get(relative):
                raise ValueError(f'File collision or another owner changed {relative}')
        if not target.exists() or target.read_text() != content:
            target.write_text(content)
        source_hashes[relative] = sha(target)
        modules.append(module)
        kinds[module] = kind

    common = ('set_option autoImplicit false\nset_option pp.fullNames true\n'
              'set_option maxRecDepth 8192\nset_option maxHeartbeats 0\n\n')
    cycle_modules = []
    for start in range(0, len(cycle_ids), CYCLE_CHUNK):
        number = start // CYCLE_CHUNK
        module = f'Jsp000404.N4R2CycleDataShard{number:03d}'
        cycle_modules.append(module)
        lines = ['import Jsp000404.N4R2ThinReplay\n\n', common,
                 f'namespace Jsp404.N4R2ReplayData.CycleShard{number:03d}\n',
                 'open N4R2ThinReplay\n\n']
        names = []
        for local, cid in enumerate(cycle_ids[start:start + CYCLE_CHUNK]):
            certificate = paths[cid]
            n = len(certificate['c'])
            assert len(certificate['nodes']) == n + 1 and len(certificate['premises']) == n
            assert certificate['nodes'][0] == certificate['nodes'][-1]
            assert certificate['accepts'] is True
            name = f'cycle{local:03d}'
            names.append(name)
            strict = vector(str(flag).lower() for flag in certificate['strict'])
            lines.extend([f'/-- Finite data for original cycle {cid}. -/\n',
                          f'def {name} : Cycle where\n  length := {n}\n  data := {{\n',
                          f'    node := {vector(VERTICES[v] for v in certificate["nodes"])}\n',
                          f'    constant := {vector(certificate["c"])}\n',
                          f'    coefficient := {vector(certificate["b"])}\n',
                          f'    strict := {strict} }}\n',
                          f'  origin := {vector(origin(name) for name in certificate["premises"])}\n\n'])
        lines.extend(['def cycles : Array Cycle := #[', ', '.join(names), ']\n',
                      'def lookup (id : ℕ) : Option Cycle := cycles[id]?\n\n',
                      f'end Jsp404.N4R2ReplayData.CycleShard{number:03d}\n'])
        emit(module, ''.join(lines), 'finite_cycle_data')

    def dispatch(blocks, access, variable):
        if len(blocks) == 1:
            return access(blocks[0])
        midpoint = len(blocks) // 2
        boundary = blocks[midpoint][1]
        return f'if {variable} < {boundary} then\n  ({dispatch(blocks[:midpoint], access, variable)}) else\n  ({dispatch(blocks[midpoint:], access, variable)})'

    blocks = [(number, start, min(CYCLE_CHUNK, len(cycle_ids) - start))
              for number, start in enumerate(range(0, len(cycle_ids), CYCLE_CHUNK))]
    lookup = dispatch(blocks, lambda block: f'CycleShard{block[0]:03d}.lookup (id - {block[1]})', 'id')
    library_module = 'Jsp000404.N4R2CycleLibrary'
    emit(library_module, ''.join(f'import {module}\n' for module in cycle_modules) + '\n' + common +
         'namespace Jsp404.N4R2ReplayData\nopen N4R2ThinReplay\n\n' +
         f'def library : Library := fun id =>\n  {lookup}\n\nend Jsp404.N4R2ReplayData\n', 'cycle_library')

    def single_id(case):
        assert case['status'] == 'DBM_EXCLUDED' and len(case['cycle_ids']) == 1
        return ids[case['cycle_ids'][0]]

    def profiles(cases, optional=False):
        assert len(cases) == 28 and {c['profile_id'] for c in cases} == set(range(28))
        by_id = {case['profile_id']: case for case in cases}
        values = []
        for p in range(28):
            case = by_id[p]
            if case['status'] == 'DBM_EXCLUDED':
                value = single_id(case)
                values.append(f'some {value}' if optional else str(value))
            else:
                assert optional and case['status'] == 'WEAK_DBM_RESIDUAL' and not case['cycle_ids']
                values.append('none')
        return vector(values)

    def leaf(word):
        stage = word['stage']
        if stage == 'TAIL_GEOMETRY':
            return f'.tail {single_id(word)}'
        if stage in ('LOW0_WEAK28', 'LOW6_WEAK28'):
            return f'.low{stage[3]} ({profiles(word["profiles"])})'
        assert stage == 'TWO_LOW_RESIDUAL_PAIRS' and word['pair_cover_closed']
        expected = set(itertools.product(word['residual_profile0_ids'], word['residual_profile6_ids']))
        pairs = word['pair_results']
        assert len(pairs) == len(expected)
        assert {(c['profile0_id'], c['profile6_id']) for c in pairs} == expected
        expression = '0'
        for case in reversed(pairs):
            expression = (f'if p0 = {case["profile0_id"]} ∧ p6 = {case["profile6_id"]} '
                          f'then {single_id(case)} else ({expression})')
        return (f'.twoLow ({profiles(word["low_profiles"]["0"], True)}) '
                f'({profiles(word["low_profiles"]["6"], True)}) '
                f'(fun p0 p6 => {expression})')

    def certified_rows(word):
        ranks = {i: {j: 0 for j in range(7) if j != i} for i in range(7)}
        for bit, (a, b, c) in zip(word["word"], TRIPLES):
            for row, u, v in [(a, b, c), (b, a, c), (c, a, b)]:
                ranks[row][v if bit == '0' else u] += 1
        result = []
        for i in range(7):
            assert sorted(ranks[i].values()) == list(range(6))
            result.append(vector(sorted(ranks[i], key=ranks[i].get)))
        return vector(result)

    leaf_modules, checked_modules, leaf_blocks = [], [], []
    local_cycle_maps = {}
    proof_strategies = dict(previous.get('leaf_proof_strategies', {}))
    regenerated_blocks = []
    words = report['word_records']
    assert len(words) == 24698
    for start in range(0, len(words), LEAF_CHUNK):
        number = start // LEAF_CHUNK
        count = min(LEAF_CHUNK, len(words) - start)
        data_module = f'Jsp000404.N4R2LeafDataShard{number:03d}'
        checked_module = f'Jsp000404.N4R2LeafCheckedShard{number:03d}'
        leaf_modules.append(data_module)
        checked_modules.append(checked_module)
        leaf_blocks.append((number, start, count))
        if args.leaf_block is not None and number not in args.leaf_block:
            for module in (data_module, checked_module):
                relative = module.replace('.', '/') + '.lean'
                assert sha(ROOT / relative) == previous['source_hashes'][relative]
                source_hashes[relative] = sha(ROOT / relative)
                modules.append(module)
                kinds[module] = previous['module_kinds'][module]
            local_cycle_maps[checked_module] = previous['leaf_local_cycle_maps'][checked_module]
            proof_strategies.setdefault(checked_module, 'block Fin quantifier and Array lookup; source only')
            continue
        regenerated_blocks.append(number)
        local_ids = set()
        for word in words[start:start + count]:
            local_ids.update(word.get('cycle_ids', []))
            for case in word.get('profiles', []):
                local_ids.update(case['cycle_ids'])
            for cases in word.get('low_profiles', {}).values():
                for case in cases:
                    local_ids.update(case['cycle_ids'])
            for case in word.get('pair_results', []):
                local_ids.update(case['cycle_ids'])
        local_lines = []
        saved_global_ids = ids
        local_order = sorted(local_ids, key=saved_global_ids.get)
        ids = {cid: local for local, cid in enumerate(local_order)}
        local_cycle_maps[checked_module] = {'start': start, 'count': count, 'original_cycle_ids': local_order, 'original_global_indices': [saved_global_ids[cid] for cid in local_order]}
        for cid in local_order:
            certificate = paths[cid]
            n = len(certificate['c'])
            name = f'localCycle{ids[cid]:05d}'
            local_lines.extend([
                f'-- Original cycle {cid}; original global index {saved_global_ids[cid]}.\n',
                f'def {name} : Cycle where\n  length := {n}\n  data := {{\n',
                f'    node := {vector(VERTICES[v] for v in certificate["nodes"])}\n',
                f'    constant := {vector(certificate["c"])}\n',
                f'    coefficient := {vector(certificate["b"])}\n',
                f'    strict := {vector(str(flag).lower() for flag in certificate["strict"])} }}\n',
                f'  origin := {vector(origin(value) for value in certificate["premises"])}\n\n'])
        def local_lookup(values):
            if not values:
                return 'none'
            if len(values) == 1:
                index = ids[values[0]]
                return f'if id = {index} then some localCycle{index:05d} else none'
            mid = len(values) // 2
            return f'if id < {ids[values[mid]]} then ({local_lookup(values[:mid])}) else ({local_lookup(values[mid:])})'
        local_lines.append(f'def library : Library := fun id => {local_lookup(local_order)}\n\n')
        entries = ',\n  '.join('{ rows := ' + certified_rows(word) +
                                ', proof := ' + leaf(word) + ' }'
                                for word in words[start:start + count])
        namespace = f'Jsp404.N4R2ReplayData.LeafShard{number:03d}'
        emit(data_module, 'import Jsp000404.N4R2RowDataReplay\n\n' + common +
             f'namespace {namespace}\nopen N4R2RowDataReplay\n\n' +
             f'def data : Array LeafData := #[\n  {entries}]\n\n' +
             'def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }\n' +
             'def lookup (offset : ℕ) : LeafData := (data[offset]?).getD fallback\n\n' +
             f'end {namespace}\n', 'finite_leaf_data')
        # Compute each word independently. The large block is assembled from
        # checked theorem references; no closed Fin128 quantifier or leaf array
        # is unfolded by the kernel during an arithmetic acceptance check.
        named_lines = []
        for offset, word in enumerate(words[start:start + count]):
            name = f'namedLeaf{offset:03d}'
            named_lines.extend([
                f'def {name} : LeafData := {{ rows := {certified_rows(word)}, proof := {leaf(word)} }}\n\n',
                f'theorem {name}_checked :\n',
                f'    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 {start + offset})) {name} = true :=\n',
                '  by decide +kernel\n\n'])

        offsets = [(offset, offset, 1) for offset in range(count)]
        named_lookup = dispatch(offsets, lambda item: f'namedLeaf{item[0]:03d}', 'offset')
        named_lines.extend([
            'def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }\n',
            f'def lookup (offset : ℕ) : LeafData :=\n  if offset < {count} then ({named_lookup}) else fallback\n\n'])

        def compose_named(values, indent):
            prefix = ' ' * indent
            if len(values) == 1:
                offset = values[0][0]
                return (prefix + f'have hj : j = ⟨{offset}, by decide⟩ := by\n' +
                        prefix + '  apply Fin.ext\n' + prefix + f'  change j.val = {offset}\n' +
                        prefix + '  omega\n' +
                        prefix + 'subst j\n' + prefix + f'exact namedLeaf{offset:03d}_checked\n')
            midpoint = len(values) // 2
            boundary = values[midpoint][1]
            return (prefix + f'by_cases h{boundary} : j.val < {boundary}\n' +
                    prefix + '· ' + compose_named(values[:midpoint], indent + 2).lstrip() +
                    prefix + '· ' + compose_named(values[midpoint:], indent + 2).lstrip())

        checked = ('import Jsp000404.N4R2RowDataReplay\n'
                   'import Jsp000404.N4R2WordCatalog\n\n' + common +
                   'set_option Elab.async false\n\n' +
                   f'namespace {namespace}\nopen N4R2RowDataReplay\n\n' +
                   ''.join(local_lines) + ''.join(named_lines) +
                   f'theorem point_checked (j : Fin {count}) :\n'
                   f'    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 ({start} + j.val))) (lookup j.val) = true := by\n'
                   f'  have hjbound : j.val < {count} := j.isLt\n' +
                   compose_named(offsets, 2) + '\n' +
                   f'theorem correct (id : Fin 24698) (hlow : {start} ≤ id.val) (hhigh : id.val < {start + count}) :\n'
                   f'    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - {start})) = true := by\n'
                   f'  let j : Fin {count} := ⟨id.val - {start}, by omega⟩\n'
                   f'  have hsum : {start} + j.val = id.val := by dsimp [j]; omega\n'
                   f'  have hindex : Fin.ofNat 24698 ({start} + j.val) = id := by\n'
                   '    apply Fin.ext\n    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]\n'
                   '  have hh := point_checked j\n  rw [hindex] at hh\n  exact hh\n\n'
                   '#print axioms point_checked\n#print axioms correct\n\n' + f'end {namespace}\n')
        emit(checked_module, checked, 'closed_leaf_kernel_check')
        proof_strategies[checked_module] = 'named per-word checks and balanced theorem-reference composition'
        ids = saved_global_ids

    all_module = 'Jsp000404.N4R2AllLeavesChecked'
    expression = dispatch(leaf_blocks, lambda block: f'LeafShard{block[0]:03d}.lookup (id.val - {block[1]})', 'id.val')
    lines = [''.join(f'import {module}\n' for module in checked_modules), '\n', common,
             'namespace Jsp404.N4R2ReplayData\nopen N4R2RowDataReplay\n\n',
             f'def libraryFor (id : Fin 24698) : Library :=\n  {dispatch(leaf_blocks, lambda block: f"LeafShard{block[0]:03d}.library", "id.val")}\n\n',
             f'def leafData (id : Fin 24698) : LeafData :=\n  {expression}\n\n',
             'theorem all_leaves_checked (id : Fin 24698) :\n'
             '    leafCheck (libraryFor id) (N4R2WordTree.catalog id) (leafData id) = true := by\n']
    def proof_dispatch(blocks, indent):
        if len(blocks) == 1:
            number, start, count = blocks[0]
            return (' ' * indent + f'exact LeafShard{number:03d}.correct id (by omega) (by omega)\n')
        midpoint = len(blocks) // 2
        boundary = blocks[midpoint][1]
        name = f'h{boundary}'
        return (' ' * indent + f'by_cases {name} : id.val < {boundary}\n' +
                ' ' * indent + f'· simp only [leafData, libraryFor, {name}, ↓reduceIte]\n' + proof_dispatch(blocks[:midpoint], indent + 2) +
                ' ' * indent + f'· simp only [leafData, libraryFor, {name}, ↓reduceIte]\n' + proof_dispatch(blocks[midpoint:], indent + 2))
    # Normalize only the selected branch in each path; the final leaf lookup
    # is definitionally the same bounded data shard used by its correct lemma.
    lines.append(proof_dispatch(leaf_blocks, 2))
    lines.extend(['\n#print axioms all_leaves_checked\nend Jsp404.N4R2ReplayData\n'])
    emit(all_module, ''.join(lines), 'aggregate_leaf_kernel_checks')

    manifest = {'status': 'SOURCE_ONLY_NOT_LEAN_KERNEL', 'Lean_compiled': False,
                'report': REPORT, 'report_sha256': sha(ROOT / REPORT),
                'data_audit': AUDIT, 'data_audit_sha256': sha(ROOT / AUDIT),
                'generator': str(Path(__file__).resolve().relative_to(ROOT)), 'generator_sha256': sha(Path(__file__)),
                'word_encoding': 'word[0] is Nat bit0; original report order retained',
                'computational_namespace': 'Jsp404.N4R2RowDataReplay',
                'actual_soundness_bridge': 'Jsp000404.N4R2RowDataReplaySoundness',
                'complete_words': len(words), 'referenced_cycles': len(cycle_ids),
                'excluded_unused_registry_cycles': len(paths) - len(cycle_ids),
                'cycle_id_order': cycle_ids, 'cycle_chunk': CYCLE_CHUNK, 'leaf_chunk': LEAF_CHUNK,
                'module_kinds': kinds, 'source_hashes': source_hashes,
                'kernel_check_order': cycle_modules + [library_module] + checked_modules + [all_module],
                'leaf_library_strategy': 'Each block referenced union, compact local0..k-1 indices; no full CycleLibrary import',
                'leaf_proof_strategies': proof_strategies,
                'regenerated_named_leaf_blocks': regenerated_blocks,
                'source_only_leaf_data_previews': leaf_modules,
                'leaf_local_cycle_maps': local_cycle_maps,
                'selected_final': 'Jsp404.N4R2ReplayData.all_leaves_checked',
                'not_claimed': ['Any source compiled', 'All-word kernel coverage', 'Original eight-point theorem']}
    (ROOT / MANIFEST).write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'status': manifest['status'], 'files': len(modules), 'cycles': len(cycle_ids),
                      'words': len(words), 'cycle_modules': len(cycle_modules),
                      'leaf_check_modules': len(checked_modules), 'source_bytes': sum((ROOT / path).stat().st_size for path in source_hashes)}))


if __name__ == '__main__':
    main()
