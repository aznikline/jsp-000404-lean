#!/usr/bin/env python3
"""Export ordinary V2 certificates with proved support-prefix contradictions.

No solver is run. Original diagnostics and trees are SHA-bound; all new bound
hypotheses are derived inside the actual ModelSix theorem before its Nat closure.
Frozen V1 sources and the unverified cohort3 V1 snapshot are never rewritten.
"""
from pathlib import Path
import argparse
import contextlib
import hashlib
import io
import json
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEFECTS = {0: 2, 1: 3, 3: 3, 4: 2}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def nat_sum(names):
    result = names[-1]
    for name in reversed(names[:-1]):
        result = f'{name} + ({result})'
    return result


def support_prune(node, positive):
    for i, special in ((0, 0), (4, 4)):
        keys = sorted(positive[i] - {special})
        if len(keys) > 1:
            return {'core': [f'hminend{i}'] + [f'hcase{i}{k}1b' for k in keys[:2]],
                    'new_leaf_kind': 'proved_unit_endpoint_count'}
    for i, c in DEFECTS.items():
        keys = sorted(positive[i])
        if len(keys) > c:
            return {'core': [f'hmincount{i}'] + [f'hcase{i}{k}1b' for k in keys[:c + 1]],
                    'new_leaf_kind': 'proved_active_count'}
    if 'core' in node:
        return node
    i, k = node['i'], node['k']
    children = []
    for arm, child in enumerate(node['children']):
        state = {j: set(values) for j, values in positive.items()}
        if arm:
            state[i].add(k)
        children.append(support_prune(child, state))
    return {'i': i, 'k': k, 'children': children}


def dependency_prune(node):
    if 'core' in node:
        return node, set(node['core'])
    i, k = node['i'], node['k']
    children = [dependency_prune(child) for child in node['children']]
    arms = [{f'hcase{i}{k}{arm}{suffix}' for suffix in 'ab'} for arm in range(2)]
    for arm, (child, deps) in enumerate(children):
        if not deps & arms[arm]:
            return child, deps
    return ({'i': i, 'k': k, 'children': [child for child, deps in children]},
            set().union(*(deps - arm for (child, deps), arm in zip(children, arms))))


def leaf_count(node):
    return 1 if 'core' in node else sum(leaf_count(child) for child in node['children'])


def helper_hashes():
    receipts = (
        ROOT / 'research/JSP404_SIX_SYMBOLIC_ACTIVE_COUNT_BOUND_RECEIPT_20261006.json',
        ROOT / 'research/JSP404_SIX_SYMBOLIC_V2_UNIT_HELPER_RECEIPT_20261006.json',
    )
    result = {}
    for path in receipts:
        receipt = json.loads(path.read_text())
        assert receipt['status'] == 'PASS'
        assert {item['stage'] for item in receipt['results']} == {'strict', 'normal'}
        assert sha(ROOT / receipt['source']) == receipt['source_sha256']
        result[receipt['source']] = receipt['source_sha256']
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mask', type=int, required=True)
    args = parser.parse_args()
    mask = args.mask
    helpers = helper_hashes()
    assert not list((ROOT / 'Jsp000404').glob(f'SixExactFloorKernelSymbolicV2Mask{mask:03d}*.lean'))
    old_generator = ROOT / 'tools/export_six_symbolic_mask_kernel_20261006.py'
    assert sha(old_generator) == 'b46199ae8d60ff503699b1dc1139c13a9551861622e8ba3bfa9d98a204677194'
    cases = json.loads((ROOT / 'research/JSP404_SIX_SYMBOLIC_REPS_DIAGNOSTIC_20261006.json').read_text())['results']
    case = next(case for case in cases if case['mask'] == mask)
    tree_cases = json.loads((ROOT / 'research/JSP404_SIX_SYMBOLIC_REPS_TREE_SIZES_20261006.json').read_text())['results']
    tree_case = next(case for case in tree_cases if case['mask'] == mask)
    assert sha(ROOT / case['private_diagnostic_path']) == case['private_diagnostic_sha256']
    assert sha(ROOT / tree_case['private_tree_path']) == tree_case['private_tree_sha256']
    assert tree_case['fingerprint_sha256'] == case['fingerprint_sha256']
    report = json.loads((ROOT / case['private_diagnostic_path']).read_text())
    tree_data = json.loads((ROOT / tree_case['private_tree_path']).read_text())
    old_tree = dependency_prune(tree_data['tree'])[0]
    tree_data['tree'] = dependency_prune(support_prune(tree_data['tree'], {i: set() for i in DEFECTS}))[0]
    bounds = {f'hmincount{i}': f'{nat_sum([f"u{i}{k}" for k in range(5)])} ≤ {c}'
              for i, c in DEFECTS.items()}
    bounds.update({'hminend0': f'{nat_sum([f"u0{k}" for k in range(1, 5)])} ≤ 1',
                   'hminend4': f'{nat_sum([f"u4{k}" for k in range(4)])} ≤ 1'})
    fingerprint = {
        'original_complete_model_fingerprint_sha256': case['fingerprint_sha256'],
        'mask': mask, 'profile': '(2,3,*,3,2)', 'n_domain': 'Nat n>=4',
        'delta_domain': '[1/2,1)', 'added_integer_bounds': bounds,
        'proved_helper_source_hashes': helpers,
        'pruning': 'Keep both min arms unless a complete proof is independent; positive-prefix overflow is closed by ordinary Omega.',
        'generator_sha256': sha(Path(__file__).resolve()),
        'original_generator_sha256': sha(old_generator),
        'all_leaf_constraints': tree_data,
    }
    fp_sha = hashlib.sha256(json.dumps(fingerprint, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    import probe_six_symbolic_cycles_20261005 as p
    with tempfile.TemporaryDirectory(prefix=f'jsp404-v2-{mask}-') as temporary:
        temp = Path(temporary)
        (temp / 'research').mkdir()
        (temp / 'Jsp000404').mkdir()
        (temp / f'research/JSP404_SIX_SYMBOLIC_CYCLES_M{mask}_BUNBOUNDED_MIN_20261005.json').write_text(json.dumps(report))
        (temp / f'research/JSP404_SIX_SYMBOLIC_M{mask}_INTEGER_TREE_PRUNED_20261006.json').write_text(json.dumps(tree_data))
        p.ROOT = temp

        def emit_actual_v2(selected_mask):
            with contextlib.redirect_stdout(io.StringIO()):
                p.emit_min_probe(selected_mask)
            raw = temp / f'Jsp000404/SixExactFloorKernelSymbolicMask{mask:03d}Probe.lean'
            text = raw.read_text().replace('SixExactFloorKernelSymbolicMask', 'SixExactFloorKernelSymbolicV2Mask')
            text = text.replace('symbolic_mask', 'symbolic_v2_mask')
            text = text.replace('import Jsp000404.SixExactFloorKernelSymbolicInterval\n',
                'import Jsp000404.SixExactFloorKernelSymbolicInterval\n'
                'import Jsp000404.SixSymbolicUnitEndCountBound\n'
                'import Mathlib.Tactic.Ring\n')
            rows = p.row_orders(mask)

            def gaps(i):
                ds = [f'M.d {a} {b}' for a, b in rows[i]]
                return [f'({ds[0]} - M.theta {i})'] + [f'({ds[k + 1]} - {ds[k]})' for k in range(3)] + [f'(M.theta {i} + ((n : ℝ) + M.delta) - {ds[3]})']

            proofs = []
            for i, c in DEFECTS.items():
                gs = gaps(i)
                proofs += [f'  have hspan{i} : ' + ' + '.join(gs) + ' = (n : ℝ) + M.delta := by ring',
                           f'  have hmincount{i} : {bounds[f"hmincount{i}"]} :=',
                           f'    active_count_le_defect n {c} ' + ' '.join([f's{i}{k}' for k in range(5)] + [f'u{i}{k}' for k in range(5)]) +
                           ' M.delta ' + ' '.join(gs) + f' hsum_nat{i} hspan{i} ' +
                           ' '.join(f'hgap{i}{k}b' for k in range(5)) + ' hdelta1']
            gs = gaps(0)
            first = rows[0][0]
            proofs += [f'  have hunit0 : 1 ≤ {gs[0]} := by linarith only [hc{first[0]}{first[1]}a]',
                       f'  have hscoreunit0 : (s00 : ℝ) + 1 ≤ {gs[0]} := by',
                       f'    change ((⌊{gs[0]}⌋₊ - 1 : ℕ) : ℝ) + 1 ≤ {gs[0]}',
                       f'    exact unit_gap_score_lower {gs[0]} hunit0',
                       f'  have hminend0 : {bounds["hminend0"]} :=',
                       '    unit_first_active_count_le_one n ' + ' '.join([f's0{k}' for k in range(5)] + [f'u0{k}' for k in range(1, 5)]) +
                       ' M.delta ' + ' '.join(gs) + ' hsum_nat0 hspan0 hscoreunit0 ' + ' '.join(f'hgap0{k}b' for k in range(1, 5)) + ' hdelta1']
            gs = gaps(4)
            last = rows[4][-1]
            proofs += [f'  have hunit4 : 1 ≤ {gs[4]} := by linarith only [hc{last[0]}{last[1]}b]',
                       f'  have hscoreunit4 : (s44 : ℝ) + 1 ≤ {gs[4]} := by',
                       f'    change ((⌊{gs[4]}⌋₊ - 1 : ℕ) : ℝ) + 1 ≤ {gs[4]}',
                       f'    exact unit_gap_score_lower {gs[4]} hunit4',
                       f'  have hminend4 : {bounds["hminend4"]} :=',
                       '    unit_last_active_count_le_one n ' + ' '.join([f's4{k}' for k in range(5)] + [f'u4{k}' for k in range(4)]) +
                       ' M.delta ' + ' '.join(gs) + ' hsum_nat4 hspan4 ' + ' '.join(f'hgap4{k}b' for k in range(4)) + ' hscoreunit4 hdelta1']
            anchor = f'  have {tree_data["selected_cut_names"][0]} : '
            assert text.count(anchor) == 1
            text = text.replace(anchor, '\n'.join(proofs) + '\n' + anchor)
            final = next(line for line in text.splitlines() if line.startswith(f'  exact symbolic_v2_mask{mask}_integer_closure '))
            added = ' '.join(bounds)
            # New base bounds follow the existing per-variable u bounds internally;
            # the public closure accepts them immediately before the min equalities.
            needle = ' (by rfl)'
            assert needle in final
            changed = final.replace(needle, ' ' + added + needle, 1)
            text = text.replace(final, changed)
            path = temp / f'Jsp000404/SixExactFloorKernelSymbolicV2Mask{mask:03d}Probe.lean'
            path.write_text(text)

        script = old_generator.read_text()
        script = script.replace('ROOT=Path(__file__).resolve().parents[1]', f'ROOT=Path({str(temp)!r})', 1)
        script = script.replace('SixExactFloorKernelSymbolicMask', 'SixExactFloorKernelSymbolicV2Mask')
        script = script.replace('symbolic_mask', 'symbolic_v2_mask')
        insertion = '\nbase += ' + repr(list(bounds.items())) + '\n'
        assert script.count('base_names=[n for n,_ in base]') == 1
        script = script.replace('base_names=[n for n,_ in base]', insertion + 'base_names=[n for n,_ in base]', 1)
        assert script.count('p.emit_min_probe(mask)') == 1
        script = script.replace('p.emit_min_probe(mask)', '_emit_actual_v2(mask)', 1)
        saved_argv = sys.argv[:]
        sys.argv = [str(old_generator), '--mask', str(mask)]
        with contextlib.redirect_stdout(io.StringIO()):
            exec(compile(script, str(old_generator), 'exec'),
                 {'__file__': str(old_generator), '__name__': '__main__', '_emit_actual_v2': emit_actual_v2})
        assert len(p.NAMES) == len(set(p.NAMES)) == 41
        reflection_script = ROOT / 'tools/export_six_symbolic_cohort_reflection_20261006.py'
        reflection = reflection_script.read_text().replace('ROOT=Path(__file__).resolve().parents[1]', f'ROOT=Path({str(temp)!r})', 1)
        reflection = reflection.replace('SixExactFloorKernelSymbolicMask', 'SixExactFloorKernelSymbolicV2Mask').replace('symbolic_mask', 'symbolic_v2_mask')
        sys.argv = [str(reflection_script), '--proved-mask', str(mask)]
        with contextlib.redirect_stdout(io.StringIO()):
            exec(compile(reflection, str(reflection_script), 'exec'), {'__file__': str(reflection_script), '__name__': '__main__'})
        sys.argv = saved_argv
        sources = sorted((temp / 'Jsp000404').glob(f'SixExactFloorKernelSymbolicV2Mask{mask:03d}*.lean'))
        for source in sources:
            (ROOT / 'Jsp000404' / source.name).write_bytes(source.read_bytes())
        manifest = json.loads((temp / f'research/JSP404_SIX_SYMBOLIC_M{mask}_NAT_SHARDS_MANIFEST_20261006.json').read_text())
    path = ROOT / f'research/JSP404_SIX_SYMBOLIC_V2_M{mask}_NAT_SHARDS_MANIFEST_20261006.json'
    manifest.update({'mask': mask, 'fingerprint_sha256': fp_sha, 'fingerprint_payload': fingerprint,
                     'original_pruned_leaves': leaf_count(old_tree), 'pruned_tree': tree_data,
                     'status': 'SOURCE_ONLY_NOT_PROVED'})
    path.write_text(json.dumps(manifest, indent=2) + '\n')
    frozen = {'mask': mask, 'kernel': 'NOT_RUN', 'normal_lake': 'NOT_RUN',
              'source_hashes': {str((Path('Jsp000404') / source.name)): sha(ROOT / 'Jsp000404' / source.name) for source in sources},
              'helper_source_hashes': helpers, 'nat_shards': len(manifest['shards']),
              'nat_leaves': manifest['total_leaves'], 'fingerprint_sha256': fp_sha,
              'scope': 'All n>=4 HIGH common ModelSix critical profile; fixed direction and typed reflection only.'}
    freeze = ROOT / f'research/JSP404_SIX_SYMBOLIC_V2_MASK{mask}_SOURCE_FREEZE_20261006.json'
    freeze.write_text(json.dumps(frozen, indent=2) + '\n')
    print(json.dumps({'mask': mask, 'source_only': True, 'sources': len(sources),
                      'original_leaves': leaf_count(old_tree), 'v2_leaves': manifest['total_leaves'],
                      'nat_shards': len(manifest['shards']),
                      'bytes': sum((ROOT / 'Jsp000404' / source.name).stat().st_size for source in sources),
                      'fingerprint_sha256': fp_sha}))


if __name__ == '__main__':
    main()
