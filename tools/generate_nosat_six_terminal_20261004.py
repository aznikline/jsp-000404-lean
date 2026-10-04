#!/usr/bin/env python3
"""Generate a kernel-checked six-point terminal using ordinary Lean tactics.

SMT selects a shared triangle-profile tree and subsets for linarith. It is
never a theorem premise or a trusted certificate. Complete triangle orders
give a strict order on every occupied row. For each cut witness we use just
its predecessor (or the maximum for the minimum witness), a necessary
linear inequality from the original occupied-cut hypothesis.
"""
import itertools
import json
import time
from pathlib import Path

import z3

ROOT = Path(__file__).resolve().parents[1]
N = 6
L, P = z3.Reals('lam p')
D = {(i, j): z3.Real(f'd{i}{j}') for i, j in itertools.combinations(range(N), 2)}


def get(i, j):
    return D[tuple(sorted((i, j)))]


def lean_d(i, j):
    a, b = sorted((i, j))
    return f'm.d {a} {b}'


def conjunction(atoms):
    return z3.And(*atoms)


def triangle(i, j, k):
    x, y, z = get(i, j), get(i, k), get(j, k)
    prefix = f'htr{i}{j}{k}'
    arms = [[x+L <= z, x < y, y < z, y-x <= P-L, z-y <= P-L],
            [z+L <= x, z < y, y < x, y-z <= P-L, x-y <= P-L]]
    lx, ly, lz = lean_d(i, j), lean_d(i, k), lean_d(j, k)
    lean_arms = [[f'{lx} + lam ≤ {lz}', f'{lx} < {ly}', f'{ly} < {lz}',
                  f'{ly}-{lx} ≤ p-lam', f'{lz}-{ly} ≤ p-lam'],
                 [f'{lz} + lam ≤ {lx}', f'{lz} < {ly}', f'{ly} < {lx}',
                  f'{ly}-{lz} ≤ p-lam', f'{lx}-{ly} ≤ p-lam']]
    return {'ijk': (i, j, k), 'names': [prefix+t for t in 'abcde'],
            'arms': arms, 'lean_arms': lean_arms,
            'expr': z3.Or(*[conjunction(a) for a in arms])}


TRI = {f'tri{i}{j}{k}': triangle(i, j, k)
       for i, j, k in itertools.combinations(range(N), 3)}
BASE = {'hlam': L > 0, 'hp0': 3*L <= P, 'hp1': P < 4*L}
for (i, j), x in D.items():
    BASE[f'hd{i}{j}a'] = x >= 0
    BASE[f'hd{i}{j}b'] = x < P

stats = {'nodes': 0, 'linarith_leaves': 0, 'diagonal_leaves': 0,
         'max_depth': 0, 'profile_count': 0, 'profile_q_cases': 0,
         'diagnostic_only': True, 'leaf_proof': 'ordinary Lean linarith',
         'whole_strip': '3*lam <= p < 4*lam', 'range_lower_bound': '0 <= d'}
started = time.monotonic()
profile_ids = {}


def run(base, pending=None):
    solver = z3.SolverFor('QF_LRA')
    solver.set(timeout=10000, random_seed=0)
    for name, expr in base.items():
        solver.assert_and_track(expr, z3.Bool(name))
    for name, info in (pending or {}).items():
        solver.assert_and_track(info['expr'], z3.Bool(name))
    ans = solver.check()
    if ans == z3.unknown:
        raise RuntimeError(solver.reason_unknown())
    return ans, ([str(x) for x in solver.unsat_core()] if ans == z3.unsat else solver.model())


def all_profiles():
    solver = z3.SolverFor('QF_LRA')
    solver.set(timeout=10000, random_seed=0)
    solver.add(*BASE.values())
    flags = {name: z3.Bool('profile_'+name) for name in TRI}
    for name, info in TRI.items():
        solver.add(info['expr'], flags[name] == conjunction(info['arms'][0]))
    profiles = []
    while True:
        ans = solver.check()
        if ans == z3.unsat:
            break
        if ans == z3.unknown:
            raise RuntimeError(solver.reason_unknown())
        model = solver.model()
        profile = {name: 0 if z3.is_true(model.eval(flag)) else 1
                   for name, flag in flags.items()}
        profiles.append(profile)
        solver.add(z3.Or(*[flag != (profile[name] == 0) for name, flag in flags.items()]))
    return sorted(profiles, key=lambda p: tuple(p[name] for name in TRI))


def indent(lines):
    return ['  '+line for line in lines]


def contradiction(core):
    stats['linarith_leaves'] += 1
    if stats['linarith_leaves']+stats['diagonal_leaves'] > 30000:
        raise RuntimeError('Stopped at the authorized 30000-leaf size limit')
    return ['linarith only ['+', '.join(core)+']']


def row_cut(i, model):
    order = sorted([j for j in range(N) if j != i],
                   key=lambda j: model.eval(get(i, j)).as_fraction())
    choices = {}
    for n, j in enumerate(order):
        k = order[-1] if n == 0 else order[n-1]
        b, a = get(i, k), get(i, j)
        bound = b-a <= P-2*L if n == 0 else b+P-a <= P-2*L
        choices[j] = {'i': i, 'j': j, 'k': k, 'wrapped': n != 0, 'bound': bound}
    return {'i': i, 'choices': choices,
            'expr': z3.Or(*[choice['bound'] for choice in choices.values()])}


def cut_tree(base, pending, q, depth):
    stats['nodes'] += 1
    stats['max_depth'] = max(stats['max_depth'], depth)
    ans, core = run(base)
    if ans == z3.unsat:
        return contradiction(core)
    ans, core = run(base, pending)
    if ans != z3.unsat:
        raise RuntimeError(f'Necessary adjacent-cut model unexpectedly satisfiable at q={q}')
    candidates = [name for name in core if name in pending]
    # The cheapest available row is often itself impossible; take it first.
    def feasible_count(name):
        return sum(run({**base, '__trial': c['bound']})[0] == z3.sat
                   for c in pending[name]['choices'].values())
    chosen = min(candidates, key=lambda name: (feasible_count(name), name))
    info = pending[chosen]
    remaining = {name: value for name, value in pending.items() if name != chosen}
    i = info['i']
    lines = [f'obtain ⟨j{i}, hj{i}, hcut{i}⟩ := hpos {i} (by decide)', f'fin_cases j{i}']
    for j in range(N):
        lines.append('·')
        if j == i:
            stats['diagonal_leaves'] += 1
            lines.append(f'  exact hj{i} rfl')
            continue
        c = info['choices'][j]
        k = c['k']
        name = f'hraw{i}{j}{k}'
        cmpname = f'hcmp{i}{j}{k}'
        b, a = get(i, k), get(i, j)
        # The complete triangle profile determines this strict comparison.
        guard = b < a if c['wrapped'] else a <= b
        ans, cmpcore = run({**base, '__negcmp': z3.Not(guard)})
        if ans != z3.unsat:
            raise RuntimeError('Triangle profile failed to determine an occupied-row order')
        cmpcore = [name for name in cmpcore if name != '__negcmp']
        cmptype = f'{lean_d(i,k)} < {lean_d(i,j)}' if c['wrapped'] else f'{lean_d(i,j)} ≤ {lean_d(i,k)}'
        branch = [f'have {name} := hcut{i} {k} (by decide)',
                  f'change (if m.d {i} {k} < m.d {i} {j} then m.d {i} {k}+p-m.d {i} {j} else m.d {i} {k}-m.d {i} {j}) ≤ p-2*lam at {name}']
        used = ', '.join(f'hcanon{i}{other}' for other in (j, k) if i > other)
        if used:
            branch.append(f'simp only [{used}] at {name}')
        branch.append(f'have {cmpname} : {cmptype} := by linarith only [{", ".join(cmpcore)}]')
        simp = f'ite_eq_left {cmpname}' if c['wrapped'] else f'ite_eq_right (not_lt.mpr {cmpname})'
        branch.append(f'simp only [{simp}] at {name}')
        branch += cut_tree({**base, name: c['bound']}, remaining, q, depth+1)
        lines += indent(branch)
    return lines


def triangle_tree(base, pending, profiles, depth=0):
    stats['nodes'] += 1
    stats['max_depth'] = max(stats['max_depth'], depth)
    ans, core = run(base)
    if ans == z3.unsat:
        return contradiction(core)
    if not pending:
        if len(profiles) != 1:
            raise RuntimeError('Expected one complete orientation profile')
        idx = profile_ids[tuple(profiles[0][name] for name in TRI)]
        args = ['⟨'+', '.join(info['names'])+'⟩' for info in TRI.values()]
        return [f'exact six_profile_{idx:03d} m q hpos '+' '.join(args)]
    # Balanced splits share a single profile tree across all six q values.
    def score(name):
        a = sum(profile[name] == 0 for profile in profiles)
        b = len(profiles)-a
        return (max(a, b), name)
    chosen = min(pending, key=score)
    info = pending[chosen]
    remaining = {name: value for name, value in pending.items() if name != chosen}
    i, j, k = info['ijk']
    pat = '⟨'+', '.join(info['names'])+'⟩'
    lines = [f'rcases m.htr {i} {j} {k} (by decide) (by decide) with',
             '  '+pat+' | '+pat]
    for armno, arm in enumerate(info['arms']):
        branch_profiles = [p for p in profiles if p[chosen] == armno]
        lines += ['·']+indent(triangle_tree({**base, **dict(zip(info['names'], arm))},
                                           remaining, branch_profiles, depth+1))
    return lines


HEADER = '''import Jsp000404.MixedStarExclusion

/-! Ordinary six-point terminal on the whole strip `3λ ≤ p < 4λ`.
Every triangle has both endpoint caps. Five positive occupied rows already
contradict the necessary angle model; no zero, no-saturation, deletion,
minimality or metric realization hypothesis is used. The generator uses
SMT solely to select branches and linarith inputs. Every leaf is checked
by Lean's kernel. -/

namespace Jsp404.NoSatSixTerminal

structure SixModel (lam p : ℝ) where
  hlam : 0 < lam
  hp : 3*lam ≤ p ∧ p < 4*lam
  d : Fin 6 → Fin 6 → ℝ
  hsymm : ∀ i j, d i j = d j i
  hrange : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < p
  htr : ∀ i j k : Fin 6, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ p-lam ∧ d j k-d i k ≤ p-lam) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ p-lam ∧ d i j-d i k ≤ p-lam)

'''


def theorem_header(name, private=False):
    visibility = 'private ' if private else ''
    return f'''set_option maxHeartbeats 16000000 in
{visibility}theorem {name} {{lam p : ℝ}} (m : SixModel lam p) (q : Fin 6)
    (hpos : ∀ i : Fin 6, i ≠ q → ∃ j : Fin 6, j ≠ i ∧
      ∀ k : Fin 6, k ≠ i →
      (if m.d i k < m.d i j then m.d i k+p-m.d i j else m.d i k-m.d i j) ≤ p-2*lam)
'''


def model_setup(canonical=True):
    setup = ['have hlam := m.hlam', 'have hp0 := m.hp.1', 'have hp1 := m.hp.2']
    for i, j in D:
        setup += [f'obtain ⟨hd{i}{j}a, hd{i}{j}b⟩ := m.hrange {i} {j} (by decide)']
    if canonical:
        for i, j in D:
            setup += [f'have hcanon{j}{i} := m.hsymm {j} {i}']
    return setup


def main():
    profiles = all_profiles()
    stats['profile_count'] = len(profiles)
    stats['profile_helpers'] = len(profiles)
    print('Feasible whole-strip orientation profiles:', len(profiles), flush=True)
    source_parts = [HEADER]
    for idx, profile in enumerate(profiles):
        profile_ids[tuple(profile[name] for name in TRI)] = idx
        decl = theorem_header(f'six_profile_{idx:03d}', private=True)
        setup = model_setup()
        base = dict(BASE)
        for name, info in TRI.items():
            arm = profile[name]
            i, j, k = info['ijk']
            hname = f'htr{i}{j}{k}'
            decl += f'    ({hname} : '+ ' ∧ '.join(info['lean_arms'][arm])+')\n'
            setup += [f'rcases {hname} with ⟨'+', '.join(info['names'])+'⟩']
            base.update(zip(info['names'], info['arms'][arm]))
        decl += '    : False := by\n'
        ans, model = run(base)
        if ans != z3.sat:
            raise RuntimeError('Unexpected inconsistent enumerated complete profile')
        proof = setup+['fin_cases q']
        for q in range(N):
            stats['profile_q_cases'] += 1
            cuts = {f'cut{i}': row_cut(i, model) for i in range(N) if i != q}
            proof += ['·']+indent(cut_tree(base, cuts, q, 1))
        source_parts += [decl+'\n'.join(indent(proof))+'\n\n']
        if (idx+1) % 20 == 0:
            print('Generated profile helpers:', idx+1, 'linarith leaves:', stats['linarith_leaves'], flush=True)
    proof = model_setup(canonical=False)+triangle_tree(BASE, TRI, profiles)
    source_parts += [theorem_header('six_model_impossible')+'    : False := by\n'+
                     '\n'.join(indent(proof))+'\n\n',
                     '#print axioms six_model_impossible\nend Jsp404.NoSatSixTerminal\n']
    source = ''.join(source_parts)
    (ROOT/'Jsp000404/NoSatSixTerminal.lean').write_text(source)
    stats['elapsed_seconds'] = round(time.monotonic()-started, 3)
    stats['source_lines'] = len(source.splitlines())
    stats['source_bytes'] = len(source.encode())
    (ROOT/'research/JSP404_NOSAT_SIX_TERMINAL_GENERATOR_20261004.json').write_text(json.dumps(stats, indent=2)+'\n')
    print(json.dumps(stats, indent=2), flush=True)


if __name__ == '__main__':
    main()
