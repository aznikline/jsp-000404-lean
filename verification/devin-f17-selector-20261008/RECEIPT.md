# Receipt: Devin F17 selector lane (2026-10-08)

- Repo: https://github.com/aznikline/jsp-000404-lean
- Branch: `agent/devin-f17-selector-20261008`
- Base (parent of the lane commit): `c152f27739f3e1b5c6001c57b60956419fe0890e`
- Machine: Devin cloud VM `devin-box`, Linux x86_64, 8 CPUs, 31 GiB RAM (not the user's Mac)
- Toolchain: `leanprover/lean4:v4.34.0` (Lean 4.34.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b), Lake 5.0.0-src+293d5d0
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (lake-manifest, unchanged); dependency oleans via `lake exe cache get`
- Resource guards: every run under `timeout 1800` and `/usr/bin/time` (max RSS recorded, peak 7.02 GB)

## Files (all new; nothing else modified)

| file | sha256 |
|---|---|
| `Jsp000404/DevinF17Selector.lean` | `15d528695b3beab771ab7b1740a2572a8379c0cb12fc12d25dcd310179c280f9` |
| `.lake/build/lib/lean/Jsp000404/DevinF17Selector.olean` (not committed) | `e03102526db1af315d203a2d5dc27dffccf82cc3ecc10c2b108378093866ec53` |
| `Jsp000404/DevinF17HullGap.lean` (unchanged, = base) | `3b02d377d28a025e82eb574055b143bf3da7acfa0a1956b9b0b731817314b615` |

`git diff --stat c152f27` before commit: empty (only untracked new files).

## Checks

1. Strict trust 0: `lake env lean --trust=0 Jsp000404/DevinF17Selector.lean` exit 0, no warnings (`attempts/a02-trust0.*`).
2. Genuine target: `lake build Jsp000404.DevinF17Selector` exit 0,
   `ℹ [8998/8998] Built Jsp000404.DevinF17Selector (3.6s)`, `Build completed successfully (8998 jobs).`
   (`attempts/a03-build.*`; `prebuild_state.txt` shows no prior olean, `postbuild_state.txt` the fresh one).
3. Axioms (`AxiomCheck.lean`, trust 0, `attempts/a04-axiomcheck.*`), every exported declaration:
   `gapScore_wrapGap_le_rowScore`, `outside_score_le_rowScore`, `restricted_score_eq`,
   `zero_observer_outside_lt_three`, `two_zero_observers_not_both_wide`,
   `boundary_event_zero`, `boundary_event_unique`, `hull_observer_windows`
   -> `[propext, Classical.choice, Quot.sound]`.
4. Forbidden tokens (`sorry|admit|axiom|unsafe|native_decide|implemented_by|extern`) in the new
   source: none (`forbidden_scan.txt`).

## Scope

Structural reduction only (see `research/DEVIN_F17_SELECTOR_20261008.md`). The F17
selector (SEL) is NOT proved; all-N lower bound for `N >= 17` remains OPEN.
