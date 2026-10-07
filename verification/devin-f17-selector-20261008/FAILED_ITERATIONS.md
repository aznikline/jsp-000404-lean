# Iteration record, Devin F17 selector lane (2026-10-08)

Every Lean run of the new module went through `tools/run.sh`, which copies the source
bytes and their SHA-256 into `attempts/<tag>.source.lean` / `.source.sha256` BEFORE
the run and records command, start/end, host, exit code, wall time, max RSS and full
output.

| tag | command | source sha256 | exit | wall | result |
|---|---|---|---|---|---|
| a01-trust0 | `lake env lean --trust=0 Jsp000404/DevinF17Selector.lean` | 227ae23c…8c18 | 0 | 5.97 s | compiled; 3 linter warnings (unused `he`, `hpzero`, `hqzero` in `hull_observer_windows`, lines 245/248/249) |
| a02-trust0 | same | 15d52869…80f9 | 0 | 4.26 s | compiled, 0 warnings |
| a03-build | `lake build Jsp000404.DevinF17Selector` | 15d52869…80f9 | 0 | 7.48 s | `Built Jsp000404.DevinF17Selector (3.6s)`; 0 warnings from the new file (the 435 `warning` lines are replayed from pre-existing modules) |
| a04-axiomcheck | `lake env lean --trust=0 verification/devin-f17-selector-20261008/AxiomCheck.lean` | 15d52869…80f9 | 0 | 3.79 s | all 8 exports: `[propext, Classical.choice, Quot.sound]` |

The only edit between runs (a01 -> a02) removed the three unused hypotheses; the
pre-edit bytes are preserved in `attempts/a01-trust0.source.lean`.

Scope of this record: it covers runs of the new module made after `tools/run.sh`
existed (from a01 on). There were no failing compiles of `DevinF17Selector.lean` in
this lane. Numeric (Python) controls are not Lean attempts; one Python failure is
noted for completeness: the first high-precision replay failed with
`ModuleNotFoundError: No module named 'mpmath'`; `pip install mpmath` was then run and
`controls/verify_controls.py` succeeded.

Historical gap (unchanged, not fabricated): the previous cloud lane
(`agent/devin-f17-hull-gap-20261008`) did NOT preserve the source bytes of its early
failed iterations; see `verification/devin-f17-hull-gap-20261008/FAILED_ITERATIONS.md`.
Those bytes are not reconstructed here.
