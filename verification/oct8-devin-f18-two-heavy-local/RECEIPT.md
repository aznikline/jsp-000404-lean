# Devin F18 two-heavy independent local verification — 2026-10-08

The exact returned source passed first-attempt local strict compilation and a genuine normal target build. All seven public theorem exports are printed by the source and passed the standard-axiom check in both runs. No local source or API repair was made. This receipt covers the returned two-heavy module, not a full-project build or an all-potential/all-N result.

## Source provenance

- Fixed Git commit: `0a47a3bb20c0e92277cb96147acf09ffe4ffc811` from `origin/agent/devin-f18-two-heavy-20261008`.
- Source: `Jsp000404/DevinF18TwoHeavyApex.lean`.
- SHA256: `13caf59d07692d00826884a7419ca5a296c39ae9323904a236c4677bb37506a4`.
- Exact source line count: 842. The supplied 838-line description was stale; the supplied hash matched exactly.
- The source was copied byte-for-byte from the fixed commit into a previously absent path, and stayed unchanged throughout local verification.
- Cloud metadata is saved unchanged as `cloud-manifest.reference.json`. Its cloud results remain reference evidence, separate from the local runs below. The returned Git commit includes cloud development snapshots and raw outputs; no cloud attempt is relabeled as a local attempt.

## Local acceptance

Each stage ran sequentially in the Root-authorized exclusive slot with an 8 GiB process-tree RSS guard, a 180-second time guard, and a global maximum of one Lean process. Exact source snapshots and full raw outputs were preserved for each local attempt. Both runs exited successfully without a guard stop.

| Stage | Attempt | Result / exit | Seconds | Peak tree RSS (KiB) | Public exports checked |
| --- | --- | --- | --- | --- | --- |
| strict | 1 | PASS / 0 | 64.973 | 5082608 | 7 |
| normal | 1 | PASS / 0 | 52.193 | 5262112 | 7 |

Strict compilation used `--trust=0 -M8192 -DautoImplicit=false`. The normal run reported an actual `Built Jsp000404.DevinF18TwoHeavyApex` and `Build completed successfully`. Both runs printed all seven public theorem exports, each depending only on `propext`, `Classical.choice`, and `Quot.sound`. There were no owned source warnings, local failures, or local source repairs. A separate import audit was unnecessary because the seven source prints cover all seven public theorems exactly.

Full commands, resource measurements, source/raw/artifact hashes, and selected axiom lists are in `checkpoint.json`. Source snapshots and raw logs are `strict-attempt01.*` and `normal-attempt01.*`. `final-result.json` checks the seven-theorem export list against both run outputs and records the normal build confirmation.

## Frozen dependency source check

Before launch, all four seeded dependencies and the two other direct imports were compared byte-for-byte with the fixed returned Git commit. All matched. The local checker required these same hashes before and after each run; none changed.

| Dependency | Role | SHA256 |
| --- | --- | --- |
| `Jsp000404/ActualF18NonacuteApex.lean` | seed | `81d57f6a76b22cac68812da5d93f086184d640bddabebb1f784bad5eeca52724` |
| `Jsp000404/ActualF18ClassWeight.lean` | seed | `6b27bf26bcc615cee3fe39d21bb333b299204ada005aa8691b48f71a3b318818` |
| `Jsp000404/ActualF18InteriorApex.lean` | seed | `4c6588c97fbf99d93534fb77896c18632a7d4a14b7492cd73960331b4e733dce` |
| `Jsp000404/ActualHeavyClumpWeight.lean` | seed | `25de371c7fad631f6217b38f56e3d73e1525b4678a4167d8a1c82e1170994936` |
| `Jsp000404/ActualMixedRigidCardinality.lean` | direct import | `e1bc970f177de68d3eb6adc13a7e7e5c28b0d38f4decacaa0e336e411c72d9bd` |
| `Jsp000404/ActualHullTurnBudget.lean` | direct import | `b4b93a4bb7dfa6a672fff558d3752871729c62545c246b3cf78d443228a356fc` |

## Complete export list

- `Jsp404.DevinF18TwoHeavyApex.actual_interior_apex_has_heavy_of_nonacute`
- `Jsp404.DevinF18TwoHeavyApex.actual_obtuse_heavy_interior_false`
- `Jsp404.DevinF18TwoHeavyApex.actual_two_interior_nonacute_heavy_false`
- `Jsp404.DevinF18TwoHeavyApex.actual_all_heavy_nonacute_interior_false`
- `Jsp404.DevinF18TwoHeavyApex.actual_F18_two_heavy_nonacute_interior_false`
- `Jsp404.DevinF18TwoHeavyApex.actual_obtuse_heavy_other_nonacute_false`
- `Jsp404.DevinF18TwoHeavyApex.actual_F18_two_heavy_false`

After the normal process exited, the exclusive slot was formally returned to Root immediately. No t3, Selector, or full-project check was started under this lease.
