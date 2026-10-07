# Devin F17 selector independent local verification — 2026-10-08

The exact returned module passed first-attempt local strict compilation and a genuine normal target build. All eight public theorem exports are printed by the source and passed the standard-axiom check in both runs. No source or API repair was made. This receipt verifies the module and its helper results; it does not claim a full F17 exclusion or a full-project build.

## Frozen source

- Commit: `949828570a670b3e4b6dc42538246b14d9bccac0` from `origin/agent/devin-f17-selector-20261008`.
- Source: `Jsp000404/DevinF17Selector.lean`, 265 lines.
- Source SHA256: `15d528695b3beab771ab7b1740a2572a8379c0cb12fc12d25dcd310179c280f9`.
- Sole direct import: `Jsp000404.DevinF17HullGap`.
- Frozen Gap source SHA256: `3b02d377d28a025e82eb574055b143bf3da7acfa0a1956b9b0b731817314b615`.

The source bytes were verified against the fixed commit before execution. The source and Gap dependency stayed unchanged before and after both local checks. The Gap bytes also match the returned commit and were previously checked locally with a complete fourteen-export strict audit.

## Local acceptance

Both stages ran sequentially under the Root-authorized exclusive slot with an 8 GiB process-tree RSS guard, a 180-second time guard, and a global maximum of one Lean process. Every local attempt preserved its exact input bytes and full raw output before execution.

| Stage | Attempt | Result / exit | Seconds | Peak tree RSS (KiB) | Public exports checked |
| --- | --- | --- | --- | --- | --- |
| strict | 1 | PASS / 0 | 39.486 | 5515504 | 8 |
| normal | 1 | PASS / 0 | 42.224 | 5325488 | 8 |

The strict run used `--trust=0 -M8192 -DautoImplicit=false`. The genuine normal run reported `Built Jsp000404.DevinF17Selector` and `Build completed successfully`. All eight exports depend only on `propext`, `Classical.choice`, and `Quot.sound`. There were no owned source warnings, no local failed attempts, no guard stops, and no local source changes. The eight source prints cover all eight public theorem exports exactly, so no separate import audit was required.

`checkpoint.json` records full commands, timings, RSS peaks, source/raw/artifact hashes, and the eight axiom reports for each run. Exact source snapshots and raw outputs are `strict-attempt01.*` and `normal-attempt01.*`. `final-result.json` cross-checks the full public theorem list against both outputs and records the actual normal build confirmation.

## Cloud history remains distinct

The returned cloud lane's original `FAILED_ITERATIONS.md` is saved unchanged as `cloud-iteration-history.reference.md`. That record preserves the selector lane's warning-only first candidate and subsequent final acceptance runs. It also explicitly records that the predecessor hull-gap cloud lane did not preserve source bytes of its early failed iterations. Those missing predecessor bytes are not reconstructed or represented as locally preserved here. Independent local acceptance does not erase that historical gap.

## Complete export list

- `Jsp404.DevinF17Selector.gapScore_wrapGap_le_rowScore`
- `Jsp404.DevinF17Selector.outside_score_le_rowScore`
- `Jsp404.DevinF17Selector.restricted_score_eq`
- `Jsp404.DevinF17Selector.zero_observer_outside_lt_three`
- `Jsp404.DevinF17Selector.two_zero_observers_not_both_wide`
- `Jsp404.DevinF17Selector.boundary_event_zero`
- `Jsp404.DevinF17Selector.boundary_event_unique`
- `Jsp404.DevinF17Selector.hull_observer_windows`

The exclusive slot was formally returned to Root immediately after the normal process exited. No full-project, t3, or further target check was started under this lease.
