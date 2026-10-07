# Devin F17 hull-gap independent local verification — 2026-10-08

The frozen returned source passed first-attempt local strict compilation, a genuine normal target build, and a separate strict import audit covering all fourteen public theorem exports. No local source repair was made. This verifies this module and its exported results; it does not claim an F17 selector or an all-model exclusion.

## Source provenance

- Fixed Git commit: `c152f27739f3e1b5c6001c57b60956419fe0890e` from the returned `origin/agent/devin-f17-hull-gap-20261008` branch.
- Source: `Jsp000404/DevinF17HullGap.lean`, 561 lines.
- SHA256: `3b02d377d28a025e82eb574055b143bf3da7acfa0a1956b9b0b731817314b615`.
- Copied byte-for-byte from that commit only into the previously absent source path. The cloud returned byte-copy has the same hash. The source was unchanged throughout all local acceptance runs.
- Local directory: `verification/oct8-devin-f17-hull-gap-local/`.

## Local acceptance

Each stage ran sequentially under the Root-authorized sole slot, with an 8 GiB process-tree RSS guard, a 180-second time guard, and a global maximum of one Lean process. Each stage saved its exact input bytes and full raw output before execution. All three stages exited successfully with no guard stop.

| Stage | Attempt | Result / exit | Seconds | Peak tree RSS (KiB) | Printed declarations |
| --- | --- | --- | --- | --- | --- |
| strict | 1 | PASS / 0 | 65.533 | 4814608 | 7 |
| normal | 1 | PASS / 0 | 71.437 | 4606416 | 7 |
| audit | 1 | PASS / 0 | 51.886 | 4783360 | 14 |

The strict source run used `--trust=0 -M8192 -DautoImplicit=false`. The genuine normal run reported `Built Jsp000404.DevinF17HullGap` and `Build completed successfully (8997 jobs)`. The final independent `AxiomCheck.lean` import run also used `--trust=0 -M8192 -DautoImplicit=false` and printed all fourteen exports. Every audited export depends only on `propext`, `Classical.choice`, and `Quot.sound`. No owned source warnings, local failed attempts, or local repairs occurred.

Raw outputs and exact snapshots are `strict-attempt01.*`, `normal-attempt01.*`, and `audit-attempt01.*`. Full commands, timings, RSS peaks, axiom lists, and artifact hashes are recorded in `checkpoint.json`. `final-result.json` cross-checks the complete fourteen-theorem source list against the independent audit output.

## Cloud provenance limitation and scope correction

The returned source itself prints seven declarations. The cloud's separate `AxiomCheck.lean` prints eight declarations, not all fourteen theorem exports. Thus the earlier cloud description of auditing every export overstated that audit's scope. The independent local fourteen-export audit supplies the complete export check without changing the frozen cloud source.

The cloud `FAILED_ITERATIONS.md` records diagnostic transcripts from early interactive list-layer development, but explicitly states that those intermediate source bytes were edited in place and were not preserved. This local receipt does not reconstruct or claim to preserve those cloud early-failure candidate bytes. Local acceptance was first-pass throughout, so there are no local failed candidate bytes to preserve.

## Complete local export audit

- `Jsp404.DevinF17HullGap.wrapGap_congr`
- `Jsp404.DevinF17HullGap.wrapGap_eq_of_head_lt_getLast`
- `Jsp404.DevinF17HullGap.wrapGap_eq_of_getLast_lt_head`
- `Jsp404.DevinF17HullGap.gapScore_add_right_of_mergeGain_zero`
- `Jsp404.DevinF17HullGap.gapScore_add_left_of_mergeGain_zero`
- `Jsp404.DevinF17HullGap.wrap_step`
- `Jsp404.DevinF17HullGap.dirRep_window`
- `Jsp404.DevinF17HullGap.row_pairwise_lt`
- `Jsp404.DevinF17HullGap.theta_transport`
- `Jsp404.DevinF17HullGap.row_wrap`
- `Jsp404.DevinF17HullGap.isHullVertex_restrict`
- `Jsp404.DevinF17HullGap.targets_and_observer_distinct`
- `Jsp404.DevinF17HullGap.actual_zero_pair_outside_gap_plateau_of_windows`
- `Jsp404.DevinF17HullGap.actual_zero_pair_outside_gap_plateau`

All local Lean/Lake processes had exited when the formal slot was returned to Root. No Selector, HA, t3, or full-project check was started under this lease.
