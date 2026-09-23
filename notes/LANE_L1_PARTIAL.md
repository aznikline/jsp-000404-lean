# Lane L1 (GadgetSelectionLowP) — partial results, lane cancelled

Status: **CHECKER-VALIDATED evidence, not Lean theorems.**  The lane was
cancelled mid-campaign; this note archives what the logs show.

## Target

`GadgetSelectionLowP`: proper + consistent skeleton with `W > 2`
carries a `Valid` gadget of bound ≥ 1/2.

## Approach taken (per LANE_B3 methodology)

Branch-taxonomy coverage scan over the 85,536 consistent W>2 skeletons
of the s=4 census (`tools/e2_census_s4.json`).  Three branch families
implemented in `tools/l1_cover.py` / `tools/l1_cover2.py`:

- `FANLINK(1fan,<=2links)`
- `FANLINK2`
- `LINK`

## Results

- Pilot (`l1_cover2_s4n4.json`): 400/400 covered, zero uncovered.
- Full campaign (`l1_cover2_s4.log`): interrupted at ~17,000/85,536
  after ~6,450s; **zero uncovered skeletons** at interruption.  Branch
  tally at 17k: FANLINK 7,476 / FANLINK2 1,936 / LINK 7,588.

## Status

Coverage is consistent with the branch taxonomy being complete at s=4,
but the scan is ~20% done — CHECKER-VALIDATED, not a proof.  The Lean
side (`GadgetSelectionLowP` branch lemmas + Kraft-style completeness)
was not reached.
