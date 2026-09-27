# JSP404-MIXED-STAR-EXCLUSION-01 — build record (2026-09-25)

Base: 55188de88ab30127bdae520900a046330b21ac84 (Owner).

## Module builds
- `lake build Jsp000404.MixedStarExclusion` → Build completed successfully (8957 jobs).

## Full-root build
- `lake build` (default target, root `Jsp000404.lean`, which imports
  ProjectionDescent, StarReceiver, MixedStarExclusion together with all
  existing modules) → **Build completed successfully (9003 jobs)**.
- First full-root attempt FAILED:
  `environment already contains 'Jsp404.gapScore_eq_zero_of_lt._proof_1_1'
  from Jsp000404.MaxGapCountermodel2` — a public name clash between
  `StarReceiver.gapScore_eq_zero_of_lt` (added in 55188de) and an
  existing lemma of the same name.  Module builds could not detect it.
  Consequence: at 55188de the full root did NOT build.  Fixed by renaming
  to `gapScore_zero_of_lt_two` (and `linRep_coe_of_mem` →
  `linRep_coe_eq_of_mem` in the new file, pre-emptively vs the private
  lemma in TwoAnchorCorridor).
- Remaining `declaration uses sorry` warnings in the full root are the
  pre-existing ones (Section4Legality:139, Deletion:1290/1298,
  GeometricDeletion:627, MainTheorem:11); none in ProjectionDescent,
  StarReceiver, MixedStarExclusion.  The `ring` "Try this" line is a
  pre-existing info message in ConeCorridor.lean:219.

## Axioms
`MIXED_STAR_AXIOMS.txt`: 21 `#print axioms` lines for the three new
modules, all `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
