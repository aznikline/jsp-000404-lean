# Actual capacity from bare finite cardinality exclusion

## Scope and status

Owned source: `Jsp000404/ActualCapacityFromCardinality.lean` only. All earlier
Safe/Uniform/Single/Inflation sources are frozen and unchanged. No root import,
root audit, normal/full Lake build, commit, publication, or quota operation was
performed by this agent.

The entire final source has a genuine combined-import strict PASS: all five
declared theorems are verified, and each prints exactly the standard three
axioms `[propext, Classical.choice, Quot.sound]`. The source is now frozen.

## PROVED generic interface

`Jsp404.ActualCapacityFromCardinality.potential_le_of_bare_exclusion`:

- `C >= 2`, `rho >= 0`;
- independent bare premise: for every `scale > rho` and every actual
  `d : Fin (C+1) -> Plane₂`, `Section4Legality d scale` is false;
- actual `c : Fin s -> Plane₂`, `s >= 3`, legal at `lam > rho`;
- arbitrary orientation `o` and nonzero reference `e`;
- conclusion: `potential lam (directionRows o e c) <= C`.

The theorem is **conditional on the displayed bare finite actual exclusion**.
It assumes no weighted capacity, global Kraft inequality, scalar realization,
row-score event, or hypothetical higher-strip terminal.

Let `F` be the original natural potential. If `F > C`, choose
`tau = (rho+lam)/2`, so `0 < tau < lam` and `rho < tau`. The frozen genuine
inflation theorem gives an actual configuration indexed by `Fin F`, legal at
`scale > tau`. The injective prefix `Fin.castLE : Fin (C+1) -> Fin F` inherits
legality: positive scale is unchanged, center injectivity composes, and each
triangle-angle bound is inherited by prefix injectivity. This contradicts the
bare exclusion at `scale > rho`. Nothing requires the final inflated row
scores to be zero.

## PROVED four threshold/regime adapters

The source uses already proved, independent actual exclusions:

1. `NoSatNineGeometry.nine_centres_angle_bound_impossible` at
   `lam > 2*pi/7`, yielding potential at most eight for all actual `s >= 3`.
2. `NoSatElevenGeometry.eleven_centres_angle_bound_impossible` at
   `lam > pi/4`, yielding potential at most ten for all actual `s >= 3`.
3. Original third-strip LOW: `floor(pi/lam)=3` and `pi/lam-3 < 1/2`
   imply `pi/lam < 7/2`, hence `lam > 2*pi/7` and `sendovCap 3 false = 8`.
4. Original third-strip HIGH: `floor(pi/lam)=3` and the strict floor upper
   inequality imply `pi/lam < 4`, hence `lam > pi/4` and
   `sendovCap 3 true = 10`. The bound itself needs no delta assumption.

These adapters do not modify or replace the older N3 capacity files.

## Remaining mathematics

The exact inflation-to-cardinality bridge is closed. The generic theorem does
not itself prove the required bare finite angle exclusion for an arbitrary
higher strip. In particular, no bare seventeen- or twenty-one-point exclusion
is asserted here. This receipt does not claim `allN`, the prize, or the original
goal complete.

## Validation

Final combined source, including both independent bare actual exclusions:

- SHA-256 `47e577e370be64cea9834c9b07d64783001211f3bdd0fbe78d073931eeee3e90`;
- real `lake env lean --trust=0` exit 0, five standard-three-axiom declarations,
  zero warnings, no cap interruption;
- elapsed 36.197 seconds; `/usr/bin/time -l` maximum RSS 6,000,476,160 bytes
  (5.588 GiB); sampled actual Lean peak 5,975,113,728 bytes;
- actual Lean admission cap 8 GiB; group peak 6,593,773,568 bytes was recorded
  only, not used as the admission criterion;
- raw log `.lake/actual-capacity-from-cardinality-final-strict-20261006.log`;
- real generated `.olean` at
  `.lake/build/lib/lean/Jsp000404/ActualCapacityFromCardinality.olean`.

The completed check's five declarations are:

1. `potential_le_of_bare_exclusion`;
2. `potential_le_eight_of_two_pi_sevenths_lt`;
3. `potential_le_ten_of_pi_quarter_lt`;
4. `third_strip_low_capacity`;
5. `third_strip_high_capacity`.

All owned Lean processes exited before the shared slot was explicitly released
to the next agent. The large combined import was checked once under the
coordinated 8-GiB cap; it was not repeatedly stopped at a smaller baseline cap.

Earlier minimal-import validation, before adding the four instances:

The minimal-import generic source, SHA-256
`50b9659be048567b27c3eb8aaf7438654fece69eea41979aab29a0f98d110f12`, passed
`lake env lean --trust=0` with real exit 0, zero warnings and exactly standard
three axioms `[propext, Classical.choice, Quot.sound]`. Its generated `.olean`
was real; it is not the eventual combined-source certificate.

Log: `.lake/actual-capacity-from-cardinality-generic-repair1-strict-20261006.log`.
Elapsed 5.781 seconds; `/usr/bin/time -l` maximum RSS 3,141,550,080 bytes
(2.926 GiB); sampled actual Lean peak 3,127,033,856 bytes. The actual Lean
admission cap was 3.5 GiB and no cap interruption occurred. Group peak
3,829,006,336 bytes was recorded only, not used as the admission criterion.

The preceding source check exited 1 because tactic-local `have ... where`
was parsed outside the local proof context; it was corrected to a local
`have ... := by refine <...>` structure. That failed check is not a PASS.

Frozen final combined-source SHA-256:
`47e577e370be64cea9834c9b07d64783001211f3bdd0fbe78d073931eeee3e90`.
No literal `sorry`, `native_decide`, or custom axiom occurs in the source.

Frozen dependency source hashes:

- SingleSplitScorePreservation:
  `af04d663329454b62a170646b9af0c27ef8c5a939ff2435a74acfa7c124c0284`.
- ActualPotentialInflation:
  `fb922937f4ca56fa29f7a1ae9b789b46aaa24749bd68077d47d10ea4567b7abb`.
- NoSatNineGeometry:
  `577e031971d2574fb45072dd0d56ba347272300c3025f30560cc6af18bf99fb4`.
- NoSatElevenGeometry:
  `d8db9ff7c4fa8e1a47faa719e3917c9765f5cb4f847033f673eecf421ee110e0`.
