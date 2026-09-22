# Integration audit, 22 September 2026

This checkpoint is **partial coverage**, not a completed JSP-000404
submission. The arbitrary-N upper bound is now proved. The arbitrary-N
lower bound is still open.

## Integrated revisions

- `lane/integration @ edef86b0d216e7e535a81802d9d43ee6a60b8478`:
  the user's designated wave-1/2 trunk.
- `agent/jsp404-l2-l3-strict-01-owner @
  b436a89e72bda007d970f230f95806ed61eacec6`: merged with the existing
  cache/log exclusions retained. The saturation chain and strict-checker
  research are available together.
- `agent/jsp404-angle-cert-goal-01-owner @
  d66a6ab9cbe324d3353dbe7300880fb438838589`: imported only `Base3.lean`,
  `Base3Bridge.lean`, the additive proof extensions in `Deletion.lean`
  and `GeometricDeletion.lean`, and `Induction.lean`. Research scripts
  and superseded status documents were not imported. Author credit remains
  with the source branch and its recorded contributors, including Devin.
- Upper constructions from `superpilot69/awards @
  722cb3caa86710c788296ca0ec954a79e9a0adcc` are retained unchanged in
  `ThirdParty/Sendov`, with license, attribution and source hashes.

The local mathlib cache was reused. A successful local build does not
constitute an independent clean-room rebuild or external kernel replay.

## Corrections to the integration contract

1. The old `GadgetSelection.low` was false even independently of the
   ghost-vertex defect. It allowed lambda = 3 pi and n = 0. Two distinct
   points satisfy the triangle condition vacuously but contribute at
   least two to a claimed capacity of one.
   `IntegrationCounterexample.not_legacySelectionLow` proves this using
   only the standard Lean axioms. The corrected selection fields require
   lambda <= pi. The existing count-bound callers already had the stronger
   lambda < pi condition.
2. Direction charts now explicitly require a nonzero reference vector.
   This condition was already required by the geometric counting theorem
   and is now also passed through the selection interface.
3. The previously arbitrary `big` argument of `staircase_of_legality`
   is constrained: choosing the low cap requires fractional part < 1/2.
   The new condition matches the existing conditional induction theorem.
4. Sharpness is now stated as arbitrarily close upper configurations:
   for every epsilon > 0 there are exactly N distinct points with all
   angles < alphaN N + epsilon. This is the original sharp universal
   threshold formulation. The old placeholder demanded exact attainment
   by an ordinary configuration, which is an additional requirement and
   was not established. `sendov_alpha_eq_of_selection` explicitly
   connects the corrected two-sided formulation to the genuine geometric
   extremal quantity.

## Completed proof paths

- `sendov_upper`: unconditional, all N >= 3, both bands and all positive
  errors. Its transitive axioms are exactly `propext`, `Classical.choice`,
  `Quot.sound`.
- `sendov_lower_three`: unconditional N = 3 lower bound.
- `Base3` / `Base3Bridge`: three-center capacities and their actual
  geometric instantiation.
- `Induction`: geometric deletion and the exponent/potential/Kraft
  bridges. `potential_le_sendovCap` and `staircase_of_cert` remain
  conditional on `CertExists`; that parameter is not a proved theorem.
- `SaturatedStructure`: B1, L2-min, full L2 and L3, with standard axioms.

## Remaining obligations for the full goal

The statement “only two OPEN nodes” describes the active gadget lanes,
not yet the full theorem's dependency graph.

One complete arbitrary-size capacity route must be closed:

- **Gadget route:** prove the low/high consequences for faithful
  skeletons and construct the geometry-to-skeleton adapter, including
  position injectivity, floor-cell nonnegativity, remainder/angle
  semantics, and exponent normalization. `Proper` alone only asserts
  position injectivity. Checker evidence with nonnegative cells does not
  prove a statement over unrestricted integer cells.
- **Geometric route:** prove the progress/certificate or Kraft packing
  theorem for arbitrary center counts, then finish the n = 1 boundary
  and connect `staircase_of_cert` to the final lower-bound pipeline.

The existing `HighSelection.gadgetSelection_high` concerns `Skeleton 4`;
it is not an arbitrary-center high theorem. Likewise, an s = 4 census
cannot prove the arbitrary-s vacuum lemma. The stronger saturation
invariant does not by itself bound every possible deficit profile.

Finally prove `sendov_lower` without placeholders, audit both root
dependency closures and statement correspondence, rebuild the submitted
revision, pin its full SHA, and prepare the complete-proof reference PR
under the awards repository's submission requirements. Until then, no
complete-proof or prize claim should be made.
