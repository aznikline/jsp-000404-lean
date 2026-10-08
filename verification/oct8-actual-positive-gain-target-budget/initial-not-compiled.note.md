# Actual positive-gain target budget — SOURCE_ONLY

New source `Jsp000404/ActualPositiveGainTargetBudget.lean` has 151 lines,
SHA `86bf7251854480fa6785d0abf802563018d147c5a90ff8e7a498e0f588ce6b07`.
This candidate has not been compiled. Its indexed merge dependency
`RowGainCyclicIncident.lean` is initially SOURCE_ONLY at SHA
`cca1b1762acee3bd56956a4ef0049d6f18465bd4be5df1585dc6e2b1aad3d397`.
The dependency must pass actual strict and genuine normal checks before
this actual consumer is verified. Neither source is a capacity proof.

The sole selected public header is

```lean
theorem actual_positive_gain_targets_card_le_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (z : Fin s) :
    ((Finset.univ.erase z).filter (fun q =>
      1 ≤ rowGain lam (directionRow o e c z) (deleteIndex o e c q z))).card ≤ 4
```

The printed name is
`Jsp404.ActualPositiveGainTargetBudget.actual_positive_gain_targets_card_le_four`.
Its intended axiom acceptance set is the standard three; no actual
axiom result has yet been obtained for this candidate.

The result is stronger than the originally requested unique-zero and
light-target subcase. It needs no original row score, potential,
minimum-counter Model, target score, gain-at-most-one, hull status,
supplied order, merge arcs or abstract incidence certificate.

For a full original row, the indexed bridge identifies the actual
incident arcs at position k as `gapAfter(pred k)` and `gapAfter(k)`.
A positive merge gain implies positive merged gap score, hence their
sum is at least `2*lam`. This implication holds even when the old row
has positive score or the merge gain is two.

The predecessor is a permutation of all original row positions. Thus
the sum of all positional adjacent-arc sums is exactly `2*pi`, counting
every original gap occurrence twice, including the wrap. Taking any
emitting-position subset gives `2*lam*card <= 2*pi`, which excludes five
positions above `2*pi/9`. The proof never deduplicates gap values.

Actual legality supplies no three collinear centers. The source proves
actual projective direction uniqueness locally from the public actual
angle formula, and proves the actual sorted row is Nodup using its actual
fan-index list. Each actual target maps to the internally produced
`deleteIndex` ordinal. The public `List.idxOf_inj` and actual direction
uniqueness prove that map injective. Its image therefore has exactly
the number of distinct actual targets; its gains are the original
actual row gains. This is the actual counting bridge, not a bound on a
caller-supplied list of arcs.

Configurations with at most five centers use the direct count of all
possible other targets. Larger configurations have a full original row
of length at least five, so the indexed merge assumptions are produced
internally. No restricted Model or subset criticality is introduced.

The stronger interior degree-three argument remains PAPER and is not
an export of this module. A unique-zero F17 consumer may use this result
to bound its possible light targets, but no mandatory deletion selector
or whole F17 contradiction follows here. Only new source and notes were
written; no Lean, solver, Git, quota or old-source edit was run.
