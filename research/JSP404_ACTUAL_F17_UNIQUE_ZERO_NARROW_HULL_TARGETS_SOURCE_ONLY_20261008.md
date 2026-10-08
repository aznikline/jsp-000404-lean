# F17 unique-zero narrow hull targets — SOURCE_ONLY

New owned source: `Jsp000404/ActualF17UniqueZeroNarrowHullTargets.lean`,
77 lines, SHA
`59b9085a09da2500e286b1f32d95981414ee3731e7e21aeed13b45d9f50e5b66`.
This candidate has not been compiled. Existing PASS sources are unchanged.

The internally defined original-index set is

```lean
noncomputable def narrowHullLightTargets {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) : Finset (Fin t) :=
  Finset.univ.filter (fun q =>
    rowScore lam (directionRow o e c q) = 1 ∧ IsHullVertex c q ∧
      ∀ a b : Fin t, a ≠ q → b ≠ q → a ≠ b →
        ∠ (c a) (c q) (c b) ≤ Real.pi - 2 * lam)
```

The sole selected public theorem is
`Jsp404.ActualF17UniqueZeroNarrowHullTargets.actual_unique_zero_narrow_hull_light_targets`.
Its arguments are `o e he H z hz hpositive`. H is the original actual
n4 LOW cap16 whole-band minimum-counter Model, z has original score zero,
and every original index other than z has positive score. These are the
actual unique-zero subcase premises. There is no caller target set,
window, bisector, common cone, hull type, gain, degree or budget input.

Its result is the conjunction

```lean
(∀ q ∈ narrowHullLightTargets o e c lam, q ≠ z ∧
  1 ≤ rowGain lam (directionRow o e c z) (deleteIndex o e c q z)) ∧
  (narrowHullLightTargets o e c lam).card ≤ 4
```

For every member q, the checked actual hull-cone producer internally
chooses actual boundary rays and their bisector, and supplies an actual
emitting observer i for deletion of q. If i differed from z, it would
have positive original score. The checked F17 positive-observer/light-
target theorem would give zero gain at i, contrary to its emission.
Therefore i=z. The fact q differs from z follows from their original
scores one and zero.

Thus all members belong to the actual positive-gain target set at the
same original observer z. The checked generic actual target budget
then gives the cardinality bound. Its pi/5 scale premise follows from
the original LOW lower bound 2*pi/9. This preserves the common-observer
field for later actual merged-gap consumers instead of discarding it
and returning only a numerical cardinality.

The code consumes the verified F17 positive-observer source `9c84db53…`,
the checked `ActualHullConeDeletion` producer, and the verified generic
actual target-budget source
`51c4e9c42b88a5287605aaa7f033c6a8a16cd036601bce2f765271e8fc265779`.
Preparation metadata records their actual complete source hashes.

No claim is made that every original light hull point belongs to this
narrow set, that this set is nonempty, or that z is on the original hull.
The theorem supplies no pair-deletion emitter or degree-three interior
bound. It excludes no complete Z=1 profile and proves no F17 selector
or contradiction. There is no assumption on the number of original
interior points, and no heavy-singleton exclusion.

Only this new source, note and preparation directory were written.
No Lean, solver, Git, quota operation or old frozen-source edit was run.
The expected selected-axiom set is the standard three; actual strict and
genuine normal checks require a subsequent formal Root resource grant.
