import Jsp000404.ActualN4LowCriticalReduction
import Jsp000404.ActualF17ZeroDeletionBoundary

/-! SOURCE_ONLY whole-band LOW4 counterexample entry and FixedCard bridge.

The existing Model.minimum_card already ranges over every legal configuration
and every scale in the whole open/closed band. A fixed-scale minimality claim
cannot replace it. Verification of the imported critical reduction is recorded
separately; this new bridge remains uncompiled. No LOW4 capacity conclusion
is assumed or asserted.

Fixed-card maximality is proved by testing every same-card band realization:
an over-cap test configuration inherits the SAME whole-band minimal cardinality
and is forced to potential17 by the critical reduction. This is an explicit
argument, not a new maximality field silently attached to an ordinary model.
-/

set_option autoImplicit false
set_option pp.fullNames true
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualLowFourWholeBandFixedCard

/-- Explicitly derive the same-cardinality whole-band maximum17. -/
theorem model_fixed_card_seventeen {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam) :
    ActualMinimalBandCounterexample.FixedCardModel o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s 17 c lam := by
  have h17 := ActualN4LowCriticalReduction.actual_n4_low_model_potential_eq_seventeen
    o e he H
  refine ⟨H, h17, ?_⟩
  intro d scale hlo hup hleg
  by_cases hover : 16 < potential scale (directionRows o e d)
  · have H' : ActualMinimalBandCounterexample.Model o e
        (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s d scale :=
      ⟨H.card_ge_three, hlo, hup, hleg, hover, H.minimum_card⟩
    exact (ActualN4LowCriticalReduction.actual_n4_low_model_potential_eq_seventeen
      o e he H').le
  · omega

/-- Counter-cardinality is selected jointly over all points and all band
scales by the already checked Nat.find producer. The new bridge then yields
an attained fixed-cardinality maximum17 without a caller maximum premise. -/
theorem exists_whole_band_fixed_card_seventeen {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam)
    (hlow : Real.pi / ((4 : ℝ) + 1 / 2) < lam)
    (hupp : lam ≤ Real.pi / 4)
    (hover : 16 < potential lam (directionRows o e c)) :
    ∃ t : ℕ, 3 ≤ t ∧ t ≤ s ∧ t ≤ 17 ∧
      ∃ scale : ℝ, ∃ d : Fin t → Plane₂,
        ActualMinimalBandCounterexample.FixedCardModel o e
          (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 t 17 d scale := by
  obtain ⟨t, hts, htcap, scale, d, H⟩ :=
    ActualMinimalBandCounterexample.exists_minimal_counter (by decide : 2 ≤ 16)
      o e hs c hleg hlow hupp hover
  exact ⟨t, H.card_ge_three, hts, htcap, scale, d, model_fixed_card_seventeen o e he H⟩

/-- The whole-band minimality field bounds every smaller legal configuration
at every band scale. It does not turn that configuration into a new Model. -/
theorem smaller_card_capacity_at_any_band_scale {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hr : 3 ≤ r) (hrs : r < s) (d : Fin r → Plane₂) (scale : ℝ)
    (hlo : Real.pi / ((4 : ℝ) + 1 / 2) < scale) (hup : scale ≤ Real.pi / 4)
    (hleg : Section4Legality d scale) : potential scale (directionRows o e d) ≤ 16 := by
  by_contra hnot
  have hmin := H.minimum_card hr d scale hlo hup hleg (by omega)
  omega

/-- All lower interior scales preserve the same original configuration's
potential17 and every full original row score. -/
theorem score_plateau {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam lam' : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hlo : Real.pi / ((4 : ℝ) + 1 / 2) < lam') (hsmall : lam' ≤ lam) :
    potential lam' (directionRows o e c) = 17 ∧
      ∀ i : Fin s, rowScore lam' (directionRow o e c i) =
        rowScore lam (directionRow o e c i) :=
  ActualMinimalBandCounterexample.actual_fixed_card_score_plateau o e
    (model_fixed_card_seventeen o e he H) (by positivity) hlo hsmall

/-- The original full-gap scores, rather than their raw floors, plateau. -/
theorem gap_score_plateau {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam lam' : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hlo : Real.pi / ((4 : ℝ) + 1 / 2) < lam') (hsmall : lam' ≤ lam) :
    ∀ i : Fin s, ∀ g ∈ cycGaps (directionRow o e c i),
      gapScore lam' g = gapScore lam g :=
  ActualMinimalBandCounterexample.actual_fixed_card_gap_score_plateau o e
    (model_fixed_card_seventeen o e he H) (by positivity) hlo hsmall

/-- Reuse the checked closed-boundary theorem for every ORIGINAL full gap.
No legality, flatness or score equality at the excluded endpoint is claimed. -/
theorem original_gap_le_score_boundary {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam) :
    ∀ i : Fin s, ∀ g ∈ cycGaps (directionRow o e c i),
      g ≤ ((gapScore lam g + 2 : ℕ) : ℝ) * (Real.pi / ((4 : ℝ) + 1 / 2)) :=
  ActualMinimalBandCounterexample.actual_fixed_card_gap_le_score_boundary o e
    (model_fixed_card_seventeen o e he H) (by positivity)

/-- The original two-zero single-deletion boundary consumer no longer
requires the caller to supply a separate FixedCard premise. The deleted
configuration is not assumed minimal, maximal or flat. -/
theorem zero_delete_gap_le_two_rho {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (q : Fin (s + 1)) (hq : rowScore lam (directionRow o e c q) = 0)
    (i : Fin s) (hi : rowScore lam (directionRow o e c (q.succAbove i)) = 0) :
    ∀ g ∈ cycGaps (directionRow o e (c ∘ q.succAbove) i),
      g ≤ 2 * (Real.pi / ((4 : ℝ) + 1 / 2)) :=
  ActualF17ZeroDeletionBoundary.actual_low_four_zero_delete_gap_le_two_rho
    hs o e (model_fixed_card_seventeen o e he H) q hq i hi

#print axioms model_fixed_card_seventeen
#print axioms exists_whole_band_fixed_card_seventeen
#print axioms smaller_card_capacity_at_any_band_scale
#print axioms score_plateau
#print axioms gap_score_plateau
#print axioms original_gap_le_score_boundary
#print axioms zero_delete_gap_le_two_rho

end Jsp404.ActualLowFourWholeBandFixedCard
