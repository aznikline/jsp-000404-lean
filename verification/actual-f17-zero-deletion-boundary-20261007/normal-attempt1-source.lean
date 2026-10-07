import Jsp000404.ActualMinimalBandCounterexample

set_option autoImplicit false

/-!
Closed lower-boundary gaps for an original zero source after deleting an
original zero target in a fixed-cardinality weighted F17 maximum.

All critical and maximum hypotheses stay on the same original point set at
strictly interior scales. The deleted configuration is not assumed critical,
flat, or maximal. Nothing is asserted about legality or row scores at rho.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualF17ZeroDeletionBoundary

/-- Shrinking the scale within the original band preserves both original
zero scores. Original minimum-cardinality then forces the actual deleted
source row to remain zero. Other original rows may have positive scores. -/
theorem actual_zero_delete_row_zero_at_smaller_scale {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam lam' : ℝ} {c : Fin (s + 1) → Plane₂}
    (H : ActualMinimalBandCounterexample.FixedCardModel o e rho upper 16 (s + 1) 17 c lam)
    (hrho : 0 ≤ rho) (hlow : rho < lam') (hsmall : lam' ≤ lam)
    (q : Fin (s + 1)) (hq : rowScore lam (directionRow o e c q) = 0)
    (i : Fin s) (hi : rowScore lam (directionRow o e c (q.succAbove i)) = 0) :
    rowScore lam' (directionRow o e (c ∘ q.succAbove) i) = 0 := by
  have H' := ActualMinimalBandCounterexample.actual_fixed_card_model_of_smaller_scale
    o e H hrho hlow hsmall
  have hplateau := (ActualMinimalBandCounterexample.actual_fixed_card_score_plateau
    o e H hrho hlow hsmall).2
  have hq' : rowScore lam' (directionRow o e c q) = 0 := (hplateau q).trans hq
  have hi' : rowScore lam' (directionRow o e c (q.succAbove i)) = 0 :=
    (hplateau (q.succAbove i)).trans hi
  have hmin : ∀ j : Fin (s + 1),
      rowScore lam' (directionRow o e c q) ≤ rowScore lam' (directionRow o e c j) := by
    intro j
    rw [hq']
    exact Nat.zero_le _
  have hdiv : 2 ^ rowScore lam' (directionRow o e c q) ∣ 16 := by simp [hq']
  have hdelete := ActualMinimalBandCounterexample.actual_delete_potential_le_cap
    hs o e H'.toModel q
  have hnormal := ActualMinimumDeletionNormalForm.actual_minimum_delete_normal_form
    (by omega : 2 ≤ s) o e H'.legality q 16 hmin hdiv H'.over_cap hdelete
  exact (hnormal.2.2.2 i).trans hi'

private theorem gap_le_two_rho_of_smaller_row_zero {rho lam : ℝ}
    (hrho : 0 ≤ rho) (habove : rho < lam) (l : List ℝ)
    (hzero : ∀ lam' : ℝ, rho < lam' → lam' ≤ lam → rowScore lam' l = 0) :
    ∀ g ∈ cycGaps l, g ≤ 2 * rho := by
  intro g hg
  by_contra hnot
  have hgt : 2 * rho < g := lt_of_not_ge hnot
  have hmin : rho < min lam (g / 2) := lt_min habove (by linarith)
  let lam' := (rho + min lam (g / 2)) / 2
  have hlo : rho < lam' := by dsimp [lam']; linarith
  have hlt : lam' < min lam (g / 2) := by dsimp [lam']; linarith
  have hsmall : lam' ≤ lam := hlt.le.trans (min_le_left _ _)
  have hb := cycGaps_lt_two_mul_of_rowScore_zero (hrho.trans_lt hlo)
    (hzero lam' hlo hsmall) g hg
  have hltg : lam' < g / 2 := hlt.trans_le (min_le_right _ _)
  linarith

/-- In the original weighted n4 LOW F17 fixed-card maximum, every actual
gap of a zero source after deleting a zero target is at most `2*rho`, with
`rho=pi/(4+1/2)=2*pi/9`. This is only a closed geometric gap bound:
equality may still have positive gap score at rho. -/
theorem actual_low_four_zero_delete_gap_le_two_rho {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {lam : ℝ} {c : Fin (s + 1) → Plane₂}
    (H : ActualMinimalBandCounterexample.FixedCardModel o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) 17 c lam)
    (q : Fin (s + 1)) (hq : rowScore lam (directionRow o e c q) = 0)
    (i : Fin s) (hi : rowScore lam (directionRow o e c (q.succAbove i)) = 0) :
    ∀ g ∈ cycGaps (directionRow o e (c ∘ q.succAbove) i),
      g ≤ 2 * (Real.pi / ((4 : ℝ) + 1 / 2)) := by
  have hrho : 0 ≤ Real.pi / ((4 : ℝ) + 1 / 2) := by positivity
  apply gap_le_two_rho_of_smaller_row_zero hrho H.scale_lower
    (directionRow o e (c ∘ q.succAbove) i)
  intro lam' hlo hsmall
  exact actual_zero_delete_row_zero_at_smaller_scale hs o e H hrho hlo hsmall q hq i hi

#print axioms actual_zero_delete_row_zero_at_smaller_scale
#print axioms actual_low_four_zero_delete_gap_le_two_rho

end Jsp404.ActualF17ZeroDeletionBoundary
