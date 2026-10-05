import Jsp000404.SatScalarModel
import Jsp000404.SixExactFloorKernelSymbolicInterval

/-!
# Ordinary arithmetic bridges for the n=4 critical-kernel replay

These are actual full-list floor-score statements and small geometric
branch cores. They are not a critical-profile exclusion or a solver oracle.
The positive indicator is computed from the actual gap score, never added
as a field to GenericModel. All rows retain their complete gap lists.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2CriticalKernel

open SatScalarModel StrongGapBudget

noncomputable def modelGaps {m n : ℕ} (M : GenericModel m n) (i : Fin m) : List ℝ :=
  linearGaps (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)

noncomputable def indicator (gs : List ℝ) : ℕ :=
  (gs.map (fun g => min (⌊g⌋₊ - 1) 1)).sum

theorem linearGaps_sum (left right : ℝ) (xs : List ℝ) :
    (linearGaps left right xs).sum = right - left := by
  induction xs generalizing left with
  | nil => simp [linearGaps]
  | cons x xs ih => simp only [linearGaps, List.sum_cons, ih]; ring

theorem model_gaps_sum {m n : ℕ} (M : GenericModel m n) (i : Fin m) :
    (modelGaps M i).sum = (n : ℝ) + M.delta := by
  rw [modelGaps, linearGaps_sum]
  ring

theorem model_gaps_nonneg {m n : ℕ} (M : GenericModel m n) (i : Fin m) :
    ∀ g ∈ modelGaps M i, 0 ≤ g := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply linearGaps_nonneg _ _ _ (by linarith [M.hdelta.1]) (M.row_sorted i)
  intro x hx
  have hm := SatScalarModel.row_mem_bounds M i x hx
  have ht := M.theta_bounds i
  constructor <;> linarith [M.hdelta.2]

/-- A positive stated defect determines the exact complete scalar score. -/
theorem model_score_of_positive_defect {m n : ℕ} (M : GenericModel m n)
    (i : Fin m) (c : ℕ) (hc : 0 < c) (hdef : SatScalarModel.rowDefect M i = c) :
    score (modelGaps M i) + c = n := by
  change n - linearGapScore 1 (M.theta i)
    (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i) = c at hdef
  have hs : score (modelGaps M i) = linearGapScore 1 (M.theta i)
      (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i) := linear_score_eq _ _ _
  omega

theorem n4_low_score {m : ℕ} (M : GenericModel m 4) (i : Fin m)
    (hdef : SatScalarModel.rowDefect M i = 2) : score (modelGaps M i) = 2 := by
  have h := model_score_of_positive_defect M i 2 (by decide) hdef
  omega

theorem n4_tail_gaps_lt_two {m : ℕ} (M : GenericModel m 4) (i : Fin m)
    (hdef : SatScalarModel.rowDefect M i = 4) :
    ∀ g ∈ modelGaps M i, g < 2 := by
  have h := model_score_of_positive_defect M i 4 (by decide) hdef
  have hz : score (modelGaps M i) = 0 := by omega
  intro g hg
  have he := SmallScoreGapBounds.each_floor_score_le (modelGaps M i) g hg
  have hs : ⌊g⌋₊ - 1 = 0 := by omega
  exact SixExactFloorKernel.zero_score_gap g (model_gaps_nonneg M i g hg) hs

/-- Full-score/min-indicator hull used by the finite Nat branch search. -/
theorem score_min_hull (s : ℕ) (hs : s ≤ 2) :
    min s 1 ≤ s ∧ min s 1 ≤ 1 ∧ s ≤ 2 * min s 1 := by
  refine ⟨Nat.min_le_left _ _, Nat.min_le_right _ _, ?_⟩
  by_cases hz : s = 0
  · simp [hz]
  · have hp : 1 ≤ s := by omega
    rw [Nat.min_eq_right hp]
    omega

theorem score_indicator_le_sum (gs : List ℝ) (hg : ∀ g ∈ gs, 0 ≤ g) :
    (score gs : ℝ) + (indicator gs : ℝ) ≤ gs.sum := by
  induction gs with
  | nil => simp [score, indicator]
  | cons g gs ih =>
    have hzero := hg g (by simp)
    have ht := ih (fun x hx => hg x (by simp [hx]))
    have hf := (SixExactFloorKernel.score_gap_min_interval g hzero).1
    simp only [score, indicator, List.map_cons, List.sum_cons, Nat.cast_add] at ht ⊢
    linarith

/-- A gap known to be at least1 has no floor0 case. -/
theorem unit_gap_score_lower (g : ℝ) (hg : 1 ≤ g) :
    ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 1 ≤ g := by
  have hq : 1 ≤ ⌊g⌋₊ := Nat.le_floor (by norm_num; exact hg)
  have he : ⌊g⌋₊ = (⌊g⌋₊ - 1) + 1 := by omega
  have heR : (⌊g⌋₊ : ℝ) = ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast he
  have hf := Nat.floor_le (by linarith : 0 ≤ g)
  linarith

/-- Full score2 and full period<5 leave at most one positive-score gap
off any guaranteed unit end. The supplied decomposition retains all gaps. -/
theorem off_unit_gap_indicator_le_one (delta g : ℝ) (rest : List ℝ)
    (hdelta : delta < 1) (hg : 1 ≤ g)
    (hnonneg : ∀ x ∈ rest, 0 ≤ x)
    (hscore : (⌊g⌋₊ - 1) + score rest = 2)
    (hperiod : g + rest.sum = 4 + delta) : indicator rest ≤ 1 := by
  have hl := unit_gap_score_lower g hg
  have hr := score_indicator_le_sum rest hnonneg
  have hsR : ((⌊g⌋₊ - 1 : ℕ) : ℝ) + (score rest : ℝ) = 2 := by
    exact_mod_cast hscore
  have hiR : (indicator rest : ℝ) < 2 := by linarith
  have hi : indicator rest < 2 := by exact_mod_cast hiR
  omega

/-- The shared chord bounds the sum of the two guaranteed-end scores.
All inputs are explicit arithmetic inequalities, not a capacity premise. -/
theorem two_unit_end_scores_le_three (delta alpha beta b : ℝ) (s t : ℕ)
    (hdelta : delta < 1) (htheta : beta - alpha ≤ delta)
    (hlower : alpha + (s : ℝ) + 1 ≤ b)
    (hupper : b ≤ beta + 4 + delta - (t : ℝ) - 1) : s + t ≤ 3 := by
  have hreal : ((s + t : ℕ) : ℝ) < 4 := by
    simp only [Nat.cast_add]
    linarith
  have hnat : s + t < 4 := by exact_mod_cast hreal
  omega

/-- A pure geometric LRA core: four consecutive upward unit steps do
not fit in the n=4 strip. This is a derived negation, not an assumed mask. -/
theorem no_four_consecutive_up (M : GenericModel 7 4) :
    ¬ (M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 1 2 + 1 ≤ M.d 2 3 ∧
      M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 3 4 + 1 ≤ M.d 4 5) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hc01 := M.corridor 0 1 (by decide)
  have hc45 := M.corridor 4 5 (by decide)
  have ht0 := M.theta_bounds 0
  have ht5 := M.theta_bounds 5
  have hd := M.hdelta.2
  norm_num at hc01 hc45
  linarith

theorem no_four_consecutive_down (M : GenericModel 7 4) :
    ¬ (M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 2 3 + 1 ≤ M.d 1 2 ∧
      M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 4 5 + 1 ≤ M.d 3 4) := by
  rintro ⟨h1, h2, h3, h4⟩
  have hc01 := M.corridor 0 1 (by decide)
  have hc45 := M.corridor 4 5 (by decide)
  have ht1 := M.theta_bounds 1
  have ht4 := M.theta_bounds 4
  have hd := M.hdelta.2
  norm_num at hc01 hc45
  linarith

#print axioms linearGaps_sum
#print axioms model_gaps_sum
#print axioms model_gaps_nonneg
#print axioms model_score_of_positive_defect
#print axioms n4_low_score
#print axioms n4_tail_gaps_lt_two
#print axioms score_min_hull
#print axioms score_indicator_le_sum
#print axioms unit_gap_score_lower
#print axioms off_unit_gap_indicator_le_one
#print axioms two_unit_end_scores_le_three
#print axioms no_four_consecutive_up
#print axioms no_four_consecutive_down

end Jsp404.N4R2CriticalKernel
