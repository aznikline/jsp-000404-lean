import Jsp000404.StrongGapBudget

/-! Genuine score/count bounds for every gap, including the zero-score gaps.
All filters retain multiplicities. These are actual natural-floor statements,
rather than conditions on a diagnostic witness sublist. -/

namespace Jsp404.SmallScoreGapBounds

open StrongGapBudget

noncomputable def countAtLeast (r : ℝ) (gs : List ℝ) : ℕ :=
  (gs.filter (fun g => decide (r ≤ g))).length

theorem each_floor_score_le (gs : List ℝ) (g : ℝ) (hg : g ∈ gs) :
    ⌊g⌋₊ - 1 ≤ score gs := by
  induction gs with
  | nil => simp at hg
  | cons x xs ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · simp only [score, List.map_cons, List.sum_cons]
      omega
    · have ht := ih hg
      simp only [score, List.map_cons, List.sum_cons] at *
      omega

theorem each_gap_lt_score_add_two (gs : List ℝ) (g : ℝ) (hg : g ∈ gs)
    (hzero : 0 ≤ g) : g < (score gs : ℝ) + 2 := by
  have hs := each_floor_score_le gs g hg
  have hq : ⌊g⌋₊ ≤ score gs + 1 := by omega
  have hqR : (⌊g⌋₊ : ℝ) ≤ (score gs : ℝ) + 1 := by exact_mod_cast hq
  have hf := Nat.lt_floor_add_one g
  linarith

theorem all_large_count_le_score (gs : List ℝ) : countAtLeast 2 gs ≤ score gs := by
  induction gs with
  | nil => simp [countAtLeast, score]
  | cons g gs ih =>
    by_cases hg : (2 : ℝ) ≤ g
    · have hq : 2 ≤ ⌊g⌋₊ := Nat.le_floor (by norm_num; exact hg)
      simp [countAtLeast, score, hg] at ih ⊢
      omega
    · simp [countAtLeast, score, hg] at ih ⊢
      omega

theorem all_unit_count_eq_support (gs : List ℝ)
    (hnonneg : ∀ g ∈ gs, 0 ≤ g) : countAtLeast 1 gs = support gs := by
  induction gs with
  | nil => simp [countAtLeast, support]
  | cons g gs ih =>
    have hg0 := hnonneg g (by simp)
    have ht := ih (fun x hx => hnonneg x (by simp [hx]))
    by_cases hg : (1 : ℝ) ≤ g
    · have hq : 1 ≤ ⌊g⌋₊ := Nat.le_floor (by norm_num; exact hg)
      simp [countAtLeast, support, hg] at ht ⊢
      omega
    · have hq : ⌊g⌋₊ < 1 := (Nat.floor_lt hg0).mpr (by norm_num; linarith)
      simp [countAtLeast, support, hg] at ht ⊢
      omega

theorem score_le_large_count_of_all_lt_three (gs : List ℝ)
    (hnonneg : ∀ g ∈ gs, 0 ≤ g) (hthree : ∀ g ∈ gs, g < 3) :
    score gs ≤ countAtLeast 2 gs := by
  induction gs with
  | nil => simp [countAtLeast, score]
  | cons g gs ih =>
    have hg0 := hnonneg g (by simp)
    have hg3 := hthree g (by simp)
    have hq3 : ⌊g⌋₊ < 3 := (Nat.floor_lt hg0).mpr (by norm_num; exact hg3)
    have ht := ih (fun x hx => hnonneg x (by simp [hx]))
      (fun x hx => hthree x (by simp [hx]))
    by_cases hg : (2 : ℝ) ≤ g
    · have hq : 2 ≤ ⌊g⌋₊ := Nat.le_floor (by norm_num; exact hg)
      simp [countAtLeast, score, hg] at ht ⊢
      omega
    · have hq : ⌊g⌋₊ < 2 := (Nat.floor_lt hg0).mpr (by norm_num; linarith)
      simp [countAtLeast, score, hg] at ht ⊢
      omega

noncomputable def modelGaps {n : ℕ} (M : SixModelCompression.ModelSix n) (i : Fin 5) : List ℝ :=
  linearGaps (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)

theorem model_gaps_nonneg {n : ℕ} (M : SixModelCompression.ModelSix n) (i : Fin 5) :
    ∀ g ∈ modelGaps M i, 0 ≤ g := by
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply linearGaps_nonneg _ _ _ (by linarith [M.hdelta.1]) (M.row_sorted i)
  intro x hx
  have hm := SixModelCompression.row_mem_bounds M i x hx
  have ht := M.theta_bounds i
  constructor <;> linarith [M.hdelta.2]

theorem model_score {n : ℕ} (M : SixModelCompression.ModelSix n) (i : Fin 5)
    (c : ℕ) (hdef : SixModelCompression.rowDefect M i = c) :
    score (modelGaps M i) + c = n := by
  have h := (SixModelBudget.row_budget M i).2.2
  rw [hdef] at h
  simpa only [modelGaps, linear_score_eq] using h

theorem model_all_bounds {n : ℕ} (M : SixModelCompression.ModelSix n) (i : Fin 5)
    (c : ℕ) (hdef : SixModelCompression.rowDefect M i = c) :
    (∀ g ∈ modelGaps M i, g < (n : ℝ) - (c : ℝ) + 2) ∧
    countAtLeast 2 (modelGaps M i) + c ≤ n ∧
    countAtLeast 1 (modelGaps M i) ≤ c ∧
    ((∀ g ∈ modelGaps M i, g < 3) → n ≤ countAtLeast 2 (modelGaps M i) + c) := by
  have hn := model_gaps_nonneg M i
  have hs := model_score M i c hdef
  have hc := SixModelBudget.support_le_defect M i
  rw [hdef] at hc
  have hsupp : support (modelGaps M i) ≤ c := by
    simpa only [modelGaps, linear_support_eq, SixModelBudget.support] using hc
  have hlarge := all_large_count_le_score (modelGaps M i)
  have hunit := all_unit_count_eq_support (modelGaps M i) hn
  constructor
  · intro g hg
    have h := each_gap_lt_score_add_two (modelGaps M i) g hg (hn g hg)
    have hsR : (score (modelGaps M i) : ℝ) + (c : ℝ) = (n : ℝ) := by exact_mod_cast hs
    linarith
  · refine ⟨by omega, by omega, ?_⟩
    intro hthree
    have h := score_le_large_count_of_all_lt_three (modelGaps M i) hn hthree
    omega

#print axioms each_gap_lt_score_add_two
#print axioms all_large_count_le_score
#print axioms all_unit_count_eq_support
#print axioms score_le_large_count_of_all_lt_three
#print axioms model_all_bounds

end Jsp404.SmallScoreGapBounds
