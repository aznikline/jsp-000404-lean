import Jsp000404.SixModelBudget

/-! Geometric budgets obtained by retaining only genuine positive-score gaps.
All multiplicities are preserved with lists.  The witness is built from the
actual natural floors; there is no solver-answer or compressed-point premise. -/

namespace Jsp404.StrongGapBudget

noncomputable def largeGaps (gs : List ℝ) : List ℝ :=
  gs.filter (fun g => decide (2 ≤ ⌊g⌋₊))

noncomputable def score (gs : List ℝ) : ℕ :=
  (gs.map (fun g => ⌊g⌋₊ - 1)).sum

noncomputable def support (gs : List ℝ) : ℕ :=
  (gs.map (fun g => min ⌊g⌋₊ 1)).sum

/-- A necessary budget on a multiplicity-preserving sublist of large gaps.
The extra count bound follows because every selected gap contributes at
least one unit of the genuine score. -/
def Budget (n c : ℕ) (gs : List ℝ) : Prop :=
  ∃ selected : List ℝ, selected.Sublist gs ∧
    0 < selected.length ∧ selected.length ≤ c ∧ c + selected.length ≤ n ∧
    (∀ g ∈ selected, 2 ≤ g) ∧
    (n : ℝ) - (c : ℝ) + (selected.length : ℝ) ≤ selected.sum

theorem large_floor_sum (gs : List ℝ) :
    ((largeGaps gs).map (fun g => ⌊g⌋₊)).sum = score gs + (largeGaps gs).length := by
  induction gs with
  | nil => simp [largeGaps, score]
  | cons g gs ih =>
    by_cases hg : 2 ≤ ⌊g⌋₊
    · simp [largeGaps, score, hg] at ih ⊢
      omega
    · simp [largeGaps, score, hg] at ih ⊢
      omega

theorem large_count_le_score (gs : List ℝ) : (largeGaps gs).length ≤ score gs := by
  induction gs with
  | nil => simp [largeGaps, score]
  | cons g gs ih =>
    by_cases hg : 2 ≤ ⌊g⌋₊
    · simp [largeGaps, score, hg] at ih ⊢
      omega
    · simp [largeGaps, score, hg] at ih ⊢
      omega

theorem large_count_le_support (gs : List ℝ) : (largeGaps gs).length ≤ support gs := by
  induction gs with
  | nil => simp [largeGaps, support]
  | cons g gs ih =>
    by_cases hg : 2 ≤ ⌊g⌋₊
    · simp [largeGaps, support, hg] at ih ⊢
      omega
    · simp [largeGaps, support, hg] at ih ⊢
      omega

private theorem floor_sum_le_sum (gs : List ℝ) (h : ∀ g ∈ gs, 0 ≤ g) :
    (((gs.map (fun g => ⌊g⌋₊)).sum : ℕ) : ℝ) ≤ gs.sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    have hf := Nat.floor_le hg
    simpa only [List.map_cons, List.sum_cons, Nat.cast_add] using add_le_add hf ht

/-- No upper bound on n is used.  This is the real geometric inequality
extracted from exact natural score and support budgets. -/
theorem budget_of_score_support (n c : ℕ) (gs : List ℝ)
    (hn : c < n) (hs : score gs + c = n) (hc : support gs ≤ c)
    (hnonneg : ∀ g ∈ gs, 0 ≤ g) : Budget n c gs := by
  have hid := large_floor_sum gs
  have hscore := large_count_le_score gs
  have hsupport := large_count_le_support gs
  have hpos : 0 < (largeGaps gs).length := by
    by_contra hh
    have hz : (largeGaps gs).length = 0 := by omega
    have he : largeGaps gs = [] := by simpa using hz
    rw [he] at hid
    simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.add_zero] at hid
    omega
  have hsub : (largeGaps gs).Sublist gs := List.filter_sublist
  have hlarge : ∀ g ∈ largeGaps gs, 2 ≤ g := by
    intro g hg
    have hm : g ∈ gs ∧ 2 ≤ ⌊g⌋₊ := by simpa [largeGaps] using hg
    have hf := Nat.floor_le (hnonneg g hm.1)
    have hq : (2 : ℝ) ≤ (⌊g⌋₊ : ℝ) := by exact_mod_cast hm.2
    exact hq.trans hf
  have hnn : ∀ g ∈ largeGaps gs, 0 ≤ g := fun g hg => hnonneg g (hsub.subset hg)
  have hsum := floor_sum_le_sum (largeGaps gs) hnn
  have hcount : c + (largeGaps gs).length ≤ n := by omega
  have heq : ((largeGaps gs).map (fun g => ⌊g⌋₊)).sum + c =
      n + (largeGaps gs).length := by omega
  have heqR : ((((largeGaps gs).map (fun g => ⌊g⌋₊)).sum : ℕ) : ℝ) + (c : ℝ) =
      (n : ℝ) + ((largeGaps gs).length : ℝ) := by exact_mod_cast heq
  refine ⟨largeGaps gs, hsub, hpos, by omega, hcount, hlarge, ?_⟩
  linarith

/-- The actual consecutive gaps of an interval row, including both ends. -/
def linearGaps (left right : ℝ) : List ℝ → List ℝ
  | [] => [right - left]
  | x :: xs => (x - left) :: linearGaps x right xs

theorem linear_score_eq (left right : ℝ) (xs : List ℝ) :
    score (linearGaps left right xs) = linearGapScore 1 left right xs := by
  induction xs generalizing left with
  | nil => simp [score, linearGaps, linearGapScore, gapScore]
  | cons x xs ih =>
    simpa only [score, linearGaps, List.map_cons, List.sum_cons,
      linearGapScore, gapScore, div_one] using congrArg (fun t => (⌊x-left⌋₊ - 1) + t) (ih x)

theorem linear_support_eq (left right : ℝ) (xs : List ℝ) :
    support (linearGaps left right xs) = linearBigCount 1 left right xs := by
  induction xs generalizing left with
  | nil => simp [support, linearGaps, linearBigCount]
  | cons x xs ih =>
    simpa only [support, linearGaps, List.map_cons, List.sum_cons,
      linearBigCount, div_one] using congrArg (fun t => min ⌊x-left⌋₊ 1 + t) (ih x)

theorem linearGaps_nonneg (left right : ℝ) (xs : List ℝ)
    (hlr : left ≤ right) (hsorted : xs.Pairwise (· ≤ ·))
    (hb : ∀ x ∈ xs, left ≤ x ∧ x ≤ right) :
    ∀ g ∈ linearGaps left right xs, 0 ≤ g := by
  induction xs generalizing left with
  | nil =>
    intro g hg
    simp only [linearGaps, List.mem_singleton] at hg
    subst g
    linarith
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := List.pairwise_cons.mp hsorted
    have hn := ih x hx.2 ht.2 (fun y hy => ⟨ht.1 y hy, (hb y (by simp [hy])).2⟩)
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · linarith
    · exact hn g hg

/-- The witness uses the exact row of the existing anchored shared-chord
model.  Integer-compression and solver results are not assumptions. -/
theorem model_row_budget {n : ℕ} (M : SixModelCompression.ModelSix n) (i : Fin 5)
    (c : ℕ) (hdef : SixModelCompression.rowDefect M i = c) (hn : c < n) :
    Budget n c (linearGaps (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)) := by
  have hscore := (SixModelBudget.row_budget M i).2.2
  have hsupport := SixModelBudget.support_le_defect M i
  rw [hdef] at hscore hsupport
  apply budget_of_score_support n c _ hn
  · simpa only [linear_score_eq] using hscore
  · simpa only [linear_support_eq, SixModelBudget.support] using hsupport
  · have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply linearGaps_nonneg (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)
      (by linarith [M.hdelta.1]) (M.row_sorted i)
    intro x hx
    have hm := SixModelCompression.row_mem_bounds M i x hx
    have ht := M.theta_bounds i
    constructor <;> linarith [M.hdelta.2]

theorem defect_two_budget {n : ℕ} (M : SixModelCompression.ModelSix n) (i : Fin 5)
    (hdef : SixModelCompression.rowDefect M i = 2) :
    Budget n 2 (linearGaps (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)) :=
  model_row_budget M i 2 hdef (by have := M.hn; omega)

theorem defect_three_budget {n : ℕ} (M : SixModelCompression.ModelSix n) (i : Fin 5)
    (hdef : SixModelCompression.rowDefect M i = 3) (hn : 4 ≤ n) :
    Budget n 3 (linearGaps (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)) :=
  model_row_budget M i 3 hdef (by omega)

#print axioms budget_of_score_support
#print axioms model_row_budget
#print axioms defect_two_budget
#print axioms defect_three_budget

end Jsp404.StrongGapBudget
