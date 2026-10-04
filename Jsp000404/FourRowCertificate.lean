import Jsp000404.SixModelBudget

/-!
Ordinary kernel proofs extracted from the four-row diagnostic.  The first
certificate eliminates orientations 1 and 513 by a single defect-three row.
The remaining orientations are not asserted to be certified here.
-/

namespace Jsp404.FourRowCertificate

open SixModelCompression SixModelBudget

/-- Three initial unit gaps exhaust a defect-three row's support budget.
Consequently its first three raw floors already consume the whole strip. -/
theorem three_unit_prefix_floor (n : ℕ) (left right a b c d : ℝ)
    (hfirst : left + 1 ≤ a) (hsecond : a + 1 ≤ b) (hthird : b + 1 ≤ c)
    (hsupport : linearBigCount 1 left right [a, b, c, d] ≤ 3)
    (hbudget : linearBigCount 1 left right [a, b, c, d] +
      (n - linearFloorSum 1 left right [a, b, c, d]) = 3)
    (hcells : linearFloorSum 1 left right [a, b, c, d] ≤ n) :
    n ≤ ⌊a - left⌋₊ + ⌊b - a⌋₊ + ⌊c - b⌋₊ := by
  have hqa : 1 ≤ ⌊a - left⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hqb : 1 ≤ ⌊b - a⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hqc : 1 ≤ ⌊c - b⌋₊ := Nat.le_floor (by norm_num; linarith)
  simp only [linearBigCount, linearFloorSum, div_one] at *
  omega

/-- The first three floor bounds telescope to the third coordinate. -/
theorem prefix_floor_le (left a b c : ℝ)
    (hfirst : left + 1 ≤ a) (hsecond : a + 1 ≤ b) (hthird : b + 1 ≤ c) :
    (⌊a - left⌋₊ + ⌊b - a⌋₊ + ⌊c - b⌋₊ : ℕ) ≤ c - left := by
  have ha := Nat.floor_le (by linarith : 0 ≤ a - left)
  have hb := Nat.floor_le (by linarith : 0 ≤ b - a)
  have hc := Nat.floor_le (by linarith : 0 ≤ c - b)
  push_cast
  linarith

/-- A row with three forced prefix gaps cannot have defect three if its
third coordinate has less than one strip of room from the row origin. -/
theorem three_unit_prefix_impossible (n : ℕ) (left right a b c d : ℝ)
    (hfirst : left + 1 ≤ a) (hsecond : a + 1 ≤ b) (hthird : b + 1 ≤ c)
    (hsupport : linearBigCount 1 left right [a, b, c, d] ≤ 3)
    (hbudget : linearBigCount 1 left right [a, b, c, d] +
      (n - linearFloorSum 1 left right [a, b, c, d]) = 3)
    (hcells : linearFloorSum 1 left right [a, b, c, d] ≤ n)
    (hshort : c - left < n) : False := by
  have hp := three_unit_prefix_floor n left right a b c d
    hfirst hsecond hthird hsupport hbudget hcells
  have hp' : (n : ℝ) ≤ (⌊a - left⌋₊ + ⌊b - a⌋₊ + ⌊c - b⌋₊ : ℕ) := by
    exact_mod_cast hp
  have hf := prefix_floor_le left a b c hfirst hsecond hthird
  linarith

/-- The same exact floor budget for a three-unit suffix. -/
theorem three_unit_suffix_floor (n : ℕ) (left right a b c d : ℝ)
    (hfirst : b + 1 ≤ c) (hsecond : c + 1 ≤ d) (hthird : d + 1 ≤ right)
    (hsupport : linearBigCount 1 left right [a, b, c, d] ≤ 3)
    (hbudget : linearBigCount 1 left right [a, b, c, d] +
      (n - linearFloorSum 1 left right [a, b, c, d]) = 3)
    (hcells : linearFloorSum 1 left right [a, b, c, d] ≤ n) :
    n ≤ ⌊c - b⌋₊ + ⌊d - c⌋₊ + ⌊right - d⌋₊ := by
  have hqc : 1 ≤ ⌊c - b⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hqd : 1 ≤ ⌊d - c⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hqe : 1 ≤ ⌊right - d⌋₊ := Nat.le_floor (by norm_num; linarith)
  simp only [linearBigCount, linearFloorSum, div_one] at *
  omega

theorem suffix_floor_le (right b c d : ℝ)
    (hfirst : b + 1 ≤ c) (hsecond : c + 1 ≤ d) (hthird : d + 1 ≤ right) :
    (⌊c - b⌋₊ + ⌊d - c⌋₊ + ⌊right - d⌋₊ : ℕ) ≤ right - b := by
  have hc := Nat.floor_le (by linarith : 0 ≤ c - b)
  have hd := Nat.floor_le (by linarith : 0 ≤ d - c)
  have he := Nat.floor_le (by linarith : 0 ≤ right - d)
  push_cast
  linarith

theorem three_unit_suffix_impossible (n : ℕ) (left right a b c d : ℝ)
    (hfirst : b + 1 ≤ c) (hsecond : c + 1 ≤ d) (hthird : d + 1 ≤ right)
    (hsupport : linearBigCount 1 left right [a, b, c, d] ≤ 3)
    (hbudget : linearBigCount 1 left right [a, b, c, d] +
      (n - linearFloorSum 1 left right [a, b, c, d]) = 3)
    (hcells : linearFloorSum 1 left right [a, b, c, d] ≤ n)
    (hshort : right - b < n) : False := by
  have hp := three_unit_suffix_floor n left right a b c d
    hfirst hsecond hthird hsupport hbudget hcells
  have hp' : (n : ℝ) ≤ (⌊c - b⌋₊ + ⌊d - c⌋₊ + ⌊right - d⌋₊ : ℕ) := by
    exact_mod_cast hp
  have hf := suffix_floor_le right b c d hfirst hsecond hthird
  linarith

/-- A reusable actual-model prefix terminal; only row identification and
the concrete geometric inequalities are supplied by an orientation branch. -/
theorem model_prefix_terminal {n : ℕ} (M : ModelSix n) (i : Fin 5)
    (a b c d : ℝ) (hrow : M.rowxs i = [a, b, c, d])
    (hfirst : M.theta i + 1 ≤ a) (hsecond : a + 1 ≤ b) (hthird : b + 1 ≤ c)
    (hdef : SixModelCompression.rowDefect M i = 3)
    (hshort : c - M.theta i < (n : ℝ)) : False := by
  have hsupport := support_le_defect M i
  have hbudget := support_add_loss M i
  have hcells := cells_le M i
  rw [hdef] at hsupport hbudget
  simp only [support, loss, cells, hrow] at hsupport hbudget hcells
  exact three_unit_prefix_impossible n (M.theta i)
    (M.theta i + ((n : ℝ) + M.delta)) a b c d
    hfirst hsecond hthird hsupport hbudget hcells hshort

/-- The suffix counterpart retains the same genuine floor budget. -/
theorem model_suffix_terminal {n : ℕ} (M : ModelSix n) (i : Fin 5)
    (a b c d : ℝ) (hrow : M.rowxs i = [a, b, c, d])
    (hfirst : b + 1 ≤ c) (hsecond : c + 1 ≤ d)
    (hthird : d + 1 ≤ M.theta i + ((n : ℝ) + M.delta))
    (hdef : SixModelCompression.rowDefect M i = 3)
    (hshort : M.theta i + ((n : ℝ) + M.delta) - b < (n : ℝ)) : False := by
  have hsupport := support_le_defect M i
  have hbudget := support_add_loss M i
  have hcells := cells_le M i
  rw [hdef] at hsupport hbudget
  simp only [support, loss, cells, hrow] at hsupport hbudget hcells
  exact three_unit_suffix_impossible n (M.theta i)
    (M.theta i + ((n : ℝ) + M.delta)) a b c d
    hfirst hsecond hthird hsupport hbudget hcells hshort

/-- Orientations 1 and 513 share these three triangle orientations.  The
certificate uses the actual sorted row and its actual natural floor budget,
with no bounded-strip or solver-answer premise. -/
theorem mask_one_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧
      M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (h013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧
      M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (h134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧
      M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (hdef : SixModelCompression.rowDefect M 1 = 3) : False := by
  have hfirst := (M.corridor 1 2 (by decide)).1
  have hsecond := h012.1
  have hthird := h013.1
  have hsort : ([M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] : List ℝ).Pairwise
      (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith [h134.2.1]
  have hperm : (M.rowxs 1).Perm [M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] := by
    have hp := M.row_perm 1
    have hs : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
    have he : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) =
        [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs]
    rw [he] at hp
    exact hp.trans (List.Perm.swap _ _ _)
  have hrow : M.rowxs 1 = [M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] :=
    hperm.eq_of_pairwise' (M.row_sorted 1) hsort
  have hsupport := support_le_defect M 1
  have hbudget := support_add_loss M 1
  have hcells := cells_le M 1
  rw [hdef] at hsupport hbudget
  simp only [support, loss, cells, hrow] at hsupport hbudget hcells
  have hupper := (M.corridor 3 4 (by decide)).2
  have ht1 := (M.theta_bounds 1).1
  have ht4 := (M.theta_bounds 4).2
  have hdelta := M.hdelta.2
  have hshort : M.d 1 3 - M.theta 1 < (n : ℝ) := by
    linarith [h134.1]
  exact three_unit_prefix_impossible n (M.theta 1)
    (M.theta 1 + ((n : ℝ) + M.delta))
    (M.d 1 2) (M.d 0 1) (M.d 1 3) (M.d 1 4)
    hfirst hsecond hthird hsupport hbudget hcells hshort

#print axioms three_unit_prefix_floor
#print axioms prefix_floor_le
#print axioms three_unit_prefix_impossible
#print axioms mask_one_impossible

-- BEGIN GENERATED THREE-GAP CERTIFICATES

/-- Three-gap certificate for acyclic orientation 1. -/
theorem orientation_1_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (h013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (h014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (h023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (h024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (h034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (h123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (h124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (h134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (h234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    (hdef : SixModelCompression.rowDefect M 1 = 3) : False := by
  obtain ⟨h012a, h012b, h012c⟩ := h012
  obtain ⟨h013a, h013b, h013c⟩ := h013
  obtain ⟨h014a, h014b, h014c⟩ := h014
  obtain ⟨h023a, h023b, h023c⟩ := h023
  obtain ⟨h024a, h024b, h024c⟩ := h024
  obtain ⟨h034a, h034b, h034c⟩ := h034
  obtain ⟨h123a, h123b, h123c⟩ := h123
  obtain ⟨h124a, h124b, h124c⟩ := h124
  obtain ⟨h134a, h134b, h134c⟩ := h134
  obtain ⟨h234a, h234b, h234c⟩ := h234
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have hdelta := M.hdelta.2
  have hsort : ([M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hperm : (M.rowxs 1).Perm [M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] := by
    have hp := M.row_perm 1
    have hs0 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
    have he : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) =
        [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs0]
    rw [he] at hp
    exact hp.trans (List.Perm.swap (M.d 1 2) (M.d 0 1) [M.d 1 3, M.d 1 4])
  have hrow : M.rowxs 1 = [M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] :=
    hperm.eq_of_pairwise' (M.row_sorted 1) hsort
  have hfirst : M.theta 1 + 1 ≤ M.d 1 2 := by linarith
  have hsecond : M.d 1 2 + 1 ≤ M.d 0 1 := by linarith
  have hthird : M.d 0 1 + 1 ≤ M.d 1 3 := by linarith
  have hshort : M.d 1 3 - M.theta 1 < (n : ℝ) := by linarith
  exact model_prefix_terminal M 1 (M.d 1 2) (M.d 0 1)
    (M.d 1 3) (M.d 1 4) hrow hfirst hsecond hthird hdef hshort
#print axioms orientation_1_impossible

/-- Three-gap certificate for acyclic orientation 63. -/
theorem orientation_63_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (h013 : M.d 1 3 + 1 ≤ M.d 0 1 ∧ M.d 1 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 1)
    (h014 : M.d 1 4 + 1 ≤ M.d 0 1 ∧ M.d 1 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 1)
    (h023 : M.d 2 3 + 1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (h024 : M.d 2 4 + 1 ≤ M.d 0 2 ∧ M.d 2 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 2)
    (h034 : M.d 3 4 + 1 ≤ M.d 0 3 ∧ M.d 3 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 3)
    (h123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (h124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (h134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (h234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    (hdef : SixModelCompression.rowDefect M 3 = 3) : False := by
  obtain ⟨h012a, h012b, h012c⟩ := h012
  obtain ⟨h013a, h013b, h013c⟩ := h013
  obtain ⟨h014a, h014b, h014c⟩ := h014
  obtain ⟨h023a, h023b, h023c⟩ := h023
  obtain ⟨h024a, h024b, h024c⟩ := h024
  obtain ⟨h034a, h034b, h034c⟩ := h034
  obtain ⟨h123a, h123b, h123c⟩ := h123
  obtain ⟨h124a, h124b, h124c⟩ := h124
  obtain ⟨h134a, h134b, h134c⟩ := h134
  obtain ⟨h234a, h234b, h234c⟩ := h234
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have hdelta := M.hdelta.2
  have hsort : ([M.d 1 3, M.d 2 3, M.d 3 4, M.d 0 3] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hperm : (M.rowxs 3).Perm [M.d 1 3, M.d 2 3, M.d 3 4, M.d 0 3] := by
    have hp := M.row_perm 3
    have hs0 : M.d 3 0 = M.d 0 3 := M.symm 3 0 (by decide)
    have hs1 : M.d 3 1 = M.d 1 3 := M.symm 3 1 (by decide)
    have hs2 : M.d 3 2 = M.d 2 3 := M.symm 3 2 (by decide)
    have he : (((List.finRange 5).erase (3 : Fin 5)).map (M.d 3)) =
        [M.d 0 3, M.d 1 3, M.d 2 3, M.d 3 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs0, hs1, hs2]
    rw [he] at hp
    exact hp.trans (((List.Perm.swap (M.d 1 3) (M.d 0 3) [M.d 2 3, M.d 3 4]).trans ((List.Perm.swap (M.d 2 3) (M.d 0 3) [M.d 3 4]).cons (M.d 1 3))).trans (((List.Perm.swap (M.d 3 4) (M.d 0 3) []).cons (M.d 2 3)).cons (M.d 1 3)))
  have hrow : M.rowxs 3 = [M.d 1 3, M.d 2 3, M.d 3 4, M.d 0 3] :=
    hperm.eq_of_pairwise' (M.row_sorted 3) hsort
  have hfirst : M.d 2 3 + 1 ≤ M.d 3 4 := by linarith
  have hsecond : M.d 3 4 + 1 ≤ M.d 0 3 := by linarith
  have hthird : M.d 0 3 + 1 ≤ M.theta 3 + ((n : ℝ) + M.delta) := by linarith
  have hshort : M.theta 3 + ((n : ℝ) + M.delta) - M.d 2 3 < (n : ℝ) := by linarith
  exact model_suffix_terminal M 3 (M.d 1 3) (M.d 2 3)
    (M.d 3 4) (M.d 0 3) hrow hfirst hsecond hthird hdef hshort
#print axioms orientation_63_impossible

/-- Three-gap certificate for acyclic orientation 74. -/
theorem orientation_74_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (h013 : M.d 1 3 + 1 ≤ M.d 0 1 ∧ M.d 1 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 1)
    (h014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (h023 : M.d 2 3 + 1 ≤ M.d 0 2 ∧ M.d 2 3 < M.d 0 3 ∧ M.d 0 3 < M.d 0 2)
    (h024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (h034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (h123 : M.d 2 3 + 1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (h124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (h134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (h234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    (hdef : SixModelCompression.rowDefect M 1 = 3) : False := by
  obtain ⟨h012a, h012b, h012c⟩ := h012
  obtain ⟨h013a, h013b, h013c⟩ := h013
  obtain ⟨h014a, h014b, h014c⟩ := h014
  obtain ⟨h023a, h023b, h023c⟩ := h023
  obtain ⟨h024a, h024b, h024c⟩ := h024
  obtain ⟨h034a, h034b, h034c⟩ := h034
  obtain ⟨h123a, h123b, h123c⟩ := h123
  obtain ⟨h124a, h124b, h124c⟩ := h124
  obtain ⟨h134a, h134b, h134c⟩ := h134
  obtain ⟨h234a, h234b, h234c⟩ := h234
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have hdelta := M.hdelta.2
  have hsort : ([M.d 1 3, M.d 0 1, M.d 1 2, M.d 1 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hperm : (M.rowxs 1).Perm [M.d 1 3, M.d 0 1, M.d 1 2, M.d 1 4] := by
    have hp := M.row_perm 1
    have hs0 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
    have he : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) =
        [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs0]
    rw [he] at hp
    exact hp.trans (((List.Perm.swap (M.d 1 3) (M.d 1 2) [M.d 1 4]).cons (M.d 0 1)).trans (List.Perm.swap (M.d 1 3) (M.d 0 1) [M.d 1 2, M.d 1 4]))
  have hrow : M.rowxs 1 = [M.d 1 3, M.d 0 1, M.d 1 2, M.d 1 4] :=
    hperm.eq_of_pairwise' (M.row_sorted 1) hsort
  have hfirst : M.theta 1 + 1 ≤ M.d 1 3 := by linarith
  have hsecond : M.d 1 3 + 1 ≤ M.d 0 1 := by linarith
  have hthird : M.d 0 1 + 1 ≤ M.d 1 2 := by linarith
  have hshort : M.d 1 2 - M.theta 1 < (n : ℝ) := by linarith
  exact model_prefix_terminal M 1 (M.d 1 3) (M.d 0 1)
    (M.d 1 2) (M.d 1 4) hrow hfirst hsecond hthird hdef hshort
#print axioms orientation_74_impossible

/-- Three-gap certificate for acyclic orientation 448. -/
theorem orientation_448_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (h013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (h014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (h023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (h024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (h034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (h123 : M.d 2 3 + 1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (h124 : M.d 2 4 + 1 ≤ M.d 1 2 ∧ M.d 2 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 2)
    (h134 : M.d 3 4 + 1 ≤ M.d 1 3 ∧ M.d 3 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 3)
    (h234 : M.d 2 3 + 1 ≤ M.d 3 4 ∧ M.d 2 3 < M.d 2 4 ∧ M.d 2 4 < M.d 3 4)
    (hdef : SixModelCompression.rowDefect M 3 = 3) : False := by
  obtain ⟨h012a, h012b, h012c⟩ := h012
  obtain ⟨h013a, h013b, h013c⟩ := h013
  obtain ⟨h014a, h014b, h014c⟩ := h014
  obtain ⟨h023a, h023b, h023c⟩ := h023
  obtain ⟨h024a, h024b, h024c⟩ := h024
  obtain ⟨h034a, h034b, h034c⟩ := h034
  obtain ⟨h123a, h123b, h123c⟩ := h123
  obtain ⟨h124a, h124b, h124c⟩ := h124
  obtain ⟨h134a, h134b, h134c⟩ := h134
  obtain ⟨h234a, h234b, h234c⟩ := h234
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have hdelta := M.hdelta.2
  have hsort : ([M.d 0 3, M.d 2 3, M.d 3 4, M.d 1 3] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hperm : (M.rowxs 3).Perm [M.d 0 3, M.d 2 3, M.d 3 4, M.d 1 3] := by
    have hp := M.row_perm 3
    have hs0 : M.d 3 0 = M.d 0 3 := M.symm 3 0 (by decide)
    have hs1 : M.d 3 1 = M.d 1 3 := M.symm 3 1 (by decide)
    have hs2 : M.d 3 2 = M.d 2 3 := M.symm 3 2 (by decide)
    have he : (((List.finRange 5).erase (3 : Fin 5)).map (M.d 3)) =
        [M.d 0 3, M.d 1 3, M.d 2 3, M.d 3 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs0, hs1, hs2]
    rw [he] at hp
    exact hp.trans (((List.Perm.swap (M.d 2 3) (M.d 1 3) [M.d 3 4]).cons (M.d 0 3)).trans (((List.Perm.swap (M.d 3 4) (M.d 1 3) []).cons (M.d 2 3)).cons (M.d 0 3)))
  have hrow : M.rowxs 3 = [M.d 0 3, M.d 2 3, M.d 3 4, M.d 1 3] :=
    hperm.eq_of_pairwise' (M.row_sorted 3) hsort
  have hfirst : M.d 2 3 + 1 ≤ M.d 3 4 := by linarith
  have hsecond : M.d 3 4 + 1 ≤ M.d 1 3 := by linarith
  have hthird : M.d 1 3 + 1 ≤ M.theta 3 + ((n : ℝ) + M.delta) := by linarith
  have hshort : M.theta 3 + ((n : ℝ) + M.delta) - M.d 2 3 < (n : ℝ) := by linarith
  exact model_suffix_terminal M 3 (M.d 0 3) (M.d 2 3)
    (M.d 3 4) (M.d 1 3) hrow hfirst hsecond hthird hdef hshort
#print axioms orientation_448_impossible

/-- Three-gap certificate for acyclic orientation 512. -/
theorem orientation_512_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (h013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (h014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (h023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (h024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (h034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (h123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (h124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (h134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (h234 : M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
    (hdef : SixModelCompression.rowDefect M 3 = 3) : False := by
  obtain ⟨h012a, h012b, h012c⟩ := h012
  obtain ⟨h013a, h013b, h013c⟩ := h013
  obtain ⟨h014a, h014b, h014c⟩ := h014
  obtain ⟨h023a, h023b, h023c⟩ := h023
  obtain ⟨h024a, h024b, h024c⟩ := h024
  obtain ⟨h034a, h034b, h034c⟩ := h034
  obtain ⟨h123a, h123b, h123c⟩ := h123
  obtain ⟨h124a, h124b, h124c⟩ := h124
  obtain ⟨h134a, h134b, h134c⟩ := h134
  obtain ⟨h234a, h234b, h234c⟩ := h234
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have hdelta := M.hdelta.2
  have hsort : ([M.d 0 3, M.d 1 3, M.d 3 4, M.d 2 3] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hperm : (M.rowxs 3).Perm [M.d 0 3, M.d 1 3, M.d 3 4, M.d 2 3] := by
    have hp := M.row_perm 3
    have hs0 : M.d 3 0 = M.d 0 3 := M.symm 3 0 (by decide)
    have hs1 : M.d 3 1 = M.d 1 3 := M.symm 3 1 (by decide)
    have hs2 : M.d 3 2 = M.d 2 3 := M.symm 3 2 (by decide)
    have he : (((List.finRange 5).erase (3 : Fin 5)).map (M.d 3)) =
        [M.d 0 3, M.d 1 3, M.d 2 3, M.d 3 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs0, hs1, hs2]
    rw [he] at hp
    exact hp.trans (((List.Perm.swap (M.d 3 4) (M.d 2 3) []).cons (M.d 1 3)).cons (M.d 0 3))
  have hrow : M.rowxs 3 = [M.d 0 3, M.d 1 3, M.d 3 4, M.d 2 3] :=
    hperm.eq_of_pairwise' (M.row_sorted 3) hsort
  have hfirst : M.d 1 3 + 1 ≤ M.d 3 4 := by linarith
  have hsecond : M.d 3 4 + 1 ≤ M.d 2 3 := by linarith
  have hthird : M.d 2 3 + 1 ≤ M.theta 3 + ((n : ℝ) + M.delta) := by linarith
  have hshort : M.theta 3 + ((n : ℝ) + M.delta) - M.d 1 3 < (n : ℝ) := by linarith
  exact model_suffix_terminal M 3 (M.d 0 3) (M.d 1 3)
    (M.d 3 4) (M.d 2 3) hrow hfirst hsecond hthird hdef hshort
#print axioms orientation_512_impossible

/-- Three-gap certificate for acyclic orientation 513. -/
theorem orientation_513_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (h013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (h014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (h023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (h024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (h034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (h123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (h124 : M.d 1 2 + 1 ≤ M.d 2 4 ∧ M.d 1 2 < M.d 1 4 ∧ M.d 1 4 < M.d 2 4)
    (h134 : M.d 1 3 + 1 ≤ M.d 3 4 ∧ M.d 1 3 < M.d 1 4 ∧ M.d 1 4 < M.d 3 4)
    (h234 : M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
    (hdef : SixModelCompression.rowDefect M 1 = 3) : False := by
  obtain ⟨h012a, h012b, h012c⟩ := h012
  obtain ⟨h013a, h013b, h013c⟩ := h013
  obtain ⟨h014a, h014b, h014c⟩ := h014
  obtain ⟨h023a, h023b, h023c⟩ := h023
  obtain ⟨h024a, h024b, h024c⟩ := h024
  obtain ⟨h034a, h034b, h034c⟩ := h034
  obtain ⟨h123a, h123b, h123c⟩ := h123
  obtain ⟨h124a, h124b, h124c⟩ := h124
  obtain ⟨h134a, h134b, h134c⟩ := h134
  obtain ⟨h234a, h234b, h234c⟩ := h234
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have hdelta := M.hdelta.2
  have hsort : ([M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hperm : (M.rowxs 1).Perm [M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] := by
    have hp := M.row_perm 1
    have hs0 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
    have he : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) =
        [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs0]
    rw [he] at hp
    exact hp.trans (List.Perm.swap (M.d 1 2) (M.d 0 1) [M.d 1 3, M.d 1 4])
  have hrow : M.rowxs 1 = [M.d 1 2, M.d 0 1, M.d 1 3, M.d 1 4] :=
    hperm.eq_of_pairwise' (M.row_sorted 1) hsort
  have hfirst : M.theta 1 + 1 ≤ M.d 1 2 := by linarith
  have hsecond : M.d 1 2 + 1 ≤ M.d 0 1 := by linarith
  have hthird : M.d 0 1 + 1 ≤ M.d 1 3 := by linarith
  have hshort : M.d 1 3 - M.theta 1 < (n : ℝ) := by linarith
  exact model_prefix_terminal M 1 (M.d 1 2) (M.d 0 1)
    (M.d 1 3) (M.d 1 4) hrow hfirst hsecond hthird hdef hshort
#print axioms orientation_513_impossible

/-- Three-gap certificate for acyclic orientation 948. -/
theorem orientation_948_impossible {n : ℕ} (M : ModelSix n)
    (h012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (h013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (h014 : M.d 1 4 + 1 ≤ M.d 0 1 ∧ M.d 1 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 1)
    (h023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (h024 : M.d 2 4 + 1 ≤ M.d 0 2 ∧ M.d 2 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 2)
    (h034 : M.d 3 4 + 1 ≤ M.d 0 3 ∧ M.d 3 4 < M.d 0 4 ∧ M.d 0 4 < M.d 0 3)
    (h123 : M.d 1 2 + 1 ≤ M.d 2 3 ∧ M.d 1 2 < M.d 1 3 ∧ M.d 1 3 < M.d 2 3)
    (h124 : M.d 2 4 + 1 ≤ M.d 1 2 ∧ M.d 2 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 2)
    (h134 : M.d 3 4 + 1 ≤ M.d 1 3 ∧ M.d 3 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 3)
    (h234 : M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
    (hdef : SixModelCompression.rowDefect M 1 = 3) : False := by
  obtain ⟨h012a, h012b, h012c⟩ := h012
  obtain ⟨h013a, h013b, h013c⟩ := h013
  obtain ⟨h014a, h014b, h014c⟩ := h014
  obtain ⟨h023a, h023b, h023c⟩ := h023
  obtain ⟨h024a, h024b, h024c⟩ := h024
  obtain ⟨h034a, h034b, h034c⟩ := h034
  obtain ⟨h123a, h123b, h123c⟩ := h123
  obtain ⟨h124a, h124b, h124c⟩ := h124
  obtain ⟨h134a, h134b, h134c⟩ := h134
  obtain ⟨h234a, h234b, h234c⟩ := h234
  obtain ⟨hc01a, hc01b⟩ := M.corridor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := M.corridor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := M.corridor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := M.corridor 0 4 (by decide)
  obtain ⟨hc12a, hc12b⟩ := M.corridor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := M.corridor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := M.corridor 1 4 (by decide)
  obtain ⟨hc23a, hc23b⟩ := M.corridor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := M.corridor 2 4 (by decide)
  obtain ⟨hc34a, hc34b⟩ := M.corridor 3 4 (by decide)
  obtain ⟨ht0a, ht0b⟩ := M.theta_bounds 0
  obtain ⟨ht1a, ht1b⟩ := M.theta_bounds 1
  obtain ⟨ht2a, ht2b⟩ := M.theta_bounds 2
  obtain ⟨ht3a, ht3b⟩ := M.theta_bounds 3
  obtain ⟨ht4a, ht4b⟩ := M.theta_bounds 4
  have hdelta := M.hdelta.2
  have hsort : ([M.d 1 4, M.d 0 1, M.d 1 2, M.d 1 3] : List ℝ).Pairwise (· ≤ ·) := by
    simp [List.pairwise_cons]
    repeat' apply And.intro
    all_goals linarith
  have hperm : (M.rowxs 1).Perm [M.d 1 4, M.d 0 1, M.d 1 2, M.d 1 3] := by
    have hp := M.row_perm 1
    have hs0 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
    have he : (((List.finRange 5).erase (1 : Fin 5)).map (M.d 1)) =
        [M.d 0 1, M.d 1 2, M.d 1 3, M.d 1 4] := by
      norm_num [List.finRange, List.ofFn_succ, hs0]
    rw [he] at hp
    exact hp.trans (((((List.Perm.swap (M.d 1 4) (M.d 1 3) []).cons (M.d 1 2)).cons (M.d 0 1)).trans ((List.Perm.swap (M.d 1 4) (M.d 1 2) [M.d 1 3]).cons (M.d 0 1))).trans (List.Perm.swap (M.d 1 4) (M.d 0 1) [M.d 1 2, M.d 1 3]))
  have hrow : M.rowxs 1 = [M.d 1 4, M.d 0 1, M.d 1 2, M.d 1 3] :=
    hperm.eq_of_pairwise' (M.row_sorted 1) hsort
  have hfirst : M.theta 1 + 1 ≤ M.d 1 4 := by linarith
  have hsecond : M.d 1 4 + 1 ≤ M.d 0 1 := by linarith
  have hthird : M.d 0 1 + 1 ≤ M.d 1 2 := by linarith
  have hshort : M.d 1 2 - M.theta 1 < (n : ℝ) := by linarith
  exact model_prefix_terminal M 1 (M.d 1 4) (M.d 0 1)
    (M.d 1 2) (M.d 1 3) hrow hfirst hsecond hthird hdef hshort
#print axioms orientation_948_impossible

-- END GENERATED THREE-GAP CERTIFICATES

end Jsp404.FourRowCertificate
