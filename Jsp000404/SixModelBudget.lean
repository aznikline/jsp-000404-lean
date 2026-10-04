import Jsp000404.SixModelCompression

/-!
Arithmetic budgets for the finite necessary six-centre scalar model.
These statements concern the existing shared-chord model, rather than a
planar realization or an SMT certificate.
-/

namespace Jsp404.SixModelBudget

open SixModelCompression

noncomputable def cells {n : ℕ} (M : ModelSix n) (i : Fin 5) : ℕ :=
  linearFloorSum 1 (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)

noncomputable def support {n : ℕ} (M : ModelSix n) (i : Fin 5) : ℕ :=
  linearBigCount 1 (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)

noncomputable def loss {n : ℕ} (M : ModelSix n) (i : Fin 5) : ℕ :=
  n - cells M i

theorem cells_le {n : ℕ} (M : ModelSix n) (i : Fin 5) : cells M i ≤ n := by
  have h := linearFloorSum_le_floor 1 (M.theta i)
    (M.theta i + ((n : ℝ) + M.delta)) (by norm_num) (M.rowxs i) (M.row_sorted i)
    (by
      intro x hx
      have hb := row_mem_bounds M i x hx
      have ht := M.theta_bounds i
      constructor <;> linarith [M.hdelta.2])
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hf : ⌊(n : ℝ) + M.delta⌋₊ = n := by
    apply (Nat.floor_eq_iff (by linarith [M.hdelta.1] : 0 ≤ (n : ℝ) + M.delta)).mpr
    constructor <;> linarith [M.hdelta.1, M.hdelta.2]
  simpa only [cells, add_sub_cancel_left, div_one, hf] using h

theorem score_add_support {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    linearGapScore 1 (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i) +
      support M i = cells M i :=
  linearGapScore_add_bigCount 1 (M.theta i)
    (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)

theorem support_add_loss {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    support M i + loss M i = SixModelCompression.rowDefect M i := by
  have hc := cells_le M i
  have hs := score_add_support M i
  unfold loss SixModelCompression.rowDefect
  omega

theorem support_le_defect {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    support M i ≤ SixModelCompression.rowDefect M i := by
  have := support_add_loss M i
  omega

private theorem score_eq_zero_of_bigCount_eq_zero (left right : ℝ) (xs : List ℝ)
    (h : linearBigCount 1 left right xs = 0) :
    linearGapScore 1 left right xs = 0 := by
  induction xs generalizing left with
  | nil =>
    simp only [linearBigCount, linearGapScore, gapScore, div_one] at *
    omega
  | cons x xs ih =>
    have hs : linearBigCount 1 x right xs = 0 := by
      simpa only [linearBigCount, Nat.add_eq_zero_iff] using (Nat.add_eq_zero_iff.mp h).2
    have hh : min ⌊x - left⌋₊ 1 = 0 := by
      simpa only [linearBigCount, div_one] using (Nat.add_eq_zero_iff.mp h).1
    have ht := ih x hs
    simp only [linearGapScore, gapScore, div_one, ht]
    omega

theorem support_pos_of_defect_lt {n : ℕ} (M : ModelSix n) (i : Fin 5)
    (hdef : SixModelCompression.rowDefect M i < n) : 0 < support M i := by
  by_contra h
  have hs : support M i = 0 := by omega
  have hscore := score_eq_zero_of_bigCount_eq_zero (M.theta i)
    (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i) hs
  unfold SixModelCompression.rowDefect at hdef
  rw [hscore] at hdef
  omega

/-- A defect-two row has only two integer budget shapes.  In particular,
no third unit-sized gap can occur, and a sole active gap costs one lost cell. -/
theorem defect_two_budget {n : ℕ} (M : ModelSix n) (i : Fin 5)
    (hdef : SixModelCompression.rowDefect M i = 2) :
    (support M i = 1 ∧ loss M i = 1) ∨
      (support M i = 2 ∧ loss M i = 0) := by
  have hc := support_add_loss M i
  have hn := M.hn
  have hp := support_pos_of_defect_lt M i (by omega)
  omega

/-- A defect-three row in every strip above the bottom strip likewise has
only the three integral support/loss shapes used by the certificate search. -/
theorem defect_three_budget {n : ℕ} (M : ModelSix n) (i : Fin 5)
    (hn : 4 ≤ n) (hdef : SixModelCompression.rowDefect M i = 3) :
    (support M i = 1 ∧ loss M i = 2) ∨
      (support M i = 2 ∧ loss M i = 1) ∨
      (support M i = 3 ∧ loss M i = 0) := by
  have hc := support_add_loss M i
  have hp := support_pos_of_defect_lt M i (by omega)
  omega

/-- The full finite-model row budget, stated without truncation ambiguity. -/
theorem row_budget {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    cells M i + loss M i = n ∧
    support M i + loss M i = SixModelCompression.rowDefect M i ∧
    linearGapScore 1 (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i) +
      SixModelCompression.rowDefect M i = n := by
  have hc := cells_le M i
  have hs := score_add_support M i
  have hb := support_add_loss M i
  unfold loss at *
  omega

#print axioms defect_three_budget
#print axioms row_budget
#print axioms cells_le
#print axioms support_add_loss
#print axioms defect_two_budget

end Jsp404.SixModelBudget
