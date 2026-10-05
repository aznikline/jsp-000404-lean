import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
Pure finite arithmetic for the n=4 R2 tail.  The anchor and two low rows
have total weight 16, so an over-20 configuration has tail weight >4.
This file classifies minimal tails with weights 1 or 2 and selects an
over-4 tail subset of at most five elements.  It assumes no geometric
capacity theorem and contains no scalar-model certificate.
-/

set_option autoImplicit false

namespace Jsp404.R2CriticalWeightClassification

open scoped BigOperators

variable {ι : Type*}

/-- Count the tail rows with a given weight. -/
noncomputable def weightCount (T : Finset ι) (w : ι → ℕ) (k : ℕ) : ℕ := by
  classical
  exact (T.filter (fun i => w i = k)).card

/-- The full tail sum is the number of weight-1 rows plus twice the
number of weight-2 rows. -/
theorem tail_sum_eq_counts (T : Finset ι) (w : ι → ℕ)
    (hw : ∀ i ∈ T, w i = 1 ∨ w i = 2) :
    (∑ i ∈ T, w i) = weightCount T w 1 + 2 * weightCount T w 2 := by
  classical
  calc
    (∑ i ∈ T, w i) =
        ∑ i ∈ T, ((if w i = 1 then 1 else 0) +
          (if w i = 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hw i hi with h | h <;> simp [h]
    _ = weightCount T w 1 + 2 * weightCount T w 2 := by
      rw [Finset.sum_add_distrib]
      simp [weightCount, Finset.sum_ite, Nat.mul_comm]

/-- Weight-1/2 tails have total weight at most twice their cardinality. -/
theorem tail_sum_le_two_mul_card (T : Finset ι) (w : ι → ℕ)
    (hw : ∀ i ∈ T, w i = 1 ∨ w i = 2) :
    (∑ i ∈ T, w i) ≤ 2 * T.card := by
  calc
    (∑ i ∈ T, w i) ≤ ∑ _i ∈ T, 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rcases hw i hi with h | h <;> omega
    _ = 2 * T.card := by simp [Nat.mul_comm]

/-- The only minimal over-4 tail count pairs `(weight2, weight1)` are
`(3,0)`, `(2,1)`, `(1,3)`, and `(0,5)`.

The deletion hypothesis concerns the original surviving weight sum only;
it does not assume a capacity theorem for any configuration. -/
theorem minimal_tail_count_classification (T : Finset ι) (w : ι → ℕ)
    (hw : ∀ i ∈ T, w i = 1 ∨ w i = 2)
    (hover : 4 < ∑ i ∈ T, w i)
    (hdelete : ∀ q ∈ T, (∑ i ∈ T, w i) - w q ≤ 4) :
    (weightCount T w 2 = 3 ∧ weightCount T w 1 = 0) ∨
    (weightCount T w 2 = 2 ∧ weightCount T w 1 = 1) ∨
    (weightCount T w 2 = 1 ∧ weightCount T w 1 = 3) ∨
    (weightCount T w 2 = 0 ∧ weightCount T w 1 = 5) := by
  classical
  have hsum := tail_sum_eq_counts T w hw
  by_cases hone : (T.filter (fun i => w i = 1)).Nonempty
  · obtain ⟨q, hq⟩ := hone
    obtain ⟨hqT, hq1⟩ := Finset.mem_filter.mp hq
    have hsmall := hdelete q hqT
    have hcount : 0 < weightCount T w 1 := by
      unfold weightCount
      exact Finset.card_pos.mpr ⟨q, hq⟩
    rw [hq1] at hsmall
    omega
  · have hzero : weightCount T w 1 = 0 := by
      unfold weightCount
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hone)
    have hne : T.Nonempty := by
      by_contra h
      have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [hT] at hover
    obtain ⟨q, hq⟩ := hne
    have hq2 : w q = 2 := by
      rcases hw q hq with hq1 | hq2
      · exact False.elim (hone ⟨q, Finset.mem_filter.mpr ⟨hq, hq1⟩⟩)
      · exact hq2
    have hsmall := hdelete q hq
    rw [hq2] at hsmall
    omega

/-- Any over-4 tail with weights 1 or 2 contains an over-4 subset of
three to five tails.  In a geometric R2 configuration these tails and
the three distinguished rows give a subset of at most eight centres;
preservation of scores under deletion is a separate geometric step. -/
theorem exists_over_four_subset_card_le_five (T : Finset ι) (w : ι → ℕ)
    (hw : ∀ i ∈ T, w i = 1 ∨ w i = 2)
    (hover : 4 < ∑ i ∈ T, w i) :
    ∃ U : Finset ι, U ⊆ T ∧ 3 ≤ U.card ∧ U.card ≤ 5 ∧
      4 < ∑ i ∈ U, w i := by
  by_cases hcard : T.card ≤ 5
  · have hbound := tail_sum_le_two_mul_card T w hw
    exact ⟨T, Finset.Subset.refl T, by omega, hcard, hover⟩
  · have hfive : 5 ≤ T.card := by omega
    obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hfive
    have hweight : 5 ≤ ∑ i ∈ U, w i := by
      calc
        5 = ∑ _i ∈ U, 1 := by simp [hUcard]
        _ ≤ ∑ i ∈ U, w i := by
          apply Finset.sum_le_sum
          intro i hi
          rcases hw i (hUT hi) with h | h <;> omega
    exact ⟨U, hUT, by omega, by omega, by omega⟩

#print axioms tail_sum_eq_counts
#print axioms tail_sum_le_two_mul_card
#print axioms minimal_tail_count_classification
#print axioms exists_over_four_subset_card_le_five

end Jsp404.R2CriticalWeightClassification
