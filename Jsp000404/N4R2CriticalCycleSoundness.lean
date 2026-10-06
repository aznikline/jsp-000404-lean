import Jsp000404.N4R2CriticalReifiedRow

/-!
# Ordinary soundness of closed affine difference-constraint cycles

No SMT result is a premise or a field. Cycle inequalities are ordinary real
inequalities; closure telescopes
their variable terms. The final model sample covers one explicit internal
direction/profile subcase, not all words or the eight-point theorem.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2CriticalCycleSoundness

open SatScalarModel N4R2CriticalReifiedRow
open scoped BigOperators

/-- Sum of every consecutive difference of a finite extended sequence. -/
theorem sum_consecutive_differences (k : ℕ) (x : Fin (k + 1) → ℝ) :
    (∑ j : Fin k, (x j.succ - x j.castSucc)) = x (Fin.last k) - x 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    have h := ih (fun j => x j.succ)
    change (x (0 : Fin (k + 1)).succ - x (0 : Fin (k + 2))) +
      (∑ j : Fin k, (x j.succ.succ - x j.castSucc.succ)) =
      x (Fin.last (k + 1)) - x (0 : Fin (k + 2))
    rw [h, Fin.succ_last]
    ring

theorem affine_sum (k : ℕ) (c b : Fin k → ℝ) (delta : ℝ) :
    (∑ j : Fin k, (c j + b j * delta)) =
      (∑ j : Fin k, c j) + (∑ j : Fin k, b j) * delta := by
  rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- A closed weak cycle cannot have a negative total affine weight. -/
theorem closed_cycle_nonstrict_exclusion (k : ℕ) (x : Fin (k + 1) → ℝ)
    (c b : Fin k → ℝ) (delta : ℝ)
    (hclosed : x (Fin.last k) = x 0)
    (hstep : ∀ j : Fin k, x j.succ - x j.castSucc ≤ c j + b j * delta)
    (hnegative : (∑ j : Fin k, c j) + (∑ j : Fin k, b j) * delta < 0) : False := by
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hstep j)
  rw [sum_consecutive_differences, hclosed, sub_self, affine_sum] at hsum
  linarith

/-- One strict edge makes a closed cycle's total affine weight positive. -/
theorem closed_cycle_strict_exclusion (k : ℕ) (x : Fin (k + 1) → ℝ)
    (c b : Fin k → ℝ) (delta : ℝ)
    (hclosed : x (Fin.last k) = x 0)
    (hstep : ∀ j : Fin k, x j.succ - x j.castSucc ≤ c j + b j * delta)
    (hstrict : ∃ j : Fin k, x j.succ - x j.castSucc < c j + b j * delta)
    (hnonpositive : (∑ j : Fin k, c j) + (∑ j : Fin k, b j) * delta ≤ 0) : False := by
  obtain ⟨j, hj⟩ := hstrict
  have hsum := Finset.sum_lt_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hstep j)
    ⟨j, Finset.mem_univ j, hj⟩
  rw [sum_consecutive_differences, hclosed, sub_self, affine_sum] at hsum
  linarith

def edgeHolds (strict : Bool) (before after c b delta : ℝ) : Prop :=
  if strict then after - before < c + b * delta else after - before ≤ c + b * delta

/-- Both strict and weak actual edges are handled without external solver
certification. The final numeric sign must be proved in ordinary arithmetic. -/
theorem closed_affine_cycle_exclusion (k : ℕ) (x : Fin (k + 1) → ℝ)
    (c b : Fin k → ℝ) (strict : Fin k → Bool) (delta : ℝ)
    (hclosed : x (Fin.last k) = x 0)
    (hstep : ∀ j : Fin k, edgeHolds (strict j) (x j.castSucc) (x j.succ) (c j) (b j) delta)
    (hnegative : ((∑ j : Fin k, c j) + (∑ j : Fin k, b j) * delta < 0) ∨
      ((∑ j : Fin k, c j) + (∑ j : Fin k, b j) * delta ≤ 0 ∧ ∃ j, strict j = true)) : False := by
  have hweak : ∀ j : Fin k, x j.succ - x j.castSucc ≤ c j + b j * delta := by
    intro j
    have h := hstep j
    cases hs : strict j
    · simpa only [edgeHolds, hs, Bool.false_eq_true, ↓reduceIte] using h
    · exact le_of_lt (by simpa only [edgeHolds, hs, ↓reduceIte] using h)
  rcases hnegative with hneg | ⟨hnonpos, j, hj⟩
  · exact closed_cycle_nonstrict_exclusion k x c b delta hclosed hweak hneg
  · have hstrict : x j.succ - x j.castSucc < c j + b j * delta := by
      simpa only [edgeHolds, hj, ↓reduceIte] using hstep j
    exact closed_cycle_strict_exclusion k x c b delta hclosed hweak ⟨j, hstrict⟩ hnonpos

def sampleOrd0 : Fin 6 → Fin 7 := ![3, 4, 5, 6, 2, 1]
def sampleOrd6 : Fin 6 → Fin 7 := ![2, 1, 0, 5, 3, 4]

theorem sampleOrd0_perm : (List.ofFn sampleOrd0).Perm ((List.finRange 7).erase (0 : Fin 7)) := by
  decide

theorem sampleOrd6_perm : (List.ofFn sampleOrd6).Perm ((List.finRange 7).erase (6 : Fin 7)) := by
  decide

/-- The five-arc core of residual word8/profile pair (10,21). Sorting
premises are explicit helper conditions; an internal ModelWordSoundness
interpretation is still required before any all-word theorem.

Every gap in the weak-profile premises is an actual complete Model row gap.
The common reified-row bridge identifies those gaps with the selected row
order; actual corridors and one actual reverse triangle arm then close the
cycle. No tail/goal-capacity/solver-feasibility assumption is introduced. -/
theorem residual_word8_profile_pair_excluded (M : GenericModel 7 4)
    (hsort0 : (List.ofFn (fun k => M.d 0 (sampleOrd0 k))).Pairwise (· ≤ ·))
    (hsort6 : (List.ofFn (fun k => M.d 6 (sampleOrd6 k))).Pairwise (· ≤ ·))
    (htri012 : M.d 1 2 + 1 ≤ M.d 0 1 ∧ M.d 1 2 < M.d 0 2 ∧ M.d 0 2 < M.d 0 1)
    (hprofile0 : 2 ≤ modelGap M 0 0 ∧ 2 ≤ modelGap M 0 4)
    (hprofile6 : 2 ≤ modelGap M 6 2 ∧ 2 ≤ modelGap M 6 6) : False := by
  have hrow0 := fullGaps_eq_modelGap_of_perm_sorted M 0 sampleOrd0 sampleOrd0_perm hsort0
  have hrow6 := fullGaps_eq_modelGap_of_perm_sorted M 6 sampleOrd6 sampleOrd6_perm hsort6
  have hg04 : 2 ≤ M.d 0 2 - M.d 0 6 := by
    have h := hprofile0.2
    rw [← hrow0] at h
    simpa [fullGaps, sampleOrd0] using h
  have hs60 : M.d 6 0 = M.d 0 6 := M.symm 6 0 (by decide)
  have hs61 : M.d 6 1 = M.d 1 6 := M.symm 6 1 (by decide)
  have hg62 : 2 ≤ M.d 0 6 - M.d 1 6 := by
    have h := hprofile6.1
    rw [← hrow6] at h
    simpa [fullGaps, sampleOrd6, hs60, hs61] using h
  have hc16 := (M.corridor 1 6 (by decide)).1
  have hc01 := (M.corridor 0 1 (by decide)).2
  norm_num at hc01
  apply closed_affine_cycle_exclusion 5
    (![M.d 0 1, M.d 0 2, M.d 0 6, M.d 1 6, M.theta 1, M.d 0 1])
    (![0, -2, -2, -1, 3]) (![0, 0, 0, 0, 1])
    (![true, false, false, false, false]) M.delta
  · rfl
  · intro j
    fin_cases j <;> norm_num [edgeHolds]
    all_goals linarith [htri012.2.2]
  · left
    norm_num [Fin.sum_univ_succ]
    linarith [M.hdelta.2]

#print axioms sum_consecutive_differences
#print axioms affine_sum
#print axioms closed_cycle_nonstrict_exclusion
#print axioms closed_cycle_strict_exclusion
#print axioms closed_affine_cycle_exclusion
#print axioms sampleOrd0_perm
#print axioms sampleOrd6_perm
#print axioms residual_word8_profile_pair_excluded

#check closed_affine_cycle_exclusion
#check residual_word8_profile_pair_excluded

end Jsp404.N4R2CriticalCycleSoundness
