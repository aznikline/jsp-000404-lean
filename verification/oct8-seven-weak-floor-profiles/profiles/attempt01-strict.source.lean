import Jsp000404.SatScalarModel
import Jsp000404.StrongGapBudget
import Jsp000404.N4R2CriticalReifiedRow
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY finite necessary floor profiles for GenericModel6 at strip4.
Five chord entries give exactly six complete linear gaps, retaining both
endpoints. All natural-floor bounds follow from the existing generic list
accounting. No HIGH assumption, caller floor ceiling, accepted order, solver
result or seven-point impossibility theorem is introduced.

The weak-two profile IDs are0..5 for one selected gap >=3 and6..20 for two
selected gaps >=2, with pairs in increasing lexicographic order. Positive
cell IDs are the six actual gap positions. These are overlapping lower
profiles, not exact raw-floor values. This candidate has not been compiled.
-/

open scoped BigOperators

namespace Jsp404.SevenWeakFloorProfiles

open SatScalarModel StrongGapBudget

noncomputable section

def modelGaps (M : GenericModel 6 4) (i : Fin 6) : List ℝ :=
  linearGaps (M.theta i) (M.theta i + (4 + M.delta)) (M.rowxs i)

theorem modelGaps_length (M : GenericModel 6 4) (i : Fin 6) :
    (modelGaps M i).length = 6 := by
  rw [modelGaps, N4R2CriticalReifiedRow.linearGaps_length, rowxs_length]

def modelGap (M : GenericModel 6 4) (i k : Fin 6) : ℝ :=
  (modelGaps M i).get (Fin.cast (modelGaps_length M i).symm k)

theorem ofFn_modelGap (M : GenericModel 6 4) (i : Fin 6) :
    List.ofFn (modelGap M i) = modelGaps M i := by
  have h := List.ofFn_congr (modelGaps_length M i) (modelGaps M i).get
  exact h.symm.trans (List.ofFn_get (modelGaps M i))

theorem modelGap_nonneg (M : GenericModel 6 4) (i k : Fin 6) :
    0 ≤ modelGap M i k := by
  have hnonneg : ∀ g ∈ modelGaps M i, 0 ≤ g := by
    apply linearGaps_nonneg _ _ _ (by linarith [M.hdelta.1]) (M.row_sorted i)
    intro x hx
    have hb := row_mem_bounds M i x hx
    have ht := M.theta_bounds i
    constructor <;> linarith [M.hdelta.2]
  apply hnonneg
  rw [← ofFn_modelGap M i]
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

/-- Exact complete-row score accounting; its floor ceiling is derived
internally from the actual sorted row and full interval length4+delta. -/
theorem modelGap_score_sum (M : GenericModel 6 4) (i : Fin 6) (c : ℕ)
    (hdef : SatScalarModel.rowDefect M i = c) :
    (∑ k : Fin 6, (Nat.floor (modelGap M i k) - 1)) + c = 4 := by
  have hf : Nat.floor ((4 : ℝ) + M.delta) = 4 := by
    apply (Nat.floor_eq_iff (by linarith [M.hdelta.1] : 0 ≤ (4 : ℝ) + M.delta)).mpr
    constructor <;> linarith [M.hdelta.1, M.hdelta.2]
  have hcells : linearFloorSum 1 (M.theta i)
      (M.theta i + (4 + M.delta)) (M.rowxs i) ≤ 4 := by
    have h := linearFloorSum_le_floor 1 (M.theta i)
      (M.theta i + (4 + M.delta)) (by norm_num) (M.rowxs i) (M.row_sorted i) (by
        intro x hx
        have hb := row_mem_bounds M i x hx
        have ht := M.theta_bounds i
        constructor <;> linarith [M.hdelta.2])
    simpa only [add_sub_cancel_left, div_one, hf] using h
  have hadd := linearGapScore_add_bigCount 1 (M.theta i)
    (M.theta i + (4 + M.delta)) (M.rowxs i)
  have hscore : linearGapScore 1 (M.theta i)
      (M.theta i + (4 + M.delta)) (M.rowxs i) ≤ 4 := by omega
  have hbudget : linearGapScore 1 (M.theta i)
      (M.theta i + (4 + M.delta)) (M.rowxs i) + SatScalarModel.rowDefect M i = 4 := by
    unfold SatScalarModel.rowDefect
    omega
  rw [hdef, ← linear_score_eq] at hbudget
  change score (modelGaps M i) + c = 4 at hbudget
  rw [← ofFn_modelGap M i] at hbudget
  simpa only [score, List.map_ofFn, List.sum_ofFn, Function.comp_def] using hbudget

/-- Six single3 profiles, then fifteen pair2 profiles in lexicographic order. -/
def profileLower : Fin 21 → Fin 6 → ℕ := ![
  ![3,0,0,0,0,0], ![0,3,0,0,0,0], ![0,0,3,0,0,0],
  ![0,0,0,3,0,0], ![0,0,0,0,3,0], ![0,0,0,0,0,3],
  ![2,2,0,0,0,0], ![2,0,2,0,0,0], ![2,0,0,2,0,0],
  ![2,0,0,0,2,0], ![2,0,0,0,0,2], ![0,2,2,0,0,0],
  ![0,2,0,2,0,0], ![0,2,0,0,2,0], ![0,2,0,0,0,2],
  ![0,0,2,2,0,0], ![0,0,2,0,2,0], ![0,0,2,0,0,2],
  ![0,0,0,2,2,0], ![0,0,0,2,0,2], ![0,0,0,0,2,2]]

def positiveLower (t k : Fin 6) : ℕ := if k = t then 2 else 0

private theorem sum_ge_two_cases {m : ℕ} (s : Fin m → ℕ) (hsum : 2 ≤ ∑ k, s k) :
    (∃ i, 2 ≤ s i) ∨ (∃ i j, i < j ∧ 1 ≤ s i ∧ 1 ≤ s j) := by
  classical
  by_cases hlarge : ∃ i, 2 ≤ s i
  · exact Or.inl hlarge
  · have hsmall (i : Fin m) : s i ≤ 1 := by
      by_contra hi
      exact hlarge ⟨i, by omega⟩
    obtain ⟨i, _hi, hi⟩ := Finset.sum_pos_iff.mp (by omega : 0 < ∑ k, s k)
    have hsi : s i = 1 := by have hh := hsmall i; omega
    have herase : 1 ≤ ∑ j ∈ Finset.univ.erase i, s j := by
      have h := Finset.sum_erase_add Finset.univ s (Finset.mem_univ i)
      rw [hsi] at h
      omega
    obtain ⟨j, hjmem, hj⟩ := Finset.sum_pos_iff.mp
      (by omega : 0 < ∑ j ∈ Finset.univ.erase i, s j)
    have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
    rcases lt_or_gt_of_ne hji with hji | hij
    · exact Or.inr ⟨j, i, hji, by omega, by omega⟩
    · exact Or.inr ⟨i, j, hij, by omega, by omega⟩

private def singleProfile (k : Fin 6) : Fin 21 :=
  ⟨k.val, lt_trans k.isLt (by decide : 6 < 21)⟩

private theorem singleProfile_value (i k : Fin 6) :
    profileLower (singleProfile i) k = if k = i then 3 else 0 := by
  fin_cases i <;> fin_cases k <;> decide

private def pairProfile (i j : Fin 6) : Fin 21 :=
  if i = 0 then
    if j = 1 then 6 else if j = 2 then 7 else if j = 3 then 8 else if j = 4 then 9 else 10
  else if i = 1 then
    if j = 2 then 11 else if j = 3 then 12 else if j = 4 then 13 else 14
  else if i = 2 then
    if j = 3 then 15 else if j = 4 then 16 else 17
  else if i = 3 then
    if j = 4 then 18 else 19
  else 20

private theorem pairProfile_value (i j : Fin 6) (hij : i < j) (k : Fin 6) :
    profileLower (pairProfile i j) k = if k = i ∨ k = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals fin_cases k <;> decide

private theorem gap_lower_of_score (M : GenericModel 6 4) (i k : Fin 6)
    (r : ℕ) (hr : 1 ≤ r) (hs : r ≤ Nat.floor (modelGap M i k) - 1) :
    ((r + 1 : ℕ) : ℝ) ≤ modelGap M i k := by
  have hfloor : r + 1 ≤ Nat.floor (modelGap M i k) := by omega
  have hcast : ((r + 1 : ℕ) : ℝ) ≤ (Nat.floor (modelGap M i k) : ℝ) := by
    exact_mod_cast hfloor
  exact hcast.trans (Nat.floor_le (modelGap_nonneg M i k))

/-- Any positive row supplies one of the six genuine gap>=2 cells. -/
theorem positive_cell (M : GenericModel 6 4) (i : Fin 6)
    (hdef : SatScalarModel.rowDefect M i ≤ 3) :
    ∃ k : Fin 6, 2 ≤ modelGap M i k := by
  have hsum := modelGap_score_sum M i (SatScalarModel.rowDefect M i) rfl
  obtain ⟨k, _hk, hk⟩ := Finset.sum_pos_iff.mp
    (by omega : 0 < ∑ k : Fin 6, (Nat.floor (modelGap M i k) - 1))
  exact ⟨k, by simpa using gap_lower_of_score M i k 1 (by decide) (by omega)⟩

/-- A positive row has one of six pointwise lower profiles, with no upper
floor or HIGH assumption. The zero lower entries retain all genuine gaps. -/
theorem positive_profile (M : GenericModel 6 4) (i : Fin 6)
    (hdef : SatScalarModel.rowDefect M i ≤ 3) :
    ∃ t : Fin 6, ∀ k : Fin 6, (positiveLower t k : ℝ) ≤ modelGap M i k := by
  obtain ⟨t, ht⟩ := positive_cell M i hdef
  refine ⟨t, ?_⟩
  intro k
  by_cases hk : k = t
  · simpa [positiveLower, hk] using ht
  · simpa [positiveLower, hk] using modelGap_nonneg M i k

/-- At least two actual score units select one of the21 weak lower
profiles. Larger actual scores are admitted; no exact floor value is assumed. -/
theorem weak_two_profile (M : GenericModel 6 4) (i : Fin 6)
    (hdef : SatScalarModel.rowDefect M i ≤ 2) :
    ∃ p : Fin 21, ∀ k : Fin 6, (profileLower p k : ℝ) ≤ modelGap M i k := by
  let s : Fin 6 → ℕ := fun k => Nat.floor (modelGap M i k) - 1
  have hbudget := modelGap_score_sum M i (SatScalarModel.rowDefect M i) rfl
  have hsum : 2 ≤ ∑ k, s k := by
    change 2 ≤ ∑ k : Fin 6, (Nat.floor (modelGap M i k) - 1)
    omega
  rcases sum_ge_two_cases s hsum with ⟨ki, hki⟩ | ⟨a, b, hab, ha, hb⟩
  · have hg : (3 : ℝ) ≤ modelGap M i ki :=
      by simpa only [show (2 + 1 : ℕ) = 3 by decide] using
        gap_lower_of_score M i ki 2 (by decide) hki
    refine ⟨singleProfile ki, ?_⟩
    intro k
    rw [singleProfile_value]
    by_cases hk : k = ki
    · simpa [hk] using hg
    · simpa [hk] using modelGap_nonneg M i k
  · have hga : (2 : ℝ) ≤ modelGap M i a := by
      simpa using gap_lower_of_score M i a 1 (by decide) ha
    have hgb : (2 : ℝ) ≤ modelGap M i b := by
      simpa using gap_lower_of_score M i b 1 (by decide) hb
    refine ⟨pairProfile a b, ?_⟩
    intro k
    rw [pairProfile_value a b hab]
    by_cases hk : k = a ∨ k = b
    · rcases hk with rfl | rfl
      · simpa using hga
      · simpa using hgb
    · simpa [hk] using modelGap_nonneg M i k

end

#print axioms modelGaps_length
#print axioms modelGap_nonneg
#print axioms modelGap_score_sum
#print axioms positive_profile
#print axioms weak_two_profile

end Jsp404.SevenWeakFloorProfiles
