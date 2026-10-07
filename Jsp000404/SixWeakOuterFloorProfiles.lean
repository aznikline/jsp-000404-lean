import Jsp000404.SixOuterFloorProfiles

/-! SOURCE_ONLY original complete-row positive-cell/weak-two profiles.
The n4 natural full-gap accounting is reused unchanged. Defect upper bounds
express actual row scores; no caller gap, profile or capacity oracle is used. -/
set_option autoImplicit false
namespace Jsp404.SixWeakOuterFloorProfiles
open SatScalarModel SixOuterFloorProfiles
open scoped BigOperators
noncomputable section

private theorem sum_ge_two_cases (s : Fin 5 → ℕ) (hsum : 2 ≤ ∑ k, s k) :
    (∃ i, 2 ≤ s i) ∨ (∃ i j, i < j ∧ 1 ≤ s i ∧ 1 ≤ s j) := by
  classical
  by_cases hlarge : ∃ i, 2 ≤ s i
  · exact Or.inl hlarge
  · have hsmall (i : Fin 5) : s i ≤ 1 := by
      by_contra hi
      exact hlarge ⟨i, by omega⟩
    have hpos : 0 < ∑ k, s k := by omega
    obtain ⟨i,_hi,hi⟩ := Finset.sum_pos_iff.mp hpos
    have hsi : s i = 1 := by have hh := hsmall i; omega
    have herase : 1 ≤ ∑ j ∈ Finset.univ.erase i, s j := by
      have h := Finset.sum_erase_add Finset.univ s (Finset.mem_univ i)
      rw [hsi] at h
      omega
    obtain ⟨j,hjmem,hj⟩ := Finset.sum_pos_iff.mp (by omega : 0 < ∑ j ∈ Finset.univ.erase i, s j)
    have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
    rcases lt_or_gt_of_ne hji with hji | hij
    · exact Or.inr ⟨j,i,hji,by omega,by omega⟩
    · exact Or.inr ⟨i,j,hij,by omega,by omega⟩

private def singleProfile (k : Fin 5) : Fin 15 :=
  ⟨k.val,lt_trans k.isLt (by decide : 5 < 15)⟩

private theorem singleProfile_value (i k : Fin 5) :
    SixOuterReplay.profileLower (singleProfile i) k = if k = i then 3 else 0 := by
  fin_cases i <;> fin_cases k <;> decide

private def pairProfile (i j : Fin 5) : Fin 15 :=
  if i = 0 then
    if j = 1 then 5 else if j = 2 then 6 else if j = 3 then 7 else 8
  else if i = 1 then
    if j = 2 then 9 else if j = 3 then 10 else 11
  else if i = 2 then
    if j = 3 then 12 else 13
  else 14

private theorem pairProfile_value (i j : Fin 5) (hij : i < j) (k : Fin 5) :
    SixOuterReplay.profileLower (pairProfile i j) k = if k = i ∨ k = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals fin_cases k <;> decide

/-- Any actual positive n4 row has a genuine full gap at least two. -/
theorem positive_cell (M : GenericModel 5 4) (i : Fin 5)
    (hdef : SatScalarModel.rowDefect M i ≤ 3) :
    ∃ k : Fin 5, 2 ≤ modelGap M i k := by
  classical
  have hsum := modelGap_score_sum M i (SatScalarModel.rowDefect M i) rfl
  have hpos : 0 < ∑ k : Fin 5, (Nat.floor (modelGap M i k) - 1) := by omega
  obtain ⟨k,_hk,hk⟩ := Finset.sum_pos_iff.mp hpos
  have hfloor : 2 ≤ Nat.floor (modelGap M i k) := by omega
  have hcast : (2 : ℝ) ≤ (Nat.floor (modelGap M i k) : ℝ) := by exact_mod_cast hfloor
  exact ⟨k, le_trans hcast (Nat.floor_le (modelGap_nonneg M i k))⟩

/-- At least two actual score units imply one of15 genuine weak lower profiles.
Unlike the frozen exact-two helper, this also accepts actual score3 or4. -/
theorem weak_two_profile (M : GenericModel 5 4) (i : Fin 5)
    (hdef : SatScalarModel.rowDefect M i ≤ 2) :
    ∃ p : Fin 15, ∀ k : Fin 5,
      (SixOuterReplay.profileLower p k : ℝ) ≤ modelGap M i k := by
  let s : Fin 5 → ℕ := fun k => Nat.floor (modelGap M i k) - 1
  have hbudget := modelGap_score_sum M i (SatScalarModel.rowDefect M i) rfl
  have hsum : 2 ≤ ∑ k, s k := by change 2 ≤ ∑ k, (Nat.floor (modelGap M i k) - 1); omega
  have hlower (k : Fin 5) : (s k : ℝ) + (min (s k) 1 : ℕ) ≤ modelGap M i k :=
    (SixExactFloorKernel.score_gap_min_interval _ (modelGap_nonneg M i k)).1
  rcases sum_ge_two_cases s hsum with ⟨ki,hki⟩ | ⟨a,b,hab,ha,hb⟩
  · have hm : min (s ki) 1 = 1 := by omega
    have hsi : (2 : ℝ) ≤ (s ki : ℝ) := by exact_mod_cast hki
    have hgap := hlower ki
    rw [hm] at hgap
    have hg : (3 : ℝ) ≤ modelGap M i ki := by norm_num at hgap; linarith
    refine ⟨singleProfile ki,?_⟩
    intro k
    rw [singleProfile_value]
    by_cases hk : k = ki
    · simpa [hk] using hg
    · simpa [hk] using modelGap_nonneg M i k
  · have hga : (2 : ℝ) ≤ modelGap M i a := by
      have h := hlower a
      have hm : min (s a) 1 = 1 := by omega
      rw [hm] at h
      have hc : (1 : ℝ) ≤ (s a : ℝ) := by exact_mod_cast ha
      norm_num at h
      linarith
    have hgb : (2 : ℝ) ≤ modelGap M i b := by
      have h := hlower b
      have hm : min (s b) 1 = 1 := by omega
      rw [hm] at h
      have hc : (1 : ℝ) ≤ (s b : ℝ) := by exact_mod_cast hb
      norm_num at h
      linarith
    refine ⟨pairProfile a b,?_⟩
    intro k
    rw [pairProfile_value a b hab]
    by_cases hk : k = a ∨ k = b
    · rcases hk with rfl | rfl
      · simpa using hga
      · simpa using hgb
    · simpa [hk] using modelGap_nonneg M i k

end
#print axioms positive_cell
#print axioms weak_two_profile
end Jsp404.SixWeakOuterFloorProfiles
