import Jsp000404.SatScalarExtraction
import Jsp000404.N4R2CriticalReifiedRow
import Jsp000404.SixExactFloorKernelSymbolicInterval
import Jsp000404.SmallScoreGapBounds
import Jsp000404.SixOuterReplay

set_option autoImplicit false

/-! SOURCE_ONLY. Complete fixed-n4 five-row floor profiles for the six-center
outer prototype. Every gap includes both genuine linear endpoints. Row
orders are chosen from the original model labels; a proposed decoder order
is compared only after proving its full permutation and scalar sorting.
No native checker, capacity premise, gap budget, or exhaustive-word claim
is used here.
-/

open scoped BigOperators

namespace Jsp404.SixOuterFloorProfiles

open SatScalarModel StrongGapBudget

noncomputable section

def modelGaps (M : GenericModel 5 4) (i : Fin 5) : List ℝ :=
  SmallScoreGapBounds.modelGaps (SatScalarExtraction.toModelSix M) i

theorem modelGaps_length (M : GenericModel 5 4) (i : Fin 5) :
    (modelGaps M i).length = 5 := by
  change (linearGaps (M.theta i) (M.theta i + (4 + M.delta)) (M.rowxs i)).length = 5
  rw [N4R2CriticalReifiedRow.linearGaps_length,SatScalarModel.rowxs_length]
  norm_num

def modelGap (M : GenericModel 5 4) (i k : Fin 5) : ℝ :=
  (modelGaps M i).get (Fin.cast (modelGaps_length M i).symm k)

theorem ofFn_modelGap (M : GenericModel 5 4) (i : Fin 5) :
    List.ofFn (modelGap M i) = modelGaps M i := by
  have h := List.ofFn_congr (modelGaps_length M i) (modelGaps M i).get
  exact h.symm.trans (List.ofFn_get (modelGaps M i))

theorem modelGap_mem (M : GenericModel 5 4) (i k : Fin 5) :
    modelGap M i k ∈ modelGaps M i := by
  rw [← ofFn_modelGap]
  exact List.mem_ofFn.mpr ⟨k,rfl⟩

theorem modelGap_nonneg (M : GenericModel 5 4) (i k : Fin 5) :
    0 ≤ modelGap M i k :=
  SmallScoreGapBounds.model_gaps_nonneg (SatScalarExtraction.toModelSix M) i
    _ (modelGap_mem M i k)

/-- The four actual chord entries and both complete linear endpoints. -/
def fullGaps (M : GenericModel 5 4) (i : Fin 5) (ord : Fin 4 → Fin 5) : Fin 5 → ℝ := ![
  M.d i (ord 0) - M.theta i,
  M.d i (ord 1) - M.d i (ord 0),
  M.d i (ord 2) - M.d i (ord 1),
  M.d i (ord 3) - M.d i (ord 2),
  M.theta i + (4 + M.delta) - M.d i (ord 3)]

theorem rowxs_eq_map_of_perm_sorted (M : GenericModel 5 4) (i : Fin 5)
    (ord : List (Fin 5)) (hperm : ord.Perm ((List.finRange 5).erase i))
    (hsorted : (ord.map (M.d i)).Pairwise (· ≤ ·)) :
    M.rowxs i = ord.map (M.d i) := by
  have hp := (M.row_perm i).trans (hperm.map (M.d i)).symm
  exact hp.eq_of_pairwise' (M.row_sorted i) hsorted

theorem ofFn_fullGaps (M : GenericModel 5 4) (i : Fin 5) (ord : Fin 4 → Fin 5) :
    List.ofFn (fullGaps M i ord) = linearGaps (M.theta i)
      (M.theta i + (4 + M.delta)) (List.ofFn (fun k => M.d i (ord k))) := by
  norm_num [List.ofFn_succ,fullGaps,linearGaps]

theorem fullGaps_eq_modelGap_of_perm_sorted (M : GenericModel 5 4) (i : Fin 5)
    (ord : Fin 4 → Fin 5)
    (hperm : (List.ofFn ord).Perm ((List.finRange 5).erase i))
    (hsorted : (List.ofFn (fun k => M.d i (ord k))).Pairwise (· ≤ ·)) :
    fullGaps M i ord = modelGap M i := by
  have hs : ((List.ofFn ord).map (M.d i)).Pairwise (· ≤ ·) := by
    simpa only [List.map_ofFn,Function.comp_def] using hsorted
  have he := rowxs_eq_map_of_perm_sorted M i (List.ofFn ord) hperm hs
  have hl : List.ofFn (fullGaps M i ord) = modelGaps M i := by
    rw [ofFn_fullGaps]
    change linearGaps _ _ _ = linearGaps _ _ (M.rowxs i)
    rw [he,List.map_ofFn]
    rfl
  exact List.ofFn_injective (hl.trans (ofFn_modelGap M i).symm)

private theorem exists_actualRowOrder (M : GenericModel 5 4) (i : Fin 5) :
    ∃ ord : Fin 4 → Fin 5,
      (List.ofFn ord).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (ord k))).Pairwise (· ≤ ·) := by
  classical
  let rel : Fin 5 → Fin 5 → Prop := fun a b => M.d i a ≤ M.d i b
  letI : Std.Total rel := ⟨fun a b => le_total (M.d i a) (M.d i b)⟩
  letI : IsTrans (Fin 5) rel := ⟨fun a b d hab hbd => le_trans hab hbd⟩
  let labels := ((List.finRange 5).erase i).insertionSort rel
  have hlen : labels.length = 4 := by
    simp [labels,List.length_erase_of_mem (List.mem_finRange i)]
  let ord : Fin 4 → Fin 5 := fun k => labels.get (Fin.cast hlen.symm k)
  have hofn : List.ofFn ord = labels := by
    have h := List.ofFn_congr hlen labels.get
    exact h.symm.trans (List.ofFn_get labels)
  have hperm : (List.ofFn ord).Perm ((List.finRange 5).erase i) := by
    rw [hofn]
    exact List.perm_insertionSort rel _
  have hsorted : ((List.ofFn ord).map (M.d i)).Pairwise (· ≤ ·) := by
    rw [hofn,List.pairwise_map]
    exact List.pairwise_insertionSort rel _
  exact ⟨ord,hperm,by simpa only [List.map_ofFn,Function.comp_def] using hsorted⟩

/-- Internally chosen complete actual label order, including multiplicity. -/
def actualRowOrder (M : GenericModel 5 4) (i : Fin 5) : Fin 4 → Fin 5 :=
  Classical.choose (exists_actualRowOrder M i)

theorem actualRowOrder_perm (M : GenericModel 5 4) (i : Fin 5) :
    (List.ofFn (actualRowOrder M i)).Perm ((List.finRange 5).erase i) :=
  (Classical.choose_spec (exists_actualRowOrder M i)).1

theorem actualRowOrder_sorted (M : GenericModel 5 4) (i : Fin 5) :
    (List.ofFn (fun k => M.d i (actualRowOrder M i k))).Pairwise (· ≤ ·) :=
  (Classical.choose_spec (exists_actualRowOrder M i)).2

theorem actualRowOrder_gaps (M : GenericModel 5 4) (i : Fin 5) :
    fullGaps M i (actualRowOrder M i) = modelGap M i :=
  fullGaps_eq_modelGap_of_perm_sorted M i (actualRowOrder M i)
    (actualRowOrder_perm M i) (actualRowOrder_sorted M i)

/-- Exact full-row floor-score accounting, before choosing any profile. -/
theorem modelGap_score_sum (M : GenericModel 5 4) (i : Fin 5) (c : ℕ)
    (hdef : SatScalarModel.rowDefect M i = c) :
    (∑ k : Fin 5, (Nat.floor (modelGap M i k) - 1)) + c = 4 := by
  have hdef6 : SixModelCompression.rowDefect (SatScalarExtraction.toModelSix M) i = c :=
    (SatScalarExtraction.toModelSix_rowDefect M i).trans hdef
  have h := SmallScoreGapBounds.model_score (SatScalarExtraction.toModelSix M) i c hdef6
  change score (modelGaps M i) + c = 4 at h
  rw [← ofFn_modelGap M i] at h
  simpa only [score,List.map_ofFn,List.sum_ofFn,Function.comp_def] using h

private theorem sum_two_weak_gap_disjunction (s : Fin 5 → ℕ) (g : Fin 5 → ℝ)
    (hsum : (∑ k : Fin 5, s k) = 2)
    (hlower : ∀ k, (s k : ℝ) + (min (s k) 1 : ℕ) ≤ g k) :
    (∃ k : Fin 5, 3 ≤ g k) ∨
      (∃ i j : Fin 5, i < j ∧ 2 ≤ g i ∧ 2 ≤ g j) := by
  by_cases hlarge : ∃ k : Fin 5, 2 ≤ s k
  · obtain ⟨k,hk⟩ := hlarge
    have hmin : min (s k) 1 = 1 := by omega
    have hkR : (2 : ℝ) ≤ s k := by exact_mod_cast hk
    have h := hlower k
    rw [hmin] at h
    norm_num at h
    exact Or.inl ⟨k,by linarith⟩
  · have hsmall : ∀ k, s k ≤ 1 := by
      intro k
      by_contra hk
      exact hlarge ⟨k,by omega⟩
    have hpos : 0 < ∑ k : Fin 5, s k := by omega
    obtain ⟨i,_hi,hi⟩ := Finset.sum_pos_iff.mp hpos
    have hsi : s i = 1 := by have hh := hsmall i; omega
    have hrem : (∑ j ∈ Finset.univ.erase i, s j) = 1 := by
      have hh := Finset.sum_erase_add Finset.univ s (Finset.mem_univ i)
      rw [hsi,hsum] at hh
      omega
    obtain ⟨j,hjmem,hj⟩ := Finset.sum_pos_iff.mp (by omega : 0 < ∑ j ∈ Finset.univ.erase i, s j)
    have hsj : s j = 1 := by have hh := hsmall j; omega
    have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
    have hgi := hlower i
    have hgj := hlower j
    rw [hsi] at hgi
    rw [hsj] at hgj
    norm_num at hgi hgj
    rcases lt_or_gt_of_ne hji with hji | hij
    · exact Or.inr ⟨j,i,hji,hgj,hgi⟩
    · exact Or.inr ⟨i,j,hij,hgi,hgj⟩

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

/-- The complete 15 weak profiles: one genuine gap at least three,
or two distinct genuine gaps at least two. No zero gap is discarded. -/
theorem defect_two_weak_profile (M : GenericModel 5 4) (i : Fin 5)
    (hdef : SatScalarModel.rowDefect M i = 2) :
    ∃ p : Fin 15, ∀ k : Fin 5,
      (SixOuterReplay.profileLower p k : ℝ) ≤ modelGap M i k := by
  have hsum : (∑ k : Fin 5, (Nat.floor (modelGap M i k) - 1)) = 2 := by
    have h := modelGap_score_sum M i 2 hdef
    omega
  have hlower (k : Fin 5) :
      ((Nat.floor (modelGap M i k) - 1 : ℕ) : ℝ) +
        (min (Nat.floor (modelGap M i k) - 1) 1 : ℕ) ≤ modelGap M i k :=
    (SixExactFloorKernel.score_gap_min_interval _ (modelGap_nonneg M i k)).1
  rcases sum_two_weak_gap_disjunction _ (modelGap M i) hsum hlower with
    ⟨k,hk⟩ | ⟨a,b,hab,ha,hb⟩
  · refine ⟨singleProfile k,?_⟩
    intro j
    rw [singleProfile_value]
    by_cases hj : j = k
    · simpa [hj] using hk
    · simpa [hj] using modelGap_nonneg M i j
  · refine ⟨pairProfile a b,?_⟩
    intro j
    rw [pairProfile_value a b hab]
    by_cases hj : j = a ∨ j = b
    · rcases hj with rfl | rfl
      · simpa using ha
      · simpa using hb
    · simpa [hj] using modelGap_nonneg M i j

/-- Exact score one selects one gap in [2,3); every other complete gap
is below two. The selected positive gap is therefore unique. -/
theorem defect_three_tail_profile (M : GenericModel 5 4) (i : Fin 5)
    (hdef : SatScalarModel.rowDefect M i = 3) :
    ∃ t : Fin 5, 2 ≤ modelGap M i t ∧ modelGap M i t < 3 ∧
      ∀ k : Fin 5, k ≠ t → modelGap M i k < 2 := by
  let s : Fin 5 → ℕ := fun k => Nat.floor (modelGap M i k) - 1
  have hsum : (∑ k : Fin 5, s k) = 1 := by
    have h := modelGap_score_sum M i 3 hdef
    change (∑ k : Fin 5, s k) + 3 = 4 at h
    omega
  obtain ⟨t,_ht,ht⟩ := Finset.sum_pos_iff.mp (by omega : 0 < ∑ k : Fin 5, s k)
  have hst : s t = 1 := by
    have hle : s t ≤ ∑ k : Fin 5, s k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    omega
  have hrest : (∑ k ∈ Finset.univ.erase t, s k) = 0 := by
    have h := Finset.sum_erase_add Finset.univ s (Finset.mem_univ t)
    rw [hst,hsum] at h
    omega
  have hzero (k : Fin 5) (hk : k ≠ t) : s k = 0 :=
    (Finset.sum_eq_zero_iff.mp hrest) k (Finset.mem_erase.mpr ⟨hk,Finset.mem_univ k⟩)
  have hinterval := SixExactFloorKernel.score_gap_min_interval _ (modelGap_nonneg M i t)
  change (s t : ℝ) + (min (s t) 1 : ℕ) ≤ modelGap M i t ∧
    modelGap M i t < (s t : ℝ) + 2 at hinterval
  rw [hst] at hinterval
  norm_num at hinterval
  refine ⟨t,hinterval.1,hinterval.2,?_⟩
  intro k hk
  have h := (SixExactFloorKernel.score_gap_min_interval _ (modelGap_nonneg M i k)).2
  change modelGap M i k < (s k : ℝ) + 2 at h
  rw [hzero k hk] at h
  simpa using h

theorem row1_weak_profile (M : GenericModel 5 4)
    (hdef : SatScalarModel.rowDefect M (1 : Fin 5) = 2) :
    ∃ p : Fin 15, ∀ k : Fin 5,
      (SixOuterReplay.profileLower p k : ℝ) ≤ modelGap M 1 k :=
  defect_two_weak_profile M 1 hdef

theorem row3_tail_profile (M : GenericModel 5 4)
    (hdef : SatScalarModel.rowDefect M (3 : Fin 5) = 3) :
    ∃ t : Fin 5, 2 ≤ modelGap M 3 t ∧ modelGap M 3 t < 3 ∧
      ∀ k : Fin 5, k ≠ t → modelGap M 3 k < 2 :=
  defect_three_tail_profile M 3 hdef

end

#print axioms modelGaps_length
#print axioms ofFn_modelGap
#print axioms modelGap_nonneg
#print axioms fullGaps_eq_modelGap_of_perm_sorted
#print axioms actualRowOrder_perm
#print axioms actualRowOrder_sorted
#print axioms actualRowOrder_gaps
#print axioms modelGap_score_sum
#print axioms defect_two_weak_profile
#print axioms defect_three_tail_profile
#print axioms row1_weak_profile
#print axioms row3_tail_profile

end Jsp404.SixOuterFloorProfiles
