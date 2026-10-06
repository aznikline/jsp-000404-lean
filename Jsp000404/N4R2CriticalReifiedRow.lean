import Jsp000404.N4R2CriticalKernelPrimitives

/-!
# Common full-row bridges for the n4 R2 replay

These helpers use the actual GenericModel row permutation and sorting fields.
An order supplied to a helper
has explicit permutation/sorting premises; interpreting the finite direction
word internally is a later obligation. No public eight-point exclusion or
caller-mask theorem is asserted here.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2CriticalReifiedRow

open SatScalarModel StrongGapBudget N4R2CriticalKernel
open scoped BigOperators

noncomputable section

/-- Equality with a proposed complete row uses BOTH its permutation and
actual scalar sorting, retaining all six entries and multiplicities. -/
theorem rowxs_eq_map_of_perm_sorted (M : GenericModel 7 4) (i : Fin 7)
    (ord : List (Fin 7))
    (hperm : ord.Perm ((List.finRange 7).erase i))
    (hsorted : (ord.map (M.d i)).Pairwise (· ≤ ·)) :
    M.rowxs i = ord.map (M.d i) := by
  have hp := (M.row_perm i).trans (hperm.map (M.d i)).symm
  exact hp.eq_of_pairwise' (M.row_sorted i) hsorted

/-- Seven consecutive gaps of a six-entry row, explicitly keeping both ends. -/
noncomputable def fullGaps (M : GenericModel 7 4) (i : Fin 7)
    (ord : Fin 6 → Fin 7) : Fin 7 → ℝ := ![
  M.d i (ord 0) - M.theta i,
  M.d i (ord 1) - M.d i (ord 0),
  M.d i (ord 2) - M.d i (ord 1),
  M.d i (ord 3) - M.d i (ord 2),
  M.d i (ord 4) - M.d i (ord 3),
  M.d i (ord 5) - M.d i (ord 4),
  M.theta i + (4 + M.delta) - M.d i (ord 5)]

theorem linearGaps_length (left right : ℝ) (xs : List ℝ) :
    (linearGaps left right xs).length = xs.length + 1 := by
  induction xs generalizing left with
  | nil => simp [linearGaps]
  | cons x xs ih => simp [linearGaps, ih]

theorem modelGaps_length (M : GenericModel 7 4) (i : Fin 7) :
    (modelGaps M i).length = 7 := by
  rw [modelGaps, linearGaps_length, rowxs_length]

/-- Actual gap indexing, independent of any proposed direction word. -/
noncomputable def modelGap (M : GenericModel 7 4) (i : Fin 7) (k : Fin 7) : ℝ :=
  (modelGaps M i).get (Fin.cast (modelGaps_length M i).symm k)

theorem ofFn_modelGap (M : GenericModel 7 4) (i : Fin 7) :
    List.ofFn (modelGap M i) = modelGaps M i := by
  have h := List.ofFn_congr (modelGaps_length M i) (modelGaps M i).get
  exact h.symm.trans (List.ofFn_get (modelGaps M i))

theorem ofFn_fullGaps (M : GenericModel 7 4) (i : Fin 7)
    (ord : Fin 6 → Fin 7) :
    List.ofFn (fullGaps M i ord) = linearGaps (M.theta i)
      (M.theta i + (4 + M.delta)) (List.ofFn (fun k => M.d i (ord k))) := by
  norm_num [List.ofFn_succ, fullGaps, linearGaps]

/-- The common list bridge replaces per-word copies of six-entry sorting
and seven-gap expansion. -/
theorem fullGaps_eq_modelGap_of_perm_sorted (M : GenericModel 7 4) (i : Fin 7)
    (ord : Fin 6 → Fin 7)
    (hperm : (List.ofFn ord).Perm ((List.finRange 7).erase i))
    (hsorted : (List.ofFn (fun k => M.d i (ord k))).Pairwise (· ≤ ·)) :
    fullGaps M i ord = modelGap M i := by
  have hs : ((List.ofFn ord).map (M.d i)).Pairwise (· ≤ ·) := by
    simpa only [List.map_ofFn, Function.comp_def] using hsorted
  have he := rowxs_eq_map_of_perm_sorted M i (List.ofFn ord) hperm hs
  have hl : List.ofFn (fullGaps M i ord) = modelGaps M i := by
    rw [ofFn_fullGaps, modelGaps, he, List.map_ofFn]
    rfl
  exact List.ofFn_injective (hl.trans (ofFn_modelGap M i).symm)

theorem modelGap_mem (M : GenericModel 7 4) (i k : Fin 7) :
    modelGap M i k ∈ modelGaps M i := by
  rw [← ofFn_modelGap]
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

theorem modelGap_nonneg (M : GenericModel 7 4) (i k : Fin 7) :
    0 ≤ modelGap M i k :=
  model_gaps_nonneg M i _ (modelGap_mem M i k)

theorem tail_fullGap_lt_two (M : GenericModel 7 4) (i k : Fin 7)
    (hdef : SatScalarModel.rowDefect M i = 4) : modelGap M i k < 2 :=
  n4_tail_gaps_lt_two M i hdef _ (modelGap_mem M i k)

theorem low_gap_score_sum (M : GenericModel 7 4) (i : Fin 7)
    (hdef : SatScalarModel.rowDefect M i = 2) :
    (∑ k : Fin 7, (Nat.floor (modelGap M i k) - 1)) = 2 := by
  have h := n4_low_score M i hdef
  rw [← ofFn_modelGap] at h
  simpa only [score, List.map_ofFn, List.sum_ofFn, Function.comp_def] using h

/-- The 7 one-two and 21 two-one possibilities are exhaustive consequences
of a complete natural score sum, not a bounded selected-gap budget. -/
theorem sum_two_weak_gap_disjunction (s : Fin 7 → ℕ) (g : Fin 7 → ℝ)
    (hsum : (∑ k : Fin 7, s k) = 2)
    (hlower : ∀ k, (s k : ℝ) + (min (s k) 1 : ℕ) ≤ g k) :
    (∃ k : Fin 7, 3 ≤ g k) ∨
    (∃ i j : Fin 7, i < j ∧ 2 ≤ g i ∧ 2 ≤ g j) := by
  by_cases hlarge : ∃ k : Fin 7, 2 ≤ s k
  · obtain ⟨k, hk⟩ := hlarge
    have hmin : min (s k) 1 = 1 := by omega
    have hkR : (2 : ℝ) ≤ s k := by exact_mod_cast hk
    have h := hlower k
    rw [hmin] at h
    norm_num at h
    exact Or.inl ⟨k, by linarith⟩
  · have hsmall : ∀ k, s k ≤ 1 := by
      intro k
      by_contra hk
      exact hlarge ⟨k, by omega⟩
    have hpos : 0 < ∑ k : Fin 7, s k := by omega
    obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hpos
    have hsi : s i = 1 := by have hh := hsmall i; omega
    have hrem : (∑ j ∈ Finset.univ.erase i, s j) = 1 := by
      have hh := Finset.sum_erase_add Finset.univ s (Finset.mem_univ i)
      rw [hsi, hsum] at hh
      omega
    have hrempos : 0 < ∑ j ∈ Finset.univ.erase i, s j := by omega
    obtain ⟨j, hjmem, hj⟩ := Finset.sum_pos_iff.mp hrempos
    have hsj : s j = 1 := by have hh := hsmall j; omega
    have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
    have hgi := hlower i
    have hgj := hlower j
    rw [hsi] at hgi
    rw [hsj] at hgj
    norm_num at hgi hgj
    rcases lt_or_gt_of_ne hji with hji | hij
    · exact Or.inr ⟨j, i, hji, hgj, hgi⟩
    · exact Or.inr ⟨i, j, hij, hgi, hgj⟩

/-- Actual low defect2 gives the full 28-case necessary gap disjunction.
Zero-score gaps retain their raw-floor0/1 possibilities. -/
theorem low_fullGap_weak_disjunction (M : GenericModel 7 4) (i : Fin 7)
    (hdef : SatScalarModel.rowDefect M i = 2) :
    (∃ k : Fin 7, 3 ≤ modelGap M i k) ∨
    (∃ j k : Fin 7, j < k ∧ 2 ≤ modelGap M i j ∧ 2 ≤ modelGap M i k) := by
  apply sum_two_weak_gap_disjunction
    (fun k => Nat.floor (modelGap M i k) - 1) (modelGap M i)
    (low_gap_score_sum M i hdef)
  intro k
  exact (SixExactFloorKernel.score_gap_min_interval (modelGap M i k)
    (modelGap_nonneg M i k)).1

end

#print axioms rowxs_eq_map_of_perm_sorted
#print axioms modelGaps_length
#print axioms ofFn_modelGap
#print axioms ofFn_fullGaps
#print axioms fullGaps_eq_modelGap_of_perm_sorted
#print axioms modelGap_nonneg
#print axioms tail_fullGap_lt_two
#print axioms low_gap_score_sum
#print axioms sum_two_weak_gap_disjunction
#print axioms low_fullGap_weak_disjunction

#check fullGaps_eq_modelGap_of_perm_sorted
#check tail_fullGap_lt_two
#check low_fullGap_weak_disjunction

end Jsp404.N4R2CriticalReifiedRow
