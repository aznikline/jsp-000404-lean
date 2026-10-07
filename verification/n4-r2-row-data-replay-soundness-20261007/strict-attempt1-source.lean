import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2ThinReplaySoundness

/-!
Checked literal rows are interpreted in the actual scalar model. All six
neighbors, distinctness and all pairwise word comparisons are checked before
any gap is decoded. No sorting/accepted-row field is added to GenericModel.
The final bridge reuses the verified complete-row and cycle semantics.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2RowDataReplaySoundness

open SatScalarModel N4R2ModelWordSoundness N4R2CriticalReifiedRow

private theorem decide_of_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p = decide q := by
  by_cases hp : p
  · have hq := h.mp hp
    simp [hp,hq]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp,hq]

/-- Literal finite checks derive the complete actual row obligations. -/
theorem checked_rows_perm_sorted (M : GenericModel 7 4) (w : Word)
    (hword : WordSound M w) (ord : N4R2RowDataReplay.RowsData) (hcheck : N4R2RowDataReplay.rowsCheck w ord = true)
    (i : Fin 7) :
    (List.ofFn (ord i)).Perm ((List.finRange 7).erase i) ∧
      ((List.ofFn (ord i)).map (M.d i)).Pairwise (· ≤ ·) := by
  have hall : ∀ i : Fin 7,
      (List.ofFn (ord i)).Nodup ∧
      (∀ j : Fin 7, j ∈ List.ofFn (ord i) ↔ j ≠ i) ∧
      (List.ofFn (ord i)).Pairwise
        (fun u v => N4R2ThinWord.rowCompare w i u v = true) :=
    of_decide_eq_true hcheck
  have hi := hall i
  constructor
  · apply List.Subperm.antisymm
    · apply List.Nodup.subperm hi.1
      intro j hj
      exact (List.nodup_finRange 7).mem_erase_iff.mpr
        ⟨(hi.2.1 j).mp hj, List.mem_finRange j⟩
    · apply List.Nodup.subperm ((List.nodup_finRange 7).erase i)
      intro j hj
      exact (hi.2.1 j).mpr (((List.nodup_finRange 7).mem_erase_iff.mp hj).1)
  · rw [List.pairwise_map]
    apply hi.2.2.imp_of_mem
    intro u v hu hv huv
    have hcu : u ≠ i := (hi.2.1 u).mp hu
    have hcv : v ≠ i := (hi.2.1 v).mp hv
    have hc : rowCompare w i u v = true := by
      rw [← N4R2ThinWordSoundness.rowCompare_eq w i]
      exact huv
    have hh := (rowCompare_iff M w hword i u v).mp hc
    simpa only [rowKey, hcu, hcv, ↓reduceIte] using hh

private theorem chord_injective_away (M : GenericModel 7 4) (w : Word)
    (hword : WordSound M w) (i : Fin 7) {u v : Fin 7}
    (hui : u ≠ i) (hvi : v ≠ i) (heq : M.d i u = M.d i v) : u = v := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with huv | hvu
  · have hc := incident_comparison M w hword i u v huv hui hvi
    split at hc <;> linarith only [hc,heq]
  · have hc := incident_comparison M w hword i v u hvu hvi hui
    split at hc <;> linarith only [hc,heq]

/-- Checked rows equal the frozen actual algorithm whenever an actual model
realizes the word. No equivalence for arbitrary invalid words is assumed. -/
theorem checked_rows_eq_actual (M : GenericModel 7 4) (w : Word)
    (hword : WordSound M w) (ord : N4R2RowDataReplay.RowsData) (hcheck : N4R2RowDataReplay.rowsCheck w ord = true) :
    ord = N4R2ThinReplay.rows w := by
  funext i k
  change ord i k = rows w i k
  have hd := checked_rows_perm_sorted M w hword ord hcheck i
  have ho := row_order_perm_sorted M w hword i
  have hsortedOld : ((List.ofFn (rows w i)).map (M.d i)).Pairwise (· ≤ ·) := by
    simpa only [List.map_ofFn, Function.comp_def] using ho.2
  have hdata := rowxs_eq_map_of_perm_sorted M i (List.ofFn (ord i)) hd.1 hd.2
  have hold := rowxs_eq_map_of_perm_sorted M i (List.ofFn (rows w i)) ho.1 hsortedOld
  have hmaps := hdata.symm.trans hold
  have hvalues : (fun j : Fin 6 => M.d i (ord i j)) =
      (fun j : Fin 6 => M.d i (rows w i j)) :=
    List.ofFn_injective (by simpa only [List.map_ofFn, Function.comp_def] using hmaps)
  have hu : ord i k ∈ ((List.finRange 7).erase i) :=
    hd.1.mem_iff.mp (List.mem_ofFn.mpr ⟨k,rfl⟩)
  have hv : rows w i k ∈ ((List.finRange 7).erase i) :=
    ho.1.mem_iff.mp (List.mem_ofFn.mpr ⟨k,rfl⟩)
  exact chord_injective_away M w hword i
    (((List.nodup_finRange 7).mem_erase_iff.mp hu).1)
    (((List.nodup_finRange 7).mem_erase_iff.mp hv).1) (congrFun hvalues k)

theorem checked_fullGaps_eq_modelGap (M : GenericModel 7 4) (w : Word)
    (hword : WordSound M w) (ord : N4R2RowDataReplay.RowsData) (hcheck : N4R2RowDataReplay.rowsCheck w ord = true)
    (i : Fin 7) : fullGaps M i (ord i) = modelGap M i := by
  have hd := checked_rows_perm_sorted M w hword ord hcheck i
  apply fullGaps_eq_modelGap_of_perm_sorted M i (ord i) hd.1
  simpa only [List.map_ofFn, Function.comp_def] using hd.2

/-- Computation agrees with the legacy checker at its own rows; this
symbolic equality does not evaluate opaque sorting during a finite check. -/
theorem decode_legacy (w : N4R2ThinReplay.Word) (p0 p6 : Option (Fin 28)) (o : N4R2ThinReplay.Origin) :
    N4R2RowDataReplay.decodeWithRows w (N4R2ThinReplay.rows w) p0 p6 o = N4R2ThinReplay.decode w p0 p6 o := by
  cases o <;> rfl

theorem cycleMatches_legacy (C : N4R2ThinReplay.Cycle) (w : N4R2ThinReplay.Word) (p0 p6 : Option (Fin 28)) :
    N4R2RowDataReplay.cycleMatches C w (N4R2ThinReplay.rows w) p0 p6 = C.matches w p0 p6 := by
  unfold N4R2RowDataReplay.cycleMatches N4R2ThinReplay.Cycle.matches
  apply decide_of_iff
  simp only [decode_legacy]

theorem cycleCheck_legacy (C : N4R2ThinReplay.Cycle) (w : N4R2ThinReplay.Word) (p0 p6 : Option (Fin 28)) :
    N4R2RowDataReplay.cycleCheck C w (N4R2ThinReplay.rows w) p0 p6 = C.check w p0 p6 := by
  simp only [N4R2RowDataReplay.cycleCheck, N4R2ThinReplay.Cycle.check, cycleMatches_legacy]

theorem libraryCheck_legacy (lib : N4R2ThinReplay.Library) (w : N4R2ThinReplay.Word)
    (p0 p6 : Option (Fin 28)) (id : ℕ) :
    N4R2RowDataReplay.libraryCheck lib w (N4R2ThinReplay.rows w) p0 p6 id = N4R2ThinReplay.libraryCheck lib w p0 p6 id := by
  cases h : lib id with
  | none => simp only [N4R2RowDataReplay.libraryCheck, N4R2ThinReplay.libraryCheck,h]
  | some C => simp only [N4R2RowDataReplay.libraryCheck, N4R2ThinReplay.libraryCheck,h,cycleCheck_legacy]

theorem leafCases_legacy (lib : N4R2ThinReplay.Library) (w : N4R2ThinReplay.Word) (proof : N4R2ThinReplay.LeafProof) :
    N4R2RowDataReplay.leafCases lib w (N4R2ThinReplay.rows w) proof = N4R2ThinReplay.leafCheck lib w proof := by
  cases proof with
  | tail id => exact libraryCheck_legacy lib w none none id
  | low0 cs =>
    simp only [N4R2RowDataReplay.leafCases, N4R2ThinReplay.leafCheck]
    apply decide_of_iff
    simp only [libraryCheck_legacy]
  | low6 cs =>
    simp only [N4R2RowDataReplay.leafCases, N4R2ThinReplay.leafCheck]
    apply decide_of_iff
    simp only [libraryCheck_legacy]
  | twoLow cs0 cs6 pairs =>
    simp only [N4R2RowDataReplay.leafCases, N4R2ThinReplay.leafCheck]
    apply decide_of_iff
    simp only [libraryCheck_legacy]

/-- The checked literal-row certificate excludes the actual complete model.
The header and every cycle/low-profile branch are validated by the kernel. -/
theorem leafCheck_sound (lib : N4R2ThinReplay.Library) (M : GenericModel 7 4) (w : N4R2ThinReplay.Word)
    (hword : WordSound M w)
    (hdef0 : SatScalarModel.rowDefect M 0 = 2)
    (hdef6 : SatScalarModel.rowDefect M 6 = 2)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4)
    (data : N4R2RowDataReplay.LeafData) (hcheck : N4R2RowDataReplay.leafCheck lib w data = true) : False := by
  have hp : N4R2RowDataReplay.rowsCheck w data.rows = true ∧
      N4R2RowDataReplay.leafCases lib w data.rows data.proof = true := by
    simpa only [N4R2RowDataReplay.leafCheck,N4R2RowDataReplay.leafCheckWithRows,Bool.and_eq_true] using hcheck
  have heq := checked_rows_eq_actual M w hword data.rows hp.1
  apply N4R2ThinReplaySoundness.leafCheck_sound lib M w hword hdef0 hdef6 htails data.proof
  rw [heq,leafCases_legacy] at hp
  exact hp.2

#print axioms checked_rows_perm_sorted
#print axioms checked_rows_eq_actual
#print axioms checked_fullGaps_eq_modelGap
#print axioms decode_legacy
#print axioms cycleMatches_legacy
#print axioms cycleCheck_legacy
#print axioms libraryCheck_legacy
#print axioms leafCases_legacy
#print axioms leafCheck_sound

end Jsp404.N4R2RowDataReplaySoundness
