import Jsp000404.PositiveRowCount
import Jsp000404.GlobalFiveLowEndpointGeometry
import Jsp000404.GlobalFiveLowGeometry

/-! Actual defect monotonicity under injective restriction. Every defect
below is the original cyclic-row defect, with its actual floor strip. -/

namespace Jsp404.GlobalLowRowCount

/-- Restricting actual points cannot increase the original row defect.
Both rows retain the same strip parameter and at least two centres. -/
theorem actual_rowDefect_le_restrict {s t n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {lam : ℝ} (hlam : 0 < lam) (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hn : ⌊Real.pi/lam⌋₊ = n)
    (pick : Fin t → Fin s) (hpick : Function.Injective pick) (i : Fin t) :
    rowDefect n lam (directionRow o e (c ∘ pick) i) ≤
      rowDefect n lam (directionRow o e c (pick i)) := by
  have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam (pick i) hs hn
  have hcells' := rowCells_directionRow_le_of_floor_eq o e (c ∘ pick) hlam i ht hn
  have hscore := PositiveRowCount.rowScore_le_restrict o e c hlam ht pick hpick i
  have hdef := rowDefect_le lam hlam n _ hcells
  have hdef' := rowDefect_le lam hlam n _ hcells'
  rw [rowScore_eq_sub_defect lam hlam n _ hcells,
    rowScore_eq_sub_defect lam hlam n _ hcells'] at hscore
  omega

/-- In every LOW strip n≥3, at most four actual centres can have defect
at most two, regardless of the total number of centres. -/
theorem defect_le_two_card_le_four {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2) :
    (Finset.univ.filter (fun i =>
      rowDefect n lam (directionRow o e c i) ≤ 2)).card ≤ 4 := by
  classical
  let P : Finset (Fin s) := Finset.univ.filter (fun i =>
    rowDefect n lam (directionRow o e c i) ≤ 2)
  change P.card ≤ 4
  by_contra hcard
  have hP : 5 ≤ P.card := by omega
  let pick : Fin 5 → Fin s := fun j => (P.orderIsoOfFin rfl (Fin.castLE hP j)).val
  have hpick : Function.Injective pick :=
    Subtype.val_injective.comp
      ((P.orderIsoOfFin rfl).injective.comp (Fin.castLE_injective hP))
  have hs5 : 5 ≤ s := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective pick hpick
  apply GlobalFiveLowEndpointGeometry.five_centres_all_defect_le_two_impossible
    o e he (hleg.restrict_injective pick hpick) hn3 hn hlow
  intro i
  have hip : pick i ∈ P := (P.orderIsoOfFin rfl (Fin.castLE hP i)).property
  have hi : rowDefect n lam (directionRow o e c (pick i)) ≤ 2 :=
    (Finset.mem_filter.mp hip).2
  exact (actual_rowDefect_le_restrict o e c hleg.lam_pos
    (by omega) (by decide) hn pick hpick i).trans hi

/-- Once an actual LOW configuration contains at least five centres,
at most three centres can have original row defect at most two. -/
theorem defect_le_two_card_le_three_of_five_le {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hs : 5 ≤ s) (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2) :
    (Finset.univ.filter (fun i =>
      rowDefect n lam (directionRow o e c i) ≤ 2)).card ≤ 3 := by
  classical
  let P : Finset (Fin s) := Finset.univ.filter (fun i =>
    rowDefect n lam (directionRow o e c i) ≤ 2)
  change P.card ≤ 3
  by_contra hcard
  have hP : 4 ≤ P.card := by omega
  obtain ⟨U, hUP, hUcard⟩ := Finset.exists_subset_card_eq hP
  obtain ⟨T, hUT, _, hTcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ U) (show U.card ≤ 5 by omega)
    (show 5 ≤ (Finset.univ : Finset (Fin s)).card by simpa using hs)
  have hdcard : (T \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset hUT, hTcard, hUcard]
  obtain ⟨q, hdiff⟩ := Finset.card_eq_one.mp hdcard
  have hqdiff : q ∈ T \ U := by rw [hdiff]; simp
  have hqT : q ∈ T := (Finset.mem_sdiff.mp hqdiff).1
  let E := T.orderIsoOfFin hTcard
  let pick : Fin 5 → Fin s := fun i => (E i).val
  let qidx : Fin 5 := E.symm ⟨q, hqT⟩
  have hpick : Function.Injective pick := Subtype.val_injective.comp E.injective
  have hpickq : pick qidx = q := by
    exact congrArg Subtype.val (E.apply_symm_apply ⟨q, hqT⟩)
  apply GlobalFiveLowGeometry.five_centres_four_defect_le_two_impossible
    o e he (hleg.restrict_injective pick hpick) hn3 hn hlow qidx
  intro i hi
  have hipT : pick i ∈ T := (E i).property
  have hipU : pick i ∈ U := by
    by_contra hnotU
    have hmem : pick i ∈ T \ U := Finset.mem_sdiff.mpr ⟨hipT, hnotU⟩
    rw [hdiff] at hmem
    have hh : pick i = q := Finset.mem_singleton.mp hmem
    exact hi (hpick (hh.trans hpickq.symm))
  have hd : rowDefect n lam (directionRow o e c (pick i)) ≤ 2 :=
    (Finset.mem_filter.mp (hUP hipU)).2
  exact (actual_rowDefect_le_restrict o e c hleg.lam_pos
    (by omega) (by decide) hn pick hpick i).trans hd

#print axioms actual_rowDefect_le_restrict
#print axioms defect_le_two_card_le_four
#print axioms defect_le_two_card_le_three_of_five_le
end Jsp404.GlobalLowRowCount
