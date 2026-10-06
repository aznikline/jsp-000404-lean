import Jsp000404.SingleSplitScorePreservation

/-! Public actual score table for a single positive-parent split.
The frozen geometric construction is repeated only to expose its stronger
conclusion. Actual child indices, old point positions, and the complete
multiplicity-preserving score table are public.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualSingleSplitScoreTable

open SingleSplitScorePreservation

abbrev Copies {s : ℕ} (v : Fin s) := SingleSplitScorePreservation.Copies v

noncomputable abbrev index {s : ℕ} (v : Fin s) :=
  SingleSplitScorePreservation.index v

noncomputable abbrev originalCopy {s : ℕ} (v i : Fin s) : Copies v :=
  SingleSplitScorePreservation.originalCopy v i

noncomputable abbrev extraCopy {s : ℕ} (v : Fin s) : Copies v :=
  SingleSplitScorePreservation.extraCopy v

noncomputable abbrev points {s : ℕ} (v : Fin s) (c : Fin s → Plane₂)
    (u : Plane₂) (eps : ℝ) := SingleSplitScorePreservation.points v c u eps

/-- Actual surviving old-child label in the new Fin enumeration. -/
noncomputable def originalIndex {s : ℕ} (v i : Fin s) : Fin (s + 1) :=
  index v (originalCopy v i)

noncomputable def extraIndex {s : ℕ} (v : Fin s) : Fin (s + 1) :=
  index v (extraCopy v)

@[simp] theorem parent_originalIndex {s : ℕ} (v i : Fin s) :
    ((index v).symm (originalIndex v i)).1 = i := by
  simp [originalIndex, originalCopy, SingleSplitScorePreservation.originalCopy]

@[simp] theorem parent_extraIndex {s : ℕ} (v : Fin s) :
    ((index v).symm (extraIndex v)).1 = v := by
  simp [extraIndex, extraCopy, SingleSplitScorePreservation.extraCopy]

theorem originalIndex_injective {s : ℕ} (v : Fin s) :
    Function.Injective (originalIndex v) := by
  intro i j h
  have := congrArg (fun r => ((index v).symm r).1) h
  simpa only [parent_originalIndex] using this

@[simp] theorem points_originalIndex {s : ℕ} (v i : Fin s)
    (c : Fin s → Plane₂) (u : Plane₂) (eps : ℝ) :
    points v c u eps (originalIndex v i) = c i := by
  change ActualPairExpansion.point c (fun _ => u) eps
    ((SingleSplitScorePreservation.index v).symm
      ((SingleSplitScorePreservation.index v)
        (SingleSplitScorePreservation.originalCopy v i))) = c i
  rw [Equiv.symm_apply_apply]
  simp [SingleSplitScorePreservation.originalCopy, ActualPairExpansion.point]

/-- The actual extra point is displaced along the constructed splitting axis. -/
@[simp] theorem points_extraIndex {s : ℕ} (v : Fin s)
    (c : Fin s → Plane₂) (u : Plane₂) (eps : ℝ) :
    points v c u eps (extraIndex v) = c v + eps • u := by
  change ActualPairExpansion.point c (fun _ => u) eps
    ((SingleSplitScorePreservation.index v).symm
      ((SingleSplitScorePreservation.index v)
        (SingleSplitScorePreservation.extraCopy v))) = c v + eps • u
  rw [Equiv.symm_apply_apply]
  simp [SingleSplitScorePreservation.extraCopy, ActualPairExpansion.point]

/-- A public complete score table with genuine positive perturbation,
common legal parameter, and exact original potential. -/
theorem exists_single_positive_split_score_table {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam tau : ℝ}
    (hleg : Section4Legality c lam) (v : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c v))
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ u : Plane₂, u ≠ 0 ∧ ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∃ eps : ℝ, 0 < eps ∧ Section4Legality (points v c u eps) lam' ∧
        (∀ r : Fin (s + 1),
          rowScore lam' (directionRow o e (points v c u eps) r) =
            if ((index v).symm r).1 = v
            then rowScore lam (directionRow o e c v) - 1
            else rowScore lam (directionRow o e c ((index v).symm r).1)) ∧
        potential lam' (directionRows o e (points v c u eps)) =
          potential lam (directionRows o e c) := by
  classical
  obtain ⟨calcRef, u, hcalc, hu, hbounds, hzero, haxis, hcap⟩ :=
    exists_endpoint_split_data o e he c hleg v hpos
  let l := directionRow o calcRef c v
  have hsorted : l.SortedLE := directionRow_sorted o calcRef c v
  have hne : l ≠ [] := List.ne_nil_of_mem hzero
  have hhead : l.head hne = 0 := by
    exact le_antisymm (hsorted.pairwise.rel_head hzero) (hbounds _ (List.head_mem hne)).1
  have happ : (l ++ [Real.pi - lam]).SortedLE := by
    apply List.sortedLE_append.mpr
    refine ⟨hsorted, by simpa [List.sortedLE_cons] using (List.sortedLE_nil : ([] : List ℝ).SortedLE), ?_⟩
    intro x hx y hy
    have hy' : y = Real.pi - lam := List.mem_singleton.mp hy
    subst y
    have h := (hbounds x hx).2
    linarith [hleg.lam_pos]
  have hsortEq : (l ++ [Real.pi - lam]).insertionSort (· ≤ ·) = l ++ [Real.pi - lam] :=
    List.Perm.eq_of_sortedLE List.sortedLE_insertionSort happ (List.perm_insertionSort _ _)
  have hend : rowScore lam (l ++ [Real.pi - lam]) + 1 = rowScore lam l := by
    simpa only [zero_add] using end_split_rowScore hleg.lam_pos (le_refl (0 : ℝ))
      hleg.lam_pos hsorted hne hhead (by simpa only [zero_add] using hbounds)
  obtain ⟨ref, href, lam', htau', hsmall, eps, heps, hleg', hactual⟩ :=
    exists_legal_split_with_limit_scores o v hs c hleg u hu hcap htau0 htau
  let k : Fin s → ℕ := fun i => rowScore lam (directionRow o e c i)
  have hold : rowScore lam l = k v :=
    (rowScore_directionRow_reference_eq o e calcRef he hcalc c hleg.inj v lam).symm
  rw [hold] at hend
  have hV (r : Fin (s + 1)) (j : Fin s) : outgoing v c u 0 r j ≠ 0 :=
    normalizedDifference_zero_ne c hleg.inj u hu
      ((index v).symm r) ((index v).symm (r.succAbove j))
      ((index v).symm.injective.ne (Fin.ne_succAbove r j))
  have htable (r : Fin (s + 1)) :
      rowScore lam' (directionRow o e (points v c u eps) r) =
        if ((index v).symm r).1 = v then k v - 1 else k ((index v).symm r).1 := by
    have hg := (rowScore_directionRow_reference_eq o e (ref r) he (href r)
      (points v c u eps) hleg'.inj r lam').trans (hactual r)
    change rowScore lam' (directionRow o e (points v c u eps) r) =
      rowScore lam (FiniteFanScoreStability.sortedFan
        (fun j => linRep (o.oangle (ref r) (outgoing v c u 0 r j)))) at hg
    by_cases hv : ((index v).symm r).1 = v
    · have hswap := nonzero_ray_family_score_reference_eq o calcRef (ref r) hcalc (href r)
        (outgoing v c u 0 r) (hV r) lam
      rw [hswap, limiting_cloned_row_score o calcRef hcalc v c u hu r hv lam,
        haxis, hsortEq] at hg
      rw [ite_eq_left hv]
      omega
    · have hswap := nonzero_ray_family_score_reference_eq o e (ref r) he (href r)
        (outgoing v c u 0 r) (hV r) lam
      rw [hswap, limiting_other_row_score o e v c u r hv lam] at hg
      rw [ite_eq_right hv]
      exact hg
  let W : Copies v → ℕ := fun x => if x.1 = v then 2 ^ (k v - 1) else 2 ^ k x.1
  have hk : 1 ≤ k v := by dsimp [k]; omega
  have hpow : 2 * 2 ^ (k v - 1) = 2 ^ k v := by
    calc
      2 * 2 ^ (k v - 1) = 2 ^ (k v - 1) * 2 := Nat.mul_comm _ _
      _ = 2 ^ ((k v - 1) + 1) := (pow_succ _ _).symm
      _ = 2 ^ k v := by rw [Nat.sub_add_cancel hk]
  have hmass : (∑ x : Copies v, W x) = potential lam (directionRows o e c) := by
    rw [Fintype.sum_sigma]
    change (∑ i : Fin s, ∑ _ : Fin (if selected v i then 2 else 1),
      if i = v then 2 ^ (k v - 1) else 2 ^ k i) = ∑ i : Fin s, 2 ^ k i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = v
    · subst i
      simpa [selected] using hpow
    · simp [selected, hi]
  refine ⟨u, hu, lam', htau', hsmall, eps, heps, hleg', htable, ?_⟩
  calc
    potential lam' (directionRows o e (points v c u eps)) =
        ∑ r : Fin (s + 1), W ((index v).symm r) := by
      unfold potential exponentAt directionRows
      apply Finset.sum_congr rfl
      intro r _
      rw [htable r]
      dsimp [W]
      split_ifs <;> rfl
    _ = ∑ x : Copies v, W x := (index v).symm.sum_comp W
    _ = potential lam (directionRows o e c) := hmass

/-- Every unselected original row retains its exact actual score. -/
theorem original_score_of_table {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (v : Fin s)
    (c : Fin s → Plane₂) (u : Plane₂) (eps lam lam' : ℝ)
    (htable : ∀ r : Fin (s + 1),
      rowScore lam' (directionRow o e (points v c u eps) r) =
        if ((index v).symm r).1 = v
        then rowScore lam (directionRow o e c v) - 1
        else rowScore lam (directionRow o e c ((index v).symm r).1))
    (i : Fin s) (hi : i ≠ v) :
    rowScore lam' (directionRow o e (points v c u eps) (originalIndex v i)) =
      rowScore lam (directionRow o e c i) := by
  simpa only [parent_originalIndex, ite_eq_right hi] using htable (originalIndex v i)

#print axioms parent_originalIndex
#print axioms parent_extraIndex
#print axioms originalIndex_injective
#print axioms points_originalIndex
#print axioms points_extraIndex
#print axioms exists_single_positive_split_score_table
#print axioms original_score_of_table

end Jsp404.ActualSingleSplitScoreTable
