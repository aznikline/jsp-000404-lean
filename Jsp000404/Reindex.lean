import Jsp000404.GeometricDeletion

/-!
# Relabeling finite center configurations

Reindexing by an equivalence preserves each sorted direction row with
all multiplicities and therefore preserves the potential. Two swaps
place any two distinct chosen centers at the first two indices.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

theorem directionRow_reindex {s t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (σ : Fin t ≃ Fin s) (i : Fin t) :
    directionRow o e (c ∘ σ) i = directionRow o e c (σ i) := by
  classical
  have hperm : ((List.finRange t).map σ).Perm (List.finRange s) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange t).map σ.injective)
      (List.nodup_finRange s)).mpr
    intro j
    simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
    exact ⟨σ.symm j, σ.apply_symm_apply j⟩
  have herase := hperm.erase (σ i)
  rw [← List.map_erase σ.injective] at herase
  have hdirs := herase.map (fun j => dirRep o e c (σ i) j)
  rw [List.map_map] at hdirs
  change (((List.finRange t).erase i).map (fun j => dirRep o e (c ∘ σ) i j)).Perm
    (((List.finRange s).erase (σ i)).map (fun j => dirRep o e c (σ i) j)) at hdirs
  apply List.Perm.eq_of_sortedLE (directionRow_sorted o e (c ∘ σ) i)
    (directionRow_sorted o e c (σ i))
  exact (List.perm_insertionSort _ _).trans
    (hdirs.trans (List.perm_insertionSort _ _).symm)

theorem potential_directionRows_reindex {s t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (σ : Fin t ≃ Fin s) (lam : ℝ) :
    potential lam (directionRows o e (c ∘ σ)) = potential lam (directionRows o e c) := by
  unfold potential exponentAt directionRows
  simp_rw [directionRow_reindex]
  exact σ.sum_comp (fun j : Fin s => (2 : ℕ) ^ rowScore lam (directionRow o e c j))

/-- Relabeling preserves the original geometric legality contract. -/
theorem Section4Legality.reindex {s t : ℕ} {lam : ℝ} {c : Fin s → Plane₂}
    (hleg : Section4Legality c lam) (σ : Fin t ≃ Fin s) :
    Section4Legality (c ∘ σ) lam where
  lam_pos := hleg.lam_pos
  inj := hleg.inj.comp σ.injective
  triAngle := fun _ _ _ hij hjk hik =>
    hleg.triAngle _ _ _ (σ.injective.ne hij) (σ.injective.ne hjk) (σ.injective.ne hik)

/-- Any two distinct centers can be assigned the first two indices.
Explicit bounded indices keep the statement independent of `NeZero s`. -/
theorem exists_equiv_zero_one {s : ℕ} (hs : 2 ≤ s) (i j : Fin s) (hij : i ≠ j) :
    ∃ σ : Fin s ≃ Fin s,
      σ ⟨0, by omega⟩ = i ∧ σ ⟨1, by omega⟩ = j := by
  let zero : Fin s := ⟨0, by omega⟩
  let one : Fin s := ⟨1, by omega⟩
  let τ : Fin s ≃ Fin s := Equiv.swap zero i
  let k : Fin s := τ.symm j
  have hzeroone : zero ≠ one := by
    intro h
    have hv := congrArg Fin.val h
    change (0 : ℕ) = 1 at hv
    omega
  have hzerok : zero ≠ k := by
    intro h
    have hv := congrArg τ h
    have hτzero : τ zero = i := Equiv.swap_apply_left _ _
    have hτk : τ k = j := τ.apply_symm_apply j
    rw [hτzero, hτk] at hv
    exact hij hv
  refine ⟨(Equiv.swap one k).trans τ, ?_, ?_⟩
  · change τ (Equiv.swap one k zero) = i
    rw [Equiv.swap_apply_of_ne_of_ne hzeroone hzerok]
    exact Equiv.swap_apply_left _ _
  · change τ (Equiv.swap one k one) = j
    rw [Equiv.swap_apply_left]
    exact τ.apply_symm_apply j

theorem exists_equiv_zero_one_add_two {t : ℕ} (i j : Fin (t + 2)) (hij : i ≠ j) :
    ∃ σ : Fin (t + 2) ≃ Fin (t + 2), σ 0 = i ∧ σ 1 = j := by
  exact exists_equiv_zero_one (by omega) i j hij

#print axioms directionRow_reindex
#print axioms potential_directionRows_reindex
#print axioms Section4Legality.reindex
#print axioms exists_equiv_zero_one
#print axioms exists_equiv_zero_one_add_two

end Jsp404
