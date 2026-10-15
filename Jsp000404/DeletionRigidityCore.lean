import Jsp000404.TwoSaturatedDeficit

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- **Deletion rigidity.** -/
theorem deletion_rigidity {s n : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (he : e ≠ 0) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam) (hs4 : 4 ≤ s)
    {A i j q : Fin (s + 1)} (hAi : A ≠ i) (hAj : A ≠ j) (hij : i ≠ j)
    (hAq : A ≠ q) (hjq : j ≠ q)
    (hA : rowDefect n lam (directionRow o e c A) = 1)
    (hi : rowDefect n lam (directionRow o e c i) = 2)
    (hj : rowDefect n lam (directionRow o e c j) = 2)
    {i' : Fin s} (hi' : q.succAbove i' = i) :
    rowScore lam (directionRow o e (c ∘ q.succAbove) i') =
        rowScore lam (directionRow o e c i) ∧
      rowDefect n lam (directionRow o e (c ∘ q.succAbove) i') = 2 := by
  classical
  obtain ⟨A', hA'⟩ := Fin.exists_succAbove_eq hAq
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hjq
  have hleg' := hleg.erase q
  have hup : ∀ x' : Fin s,
      rowScore lam (directionRow o e c (q.succAbove x')) ≤
        rowScore lam (directionRow o e (c ∘ q.succAbove) x') := by
    intro x'
    rw [eraseIdx_directionRow o e q x']
    have hx : q.succAbove x' ≠ q := Fin.succAbove_ne q x'
    rw [rowScore_eraseIdx' hlam (directionRow_sorted o e c _)
      (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
      (deleteIndex_lt o e c hx) (by rw [directionRow_length]; omega)]
    omega
  have cO : ∀ x, rowCells lam (directionRow o e c x) ≤ n := fun x =>
    rowCells_directionRow_le_of_floor_eq o e c hlam x (by omega) hn
  have cN : ∀ x', rowCells lam (directionRow o e (c ∘ q.succAbove) x') ≤ n :=
    fun x' => rowCells_directionRow_le_of_floor_eq o e _ hlam x' (by omega) hn
  have sO := fun x => rowScore_eq_sub_defect lam hlam n _ (cO x)
  have sN := fun x' => rowScore_eq_sub_defect lam hlam n _ (cN x')
  have dN := fun x' => rowDefect_le lam hlam n _ (cN x')
  have gN := fun x' => one_le_rowDefect lam hlam n _ (by omega) (cN x')
  have dO := fun x => rowDefect_le lam hlam n _ (cO x)
  have uA := hup A'
  have ui := hup i'
  have uj := hup j'
  rw [hA'] at uA
  rw [hi'] at ui
  rw [hj'] at uj
  have sA := sO A
  have si := sO i
  have sj := sO j
  have sA' := sN A'
  have si' := sN i'
  have sj' := sN j'
  have gA' := gN A'
  have gi' := gN i'
  have dA' := dN A'
  have di' := dN i'
  have dj' := dN j'
  have dA := dO A
  have hA1 : rowDefect n lam (directionRow o e (c ∘ q.succAbove) A') = 1 := by
    omega
  have hAi' : A' ≠ i' := fun h => hAi (by rw [← hA', ← hi', h])
  have hAj' : A' ≠ j' := fun h => hAj (by rw [← hA', ← hj', h])
  have hij' : i' ≠ j' := fun h => hij (by rw [← hi', ← hj', h])
  have hi2 : rowDefect n lam (directionRow o e (c ∘ q.succAbove) i') = 2 := by
    by_contra hne
    have hi1 : rowDefect n lam (directionRow o e (c ∘ q.succAbove) i') = 1 := by
      omega
    have h3 := rowScore_add_three_le_of_two_saturated o e he hn2 hlam hn hleg'
      hs4 hAi' hAj' hij' hA1 hi1
    omega
  exact ⟨by omega, hi2⟩


end Jsp404
