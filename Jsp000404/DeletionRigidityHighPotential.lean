import Jsp000404.DeletionRigidityCore
import Jsp000404.DeletionRigidityRows

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section TwoIn

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- **Four-point equality configuration.**  In a five-point `R = 3`
configuration, deleting the high-defect non-anchor row `h` leaves a
four-point configuration with potential exactly `5 · 2^{n-2}`: the
anchor stays saturated and the three defect-`2` rows are rigid.
This is an equality datum, not a contradiction. -/
theorem five_point_delete_high_potential {h i j k : Fin 4}
    (hhi : h ≠ i) (hhj : h ≠ j) (hhk : h ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hk : rowDefect n lam (directionRow o e c (v.succAbove k)) = 2) :
    potential lam (fun x : Fin 4 =>
        directionRow o e (c ∘ (v.succAbove h).succAbove) x) = 5 * 2 ^ (n - 2) := by
  classical
  have hn3 := C.hn3
  obtain ⟨A', hA'⟩ := Fin.exists_succAbove_eq (Fin.ne_succAbove v h)
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq
    (fun e => absurd (Fin.succAbove_right_injective e) (Ne.symm hhi))
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq
    (fun e => absurd (Fin.succAbove_right_injective e) (Ne.symm hhj))
  obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq
    (fun e => absurd (Fin.succAbove_right_injective e) (Ne.symm hhk))
  have hup : ∀ x' : Fin 4,
      rowScore lam (directionRow o e c ((v.succAbove h).succAbove x')) ≤
        rowScore lam (directionRow o e (c ∘ (v.succAbove h).succAbove) x') := by
    intro x'
    rw [eraseIdx_directionRow o e (v.succAbove h) x']
    have hx : (v.succAbove h).succAbove x' ≠ v.succAbove h :=
      Fin.succAbove_ne (v.succAbove h) x'
    rw [rowScore_eraseIdx' C.hlam (directionRow_sorted o e c _)
      (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
      (deleteIndex_lt o e c hx) (by rw [directionRow_length]; omega)]
    omega
  have cO : ∀ x, rowCells lam (directionRow o e c x) ≤ n :=
    fun x => rowCells_directionRow_le_of_floor_eq o e c C.hlam x (by omega) C.hn
  have cN : ∀ x', rowCells lam (directionRow o e (c ∘ (v.succAbove h).succAbove) x')
      ≤ n :=
    fun x' => rowCells_directionRow_le_of_floor_eq o e _ C.hlam x' (by omega) C.hn
  have sN := fun x' => rowScore_eq_sub_defect lam C.hlam n _ (cN x')
  have gN := fun x' => one_le_rowDefect lam C.hlam n _ (by omega) (cN x')
  have sAv : rowScore lam (directionRow o e c v) = n - 1 := by
    have := rowScore_eq_sub_defect lam C.hlam n _ (cO v); omega
  have hsA : rowScore lam
      (directionRow o e (c ∘ (v.succAbove h).succAbove) A') = n - 1 := by
    have h1 := hup A'
    rw [hA'] at h1
    have h2 := sN A'
    have h3 := gN A'
    omega
  have sne : ∀ {x y : Fin 4}, x ≠ y → v.succAbove x ≠ v.succAbove y :=
    fun hxy e => hxy (Fin.succAbove_right_injective e)
  have hdi : rowDefect n lam
      (directionRow o e (c ∘ (v.succAbove h).succAbove) i') = 2 :=
    (deletion_rigidity o e C.he (by omega) C.hlam C.hn C.hleg (le_refl 4)
      (Fin.ne_succAbove v i) (Fin.ne_succAbove v j) (sne hij)
      (Fin.ne_succAbove v h) (sne hhj.symm) hA hi hj hi').2
  have hdj : rowDefect n lam
      (directionRow o e (c ∘ (v.succAbove h).succAbove) j') = 2 :=
    (deletion_rigidity o e C.he (by omega) C.hlam C.hn C.hleg (le_refl 4)
      (Fin.ne_succAbove v j) (Fin.ne_succAbove v i) (sne hij.symm)
      (Fin.ne_succAbove v h) (sne hhi.symm) hA hj hi hj').2
  have hdk : rowDefect n lam
      (directionRow o e (c ∘ (v.succAbove h).succAbove) k') = 2 :=
    (deletion_rigidity o e C.he (by omega) C.hlam C.hn C.hleg (le_refl 4)
      (Fin.ne_succAbove v k) (Fin.ne_succAbove v i) (sne hik.symm)
      (Fin.ne_succAbove v h) (sne hhi.symm) hA hk hi hk').2
  have hsi : rowScore lam
      (directionRow o e (c ∘ (v.succAbove h).succAbove) i') = n - 2 := by
    have h1 := sN i'; rw [hdi] at h1; exact h1
  have hsj : rowScore lam
      (directionRow o e (c ∘ (v.succAbove h).succAbove) j') = n - 2 := by
    have h1 := sN j'; rw [hdj] at h1; exact h1
  have hsk : rowScore lam
      (directionRow o e (c ∘ (v.succAbove h).succAbove) k') = n - 2 := by
    have h1 := sN k'; rw [hdk] at h1; exact h1
  -- The four reduced indices `A', i', j', k'` are pairwise distinct:
  -- their `succAbove` images `v, i, j, k` are.
  have hAi' : A' ≠ i' := fun e =>
    (Fin.ne_succAbove v i) (hA'.symm.trans ((congrArg _ e).trans hi'))
  have hAj' : A' ≠ j' := fun e =>
    (Fin.ne_succAbove v j) (hA'.symm.trans ((congrArg _ e).trans hj'))
  have hAk' : A' ≠ k' := fun e =>
    (Fin.ne_succAbove v k) (hA'.symm.trans ((congrArg _ e).trans hk'))
  have hij' : i' ≠ j' := fun e =>
    hij (Fin.succAbove_right_injective (hi'.symm.trans ((congrArg _ e).trans hj')))
  have hik' : i' ≠ k' := fun e =>
    hik (Fin.succAbove_right_injective (hi'.symm.trans ((congrArg _ e).trans hk')))
  have hjk' : j' ≠ k' := fun e =>
    hjk (Fin.succAbove_right_injective (hj'.symm.trans ((congrArg _ e).trans hk')))
  have hnAi : A' ∉ ({i', j', k'} : Finset (Fin 4)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hAi', hAj', hAk'⟩
  have hnij : i' ∉ ({j', k'} : Finset (Fin 4)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hij', hik'⟩
  have hnjk : j' ∉ ({k'} : Finset (Fin 4)) := by
    simp only [Finset.mem_singleton]
    exact hjk'
  -- `Fin 4 = {A', i', j', k'}`: a fifth distinct element would give card 5 ≤ 4.
  have huniv : ({A', i', j', k'} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro w
    by_contra hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    have hnw : w ∉ ({A', i', j', k'} : Finset (Fin 4)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1, h2, h3, h4⟩
    have hcard : ({w, A', i', j', k'} : Finset (Fin 4)).card = 5 := by
      rw [Finset.card_insert_of_notMem hnw, Finset.card_insert_of_notMem hnAi,
        Finset.card_insert_of_notMem hnij, Finset.card_insert_of_notMem hnjk,
        Finset.card_singleton]
    have := Finset.card_le_univ ({w, A', i', j', k'} : Finset (Fin 4))
    rw [hcard, Fintype.card_fin] at this
    omega
  rw [potential_eq_exponent_sum, ← huniv,
    Finset.sum_insert hnAi, Finset.sum_insert hnij, Finset.sum_insert hnjk,
    Finset.sum_singleton]
  simp only [exponentAt]
  rw [hsA, hsi, hsj, hsk]
  have hp : (2 : ℕ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ, mul_comm]
  rw [hp]
  ring

end TwoIn

end Jsp404
