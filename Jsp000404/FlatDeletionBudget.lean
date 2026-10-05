import Jsp000404.GeometricDeletion

/-! Exact flat deletion budgets. A bound on the one actual deleted
configuration is explicit. No global sharp capacity is assumed.
-/

open scoped EuclideanGeometry BigOperators

namespace Jsp404.FlatDeletionBudget

/-- Removing one unit per surviving row isolates all the deletion excess. -/
theorem gain_budget_le_one {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (g : ι → ℕ) (hcap : ∑ i ∈ T, 2 ^ g i ≤ T.card + 1) :
    ∑ i ∈ T, (2 ^ g i - 1) ≤ 1 := by
  have hid : (∑ i ∈ T, 2 ^ g i) = (∑ i ∈ T, (2 ^ g i - 1)) + T.card := by
    calc
      (∑ i ∈ T, 2 ^ g i) = ∑ i ∈ T, ((2 ^ g i - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Nat.sub_add_cancel (Nat.one_le_pow _ 2 (by decide))).symm
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  omega

/-- Under a one-unit budget, no individual surviving row has gain two. -/
theorem gain_le_one_of_budget {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (g : ι → ℕ) (hbudget : ∑ i ∈ T, (2 ^ g i - 1) ≤ 1)
    {i : ι} (hi : i ∈ T) : g i ≤ 1 := by
  have hterm : 2 ^ g i - 1 ≤ ∑ j ∈ T, (2 ^ g j - 1) :=
    Finset.single_le_sum (f := fun j => 2 ^ g j - 1) (fun _ _ => Nat.zero_le _) hi
  by_contra hnot
  have hg : 2 ≤ g i := by omega
  have hpow : 2 ^ 2 ≤ 2 ^ g i := Nat.pow_le_pow_right (by decide : 0 < 2) hg
  norm_num at hpow
  omega

/-- Two distinct positive incoming gains already spend two units. -/
theorem positive_gain_unique_of_budget {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (g : ι → ℕ) (hbudget : ∑ i ∈ T, (2 ^ g i - 1) ≤ 1)
    {i j : ι} (hi : i ∈ T) (hj : j ∈ T) (hgi : 1 ≤ g i) (hgj : 1 ≤ g j) :
    i = j := by
  by_contra hij
  have hsub : ({i, j} : Finset ι) ⊆ T := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  have hpair : (2 ^ g i - 1) + (2 ^ g j - 1) ≤ ∑ k ∈ T, (2 ^ g k - 1) := by
    have h := Finset.sum_le_sum_of_subset hsub (f := fun k => 2 ^ g k - 1)
    simpa [Finset.sum_pair hij] using h
  have hpi : 2 ^ 1 ≤ 2 ^ g i := Nat.pow_le_pow_right (by decide : 0 < 2) hgi
  have hpj : 2 ^ 1 ≤ 2 ^ g j := Nat.pow_le_pow_right (by decide : 0 < 2) hgj
  norm_num at hpi hpj
  omega

/-- At most one surviving row can emit into the fixed deleted point. -/
theorem positive_gain_card_le_one {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (g : ι → ℕ) (hbudget : ∑ i ∈ T, (2 ^ g i - 1) ≤ 1) :
    (T.filter (fun i => 1 ≤ g i)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact positive_gain_unique_of_budget T g hbudget
    (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Actual flat rows give the unweighted multiplicative deletion ledger. -/
theorem actual_flat_delete_potential_eq_sum_pow_gain {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hflat : Flat lam (directionRows o e c)) (q : Fin (s + 1)) :
    potential lam (directionRows o e (c ∘ q.succAbove)) =
      ∑ i ∈ Finset.univ.erase q,
        2 ^ rowGain lam (directionRow o e c i) (deleteIndex o e c q i) := by
  classical
  rw [potential_sub_config o e q lam]
  unfold potentialErase directionRows
  rw [Finset.sum_ite]
  simp only [Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.sum_singleton, Finset.filter_ne']
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i ≠ q := (Finset.mem_erase.mp hi).1
  rw [rowScore_eraseIdx' hlam (directionRow_sorted o e c i)
    (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
    (deleteIndex_lt o e c hiq)
    (by rw [directionRow_length o e c i]; omega)]
  have hz : rowScore lam (directionRow o e c i) = 0 := hflat i
  rw [hz, zero_add]

/-- Bounding a flat actual deletion by the original point count forces
gain at most one in every survivor and at most one positive incoming gain. -/
theorem actual_flat_delete_has_at_most_one_emitter {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hflat : Flat lam (directionRows o e c)) (q : Fin (s + 1))
    (hdelete : potential lam (directionRows o e (c ∘ q.succAbove)) ≤ s + 1) :
    (∀ i : Fin (s + 1), i ≠ q →
      rowGain lam (directionRow o e c i) (deleteIndex o e c q i) ≤ 1) ∧
      ((Finset.univ.erase q).filter (fun i =>
        1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c q i))).card ≤ 1 := by
  classical
  let T : Finset (Fin (s + 1)) := Finset.univ.erase q
  let g (i : Fin (s + 1)) :=
    rowGain lam (directionRow o e c i) (deleteIndex o e c q i)
  have hcard : T.card = s := by dsimp [T]; simp
  have hledger := actual_flat_delete_potential_eq_sum_pow_gain hs o e (c := c) hlam hflat q
  have hsum : ∑ i ∈ T, 2 ^ g i ≤ T.card + 1 := by
    rw [hcard, ← hledger]
    exact hdelete
  have hbudget := gain_budget_le_one T g hsum
  refine ⟨?_, positive_gain_card_le_one T g hbudget⟩
  intro i hi
  exact gain_le_one_of_budget T g hbudget (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)

#print axioms gain_budget_le_one
#print axioms gain_le_one_of_budget
#print axioms positive_gain_unique_of_budget
#print axioms positive_gain_card_le_one
#print axioms actual_flat_delete_potential_eq_sum_pow_gain
#print axioms actual_flat_delete_has_at_most_one_emitter

end Jsp404.FlatDeletionBudget
