import Jsp000404.Induction

/-! # The number of saturated centers in the actual geometric model -/

open scoped EuclideanGeometry

namespace Jsp404

theorem not_three_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1)
    (hk : rowDefect n lam (directionRow o e c k) = 1) : False := by
  have h₀ := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    hij hik hjk hi
  have h₁ := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    hij.symm hjk hik hj
  have h₂ := angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
    hik.symm hjk.symm hij hk
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c k)
    (fun h => hij (hleg.inj h))
  rw [EuclideanGeometry.angle_comm (c k) (c j) (c i)] at hsum
  have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  nlinarith

noncomputable def saturatedCenters {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (n : ℕ) (lam : ℝ) (c : Fin s → Plane₂) : Finset (Fin s) :=
  Finset.univ.filter fun i => rowDefect n lam (directionRow o e c i) = 1

theorem saturatedCenters_card_le_two {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s) :
    (saturatedCenters o e n lam c).card ≤ 2 := by
  classical
  by_contra h
  have h3 : 2 < (saturatedCenters o e n lam c).card := by omega
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.mp h3
  exact not_three_saturated o e he hn2 hlam hn hleg hs2 hij hik hjk
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2

theorem saturatedCenters_card_le_one_low {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs3 : 3 ≤ s)
    (hδ : Real.pi / lam - n < 1/2) :
    (saturatedCenters o e n lam c).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hdelta : Real.pi < ((n : ℝ) + 1/2) * lam :=
    (div_lt_iff₀ hlam).mp (by linarith)
  exact not_two_saturated_of_delta_lt_half o e hn2 hlam hn hleg he hs3 hij
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hdelta

#print axioms not_three_saturated
#print axioms saturatedCenters_card_le_two
#print axioms saturatedCenters_card_le_one_low

end Jsp404
