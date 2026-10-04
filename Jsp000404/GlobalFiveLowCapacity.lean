import Jsp000404.GlobalLowRowCount
import Jsp000404.FivePointCapacity

/-! Uniform actual five-centre LOW capacity. The arithmetic consumes the
original row scores and the actual low-row count; it does not assume a
scalar array realization or the desired capacity. -/

namespace Jsp404.GlobalFiveLowCapacity

/-- Every original legal five-centre configuration satisfies the LOW
capacity in every strip n≥3. -/
theorem potential_le_two_pow_of_five_low
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {n : ℕ} (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : ⌊Real.pi/lam⌋₊ = n) (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    {c : Fin 5 → Plane₂} (hleg : Section4Legality c lam) :
    potential lam (directionRows o e c) ≤ 2^n := by
  classical
  by_cases hsat : ∃ i : Fin 5, rowDefect n lam (directionRow o e c i) = 1
  · obtain ⟨i, hi⟩ := hsat
    exact potential_le_two_pow_of_saturated o e he (by decide) (by omega)
      hlam hn hleg i hi hlow
  have hcells : ∀ i : Fin 5, rowCells lam (directionRow o e c i) ≤ n :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i (by decide) hn
  have hdef2 : ∀ i : Fin 5, 2 ≤ rowDefect n lam (directionRow o e c i) := by
    intro i
    have h1 := one_le_rowDefect lam hlam n _ (by omega) (hcells i)
    have hne : rowDefect n lam (directionRow o e c i) ≠ 1 := fun h => hsat ⟨i,h⟩
    omega
  let P : Finset (Fin 5) := Finset.univ.filter (fun i =>
    rowDefect n lam (directionRow o e c i) ≤ 2)
  have hP : P.card ≤ 3 := GlobalLowRowCount.defect_le_two_card_le_three_of_five_le
    o e he hleg (by decide) hn3 hn hlow
  let base : ℕ := 2^(n-3)
  have hpow2 : (2 : ℕ)^(n-2) = 2*base := by
    change 2^(n-2) = 2*2^(n-3)
    rw [show n-2 = (n-3)+1 by omega, pow_add]
    ring
  have hpow3 : (2 : ℕ)^n = 8*base := by
    change 2^n = 8*2^(n-3)
    conv_lhs => rw [show n = (n-3)+3 by omega, pow_add]
    ring
  have hweight (i : Fin 5) : 2^(rowScore lam (directionRow o e c i)) ≤
      base + (if i ∈ P then base else 0) := by
    have hscore := rowScore_eq_sub_defect lam hlam n _ (hcells i)
    by_cases hi : i ∈ P
    · rw [ite_eq_left hi]
      calc
        2^(rowScore lam (directionRow o e c i)) ≤ 2^(n-2) :=
          Nat.pow_le_pow_right (by omega) (by have := hdef2 i; omega)
        _ = base+base := by rw [hpow2]; ring
    · rw [ite_eq_right hi, add_zero]
      have hge3 : 3 ≤ rowDefect n lam (directionRow o e c i) := by
        have hnmem : ¬ rowDefect n lam (directionRow o e c i) ≤ 2 := by
          intro h
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩)
        omega
      exact Nat.pow_le_pow_right (by omega) (by omega)
  have hfilter : (Finset.univ : Finset (Fin 5)).filter (fun i => i ∈ P) = P := by
    ext i
    simp
  have hsum : (∑ i : Fin 5, if i ∈ P then base else 0) = P.card*base := by
    rw [Finset.sum_ite, hfilter]
    simp
  calc
    potential lam (directionRows o e c) ≤
        ∑ i : Fin 5, (base+(if i ∈ P then base else 0)) := by
      unfold potential exponentAt directionRows
      exact Finset.sum_le_sum (fun i _ => hweight i)
    _ = 5*base+P.card*base := by rw [Finset.sum_add_distrib, hsum]; simp
    _ = (5+P.card)*base := by ring
    _ ≤ 8*base := Nat.mul_le_mul_right base (by omega)
    _ = 2^n := hpow3.symm

/-- Uniform LOW capacity for all original sizes from three through five. -/
theorem potential_le_two_pow_of_le_five_low {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs3 : 3 ≤ s) (hs5 : s ≤ 5) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : ⌊Real.pi/lam⌋₊ = n) (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) :
    potential lam (directionRows o e c) ≤ 2^n := by
  by_cases hs4 : s ≤ 4
  · exact Jsp404.potential_le_two_pow_of_le_four_low o e he hs3 hs4 hn3 hlam hn hlow hleg
  · have hs : s=5 := by omega
    subst s
    exact potential_le_two_pow_of_five_low o e he hn3 hlam hn hlow hleg

#print axioms potential_le_two_pow_of_five_low
#print axioms potential_le_two_pow_of_le_five_low
end Jsp404.GlobalFiveLowCapacity
