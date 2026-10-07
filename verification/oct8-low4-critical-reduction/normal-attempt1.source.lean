import Jsp000404.ActualF18Complete
import Jsp000404.GlobalFiveLowCapacity

set_option autoImplicit false

/-!
SOURCE_ONLY: every original n4 LOW minimal counter to cap16 has
potential17. The minimum-score point, nonsaturation and the original
small-cardinality exclusion are all derived internally. The five-point
bound used here is the verified LOW cap16, not the HIGH cap20.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualN4LowCriticalReduction

/-- The original LOW Model internally reduces to the potential17 case.
No minimum-score witness, saturation exclusion, potential value or
capacity certificate is supplied by the caller. -/
theorem actual_n4_low_model_potential_eq_seventeen {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam) :
    potential lam (directionRows o e c) = 17 := by
  classical
  obtain ⟨hn,hlow,_hpi⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hs6 : 6 ≤ s := by
    by_contra hnot
    have hs5 : s ≤ 5 := by omega
    have hcap : potential lam (directionRows o e c) ≤ 16 := by
      simpa using GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low
        o e he H.card_ge_three hs5 (by decide : 3 ≤ 4)
        H.legality.lam_pos hn hlow H.legality
    have hover := H.over_cap
    omega
  have hdef := ActualMinimalBandCounterexample.low_model_nonsaturated
    (n := 4) (by decide : 2 ≤ 4) o e he H
  have hupper (i : Fin s) : rowScore lam (directionRow o e c i) ≤ 2 := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos i
      (by omega : 2 ≤ s) hn
    have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
    have hi := hdef i
    omega
  obtain ⟨t,rfl⟩ : ∃ t : ℕ, s = t+1 := ⟨s-1,by omega⟩
  obtain ⟨m,hmin⟩ := Finite.exists_min
    (fun i : Fin (t+1) => rowScore lam (directionRow o e c i))
  have hcritical := ActualMinimalBandCounterexample.low_minimum_score_critical_form
    (n := 4) (by omega : 3 ≤ t) (by decide : 2 ≤ 4) o e H m hmin
  have hF : potential lam (directionRows o e c) =
      16 + 2 ^ rowScore lam (directionRow o e c m) := by
    simpa using hcritical.1
  have hmin_le := hupper m
  have hcases : rowScore lam (directionRow o e c m) = 0 ∨
      rowScore lam (directionRow o e c m) = 1 ∨
      rowScore lam (directionRow o e c m) = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · simpa [h0] using hF
  · have hF18 : potential lam (directionRows o e c) = 18 := by simpa only [h1,pow_one] using hF
    exact False.elim (ActualF18Complete.actual_F18_impossible o e he H hF18)
  · have hall (i : Fin (t+1)) : rowScore lam (directionRow o e c i) = 2 := by
      have hlow := hmin i
      have hi := hupper i
      omega
    have hF20 : potential lam (directionRows o e c) = 20 := by
      simpa only [h2,show (2 : ℕ)^2 = 4 by decide] using hF
    have hmass : potential lam (directionRows o e c) = 4*(t+1) := by
      unfold potential exponentAt directionRows
      simp only [hall,show (2 : ℕ)^2 = 4 by decide,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm]
    have hcard5 : t+1 = 5 := by omega
    omega

#print axioms actual_n4_low_model_potential_eq_seventeen

end Jsp404.ActualN4LowCriticalReduction
