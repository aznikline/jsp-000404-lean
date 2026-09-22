import Jsp000404.SecondStrip
import Jsp000404.VaryingFanPacking
import Jsp000404.WeightedCircleSeparation

/-! # Complete weighted capacity in the second strip -/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- In the second strip, each saturated fan contributes exterior width
2 lambda and every other fan contributes lambda. Their actual inward
bisectors pack these widths around one full circle. -/
theorem potential_mul_lam_le_two_pi_of_second_strip {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) :
    (potential lam (directionRows o e c) : ℝ) * lam ≤ 2*Real.pi := by
  classical
  let a : Fin s → ℝ := fun i =>
    if rowDefect 2 lam (directionRow o e c i) = 1 then Real.pi-2*lam else Real.pi-lam
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  norm_num at hfloor
  have hltfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hltfloor
  norm_num at hltfloor
  have ha (i : Fin s) : 0 ≤ a i := by dsimp [a]; split_ifs <;> linarith
  have hsmall (i : Fin s) : 3*a i < 2*Real.pi := by
    dsimp [a]; split_ifs <;> linarith
  have hcap (i j k : Fin s) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      ∠ (c i) (c j) (c k) ≤ a j := by
    dsimp [a]
    split_ifs with hj
    · exact angle_le_pi_sub_of_saturation o e (by decide) hlam hn hleg he hs
        hij.symm hjk hik hj
    · exact hleg.triAngle i j k hij hjk hik
  obtain ⟨m, hm, hsep⟩ := exists_separated_varying_inward_bisectors o hs hleg.inj
    a ha hsmall hcap
  let w : Fin s → ℝ := fun i => Real.pi-a i
  have hpack := weighted_circle_separation_bound o hs m hm w (fun i j hij => by
    have h := hsep i j hij
    dsimp [w]
    linarith)
  have hw (i : Fin s) : w i = (2 : ℝ)^rowScore lam (directionRow o e c i) * lam := by
    have hc := rowCells_directionRow_le_of_floor_eq o e c hlam i hs hn
    by_cases hi : rowDefect 2 lam (directionRow o e c i) = 1
    · have hk : rowScore lam (directionRow o e c i) = 1 := by
        rw [rowScore_eq_sub_defect lam hlam 2 _ hc, hi]
      simp [w, a, hi, hk]
    · have hk := rowScore_eq_zero_of_two_cells_nonsaturated hlam
        (directionRow o e c i) hc hi
      simp [w, a, hi, hk]
  have heq : (potential lam (directionRows o e c) : ℝ) * lam = ∑ i, w i := by
    unfold potential exponentAt directionRows
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => (hw i).symm)
  rwa [heq]

/-- The entire second HIGH strip has potential at most five. This
also holds uniformly in its LOW subrange. -/
theorem potential_le_five_of_second_strip {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) :
    potential lam (directionRows o e c) ≤ 5 := by
  have hW := potential_mul_lam_le_two_pi_of_second_strip o e he hs hlam hn hleg
  have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor
  norm_num at hfloor
  have hlt : (potential lam (directionRows o e c) : ℝ) < 6 := by nlinarith
  have hnat : potential lam (directionRows o e c) < 6 := by exact_mod_cast hlt
  omega

#print axioms potential_mul_lam_le_two_pi_of_second_strip
#print axioms potential_le_five_of_second_strip

end Jsp404
