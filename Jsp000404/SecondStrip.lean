import Jsp000404.AcuteFanPacking
import Jsp000404.CircleSeparation
import Jsp000404.OneSaturatedLow

/-!
# Complete capacity in the second low strip

When floor(pi/lambda)=2 and the fractional part is below one half,
inward bisector separation bounds the number of centers by four.
Without saturation every row then has exponent zero. With saturation,
the already proved anchored interval argument gives the same capacity.
-/

namespace Jsp404

open scoped EuclideanGeometry EuclideanSpace

/-- A row with at most two lambda-cells either is saturated or has
zero exponent. This includes the empty row. -/
theorem rowScore_eq_zero_of_two_cells_nonsaturated {lam : ℝ} (hlam : 0 < lam)
    (l : List ℝ) (hcells : rowCells lam l ≤ 2) (hns : rowDefect 2 lam l ≠ 1) :
    rowScore lam l = 0 := by
  by_cases hb : rowBig lam l = 0
  · rw [rowScore_eq_cells_sub_big lam hlam l,
      rowCells_eq_zero_of_rowBig_eq_zero lam hlam hb, hb]
  · have hdef : 1 ≤ rowDefect 2 lam l := by unfold rowDefect; omega
    rw [rowScore_eq_sub_defect lam hlam 2 l hcells]
    omega

/-- Actual legal configurations in the second low strip have at most
four centers, independently of whether any row is saturated. -/
theorem card_le_four_of_second_strip_low {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 2 ≤ s)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 2)
    (hδ : Real.pi / lam - 2 < 1/2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) : s ≤ 4 := by
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  norm_num at hfloor
  have hpi : Real.pi < (5/2 : ℝ) * lam :=
    (div_lt_iff₀ hlam).mp (by linarith)
  have halpha : 0 ≤ Real.pi - lam := by linarith
  have hsmall : 3 * (Real.pi - lam) < 2 * Real.pi := by nlinarith
  obtain ⟨m, hm, hsep⟩ := exists_separated_inward_bisectors o hs hleg.inj
    halpha hsmall hleg.triAngle
  have hpack := circle_separation_bound o hs m hm hsep
  have hsl : (s : ℝ) * lam ≤ 2 * Real.pi := by
    convert hpack using 1 <;> ring
  have hslt : (s : ℝ) < 5 :=
    (mul_lt_mul_iff_left₀ hlam).mp (by nlinarith)
  have hsnat : s < 5 := by exact_mod_cast hslt
  omega

/-- The low-regime potential bound in the entire second strip. No
saturation, certificate, or packing hypothesis is assumed. -/
theorem potential_le_four_of_second_strip_low {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 2) (hδ : Real.pi / lam - 2 < 1/2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) :
    potential lam (directionRows o e c) ≤ 4 := by
  classical
  by_cases hsat : ∃ v, rowDefect 2 lam (directionRow o e c v) = 1
  · obtain ⟨v, hv⟩ := hsat
    simpa using potential_le_two_pow_of_saturated o e he hs (by decide)
      hlam hn hleg v hv hδ
  · have hscore (i : Fin s) : rowScore lam (directionRow o e c i) = 0 := by
      apply rowScore_eq_zero_of_two_cells_nonsaturated hlam
        (directionRow o e c i)
        (rowCells_directionRow_le_of_floor_eq o e c hlam i hs hn)
      exact fun hi => hsat ⟨i, hi⟩
    calc potential lam (directionRows o e c) = s := by
          simp [potential, exponentAt, directionRows, hscore]
      _ ≤ 4 := card_le_four_of_second_strip_low o hs hlam hn hδ hleg

#print axioms rowScore_eq_zero_of_two_cells_nonsaturated
#print axioms card_le_four_of_second_strip_low
#print axioms potential_le_four_of_second_strip_low

end Jsp404
