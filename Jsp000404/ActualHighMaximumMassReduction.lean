import Jsp000404.ActualMaximumMassReduction

/-! A genuine flat maximal model for an actual HIGH counterexample.
The classical bound used for existence of the maximum is 2^(n+1), not
the sharp Sendov HIGH cap. Neither maximality nor flatness is supplied
by the caller. This module is a counterexample reduction, not a capacity
or a bare finite angle exclusion.
-/

open scoped EuclideanGeometry

namespace Jsp404.ActualHighMaximumMassReduction

/-- An actual HIGH counterexample gives an attained band maximum and a
genuine flat realization indexed by that maximum. The floor condition
itself supplies the strict upper delta bound `pi/lam-n < 1`.
All configurations in the displayed HIGH band are bounded by the derived
maximum. No caller-supplied extremal or sharp-capacity premise is used. -/
theorem exists_flat_high_band_counter_maximizer {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hhigh : 1 / 2 ≤ Real.pi / lam - (n : ℝ))
    (hover : sendovCap n true < potential lam (directionRows o e c)) :
    ∃ M : ℕ, sendovCap n true < M ∧ M ≤ 2 ^ (n + 1) ∧
      ActualMaximumMassReduction.BandMaximal o e
        (Real.pi / ((n : ℝ) + 1)) (Real.pi / ((n : ℝ) + 1 / 2)) M ∧
      ∃ scale : ℝ, Real.pi / ((n : ℝ) + 1) < scale ∧
        scale ≤ Real.pi / ((n : ℝ) + 1 / 2) ∧
        ∃ d : Fin M → Plane₂, Section4Legality d scale ∧
          Flat scale (directionRows o e d) ∧
          potential scale (directionRows o e d) = M := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hden1 : 0 < (n : ℝ) + 1 := by linarith
  have hclassical : Real.pi / ((n + 1 : ℕ) : ℝ) ≤
      Real.pi / ((n : ℝ) + 1) := by
    push_cast
    exact le_rfl
  have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn] at hfloor
  have hm := (div_lt_iff₀ hleg.lam_pos).mp hfloor
  have habove : Real.pi / ((n : ℝ) + 1) < lam :=
    (div_lt_iff₀ hden1).mpr (by nlinarith)
  have hratio : (n : ℝ) + 1 / 2 ≤ Real.pi / lam := by linarith
  have hmhigh := (le_div_iff₀ hleg.lam_pos).mp hratio
  have hbelow : lam ≤ Real.pi / ((n : ℝ) + 1 / 2) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  obtain ⟨M, hMge, hMbound, hmax, hmodel⟩ :=
    ActualMaximumMassReduction.exists_flat_band_maximizer
      (k := n + 1) (by omega) o e he hclassical hs c hleg habove hbelow
  exact ⟨M, hover.trans_le hMge, hMbound, hmax, hmodel⟩

#print axioms exists_flat_high_band_counter_maximizer

end Jsp404.ActualHighMaximumMassReduction
