import Jsp000404.ActualPotentialInflation
import Jsp000404.NoSatNineGeometry
import Jsp000404.NoSatElevenGeometry

/-! Conditional weighted capacity from a bare finite actual angle exclusion.
The remaining mathematical premise is stated explicitly as an exclusion of
actual C+1-point configurations above the threshold. It is not a capacity,
Kraft inequality, scalar-array realization, or row-score hypothesis.
-/

open scoped EuclideanGeometry

namespace Jsp404.ActualCapacityFromCardinality

/-- A bare actual finite exclusion consumes the genuine point inflation to
bound every original potential. This theorem is conditional on that bare
exclusion, which must be proved independently. -/
theorem potential_le_of_bare_exclusion {C s : ℕ}
    (_hC : 2 ≤ C) (rho : ℝ) (hrho : 0 ≤ rho)
    (hbare : ∀ scale : ℝ, rho < scale → ∀ d : Fin (C + 1) → Plane₂,
      ¬ Section4Legality d scale)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hlarge : rho < lam) :
    potential lam (directionRows o e c) ≤ C := by
  by_contra hnot
  have hcard : C + 1 ≤ potential lam (directionRows o e c) := by omega
  let tau := (rho + lam) / 2
  have hrhotau : rho < tau := by dsimp [tau]; linarith
  have htau0 : 0 < tau := lt_of_le_of_lt hrho hrhotau
  have htaulam : tau < lam := by dsimp [tau]; linarith
  obtain ⟨scale, htauscale, _, d, hd⟩ :=
    ActualPotentialInflation.exists_exact_actual_inflation o e he hs c hleg htau0 htaulam
  let pick : Fin (C + 1) → Fin (potential lam (directionRows o e c)) := Fin.castLE hcard
  have hpick : Function.Injective pick := Fin.castLE_injective hcard
  have hrestricted : Section4Legality (d ∘ pick) scale := by
    refine ⟨hd.lam_pos, hd.inj.comp hpick, ?_⟩
    intro i j k hij hjk hik
    exact hd.triAngle (pick i) (pick j) (pick k)
      (fun h => hij (hpick h)) (fun h => hjk (hpick h))
      (fun h => hik (hpick h))
  exact hbare scale (hrhotau.trans htauscale) (d ∘ pick) hrestricted

/-- The independently proved bare nine-point exclusion gives capacity eight
for every actual configuration above `2*pi/7`, with no floor hypothesis. -/
theorem potential_le_eight_of_two_pi_sevenths_lt {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlow : 2 * Real.pi / 7 < lam) :
    potential lam (directionRows o e c) ≤ 8 := by
  apply potential_le_of_bare_exclusion (C := 8) (by decide)
    (2 * Real.pi / 7) (by linarith [Real.pi_pos]) ?_ o e he hs c hleg hlow
  intro scale hscale d hd
  exact NoSatNineGeometry.nine_centres_angle_bound_impossible o e he hd hscale

/-- The independently proved bare eleven-point exclusion gives capacity ten
for every actual configuration above `pi/4`, with no floor hypothesis. -/
theorem potential_le_ten_of_pi_quarter_lt {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hhigh : Real.pi / 4 < lam) :
    potential lam (directionRows o e c) ≤ 10 := by
  apply potential_le_of_bare_exclusion (C := 10) (by decide)
    (Real.pi / 4) (by linarith [Real.pi_pos]) ?_ o e he hs c hleg hhigh
  intro scale hscale d hd
  exact NoSatElevenGeometry.eleven_centres_angle_bound_impossible o e he hd hscale

/-- Original third-strip LOW parameters, consumed through the generic
inflation/cardinality bridge. The floor identifies the strip; its numeric
delta inequality supplies the strict bare-exclusion threshold. -/
theorem third_strip_low_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (_hn : Nat.floor (Real.pi / lam) = 3)
    (hdelta : Real.pi / lam - 3 < 1 / 2) :
    potential lam (directionRows o e c) ≤ sendovCap 3 false := by
  have hd : Real.pi / lam < 7 / 2 := by linarith
  have hm := (div_lt_iff₀ hleg.lam_pos).mp hd
  have hl : 2 * Real.pi / 7 < lam := by linarith
  simpa [sendovCap] using
    potential_le_eight_of_two_pi_sevenths_lt o e he hs hleg hl

/-- Original third-strip HIGH bound. The floor-three condition already
implies `pi/4 < lam`, so no delta assumption is needed for this bound. -/
theorem third_strip_high_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3) :
    potential lam (directionRows o e c) ≤ sendovCap 3 true := by
  have hhigh : Real.pi / 4 < lam := by
    have h := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hleg.lam_pos] at h
    norm_num at h
    linarith
  simpa [sendovCap] using potential_le_ten_of_pi_quarter_lt o e he hs hleg hhigh

#print axioms potential_le_of_bare_exclusion
#print axioms potential_le_eight_of_two_pi_sevenths_lt
#print axioms potential_le_ten_of_pi_quarter_lt
#print axioms third_strip_low_capacity
#print axioms third_strip_high_capacity

end Jsp404.ActualCapacityFromCardinality
