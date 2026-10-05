import Jsp000404.ActualFlatPotentialInflation
import JSP404.EquallySpacedDirections

/-!
# A genuine flat maximizer from an independent classical coarse bound

The bounding cardinality is the independently proved classical `2^k`
bound above `π/k`. For the LOW strip consumer, `k = n+1`, whereas the
sharp target is `2^n`. The sharp target is never used as the coarse bound.

Attainment is a maximum of finitely bounded natural potential values,
not a compactness assertion for configurations or real angle optima.
Actual flat inflation remains in the original parameter band.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualMaximumMassReduction

/-- Actual legality above the classical threshold gives the independent
coarse cardinality bound. Every counted point is genuinely distinct. -/
theorem actual_card_le_classical_power {s k : ℕ} (hk : 2 ≤ k)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlarge : Real.pi / (k : ℝ) < lam) : s ≤ 2 ^ k := by
  classical
  let P : Finset JSP404.Point := Finset.univ.image c
  have hPcard : P.card = s := by
    simpa only [P, Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective Finset.univ hleg.inj
  by_contra hnot
  have hslarge : 2 ^ k < s := by omega
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd, hangle⟩ :=
    JSP404.szekeres_lower_bound s k hk hslarge P hPcard
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hd
  have hupper := hleg.triAngle i j r
    (fun h => hab (congrArg c h)) (fun h => hbd (congrArg c h))
    (fun h => had (congrArg c h))
  have heq : (1 - 1 / (k : ℝ)) * Real.pi = Real.pi - Real.pi / (k : ℝ) := by
    ring
  rw [heq] at hangle
  linarith

/-- Actual inflation turns the independent coarse cardinality bound into
a coarse potential bound. No sharp capacity hypothesis is present. -/
theorem actual_potential_le_classical_power {s k : ℕ} (hk : 2 ≤ k)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlarge : Real.pi / (k : ℝ) < lam) :
    potential lam (directionRows o e c) ≤ 2 ^ k := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let tau := (Real.pi / (k : ℝ) + lam) / 2
  have htau0 : 0 < tau := by
    dsimp [tau]
    linarith [div_pos Real.pi_pos hkpos]
  have htaulam : tau < lam := by dsimp [tau]; linarith
  have hthreshold : Real.pi / (k : ℝ) < tau := by dsimp [tau]; linarith
  obtain ⟨scale, htauscale, _, d, hd⟩ :=
    ActualPotentialInflation.exists_exact_actual_inflation o e he hs c hleg htau0 htaulam
  exact actual_card_le_classical_power hk hd (hthreshold.trans htauscale)

/-- All actual potentials in a fixed scale band are bounded by `M`. -/
def BandMaximal (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (M : ℕ) : Prop :=
  ∀ {t : ℕ}, 3 ≤ t → ∀ (d : Fin t → Plane₂) (scale : ℝ),
    rho < scale → scale ≤ upper → Section4Legality d scale →
      potential scale (directionRows o e d) ≤ M

private def Attained (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (rho upper : ℝ) (F : ℕ) : Prop :=
  ∃ t : ℕ, 3 ≤ t ∧ ∃ d : Fin t → Plane₂, ∃ scale : ℝ,
    rho < scale ∧ scale ≤ upper ∧ Section4Legality d scale ∧
      potential scale (directionRows o e d) = F

/-- A bounded band of actual potential values has an attained greatest
natural value and a genuine flat realization of exactly that many points. -/
theorem exists_flat_band_maximizer {s k : ℕ} (hk : 2 ≤ k)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {rho upper lam : ℝ} (hclassical : Real.pi / (k : ℝ) ≤ rho)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) (hleg : Section4Legality c lam)
    (habove : rho < lam) (hbelow : lam ≤ upper) :
    ∃ M : ℕ, potential lam (directionRows o e c) ≤ M ∧ M ≤ 2 ^ k ∧
      BandMaximal o e rho upper M ∧
      ∃ scale : ℝ, rho < scale ∧ scale ≤ upper ∧
        ∃ d : Fin M → Plane₂, Section4Legality d scale ∧
          Flat scale (directionRows o e d) ∧
          potential scale (directionRows o e d) = M := by
  classical
  let A : ℕ → Prop := Attained o e rho upper
  let M := Nat.findGreatest A (2 ^ k)
  have hbound := actual_potential_le_classical_power hk o e he hs hleg
    (hclassical.trans_lt habove)
  have hA0 : A (potential lam (directionRows o e c)) :=
    ⟨s, hs, c, lam, habove, hbelow, hleg, rfl⟩
  have hMspec : A M := Nat.findGreatest_spec hbound hA0
  have hMge : potential lam (directionRows o e c) ≤ M :=
    Nat.le_findGreatest hbound hA0
  have hMbound : M ≤ 2 ^ k := Nat.findGreatest_le _
  have hmax : BandMaximal o e rho upper M := by
    intro t ht d scale hlo hup hlegal
    have hb := actual_potential_le_classical_power hk o e he ht hlegal
      (hclassical.trans_lt hlo)
    exact Nat.le_findGreatest hb
      (show A (potential scale (directionRows o e d)) from
        ⟨t, ht, d, scale, hlo, hup, hlegal, rfl⟩)
  obtain ⟨t, ht, p, scale, hrhoscale, hscaleupper, hp, hpot⟩ := hMspec
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hrho0 : 0 < rho := (div_pos Real.pi_pos hkpos).trans_le hclassical
  let tau := (rho + scale) / 2
  have hrhotau : rho < tau := by dsimp [tau]; linarith
  have htau0 : 0 < tau := hrho0.trans hrhotau
  have htausc : tau < scale := by dsimp [tau]; linarith
  obtain ⟨scaleFinal, htFinal, hFinalSmall, pFinal, hFinalLeg, _hFinalFlat, hFinalPot⟩ :=
    ActualFlatPotentialInflation.exists_exact_flat_actual_inflation
      o e he ht p hp htau0 htausc
  let sigma : Fin M ≃ Fin (potential scale (directionRows o e p)) :=
    finCongr hpot.symm
  let d : Fin M → Plane₂ := pFinal ∘ sigma
  have hdleg : Section4Legality d scaleFinal := hFinalLeg.reindex sigma
  have hdpot : potential scaleFinal (directionRows o e d) = M := by
    rw [potential_directionRows_reindex o e pFinal sigma scaleFinal]
    exact hFinalPot.trans hpot
  have hdflat : Flat scaleFinal (directionRows o e d) :=
    ActualFlatPotentialInflation.flat_of_potential_eq_card scaleFinal _ hdpot
  exact ⟨M, hMge, hMbound, hmax, scaleFinal, hrhotau.trans htFinal,
    hFinalSmall.le.trans hscaleupper, d, hdleg, hdflat, hdpot⟩

/-- An original LOW counterexample therefore gives a flat actual maximal
model above the sharp cap, bounded only by the independent coarser cap. -/
theorem exists_flat_low_band_counter_maximizer {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hlow : Real.pi / lam - (n : ℝ) < 1 / 2)
    (hover : 2 ^ n < potential lam (directionRows o e c)) :
    ∃ M : ℕ, 2 ^ n < M ∧ M ≤ 2 ^ (n + 1) ∧
      BandMaximal o e (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) M ∧
      ∃ scale : ℝ, Real.pi / ((n : ℝ) + 1 / 2) < scale ∧
        scale ≤ Real.pi / (n : ℝ) ∧
        ∃ d : Fin M → Plane₂, Section4Legality d scale ∧
          Flat scale (directionRows o e d) ∧
          potential scale (directionRows o e d) = M := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hclassical : Real.pi / ((n + 1 : ℕ) : ℝ) ≤
      Real.pi / ((n : ℝ) + 1 / 2) := by
    push_cast
    apply (div_le_div_iff₀ (by linarith : 0 < (n : ℝ) + 1) hden).mpr
    nlinarith [Real.pi_pos]
  have habove : Real.pi / ((n : ℝ) + 1 / 2) < lam := by
    have hdiv : Real.pi / lam < (n : ℝ) + 1 / 2 := by linarith
    have hm := (div_lt_iff₀ hleg.lam_pos).mp hdiv
    exact (div_lt_iff₀ hden).mpr (by nlinarith)
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hleg.lam_pos.le)
  rw [hn] at hfloor
  have hm := (le_div_iff₀ hleg.lam_pos).mp hfloor
  have hbelow : lam ≤ Real.pi / (n : ℝ) :=
    (le_div_iff₀ hnpos).mpr (by nlinarith)
  obtain ⟨M, hMge, hMbound, hmax, hmodel⟩ :=
    exists_flat_band_maximizer (k := n + 1) (by omega) o e he hclassical
      hs c hleg habove hbelow
  exact ⟨M, hover.trans_le hMge, hMbound, hmax, hmodel⟩

#print axioms actual_card_le_classical_power
#print axioms actual_potential_le_classical_power
#print axioms exists_flat_band_maximizer
#print axioms exists_flat_low_band_counter_maximizer

end Jsp404.ActualMaximumMassReduction
