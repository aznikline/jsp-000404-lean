import Jsp000404.ActualPairExpansion
import Jsp000404.PositiveSplitAxis
import Jsp000404.NoSatNineGeometry
import Jsp000404.N3SaturatedBounds
import Jsp000404.N3NoSaturatedBound

/-! Unconditional LOW third-strip capacity. Positive score-one rows are
expanded into pairs of actual distinct points at a strictly smaller lambda;
the genuine nine-point exclusion bounds their total count. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.N3LowPairClosure

theorem nonsaturated_low_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3)
    (hlow : 2*Real.pi/7 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)) :
    potential lam (directionRows o e c) ≤ 8 := by
  classical
  let P : Fin s → Bool := fun i => decide (0 < rowScore lam (directionRow o e c i))
  have hF : potential lam (directionRows o e c) =
      s + ActualPairExpansion.Reindex.countPairs P := by
    have h := N3NoSaturatedBound.nonsaturated_potential_eq_card_add_positive
      o e (by omega : 2 ≤ s) hleg.lam_pos hn hns
    simpa [P, ActualPairExpansion.Reindex.countPairs] using h
  have haxes : ∀ i, P i = true → ∃ u : Plane₂, u ≠ 0 ∧ ∀ j, j ≠ i →
      InnerProductGeometry.angle u (c j-c i) ≤ Real.pi-lam ∧
        InnerProductGeometry.angle (-u) (c j-c i) ≤ Real.pi-lam := by
    intro i hi
    have hp : 0 < rowScore lam (directionRow o e c i) := by simpa [P] using hi
    exact PositiveSplitAxis.positive_row_exists_both_split_caps
      o e he c hleg.inj hleg.lam_pos i hp
  let lam' := (lam+2*Real.pi/7)/2
  have hl' : 2*Real.pi/7 < lam' := by dsimp [lam']; linarith
  have hp' : 0 < lam' := by linarith [Real.pi_pos]
  have hs' : lam' < lam := by dsimp [lam']; linarith
  obtain ⟨c', hleg'⟩ := ActualPairExpansion.exists_pair_expansion_of_axes
    c hs hleg haxes hp' hs'
  have hcard := NoSatNineGeometry.centres_low_card_le_eight o e he hleg' hl'
  omega

/-- All actual n=3 LOW configurations satisfy cap eight, with no finite
exclusion hypothesis. Saturation is consumed by the proved LOW theorem. -/
theorem low_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3)
    (hlow : 2*Real.pi/7 < lam) :
    potential lam (directionRows o e c) ≤ 8 := by
  classical
  by_cases hsat : ∃ v, rowDefect 3 lam (directionRow o e c v) = 1
  · obtain ⟨v, hv⟩ := hsat
    have hd : Real.pi/lam-3 < 1/2 := by
      have hm : Real.pi < (7/2)*lam := by linarith
      have hh := (div_lt_iff₀ hleg.lam_pos).mpr hm
      linarith
    have h := N3SaturatedBounds.saturated_strip_capacity o e he hs hleg.lam_pos
      hn hleg v hv false (fun _ => hd)
    simpa [sendovCap] using h
  · have hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i) := by
      intro i
      have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos i
        (by omega : 2 ≤ s) hn
      have h1 := one_le_rowDefect lam hleg.lam_pos 3 _ (by omega) hc
      have hh : rowDefect 3 lam (directionRow o e c i) ≠ 1 := fun h => hsat ⟨i,h⟩
      omega
    exact nonsaturated_low_capacity o e he hs hleg hn hlow hns

/-- Original delta-form LOW capacity, suitable for the strip consumer. -/
theorem low_capacity_of_delta {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3)
    (hdelta : Real.pi/lam-3 < 1/2) :
    potential lam (directionRows o e c) ≤ sendovCap 3 false := by
  have hd : Real.pi/lam < 7/2 := by linarith
  have hm := (div_lt_iff₀ hleg.lam_pos).mp hd
  have hl : 2*Real.pi/7 < lam := by linarith
  simpa [sendovCap] using low_capacity o e he hs hleg hn hl

/-- The original LOW geometric progress premise is vacuous at n=3:
its actual over-capacity domain has been proved empty. -/
theorem low_certificates
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi/lam) = 3)
    (hdelta : Real.pi/lam-3 < 1/2) : CertExists o e 3 false lam := by
  intro t c ht hleg hover
  have hc := low_capacity_of_delta o e he (by omega : 3 ≤ t) hleg hn hdelta
  exact False.elim ((not_lt_of_ge hc) hover)

#print axioms nonsaturated_low_capacity
#print axioms low_capacity
#print axioms low_capacity_of_delta
#print axioms low_certificates
end Jsp404.N3LowPairClosure
