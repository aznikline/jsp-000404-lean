import Jsp000404.ActualPairExpansion
import Jsp000404.PositiveSplitAxis
import Jsp000404.NoSatElevenGeometry
import Jsp000404.N3SaturatedBounds
import Jsp000404.N3NoSaturatedBound
import Jsp000404.N3LowPairClosure

/-! Unconditional HIGH third-strip capacity. Positive score-one rows are
expanded into pairs of actual distinct points at a strictly smaller lambda;
the genuine eleven-point exclusion bounds their total count. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.N3HighPairClosure

theorem nonsaturated_high_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)) :
    potential lam (directionRows o e c) ≤ 10 := by
  classical
  have hquarter : Real.pi/4 < lam := by
    have h := Nat.lt_floor_add_one (Real.pi/lam)
    rw [hn, div_lt_iff₀ hleg.lam_pos] at h
    norm_num at h
    linarith
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
  let lam' := (lam+Real.pi/4)/2
  have hl' : Real.pi/4 < lam' := by dsimp [lam']; linarith
  have hp' : 0 < lam' := by linarith [Real.pi_pos]
  have hs' : lam' < lam := by dsimp [lam']; linarith
  obtain ⟨c', hleg'⟩ := ActualPairExpansion.exists_pair_expansion_of_axes
    c hs hleg haxes hp' hs'
  have hcard := NoSatElevenGeometry.centres_high_card_le_ten o e he hleg' hl'
  omega

/-- All actual n=3 configurations satisfy cap ten. Saturation is consumed
by the previously proved HIGH theorem; the other branch uses real pairs. -/
theorem high_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3) :
    potential lam (directionRows o e c) ≤ sendovCap 3 true := by
  classical
  by_cases hsat : ∃ v, rowDefect 3 lam (directionRow o e c v) = 1
  · obtain ⟨v, hv⟩ := hsat
    simpa [sendovCap] using
      N3SaturatedBounds.saturated_high_capacity o e he hs hleg.lam_pos hn hleg v hv
  · have hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i) := by
      intro i
      have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos i
        (by omega : 2 ≤ s) hn
      have h1 := one_le_rowDefect lam hleg.lam_pos 3 _ (by omega) hc
      have hh : rowDefect 3 lam (directionRow o e c i) ≠ 1 := fun h => hsat ⟨i,h⟩
      omega
    simpa [sendovCap] using nonsaturated_high_capacity o e he hs hleg hn hns

/-- Original HIGH progress certificates exist because their actual
over-capacity domain has been proved empty. -/
theorem high_certificates
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi/lam) = 3) : CertExists o e 3 true lam := by
  intro t c ht hleg hover
  have hc := high_capacity o e he (by omega : 3 ≤ t) hleg hn
  exact False.elim ((not_lt_of_ge hc) hover)

/-- Both original third-strip branches now have unconditional capacity. -/
theorem strip_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3)
    (big : Bool) (hbig : big = false → Real.pi/lam-3 < 1/2) :
    potential lam (directionRows o e c) ≤ sendovCap 3 big := by
  cases big with
  | false => exact N3LowPairClosure.low_capacity_of_delta o e he hs hleg hn (hbig rfl)
  | true => exact high_capacity o e he hs hleg hn

theorem strip_certificates
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi/lam) = 3)
    (big : Bool) (hbig : big = false → Real.pi/lam-3 < 1/2) :
    CertExists o e 3 big lam := by
  cases big with
  | false => exact N3LowPairClosure.low_certificates o e he hn (hbig rfl)
  | true => exact high_certificates o e he hn

#print axioms nonsaturated_high_capacity
#print axioms high_capacity
#print axioms high_certificates
#print axioms strip_capacity
#print axioms strip_certificates
end Jsp404.N3HighPairClosure
