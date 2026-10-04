import Jsp000404.NoSatFiveGeometry
import Jsp000404.N3CapacityReduction

/-! The finite positive-row exclusions are lifted by actual injective
restrictions. No no-saturation assumption is used for the positive counts;
the exact no-saturation weight identity is used only in the cap consumers. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.N3PositiveBounds

/-- Any actual low-third-strip configuration with at least five centers
has at most three positive rows. -/
theorem low_positive_card_le_three {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 5 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3)
    (hlow : 2*Real.pi/7 < lam) :
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 3 := by
  classical
  let P : Finset (Fin s) := Finset.univ.filter
    (fun i => 0 < rowScore lam (directionRow o e c i))
  change P.card ≤ 3
  by_contra hb
  obtain ⟨K, hKP, hK⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ P.card)
  obtain ⟨pick, hpick, hkeep⟩ := N3SaturatedBounds.exists_restriction_containing
    K (by omega : K.card ≤ 5) hs
  let P' : Finset (Fin 5) := Finset.univ.filter
    (fun i => 0 < rowScore lam (directionRow o e (c ∘ pick) i))
  have hsub : K ⊆ P'.image pick := by
    intro v hv
    obtain ⟨i, hi⟩ := hkeep v hv
    have hvP := (Finset.mem_filter.mp (hKP hv)).2
    have hpos : 0 < rowScore lam (directionRow o e (c ∘ pick) i) := by
      have hm := PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos
        (by omega : 2 ≤ 5) pick hpick i
      rw [hi] at hm
      exact hvP.trans_le hm
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩, hi⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hpick] at hcard
  have hsmall : P'.card ≤ 3 := NoSatFiveGeometry.five_positive_card_le_three
    o e he (hleg.restrict_injective pick hpick) hn hlow
  omega

/-- The original LOW capacity for every actual five-center third-strip
configuration; saturation and no-saturation are both covered. -/
theorem five_low_capacity
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3) (hlow : 2*Real.pi/7 < lam) :
    potential lam (directionRows o e c) ≤ 8 := by
  classical
  by_cases hsat : ∃ v, rowDefect 3 lam (directionRow o e c v) = 1
  · obtain ⟨v, hv⟩ := hsat
    have hd : Real.pi/lam-3 < 1/2 := by
      have hm : Real.pi < (7/2)*lam := by linarith
      have hh := (div_lt_iff₀ hleg.lam_pos).mpr hm
      linarith
    have h := N3SaturatedBounds.saturated_strip_capacity o e he (by omega : 3 ≤ 5)
      hleg.lam_pos hn hleg v hv false (fun _ => hd)
    simpa [sendovCap] using h
  · have hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i) := by
      intro i
      have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos i
        (by omega : 2 ≤ 5) hn
      have h1 := one_le_rowDefect lam hleg.lam_pos 3 _ (by omega) hc
      have hh : rowDefect 3 lam (directionRow o e c i) ≠ 1 := fun h => hsat ⟨i, h⟩
      omega
    have hw := N3NoSaturatedBound.nonsaturated_potential_eq_card_add_positive
      o e (by omega : 2 ≤ 5) hleg.lam_pos hn hns
    have hp := low_positive_card_le_three o e he (by omega : 5 ≤ 5) hleg hn hlow
    omega

/-- Only four actual LOW no-saturation exclusions remain after the new
five-point theorem. This predicate intentionally remains an open hypothesis. -/
def LowRemainingExclusion
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (lam : ℝ) : Prop :=
  ∀ s : ℕ, 6 ≤ s+1 → s+1 ≤ 9 → ∀ c : Fin (s+1) → Plane₂,
    N3CapacityReduction.MinimalNoSaturated o e lam 8 s c →
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 3 →
    s+1+(Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card = 9 →
    False

/-- Actual arbitrary-cardinality LOW capacity, with exactly the four
remaining geometric exclusions exposed as a hypothesis. -/
theorem low_capacity_of_remaining_exclusion {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 3)
    (hlow : 2*Real.pi/7 < lam) (hex : LowRemainingExclusion o e lam) :
    potential lam (directionRows o e c) ≤ 8 := by
  apply N3CapacityReduction.low_capacity_of_finite_exclusion o e he hs hleg hn hlow
  intro t ht5 ht9 c' hM _hr hsum
  have hp := low_positive_card_le_three o e he ht5 hM.legality hM.strip hlow
  have ht6 : 6 ≤ t+1 := by omega
  exact hex t ht6 ht9 c' hM hp hsum

#print axioms low_positive_card_le_three
#print axioms five_low_capacity
#print axioms low_capacity_of_remaining_exclusion
end Jsp404.N3PositiveBounds
