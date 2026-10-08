import Jsp000404.ActualF17PositiveObserverZeroGain
import Jsp000404.ActualHullConeDeletion
import Jsp000404.ActualPositiveGainTargetBudget

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY unique-zero narrow-hull-light targets. The actual target set
is defined on original point indices. Every member is forced to have the
same actual emitting observer z; its cardinality then uses the checked
actual positive-gain target budget. No target set, common cone, bisector,
window, type, degree bound or gain certificate is a caller input.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF17UniqueZeroNarrowHullTargets

/-- Original light full-hull centers whose actual full ray cone has the
narrow angular cap. The predicate quantifies over original actual rays. -/
noncomputable def narrowHullLightTargets {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) : Finset (Fin t) := by
  classical
  exact Finset.univ.filter (fun q =>
    rowScore lam (directionRow o e c q) = 1 ∧ IsHullVertex c q ∧
      ∀ a b : Fin t, a ≠ q → b ≠ q → a ≠ b →
        ∠ (c a) (c q) (c b) ≤ Real.pi - 2 * lam)

/-- In the original unique-zero LOW4 Model, each internally defined
narrow light hull target is emitted to by the same original zero
observer z. Consequently there are at most four such actual targets.
The common-observer field is retained, not merely its cardinality. -/
theorem actual_unique_zero_narrow_hull_light_targets {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ q : Fin (s + 1), q ≠ z → 1 ≤ rowScore lam (directionRow o e c q)) :
    (∀ q ∈ narrowHullLightTargets o e c lam, q ≠ z ∧
      1 ≤ rowGain lam (directionRow o e c z) (deleteIndex o e c q z)) ∧
      (narrowHullLightTargets o e c lam).card ≤ 4 := by
  classical
  have hs2 : 2 ≤ s := by have := H.card_ge_three; omega
  have hemit (q : Fin (s + 1)) (hq : q ∈ narrowHullLightTargets o e c lam) :
      q ≠ z ∧ 1 ≤ rowGain lam (directionRow o e c z) (deleteIndex o e c q z) := by
    have hdata : rowScore lam (directionRow o e c q) = 1 ∧ IsHullVertex c q ∧
        ∀ a b : Fin (s + 1), a ≠ q → b ≠ q → a ≠ b →
          ∠ (c a) (c q) (c b) ≤ Real.pi - 2 * lam := by
      simpa only [narrowHullLightTargets, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    obtain ⟨hlight, hhull, hcap⟩ := hdata
    have hqz : q ≠ z := by
      intro heq
      rw [heq, hz] at hlight
      omega
    obtain ⟨i, hiq, hgain⟩ := ActualHullConeDeletion.exists_emitter_of_actual_hull_angle_bound
      hs2 o e he H.legality q hhull hcap
    have hiz : i = z := by
      by_contra hne
      have hzero := ActualF17PositiveObserverZeroGain.actual_positive_observer_light_target_gain_zero
        o e he H q hlight i hiq (hpositive i hne)
      omega
    exact ⟨hqz, by simpa only [hiz] using hgain⟩
  have hsub : narrowHullLightTargets o e c lam ⊆
      (Finset.univ.erase z).filter (fun q =>
        1 ≤ rowGain lam (directionRow o e c z) (deleteIndex o e c q z)) := by
    intro q hq
    have hm := hemit q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hm.1, Finset.mem_univ q⟩, hm.2⟩
  have hrho : Real.pi / ((4 : ℝ) + 1 / 2) = 2 * Real.pi / 9 := by ring
  have hscale : 2 * Real.pi / 9 < lam := by rw [← hrho]; exact H.scale_lower
  have h5 : Real.pi / 5 < lam := by linarith only [hscale, Real.pi_pos]
  have hdegree := ActualPositiveGainTargetBudget.actual_positive_gain_targets_card_le_four
    o e he H.legality h5 z
  exact ⟨hemit, (Finset.card_le_card hsub).trans hdegree⟩

#print axioms actual_unique_zero_narrow_hull_light_targets

end Jsp404.ActualF17UniqueZeroNarrowHullTargets
