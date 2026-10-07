import Jsp000404.ActualN4LowCriticalReduction
import Jsp000404.ActualZeroPairDeletionBudget

set_option autoImplicit false

/-!
SOURCE_ONLY: deleting an original score-one target has zero gain at
every original positive-score observer in the original n4 LOW Model.
The original F17 value and the actual deletion cap are derived internally.
This does not assert zero gain at an original score-zero observer.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF17PositiveObserverZeroGain

/-- The original F17 retained mass after a light deletion is fifteen.
Its at-most-one expense cannot pay any positive-score observer's growth.
No caller deletion cap, potential value or gain array is supplied. -/
theorem actual_positive_observer_light_target_gain_zero {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (q : Fin (s + 1)) (hq : rowScore lam (directionRow o e c q) = 1)
    (i : Fin (s + 1)) (hiq : i ≠ q)
    (hi : 1 ≤ rowScore lam (directionRow o e c i)) :
    rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0 := by
  classical
  have hF := ActualN4LowCriticalReduction.actual_n4_low_model_potential_eq_seventeen
    o e he H
  have hs3 : 3 ≤ s := by
    by_contra hnot
    obtain ⟨hn, hlow, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
      (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
    have hcap : potential lam (directionRows o e c) ≤ 16 := by
      simpa using GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low
        o e he H.card_ge_three (by omega : s + 1 ≤ 5) (by decide : 3 ≤ 4)
        H.legality.lam_pos hn hlow H.legality
    omega
  let T : Finset (Fin (s + 1)) := Finset.univ.erase q
  let k : Fin (s + 1) → ℕ := fun j => rowScore lam (directionRow o e c j)
  let g : Fin (s + 1) → ℕ := fun j =>
    rowGain lam (directionRow o e c j) (deleteIndex o e c q j)
  have hmass : (∑ j : Fin (s + 1), 2 ^ k j) = 17 := by
    simpa only [k, potential, exponentAt, directionRows] using hF
  have htarget : k q = 1 := hq
  have hbase : (∑ j ∈ T, 2 ^ k j) = 15 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin (s + 1)))
      (fun j => 2 ^ k j) (Finset.mem_univ q)
    rw [htarget, pow_one, hmass] at hsplit
    dsimp only [T]
    omega
  have hdelete := ActualMinimalBandCounterexample.actual_delete_potential_le_cap
    hs3 o e H q
  have hledger := ActualMinimumDeletionNormalForm.actual_delete_potential_eq_sum_pow_gain
    (by omega : 2 ≤ s) o e (c := c) H.legality.lam_pos q
  have hcap : (∑ j ∈ T, 2 ^ k j * 2 ^ g j) ≤ (∑ j ∈ T, 2 ^ k j) + 1 := by
    change (∑ j ∈ Finset.univ.erase q,
      2 ^ rowScore lam (directionRow o e c j) *
        2 ^ rowGain lam (directionRow o e c j) (deleteIndex o e c q j)) ≤ _
    rw [← hledger, hbase]
    exact hdelete
  have hbudget := ActualZeroPairDeletionBudget.weighted_gain_budget_le_one T k g hcap
  exact ActualZeroPairDeletionBudget.positive_score_gain_eq_zero T k g hbudget
    (Finset.mem_erase.mpr ⟨hiq, Finset.mem_univ i⟩) hi

#print axioms actual_positive_observer_light_target_gain_zero

end Jsp404.ActualF17PositiveObserverZeroGain
