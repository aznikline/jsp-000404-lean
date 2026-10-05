import Jsp000404.ActualHighMaximumMassReduction
import Jsp000404.FlatBandMaximumDeletion

/-! A genuine HIGH flat functional counter-model.
Both band maximality and the bound on every actual deletion are obtained
internally from the original geometric counterexample. The remaining
task is a geometric exclusion of this explicit model, not assumed here.
-/

open scoped EuclideanGeometry

namespace Jsp404.HighFlatFunctionalReduction

/-- Every actual HIGH counterexample yields a flat real configuration
above the sharp cap whose every deletion has at most one positive emitter,
and every individual incoming row gain is at most one. No free maximality,
deletion-capacity, flatness, or sharp-capacity hypothesis is required. -/
theorem exists_high_flat_functional_counter_model {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hhigh : 1 / 2 ≤ Real.pi / lam - (n : ℝ))
    (hover : sendovCap n true < potential lam (directionRows o e c)) :
    ∃ t : ℕ, 3 ≤ t ∧ sendovCap n true < t + 1 ∧ t + 1 ≤ 2 ^ (n + 1) ∧
      ∃ scale : ℝ, Real.pi / ((n : ℝ) + 1) < scale ∧
        scale ≤ Real.pi / ((n : ℝ) + 1 / 2) ∧
        ∃ d : Fin (t + 1) → Plane₂, Section4Legality d scale ∧
          Flat scale (directionRows o e d) ∧ potential scale (directionRows o e d) = t + 1 ∧
          ∀ q : Fin (t + 1),
            (∀ i : Fin (t + 1), i ≠ q →
              rowGain scale (directionRow o e d i) (deleteIndex o e d q i) ≤ 1) ∧
              ((Finset.univ.erase q).filter (fun i =>
                1 ≤ rowGain scale (directionRow o e d i) (deleteIndex o e d q i))).card ≤ 1 := by
  obtain ⟨M, hoverM, hboundM, hmax, scale, habove, hbelow, d, hd, hflat, hpot⟩ :=
    ActualHighMaximumMassReduction.exists_flat_high_band_counter_maximizer
      hn4 o e he hs c hleg hn hhigh hover
  have hp : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn4
  norm_num at hp
  have hcap : 2 ^ n ≤ sendovCap n true := by simp [sendovCap]
  cases M with
  | zero => omega
  | succ t =>
      have ht : 3 ≤ t := by omega
      refine ⟨t, ht, hoverM, hboundM, scale, habove, hbelow, d, hd, hflat, hpot, ?_⟩
      intro q
      exact FlatBandMaximumDeletion.actual_band_maximizer_delete_has_at_most_one_emitter
        ht o e hd hflat habove hbelow hmax q

#print axioms exists_high_flat_functional_counter_model

end Jsp404.HighFlatFunctionalReduction
