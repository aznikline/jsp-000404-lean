import Jsp000404.ActualMaximumMassReduction
import Jsp000404.FlatDeletionBudget

/-! A flat actual band maximizer has a functional incoming-emission graph.
The attained maximum is supplied by the independent classical coarse bound.
No sharp capacity or emitter-selection hypothesis occurs in the LOW consumer.
-/

open scoped EuclideanGeometry BigOperators

namespace Jsp404.FlatBandMaximumDeletion

theorem actual_band_maximizer_delete_has_at_most_one_emitter {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {d : Fin (s + 1) → Plane₂} {lam rho upper : ℝ}
    (hleg : Section4Legality d lam) (hflat : Flat lam (directionRows o e d))
    (habove : rho < lam) (hbelow : lam ≤ upper)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper (s + 1))
    (q : Fin (s + 1)) :
    (∀ i : Fin (s + 1), i ≠ q →
      rowGain lam (directionRow o e d i) (deleteIndex o e d q i) ≤ 1) ∧
      ((Finset.univ.erase q).filter (fun i =>
        1 ≤ rowGain lam (directionRow o e d i) (deleteIndex o e d q i))).card ≤ 1 := by
  have hdelete := hmax hs (d ∘ q.succAbove) lam habove hbelow (hleg.erase q)
  exact FlatDeletionBudget.actual_flat_delete_has_at_most_one_emitter
    (by omega) o e hleg.lam_pos hflat q hdelete

/-- A LOW counterexample gives a genuine flat model above the sharp cap
whose every actual deletion has at most one positive incoming gain. The
remaining geometric task is to exclude this explicit constrained model. -/
theorem exists_low_flat_functional_counter_model {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hlow : Real.pi / lam - (n : ℝ) < 1 / 2)
    (hover : 2 ^ n < potential lam (directionRows o e c)) :
    ∃ t : ℕ, 3 ≤ t ∧ 2 ^ n < t + 1 ∧ t + 1 ≤ 2 ^ (n + 1) ∧
      ∃ scale : ℝ, Real.pi / ((n : ℝ) + 1 / 2) < scale ∧
        scale ≤ Real.pi / (n : ℝ) ∧
        ∃ d : Fin (t + 1) → Plane₂, Section4Legality d scale ∧
          Flat scale (directionRows o e d) ∧ potential scale (directionRows o e d) = t + 1 ∧
          ∀ q : Fin (t + 1),
            (∀ i : Fin (t + 1), i ≠ q →
              rowGain scale (directionRow o e d i) (deleteIndex o e d q i) ≤ 1) ∧
              ((Finset.univ.erase q).filter (fun i =>
                1 ≤ rowGain scale (directionRow o e d i) (deleteIndex o e d q i))).card ≤ 1 := by
  obtain ⟨M, hoverM, hboundM, hmax, scale, habove, hbelow, d, hd, hflat, hpot⟩ :=
    ActualMaximumMassReduction.exists_flat_low_band_counter_maximizer
      hn4 o e he hs c hleg hn hlow hover
  have hp : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn4
  norm_num at hp
  cases M with
  | zero => omega
  | succ t =>
      have ht : 3 ≤ t := by omega
      refine ⟨t, ht, hoverM, hboundM, scale, habove, hbelow, d, hd, hflat, hpot, ?_⟩
      intro q
      exact actual_band_maximizer_delete_has_at_most_one_emitter ht o e
        hd hflat habove hbelow hmax q

#print axioms actual_band_maximizer_delete_has_at_most_one_emitter
#print axioms exists_low_flat_functional_counter_model

end Jsp404.FlatBandMaximumDeletion
