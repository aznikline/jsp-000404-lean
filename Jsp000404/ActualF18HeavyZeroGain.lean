import Jsp000404.ActualMinimalBandCounterexample

set_option autoImplicit false

/-! Every original score-two observer has zero outgoing actual row gain
in any original n4 LOW minimal counter to cap sixteen. The original
nonsaturation and score bounds are produced internally. F18 is a corollary.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualF18HeavyZeroGain

/-- The original LOW model supplies nonsaturation and hence score at most
two. Positive gain at a score-two observer p would cover the original
weight of any distinct deleted target q and make q actually removable.
Neither potential eighteen nor a caller-supplied score/gain cap is needed. -/
theorem actual_low_four_heavy_observer_gain_eq_zero {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (q : Fin s) (hpq : p ≠ q) :
    rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0 := by
  obtain ⟨hn,hdelta,hpi⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hdef := ActualMinimalBandCounterexample.low_model_nonsaturated
    (n := 4) (by decide : 2 ≤ 4) o e he H
  have hupper (i : Fin s) : rowScore lam (directionRow o e c i) ≤ 2 := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos i
      (by have := H.card_ge_three; omega) hn
    have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
    have hi := hdef i
    omega
  have hs4 : 4 ≤ s := by
    by_contra hnot
    have hs3 : s = 3 := by have := H.card_ge_three; omega
    subst s
    have hcap : potential lam (directionRows o e c) ≤ 16 := by
      simpa using base3_potential_le (o := o) (e := e) H.legality he hpi hn
        (by decide : 2 ≤ 4) hdelta
    have hover := H.over_cap
    omega
  obtain ⟨u,rfl⟩ : ∃ u : ℕ, s = u+1 := ⟨s-1,by omega⟩
  have hs3 : 3 ≤ u := by omega
  by_contra hnot
  have hpos : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by omega
  have hrem : Removable lam (fun v i => deleteIndex o e c v i)
      (directionRows o e c) q := by
    apply removable_of_gain1_ge H.legality.lam_pos
      (fun v i => deleteIndex o e c v i) (directionRows o e c) q
      (fun i => directionRow_sorted o e c i)
      (fun i x hx => Set.mem_Ico.mp (directionRow_mem_Ico o e c hx))
      (fun i => by change 2 ≤ (directionRow o e c i).length
                   rw [directionRow_length]; omega)
      (fun i hi => deleteIndex_lt o e c hi) p hpq hpos
    change rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c p)
    rw [hp]
    exact hupper q
  exact ActualMinimalBandCounterexample.not_actual_removable hs3 o e H q hrem

/-- The F18 specialization preserves the original public conclusion;
its potential hypothesis is not needed by the stronger LOW theorem. -/
theorem actual_heavy_observer_gain_eq_zero {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (_hF : potential lam (directionRows o e c) = 18)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (q : Fin s) (hpq : p ≠ q) :
    rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0 :=
  actual_low_four_heavy_observer_gain_eq_zero o e he H p hp q hpq

#print axioms actual_low_four_heavy_observer_gain_eq_zero
#print axioms actual_heavy_observer_gain_eq_zero

end Jsp404.ActualF18HeavyZeroGain
