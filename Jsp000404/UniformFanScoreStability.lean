import Jsp000404.FiniteFanScoreStability

/-! A common strictly smaller parameter for a finite family of finite fans.
The scale is chosen once from all limiting row gaps, before intersecting
the row/permutation/gap events. No per-row existential scales are combined.
-/

open Filter Topology
open scoped BigOperators

namespace Jsp404.UniformFanScoreStability

open FiniteFanScoreStability

/-- Continuity turns the common arithmetic margins into a coordinate event.
Zero-floor trajectories need only stay below their strict upper margin. -/
private theorem eventually_floor_of_common_margins {f : ℝ → ℝ}
    {g lam lam' : ℝ} (hf : ContinuousAt f 0) (hzero : f 0 = g)
    (hlam' : 0 < lam')
    (hupper : g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam')
    (hlower : 0 < ⌊g / lam⌋₊ → (⌊g / lam⌋₊ : ℝ) * lam' < g) :
    ∀ᶠ eps in 𝓝 (0 : ℝ), ⌊f eps / lam'⌋₊ = ⌊g / lam⌋₊ := by
  have hupper0 : f 0 < ((⌊g / lam⌋₊ : ℝ) + 1) * lam' := by
    rw [hzero]
    exact hupper
  have hu := hf.eventually_lt continuousAt_const hupper0
  by_cases hq : 0 < ⌊g / lam⌋₊
  · have hlower0 : (⌊g / lam⌋₊ : ℝ) * lam' < f 0 := by
      rw [hzero]
      exact hlower hq
    have hl := continuousAt_const.eventually_lt hf hlower0
    filter_upwards [hu, hl] with eps hup hlo
    apply (Nat.floor_eq_iff' (ne_of_gt hq)).mpr
    exact ⟨(le_div_iff₀ hlam').mpr hlo.le, (div_lt_iff₀ hlam').mpr hup⟩
  · have hz : ⌊g / lam⌋₊ = 0 := Nat.eq_zero_of_not_pos hq
    filter_upwards [hu] with eps hup
    rw [hz]
    apply Nat.floor_eq_zero.mpr
    apply (div_lt_one hlam').mpr
    simpa only [hz, Nat.cast_zero, zero_add, one_mul] using hup

/-- All rows and all actual sorted gap floors use one common parameter.
Row labels may form the empty type; fan labels are nonempty and may have
coincident limiting values. The actual sorting permutation is chosen
internally at every perturbation value. -/
theorem exists_uniform_sorted_gap_floor_stability {R : Type*} [Fintype R]
    {n : ℕ} (hn : 0 < n) (A : ℝ → R → Fin n → ℝ)
    (hcont : ∀ r i, ContinuousAt (fun eps => A eps r i) 0)
    (hrange : ∀ r i, A 0 r i ∈ Set.Ioo 0 Real.pi)
    {lam tau : ℝ} (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ r (i : Fin n),
        ⌊indexedGap (sortedTuple (A eps r)) i / lam'⌋₊ =
          ⌊indexedGap (sortedTuple (A 0 r)) i / lam⌋₊ := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let enum : (R × Fin (m + 1)) ≃ Fin (Fintype.card (R × Fin (m + 1))) :=
    Fintype.equivFin _
  let gs : Fin (Fintype.card (R × Fin (m + 1))) → ℝ := fun j =>
    indexedGap (sortedTuple (A 0 (enum.symm j).1)) (enum.symm j).2
  have hgs : ∀ j, 0 ≤ gs j := fun j =>
    indexedGap_sorted_nonneg (by omega) (A 0 (enum.symm j).1)
      (hrange (enum.symm j).1) (enum.symm j).2
  obtain ⟨lam', htau', hsmall, hm⟩ :=
    GapSplitFloorStability.exists_floor_stable_scale_with_margins
      (List.ofFn gs) hlam
      (fun g hg => by
        rcases List.mem_ofFn.mp hg with ⟨j, rfl⟩
        exact hgs j) htau0 htau
  have hlam' : 0 < lam' := htau0.trans htau'
  have hmargin (r : R) (i : Fin (m + 1)) :
      let g := indexedGap (sortedTuple (A 0 r)) i
      g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam' ∧
        (0 < ⌊g / lam⌋₊ → (⌊g / lam⌋₊ : ℝ) * lam' < g) := by
    have hmem : indexedGap (sortedTuple (A 0 r)) i ∈ List.ofFn gs :=
      List.mem_ofFn.mpr ⟨enum (r, i), by simp only [gs, Equiv.symm_apply_apply]⟩
    exact (hm _ hmem).2
  have hfixed : ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ r,
      ∀ perm : Equiv.Perm (Fin (m + 1)),
      (List.ofFn (fun j => A 0 r (perm j))).SortedLE → ∀ i,
        ⌊indexedGap (fun j => A eps r (perm j)) i / lam'⌋₊ =
          ⌊indexedGap (sortedTuple (A 0 r)) i / lam⌋₊ := by
    apply eventually_all.mpr
    intro r
    apply eventually_all.mpr
    intro perm
    by_cases hs0 : (List.ofFn (fun j => A 0 r (perm j))).SortedLE
    · have heq : (fun j => A 0 r (perm j)) = sortedTuple (A 0 r) :=
        Tuple.comp_sort_eq_comp_iff_monotone.mpr (List.sortedLE_ofFn_iff.mp hs0)
      have hper : ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ i,
          ⌊indexedGap (fun j => A eps r (perm j)) i / lam'⌋₊ =
            ⌊indexedGap (sortedTuple (A 0 r)) i / lam⌋₊ := by
        apply eventually_all.mpr
        intro i
        have hc : ContinuousAt (fun eps =>
            indexedGap (fun j => A eps r (perm j)) i) 0 :=
          ActualScorePreservingExpansion.continuousAt_gapAfter_ofFn
            (fun j eps => A eps r (perm j)) (fun j => hcont r (perm j)) i
        have hz : indexedGap (fun j => A 0 r (perm j)) i =
            indexedGap (sortedTuple (A 0 r)) i := by rw [heq]
        exact eventually_floor_of_common_margins hc hz hlam' (hmargin r i).1
          (hmargin r i).2
      exact hper.mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => False.elim (hs0 h)
  have hsortLimit : ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ r,
      ∀ perm : Equiv.Perm (Fin (m + 1)),
      (List.ofFn (fun j => A eps r (perm j))).SortedLE →
        (List.ofFn (fun j => A 0 r (perm j))).SortedLE := by
    apply eventually_all.mpr
    intro r
    exact ActualScorePreservingExpansion.eventually_sorted_limit_of_sorted
      (fun i eps => A eps r i) (hcont r)
  refine ⟨lam', htau', hsmall, ?_⟩
  filter_upwards [hfixed, hsortLimit] with eps hfix hlim
  intro r
  have hactual : (List.ofFn (sortedTuple (A eps r))).SortedLE :=
    sortedFan_sorted (A eps r)
  have hlimit : (List.ofFn (fun j => A 0 r (Tuple.sort (A eps r) j))).SortedLE :=
    hlim r (Tuple.sort (A eps r)) hactual
  exact hfix r (Tuple.sort (A eps r)) hlimit

/-- A finite family of finite fans preserves all cyclic row scores at one
common strictly smaller parameter and one common perturbation event. -/
theorem exists_uniform_sorted_score_stability {R : Type*} [Fintype R]
    {n : ℕ} (hn : 0 < n) (A : ℝ → R → Fin n → ℝ)
    (hcont : ∀ r i, ContinuousAt (fun eps => A eps r i) 0)
    (hrange : ∀ r i, A 0 r i ∈ Set.Ioo 0 Real.pi)
    {lam tau : ℝ} (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ r,
        rowScore lam' (sortedFan (A eps r)) = rowScore lam (sortedFan (A 0 r)) := by
  obtain ⟨lam', htau', hsmall, hevent⟩ :=
    exists_uniform_sorted_gap_floor_stability hn A hcont hrange hlam htau0 htau
  refine ⟨lam', htau', hsmall, hevent.mono ?_⟩
  intro eps hfloor r
  rw [rowScore_sortedFan_eq_sum, rowScore_sortedFan_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hfloor r i]

#print axioms exists_uniform_sorted_gap_floor_stability
#print axioms exists_uniform_sorted_score_stability

end Jsp404.UniformFanScoreStability
