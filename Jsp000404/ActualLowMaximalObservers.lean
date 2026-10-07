import Jsp000404.ActualMinimalBandCounterexample
import Jsp000404.ActualMaximalLowRowClumps
import Jsp000404.SmallTwoClusterGeometry

set_option autoImplicit false

/-! Original maximal-score observers in an arbitrary LOW minimal model.

The score bound, all outgoing zero gains, full-hull membership, actual
two-clump data and same-clump companions are derived internally. The
selected centers only supply their original score and an actual wide
pair of rays. This file is SOURCE_ONLY until independently checked.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualLowMaximalObservers

/-- Nonsaturation bounds every original score by `n-2` in the original
LOW minimal counter-model. No score cap is supplied by the caller. -/
theorem actual_low_score_le_maximal {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) (s + 1) c lam)
    (p : Fin (s + 1)) : rowScore lam (directionRow o e c p) ≤ n - 2 := by
  obtain ⟨hfloor, _, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by omega : 2 ≤ n) H.legality.lam_pos H.scale_lower H.scale_upper
  have hdef := ActualMinimalBandCounterexample.low_model_nonsaturated
    (by omega : 2 ≤ n) o e he H p
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by have := H.card_ge_three; omega) hfloor
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos n _ hcells
  omega

/-- A maximal original observer has zero actual row gain when any
other original target is deleted: positive gain would make that target
removable by Certificate A and contradict the model's minimum card. -/
theorem actual_maximal_observer_gain_eq_zero {s n : ℕ} (hs3 : 3 ≤ s) (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) (s + 1) c lam)
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (q : Fin (s + 1)) (hpq : p ≠ q) :
    rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0 := by
  by_contra hnot
  have hpos : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
    omega
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
    exact actual_low_score_le_maximal hn4 o e he H q
  exact ActualMinimalBandCounterexample.not_actual_removable hs3 o e H q hrem

private theorem actual_maximal_two_clusters {s n : ℕ} (hs3 : 3 ≤ s) (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) (s + 1) c lam)
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (hwide : ∃ a b : Fin (s + 1), a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b)) :
    Nonempty (SmallTwoClusterGeometry.TwoClusters c lam (Real.pi - (n : ℝ) * lam) p) := by
  classical
  obtain ⟨hfloor, _, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by omega : 2 ≤ n) H.legality.lam_pos H.scale_lower H.scale_upper
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by omega : 2 ≤ s + 1) hfloor
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos n _ hcells
  have hdef : rowDefect n lam (directionRow o e c p) ≤ 2 := by omega
  have hhull := FullHullInteriorDefect.low_defect_is_full_hull_vertex
    o e he H.legality hfloor p hdef
  obtain ⟨D⟩ := ActualMaximalLowRowClumps.exists_actual_maximal_low_row_clumps
    (by omega : 3 ≤ s + 1) hn4 o e he H.legality
    H.scale_lower H.scale_upper p hhull hp hwide
  refine ⟨{
    code := D.clumps.code
    same_angle := ?_
    different_angle := ?_
    companion := ?_ }⟩
  · intro i j hi hj hsame
    exact D.clumps.same_angle_le H.legality i j hi hj hsame
  · intro i j hi hj hdiff
    exact D.clumps.different_angle_ge H.legality i j hi hj hdiff
  · intro q hqp
    by_contra hnone
    push_neg at hnone
    have hgain : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
      apply rowGain_pos_of_forall_angle_ge o e c H.legality he
        hqp.symm (by omega : 3 ≤ s + 1)
      intro j hjp hjq
      have hangle := D.clumps.different_angle_ge H.legality q j hqp hjp
        (Ne.symm (hnone j hjp hjq))
      linarith [H.legality.lam_pos]
    have hzero := actual_maximal_observer_gain_eq_zero hs3 hn4 o e he H p hp q hqp.symm
    omega

/-- Three distinct original maximal-score centers with actual wide
pairs cannot occur in an arbitrary `n ≥ 4` LOW minimal model. Their
two clusters, companions and gains are not caller inputs. -/
theorem no_three_nonacute_maximal_observers {s n : ℕ} (hs3 : 3 ≤ s) (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) (s + 1) c lam)
    (pick : Fin 3 → Fin (s + 1)) (hpick : Function.Injective pick)
    (hselected : ∀ i : Fin 3,
      rowScore lam (directionRow o e c (pick i)) = n - 2 ∧
      ∃ a b : Fin (s + 1), a ≠ pick i ∧ b ≠ pick i ∧ a ≠ b ∧
        2 * lam ≤ ∠ (c a) (c (pick i)) (c b)) : False := by
  classical
  have hex (i : Fin 3) : Nonempty
      (SmallTwoClusterGeometry.TwoClusters c lam (Real.pi - (n : ℝ) * lam) (pick i)) :=
    actual_maximal_two_clusters hs3 hn4 o e he H (pick i) (hselected i).1 (hselected i).2
  let D : ∀ i : Fin 3,
      SmallTwoClusterGeometry.TwoClusters c lam (Real.pi - (n : ℝ) * lam) (pick i) :=
    fun i => Classical.choice (hex i)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hden : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hmul := (div_lt_iff₀ hden).mp H.scale_lower
  have hR : Real.pi - (n : ℝ) * lam < lam / 2 := by nlinarith
  exact SmallTwoClusterGeometry.no_three_small_two_clusters H.legality hR pick hpick D

#print axioms actual_low_score_le_maximal
#print axioms actual_maximal_observer_gain_eq_zero
#print axioms no_three_nonacute_maximal_observers

end Jsp404.ActualLowMaximalObservers
