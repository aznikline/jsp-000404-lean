import Jsp000404.AnchoredRows
import Jsp000404.BinGraphs
import Jsp000404.ChartInvariance

/-!
# The low-regime capacity bound with a saturated center

The saturated center provides a narrow anchor cone. All other chord
directions fit into n-1 bins; local empty-bin counts and disjoint binary
subcubes bound their total weight. Reference invariance returns the result
to the original chart. No certificate or global packing premise is used.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

private lemma directionRow_score_le_floor {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (hs : 2 ≤ s) {lam : ℝ} (hlam : 0 < lam) (i : Fin s) :
    rowScore lam (directionRow o e c i) ≤ Nat.floor (Real.pi / lam) - 1 := by
  classical
  let l := directionRow o e c i
  have hsort : l.SortedLE := directionRow_sorted o e c i
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [directionRow_length]
    omega
  have hsortD : l.dedup.SortedLE :=
    (hsort.pairwise.sublist (List.dedup_sublist l)).sortedLE
  have hneD : l.dedup ≠ [] := fun h => hne ((List.dedup_eq_nil l).mp h)
  have hmemD : ∀ x ∈ l.dedup, x ∈ Set.Ico 0 Real.pi := by
    intro x hx
    exact directionRow_mem_Ico o e c (List.mem_dedup.mp hx)
  have h := exponent_le_floor hsortD (List.nodup_dedup l) hmemD hneD hlam
  rw [exponents_entry_eq_rowScore hsortD, rowScore_dedup lam hsort] at h
  exact h

theorem one_saturated_low_capacity_chart {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 1 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : Real.pi / lam - n < 1/2) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ potential lam (directionRows o e' c) ≤ 2 ^ n := by
  classical
  obtain ⟨e', he', theta, htheta, hcorr⟩ :=
    saturated_low_corridor o e he hs hn2 hlam hn hleg v hsat hδ
  let m := n - 1
  let width : ℝ := (Real.pi - 3 * lam / 2) / m
  have hm : 0 < m := by dsimp [m]; omega
  have hw : 0 < width := (low_corridor_grid_width hn2 hlam hn hδ).1
  have hwidth : width < lam := (low_corridor_grid_width hn2 hlam hn hδ).2
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hend : lam + (m : ℝ) * width = Real.pi - lam / 2 := by
    dsimp [width]
    field_simp
    <;> ring
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlampi : lam < Real.pi := by nlinarith
  let p := c ∘ v.succAbove
  have hp : Function.Injective p := hleg.inj.comp Fin.succAbove_right_injective
  have hpos : ∀ i j : Fin s, i ≠ j →
      dirRep o e' p i j ∈ Set.Icc lam (lam + m * width) := by
    intro i j hij
    rw [hend]
    exact hcorr i j hij
  have hangle : ∀ i j k : Fin s, i ≠ j → i ≠ k → j ≠ k →
      ∠ (p i) (p j) (p k) ≤ Real.pi - lam := by
    intro i j k hij hik hjk
    exact hleg.triAngle _ _ _
      (fun h => hij (Fin.succAbove_right_injective h))
      (fun h => hjk (Fin.succAbove_right_injective h))
      (fun h => hik (Fin.succAbove_right_injective h))
  have hbins := directionBinGraph_row_weighted_bound o e' p he' hp hm hw hwidth
    hlam.le (by rw [hend]; linarith) hangle hpos
  have hlocal (i : Fin s) :
      rowScore lam (directionRow o e' c (v.succAbove i)) ≤
        m - ((directionRow o e' p i).map (uniformBin lam width m)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e' he' c hleg.inj v hlam hlampi theta
      (fun i => ⟨(Set.Icc_subset_Icc le_rfl (half_le_self hlam.le))
        (htheta i).1, (htheta i).2⟩)
      (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval hm hw hwidth
      (by linarith [(htheta i).1.1])
      (by rw [hend]; linarith [(htheta i).1.2])
      _ (directionRow_sorted o e' p i)
    intro x hx
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e' p).mp hx
    exact hpos i j hji.symm
  have hrest : (∑ i : Fin s, 2 ^ rowScore lam (directionRow o e' c (v.succAbove i)))
      ≤ 2 ^ m := by
    exact (Finset.sum_le_sum (fun i _ =>
      Nat.pow_le_pow_right (by omega) (hlocal i))).trans hbins
  have hv : rowScore lam (directionRow o e' c v) ≤ m := by
    have h := directionRow_score_le_floor o e' c (by omega) hlam v
    rwa [hn] at h
  refine ⟨e', he', ?_⟩
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  calc 2 ^ rowScore lam (directionRow o e' c v) +
        ∑ i : Fin s, 2 ^ rowScore lam (directionRow o e' c (v.succAbove i))
      ≤ 2 ^ m + 2 ^ m := Nat.add_le_add (Nat.pow_le_pow_right (by omega) hv) hrest
    _ = 2 ^ n := by
      rw [← two_mul, ← pow_succ']
      congr 1
      dsimp [m]
      omega

/-- The complete low capacity bound for configurations with a saturated
center, in the original arbitrary nonzero reference chart. -/
theorem potential_le_two_pow_of_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : Real.pi / lam - n < 1/2) :
    potential lam (directionRows o e c) ≤ 2 ^ n := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  obtain ⟨e', he', hbound⟩ :=
    one_saturated_low_capacity_chart o e he (by omega) hn2 hlam hn hleg v hsat hδ
  rw [potential_directionRows_reference_eq o e e' he he' c hleg.inj lam]
  exact hbound

/-- The normalized Kraft form of the same arbitrary-size low bound. -/
theorem kraft_le_one_of_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : Real.pi / lam - n < 1/2) :
    ∑ i : Fin s, (1/2 : ℚ) ^ rowDefect n lam (directionRow o e c i) ≤ 1 := by
  have hcells : ∀ i, rowCells lam (directionRows o e c i) ≤ n :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i hs hn
  exact (potential_le_two_pow_iff_kraft hlam hcells).mp
    (potential_le_two_pow_of_saturated o e he hs hn2 hlam hn hleg v hsat hδ)

/-- The formerly open one-saturated LOW packing case: the other centers
use at most half the normalized capacity. -/
theorem rest_kraft_le_half_of_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : Real.pi / lam - n < 1/2) :
    ∑ i ∈ Finset.univ.erase v,
      (1/2 : ℚ) ^ rowDefect n lam (directionRow o e c i) ≤ 1/2 := by
  have hK := kraft_le_one_of_saturated o e he hs hn2 hlam hn hleg v hsat hδ
  have hsum := Finset.add_sum_erase Finset.univ
    (fun i => (1/2 : ℚ) ^ rowDefect n lam (directionRow o e c i))
    (Finset.mem_univ v)
  rw [hsat, pow_one] at hsum
  linarith

#print axioms one_saturated_low_capacity_chart
#print axioms potential_le_two_pow_of_saturated
#print axioms rest_kraft_le_half_of_saturated

end Jsp404
