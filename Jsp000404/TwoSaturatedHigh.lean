import Jsp000404.TwoAnchorAssembly
import Jsp000404.TwoAnchorCorridor
import Jsp000404.TwoSaturatedDeficit
import Jsp000404.Reindex

/-! # Global capacity with two saturated centers -/

namespace Jsp404

open scoped EuclideanGeometry

/-- Two saturated first centers: the remaining centers occupy at most
2^(n-2) of the original weight. Geometry constructs the common corridor;
the two-anchor assembly then gives the full high-regime capacity. -/
theorem potential_le_high_of_first_two_saturated {t n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (ht : 2 ≤ t) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (t + 2) → Plane₂} (hleg : Section4Legality c lam)
    (h0 : rowDefect n lam (directionRow o e c 0) = 1)
    (h1 : rowDefect n lam (directionRow o e c 1) = 1) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  have h01 : (0 : Fin (t + 2)) ≠ 1 := by
    intro h; have := congrArg Fin.val h; simp at this
  let k : Fin (t + 2) := ⟨2, by omega⟩
  have h0k : (0 : Fin (t + 2)) ≠ k := by
    intro h; have := congrArg Fin.val h; simp [k] at this
  have h1k : (1 : Fin (t + 2)) ≠ k := by
    intro h; have := congrArg Fin.val h; simp [k] at this
  have hdef := rowScore_add_three_le_of_two_saturated o e he hn2 hlam hn hleg
    (by omega) h01 h0k h1k h0 h1
  have hn3 : 3 ≤ n := by omega
  obtain ⟨d⟩ := two_saturated_corridor_data o e he hn2 hlam hn hleg
    (by omega) h01 h0 h1
  have hf : c 1 - c 0 ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne h01.symm)
  have hz (i : Fin t) : (0 : Fin (t + 2)) ≠ i.succ.succ := by
    intro h; have := congrArg Fin.val h; simp at this
  have ho (i : Fin t) : (1 : Fin (t + 2)) ≠ i.succ.succ := by
    intro h; have := congrArg Fin.val h; simp at this
  exact potential_le_high_of_two_anchor_data o e (c 1 - c 0) he hf c hleg hn3 hn h0 h1
    (fun i : Fin t => d.a i.succ.succ) (fun i : Fin t => d.b i.succ.succ)
    d.amin d.bmin
    (fun i => (d.row_bounds _ (hz i) (ho i)).2.1)
    (fun i => (d.row_bounds _ (hz i) (ho i)).2.2.2.1)
    d.amin_pos d.bmin_pos
    (fun i => (d.row_bounds _ (hz i) (ho i)).2.2.2.2.2)
    d.min_sum_lower d.min_sum_upper
    (fun i => d.anchor_reps _ (hz i) (ho i))
    (fun i j hij => d.chords _ _ (hz i) (ho i) (hz j) (ho j)
      (fun h => hij (Fin.succ_injective t ((Fin.succ_injective (t + 1)) h))))

/-- The full HIGH capacity bound with any two saturated centers, for
arbitrary configuration size and in the original reference chart. -/
theorem potential_le_high_of_two_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    {i j : Fin s} (hij : i ≠ j)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  by_cases hs4 : 4 ≤ s
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s-2, by omega⟩
    obtain ⟨σ, hσ0, hσ1⟩ := exists_equiv_zero_one_add_two i j hij
    have h0 : rowDefect n lam (directionRow o e (c ∘ σ) 0) = 1 := by
      rwa [directionRow_reindex, hσ0]
    have h1 : rowDefect n lam (directionRow o e (c ∘ σ) 1) = 1 := by
      rwa [directionRow_reindex, hσ1]
    have h := potential_le_high_of_first_two_saturated o e he (by omega)
      hn2 hlam hn (hleg.reindex σ) h0 h1
    rwa [potential_directionRows_reindex] at h
  · have hs3 : s = 3 := by omega
    subst s
    have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfloor
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have h := base3_potential_le_big (o := o) (e := e) hleg he
      (by nlinarith : lam < Real.pi) hn hn2
    have heq : 5 * 2 ^ (n-2) = 2 ^ n + 2 ^ (n-2) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
      simp only [Nat.add_sub_cancel, pow_add]
      ring
    rwa [heq] at h

/-- Normalized HIGH packing with two saturated centers. -/
theorem kraft_le_five_quarters_of_two_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    {i j : Fin s} (hij : i ≠ j)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    ∑ k : Fin s, (1/2 : ℚ) ^ rowDefect n lam (directionRow o e c k) ≤ 5/4 := by
  have hW := potential_le_high_of_two_saturated o e he hs hn2 hlam hn hleg hij hi hj
  have hK := (potential_le_sendovCap_iff_kraft o e hn2 true hlam hn c (by omega)).mp
    (by simpa [sendovCap] using hW)
  norm_num only [ite_true] at hK
  simpa only [directionRows] using hK

/-- The two anchor terms consume one unit; all remaining actual row
weights use at most a quarter of the normalized capacity. -/
theorem rest_kraft_le_quarter_of_two_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    {i j : Fin s} (hij : i ≠ j)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    ∑ k ∈ (Finset.univ.erase i).erase j,
      (1/2 : ℚ) ^ rowDefect n lam (directionRow o e c k) ≤ 1/4 := by
  classical
  have hK := kraft_le_five_quarters_of_two_saturated o e he hs hn2 hlam hn hleg hij hi hj
  have hsum0 := Finset.add_sum_erase Finset.univ
    (fun k => (1/2 : ℚ) ^ rowDefect n lam (directionRow o e c k)) (Finset.mem_univ i)
  have hsum1 := Finset.add_sum_erase (Finset.univ.erase i)
    (fun k => (1/2 : ℚ) ^ rowDefect n lam (directionRow o e c k))
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  rw [hi, pow_one] at hsum0
  rw [hj, pow_one] at hsum1
  linarith

#print axioms potential_le_high_of_first_two_saturated
#print axioms potential_le_high_of_two_saturated
#print axioms kraft_le_five_quarters_of_two_saturated
#print axioms rest_kraft_le_quarter_of_two_saturated

end Jsp404
