import Jsp000404.Induction

/-!
# Actual cyclic-gap support and fractional remainder structure

These bounds concern `rowDefect` and the genuine sorted `directionRow`.
They do not assume a packing or capacity theorem. In particular a six-point
row has five gaps, so its defect is at most nine for every strip parameter.
-/

namespace Jsp404

/-- Fractional floor remainders of the actual cyclic gaps, counted with
multiplicity in exactly the same way as `rowCells`. -/
noncomputable def rowResidual (lam : ℝ) (l : List ℝ) : ℝ :=
  ∑ j : Fin l.length,
    (gapAfter l j / lam - (⌊gapAfter l j / lam⌋₊ : ℝ))

/-- The fractional remainders sum to `π/λ − cells`. -/
theorem rowResidual_eq_ratio_sub_cells {lam : ℝ} (_hlam : 0 < lam)
    {l : List ℝ} (hs : l.SortedLE) (hne : l ≠ []) :
    rowResidual lam l = Real.pi / lam - (rowCells lam l : ℝ) := by
  unfold rowResidual
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, gapAfter_sum hne,
    rowCells_eq_sum_floor hs]
  norm_cast

/-- The exact support/remainder identity for the existing defect. -/
theorem rowResidual_identity {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (hne : l ≠ [])
    (hn : ⌊Real.pi / lam⌋₊ = n) :
    rowResidual lam l = (rowDefect n lam l : ℝ) - (rowBig lam l : ℝ) +
      (Real.pi / lam - (n : ℝ)) := by
  have hcells : rowCells lam l ≤ n := by
    rw [← hn]
    exact rowCells_le_floor_pi hlam hs hmem hne
  rw [rowResidual_eq_ratio_sub_cells hlam hs hne, rowDefect,
    Nat.cast_add, Nat.cast_sub hcells]
  ring

/-- Every gap has a nonnegative floor remainder, strictly below one. -/
theorem rowResidual_bounds {lam : ℝ} (hlam : 0 < lam)
    {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (hne : l ≠ []) :
    0 ≤ rowResidual lam l ∧ rowResidual lam l < (l.length : ℝ) := by
  have hn := gapAfter_nonneg hs hmem hne
  have hres : ∀ j : Fin l.length,
      0 ≤ gapAfter l j / lam - (⌊gapAfter l j / lam⌋₊ : ℝ) ∧
      gapAfter l j / lam - (⌊gapAfter l j / lam⌋₊ : ℝ) < 1 := by
    intro j
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le (div_nonneg (hn j) hlam.le))
    · have h := Nat.lt_floor_add_one (gapAfter l j / lam)
      linarith
  constructor
  · exact Finset.sum_nonneg (fun j _ => (hres j).1)
  · unfold rowResidual
    have hpos : 0 < l.length := List.length_pos_iff.mpr hne
    have hlt : (∑ j : Fin l.length,
        (gapAfter l j / lam - (⌊gapAfter l j / lam⌋₊ : ℝ))) <
        ∑ _j : Fin l.length, (1 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact (hres j).2.le
      · exact ⟨⟨0, hpos⟩, Finset.mem_univ _, (hres ⟨0, hpos⟩).2⟩
    simpa using hlt

/-- At most `m−1` cells are lost to flooring a row of `m` gaps. -/
theorem rowFloorLoss_lt_length {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (hne : l ≠ [])
    (hn : ⌊Real.pi / lam⌋₊ = n) :
    n - rowCells lam l < l.length := by
  have hcells : rowCells lam l ≤ n := by
    rw [← hn]
    exact rowCells_le_floor_pi hlam hs hmem hne
  have hfloor : (n : ℝ) ≤ Real.pi / lam := by
    rw [← hn]
    exact Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  have hlt := (rowResidual_bounds hlam hs hmem hne).2
  rw [rowResidual_eq_ratio_sub_cells hlam hs hne] at hlt
  have hcast : ((n - rowCells lam l : ℕ) : ℝ) < (l.length : ℝ) := by
    rw [Nat.cast_sub hcells]
    linarith
  exact_mod_cast hcast

/-- Support plus floor loss gives the uniform `2m−1` defect bound. -/
theorem rowDefect_le_two_length_sub_one {lam : ℝ} (hlam : 0 < lam)
    {n : ℕ} {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (hne : l ≠ [])
    (hn : ⌊Real.pi / lam⌋₊ = n) :
    rowDefect n lam l ≤ 2 * l.length - 1 := by
  have hloss := rowFloorLoss_lt_length hlam hs hmem hne hn
  have hbig : rowBig lam l ≤ l.length := by
    unfold rowBig
    calc
      _ ≤ (cycGaps l).length := List.length_filter_le _ _
      _ = l.length := by rw [cycGaps_eq_ofFn_gapAfter hs, List.length_ofFn]
  unfold rowDefect
  omega

/-- Any actual six-point direction row has defect at most nine, uniformly
in `n`. No injectivity or legality is needed for this arithmetic bound. -/
theorem directionRow_defect_le_nine
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin 6 → Plane₂) {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn : ⌊Real.pi / lam⌋₊ = n) (i : Fin 6) :
    rowDefect n lam (directionRow o e c i) ≤ 9 := by
  have hs := directionRow_sorted o e c i
  have hmem : ∀ x ∈ directionRow o e c i, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have hne : directionRow o e c i ≠ [] := by
    apply List.length_pos_iff.mp
    rw [directionRow_length]
    norm_num
  have h := rowDefect_le_two_length_sub_one hlam hs hmem hne hn
  simpa only [directionRow_length] using h

/-- A defect-three row has support at most three. Zero support is possible
only in strip `n = 3`; otherwise the support is positive. -/
theorem rowDefect_eq_three_support {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    {l : List ℝ} (hdef : rowDefect n lam l = 3) :
    rowBig lam l ≤ 3 ∧ (rowBig lam l = 0 → n = 3) := by
  constructor
  · unfold rowDefect at hdef
    omega
  · intro hzero
    have hcells := rowCells_eq_zero_of_rowBig_eq_zero lam hlam hzero
    simp [rowDefect, hzero, hcells] at hdef
    exact hdef

/-- In a full-cell row, the total length of all inactive (`< λ`) gaps is
at most the strip remainder `β = π − nλ`. This applies, in particular,
to the existing Type II defect-two classification. -/
theorem rowInactiveLength_le_stripRemainder {lam : ℝ} (hlam : 0 < lam)
    {n : ℕ} {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (hne : l ≠ [])
    (hcells : rowCells lam l = n) :
    (∑ j : Fin l.length,
      if gapAfter l j < lam then gapAfter l j else 0) ≤
      Real.pi - (n : ℝ) * lam := by
  classical
  have hn := gapAfter_nonneg hs hmem hne
  have hres : ∀ j : Fin l.length,
      (if gapAfter l j < lam then gapAfter l j else 0) ≤
      lam * (gapAfter l j / lam - (⌊gapAfter l j / lam⌋₊ : ℝ)) := by
    intro j
    by_cases hj : gapAfter l j < lam
    · rw [ite_eq_left hj]
      have hf : ⌊gapAfter l j / lam⌋₊ = 0 :=
        Nat.floor_eq_zero.mpr ((div_lt_one hlam).mpr hj)
      rw [hf, Nat.cast_zero, sub_zero, mul_div_cancel₀ _ hlam.ne']
    · rw [ite_eq_right hj]
      exact mul_nonneg hlam.le
        (sub_nonneg.mpr (Nat.floor_le (div_nonneg (hn j) hlam.le)))
  calc
    _ ≤ ∑ j : Fin l.length,
        lam * (gapAfter l j / lam - (⌊gapAfter l j / lam⌋₊ : ℝ)) :=
      Finset.sum_le_sum (fun j _ => hres j)
    _ = lam * rowResidual lam l := by rw [rowResidual, Finset.mul_sum]
    _ = Real.pi - (n : ℝ) * lam := by
      rw [rowResidual_eq_ratio_sub_cells hlam hs hne, hcells, mul_sub,
        mul_div_cancel₀ _ hlam.ne', mul_comm lam]

/-- The six-point arithmetic bounds, including the exact strip bound. -/
theorem directionRow_defect_bounds
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin 6 → Plane₂) {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn : ⌊Real.pi / lam⌋₊ = n) (i : Fin 6) :
    rowDefect n lam (directionRow o e c i) ≤ n ∧
      rowDefect n lam (directionRow o e c i) ≤ 9 := by
  constructor
  · apply rowDefect_le lam hlam n
    exact rowCells_directionRow_le_of_floor_eq o e c hlam i (by omega) hn
  · exact directionRow_defect_le_nine o e c hlam hn i

/-- The full support/cell classification at defect three, including the
zero-support case in the third strip. -/
theorem rowDefect_three_support_cells {lam : ℝ} (hlam : 0 < lam)
    {n : ℕ} (hn3 : 3 ≤ n) {l : List ℝ} (hcells : rowCells lam l ≤ n)
    (hdef : rowDefect n lam l = 3) :
    (rowBig lam l = 0 ∧ n = 3 ∧ rowCells lam l = 0) ∨
      (rowBig lam l = 1 ∧ rowCells lam l = n - 2) ∨
      (rowBig lam l = 2 ∧ rowCells lam l = n - 1) ∨
      (rowBig lam l = 3 ∧ rowCells lam l = n) := by
  have hb := (rowDefect_eq_three_support hlam hdef).1
  have hd := hdef
  unfold rowDefect at hd
  interval_cases heq : rowBig lam l
  · have hc0 := rowCells_eq_zero_of_rowBig_eq_zero lam hlam heq
    exact Or.inl ⟨rfl, by omega, hc0⟩
  · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))

/-- The exact floor-remainder identity for an actual configuration row. -/
theorem directionRow_residual_identity {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (hs2 : 2 ≤ s) {lam : ℝ} (hlam : 0 < lam)
    (hn : ⌊Real.pi / lam⌋₊ = n) (i : Fin s) :
    rowResidual lam (directionRow o e c i) =
      (rowDefect n lam (directionRow o e c i) : ℝ) -
      (rowBig lam (directionRow o e c i) : ℝ) +
      (Real.pi / lam - (n : ℝ)) := by
  apply rowResidual_identity hlam (directionRow_sorted o e c i)
    (fun x hx => directionRow_mem_Ico o e c hx) _ hn
  apply List.length_pos_iff.mp
  rw [directionRow_length]
  omega

/-- The Type II inactive-gap bound for actual directions, obtained from
the genuine row defect and support rather than an abstract signature. -/
theorem directionRow_typeII_inactiveLength_le {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (hs2 : 2 ≤ s) {lam : ℝ} (hlam : 0 < lam)
    (hn : ⌊Real.pi / lam⌋₊ = n) (i : Fin s)
    (hdef : rowDefect n lam (directionRow o e c i) = 2)
    (hbig : rowBig lam (directionRow o e c i) = 2) :
    (∑ j : Fin (directionRow o e c i).length,
      if gapAfter (directionRow o e c i) j < lam then
        gapAfter (directionRow o e c i) j else 0) ≤
      Real.pi - (n : ℝ) * lam := by
  have hcl := rowCells_directionRow_le_of_floor_eq o e c hlam i hs2 hn
  have hc : rowCells lam (directionRow o e c i) = n := by
    unfold rowDefect at hdef
    omega
  apply rowInactiveLength_le_stripRemainder hlam
    (directionRow_sorted o e c i) (fun x hx => directionRow_mem_Ico o e c hx) _ hc
  apply List.length_pos_iff.mp
  rw [directionRow_length]
  omega

#print axioms rowResidual_identity
#print axioms rowFloorLoss_lt_length
#print axioms rowDefect_le_two_length_sub_one
#print axioms directionRow_defect_le_nine
#print axioms rowDefect_eq_three_support
#print axioms rowInactiveLength_le_stripRemainder
#print axioms directionRow_defect_bounds
#print axioms rowDefect_three_support_cells
#print axioms directionRow_residual_identity
#print axioms directionRow_typeII_inactiveLength_le

end Jsp404
