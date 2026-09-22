import Jsp000404.Base3
import Jsp000404.GeometricDeletion
import Mathlib.Geometry.Euclidean.Triangle

/-!
# The `s = 3` bridge: legality → `Base3CellData` → potential bound

This is the induction anchor of the Section-4 deletion argument.

* `linRep_oangle_eq_angle_or_pi_sub`: the projective sweep
  `linRep (oangle (j - i) (k - i))` between the two direction
  representatives at center `i` equals the unoriented triangle angle
  `∠ j i k` or its complement `π - ∠`.
* `rowScore_eq_gapScore_arcs`: at `s = 3` a direction row has exactly
  two gaps — the triangle angle and its complement — so the exponent is
  `gapScore ∠ + gapScore (π - ∠)`.
* `base3CellData`: `ext i = ⌊(π - ∠ᵢ)/λ⌋₊` (the exterior cell count) and
  `k i = rowScore` satisfy the four `Base3CellData` fields from
  `Section4Legality` alone.
* `base3_potential_le` / `base3_potential_le_big`: the potential bounds
  `2^n` (low `δ`) and `5·2^{n-2} = 2^n + 2^{n-2}` (uniform).
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- **Arc ↔ angle.** The projective sweep between the direction
representatives of `i → j` and `i → k` equals the unoriented triangle
angle `∠ j i k` or its complement. -/
lemma linRep_oangle_eq_angle_or_pi_sub {s : ℕ} {c : Fin s → Plane₂}
    {i j k : Fin s} (hij : c j ≠ c i) (hik : c k ≠ c i) :
    linRep (o.oangle (c j - c i) (c k - c i)) = ∠ (c j) (c i) (c k) ∨
      linRep (o.oangle (c j - c i) (c k - c i)) =
        Real.pi - ∠ (c j) (c i) (c k) := by
  have hangle : ∠ (c j) (c i) (c k) =
      |(o.oangle (c j - c i) (c k - c i)).toReal| := by
    show InnerProductGeometry.angle (c j -ᵥ c i) (c k -ᵥ c i) = _
    rw [vsub_eq_sub, vsub_eq_sub]
    exact o.angle_eq_abs_oangle_toReal
      (sub_ne_zero.mpr hij) (sub_ne_zero.mpr hik)
  unfold linRep
  split_ifs with h1 h2
  · rw [hangle]; right; rw [abs_of_neg h1]; ring
  · rw [hangle]; right; rw [h2, abs_of_pos Real.pi_pos]; ring
  · rw [hangle]; left; rw [abs_of_nonneg (le_of_not_gt h1)]

/-- `⌊x⌋₊ + ⌊y⌋₊ ≤ ⌊x + y⌋₊` for nonnegative reals. -/
lemma Nat.floor_add_floor_le_floor_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⌊x⌋₊ + ⌊y⌋₊ ≤ ⌊x + y⌋₊ := by
  rcases Nat.eq_zero_or_pos (⌊x⌋₊ + ⌊y⌋₊) with h | h
  · omega
  · rw [Nat.le_floor_iff' (Nat.ne_of_gt h)]
    push_cast
    exact add_le_add (Nat.floor_le hx) (Nat.floor_le hy)

/-- The cyclic gaps of a sorted two-element list are `b - a` and its
complement `π - (b - a)`. -/
lemma cycGaps_pair {a b : ℝ} (hab : a ≤ b) :
    cycGaps [a, b] = [b - a, Real.pi - (b - a)] := by
  have hhead : List.head [a, b] (by simp) = a := rfl
  have hlast : List.getLast [a, b] (by simp) = b := rfl
  have hwrap : wrapGap [a, b] (by simp) = Real.pi - (b - a) := by
    unfold wrapGap
    rw [hhead, hlast]
    split_ifs with h
    · have hba : b = a := h b (by simp)
      rw [hba]; ring
    · unfold cyclicDiff
      split_ifs with h1 h2
      · exfalso
        apply h
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · rfl
        · exact h1
      · exfalso; linarith
      · ring
  rw [cycGaps_eq_map_append_wrap _ (by simp)]
  have hcd : cyclicDiff a b = b - a := by
    unfold cyclicDiff
    split_ifs with h1 h2
    · linarith
    · rfl
    · exfalso; exact h2 (lt_of_le_of_ne hab h1)
  simp [hcd, hwrap]

/-- The smaller of the two indices of `Fin 3` different from `i`. -/
def other1 : Fin 3 → Fin 3 := fun i => if i = 0 then 1 else 0

/-- The larger of the two indices of `Fin 3` different from `i`. -/
def other2 : Fin 3 → Fin 3 := fun i => if i = 2 then 1 else 2

lemma other1_ne (i : Fin 3) : other1 i ≠ i := by
  fin_cases i <;> decide

lemma other2_ne (i : Fin 3) : other2 i ≠ i := by
  fin_cases i <;> decide

lemma other1_ne_other2 (i : Fin 3) : other1 i ≠ other2 i := by
  fin_cases i <;> decide

lemma erase_finRange_eq (i : Fin 3) :
    (List.finRange 3).erase i = [other1 i, other2 i] := by
  fin_cases i <;> rfl

/-- The unoriented angle of the unique triangle at center `i`. -/
noncomputable def triAng (c : Fin 3 → Plane₂) (i : Fin 3) : ℝ :=
  ∠ (c (other1 i)) (c i) (c (other2 i))

/-- Legality forces the exterior arc `π - ∠ᵢ` to contain a cell. -/
lemma lam_le_pi_sub_triAng {c : Fin 3 → Plane₂} {lam : ℝ}
    (hlegal : Section4Legality c lam) (i : Fin 3) :
    lam ≤ Real.pi - triAng c i := by
  have hle := hlegal.triAngle (other1 i) i (other2 i)
    (other1_ne i) (Ne.symm (other2_ne i)) (other1_ne_other2 i)
  have h : triAng c i ≤ Real.pi - lam := hle
  linarith

/-- Permutation form of the `s = 3` direction row. -/
lemma directionRow_perm_pair {c : Fin 3 → Plane₂} (i : Fin 3) :
    List.Perm (directionRow o e c i)
      [dirRep o e c i (other1 i), dirRep o e c i (other2 i)] := by
  unfold directionRow
  rw [erase_finRange_eq]
  exact List.perm_insertionSort _ _

/-- At `s = 3` the row score is `gapScore ∠ᵢ + gapScore (π - ∠ᵢ)`. -/
lemma rowScore_eq_gapScore_arcs {c : Fin 3 → Plane₂} {lam : ℝ}
    (hlegal : Section4Legality c lam) (he : e ≠ 0) (i : Fin 3) :
    rowScore lam (directionRow o e c i) =
      gapScore lam (triAng c i) + gapScore lam (Real.pi - triAng c i) := by
  classical
  set p1 := dirRep o e c i (other1 i) with hp1
  set p2 := dirRep o e c i (other2 i) with hp2
  have h1ne : c (other1 i) ≠ c i := fun h => other1_ne i (hlegal.inj h)
  have h2ne : c (other2 i) ≠ c i := fun h => other2_ne i (hlegal.inj h)
  have hcd : cyclicDiff p1 p2 =
      linRep (o.oangle (c (other1 i) - c i) (c (other2 i) - c i)) :=
    cyclicDiff_dirRep o e c he h1ne h2ne
  have hperm := directionRow_perm_pair (o := o) (e := e) (c := c) i
  have hsorted := directionRow_sorted o e c i
  have hA : cyclicDiff p1 p2 = triAng c i ∨
      cyclicDiff p1 p2 = Real.pi - triAng c i := by
    rw [hcd]
    exact linRep_oangle_eq_angle_or_pi_sub h1ne h2ne
  -- the row score equals `g(A) + g(π - A)` for `A = cyclicDiff p1 p2`
  have hkey : rowScore lam (directionRow o e c i) =
      gapScore lam (cyclicDiff p1 p2) +
        gapScore lam (Real.pi - cyclicDiff p1 p2) := by
    by_cases h : p1 ≤ p2
    · have hrow : directionRow o e c i = [p1, p2] := by
        exact hperm.eq_of_sortedLE hsorted
          (List.pairwise_pair.mpr h).sortedLE
      have hcd1 : cyclicDiff p1 p2 = p2 - p1 := by
        unfold cyclicDiff
        split_ifs with h1 h2
        · linarith
        · rfl
        · exfalso; exact h2 (lt_of_le_of_ne h h1)
      rw [hrow]
      unfold rowScore
      rw [cycGaps_pair h, hcd1]
      simp
    · have h2 : p2 ≤ p1 := le_of_lt (not_le.mp h)
      have hrow : directionRow o e c i = [p2, p1] := by
        exact (hperm.trans (List.Perm.swap p1 p2 []).symm).eq_of_sortedLE
          hsorted (List.pairwise_pair.mpr h2).sortedLE
      have hcd2 : cyclicDiff p1 p2 = Real.pi + p2 - p1 := by
        unfold cyclicDiff
        split_ifs with h1 h2
        · exfalso; exact h (le_of_eq h1)
        · exfalso; exact h (le_of_lt h2)
        · rfl
      rw [hrow]
      unfold rowScore
      rw [cycGaps_pair h2, hcd2]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [show Real.pi + p2 - p1 = Real.pi - (p1 - p2) from by ring,
        show Real.pi - (Real.pi - (p1 - p2)) = p1 - p2 from by ring]
      exact add_comm _ _
  rw [hkey]
  rcases hA with hA | hA
  · rw [hA]
  · rw [hA, show Real.pi - (Real.pi - triAng c i) = triAng c i from by ring]
    exact add_comm _ _

/-- **The `s = 3` cell data** extracted from a legal configuration:
`ext i = ⌊(π - ∠ᵢ)/λ⌋₊` exterior cells, `k i = rowScore`. -/
noncomputable def base3CellData {c : Fin 3 → Plane₂} {lam : ℝ}
    (hlegal : Section4Legality c lam) (he : e ≠ 0)
    {n : ℕ} (hn : Nat.floor (Real.pi / lam) = n) (hlampi : lam < Real.pi) :
    Base3CellData n (Real.pi / lam - n) where
  ext := fun i => ⌊(Real.pi - triAng c i) / lam⌋₊
  k := fun i => rowScore lam (directionRow o e c i)
  ext_pos := by
    intro i
    have hge := lam_le_pi_sub_triAng hlegal i
    change 1 ≤ ⌊(Real.pi - triAng c i) / lam⌋₊
    rw [Nat.one_le_floor_iff, one_le_div_iff]
    exact Or.inl ⟨hlegal.lam_pos, hge⟩
  top_requires_sat := by
    intro i htop
    have hk : rowScore lam (directionRow o e c i) = n - 1 := htop
    rw [rowScore_eq_gapScore_arcs hlegal he i] at hk
    unfold gapScore at hk
    have hge := lam_le_pi_sub_triAng hlegal i
    have hme_pos : 1 ≤ ⌊(Real.pi - triAng c i) / lam⌋₊ := by
      rw [Nat.one_le_floor_iff, one_le_div_iff]
      exact Or.inl ⟨hlegal.lam_pos, hge⟩
    have hsum : ⌊triAng c i / lam⌋₊ + ⌊(Real.pi - triAng c i) / lam⌋₊
        ≤ n := by
      have hma_nonneg : 0 ≤ triAng c i / lam :=
        div_nonneg (EuclideanGeometry.angle_nonneg _ _ _)
          hlegal.lam_pos.le
      have hme_nonneg : 0 ≤ (Real.pi - triAng c i) / lam :=
        div_nonneg (by linarith [hlegal.lam_pos]) hlegal.lam_pos.le
      have h := Nat.floor_add_floor_le_floor_add hma_nonneg hme_nonneg
      have hdiv : triAng c i / lam + (Real.pi - triAng c i) / lam =
          Real.pi / lam := by
        rw [← add_div]; ring
      rwa [hdiv, hn] at h
    change ⌊(Real.pi - triAng c i) / lam⌋₊ = n
    rcases Nat.eq_zero_or_pos ⌊triAng c i / lam⌋₊ with hma | hma <;> omega
  ext_budget := by
    have h1 : ∀ i : Fin 3, ((⌊(Real.pi - triAng c i) / lam⌋₊ : ℕ) : ℝ) ≤
        (Real.pi - triAng c i) / lam := by
      intro i
      apply Nat.floor_le
      apply div_nonneg _ hlegal.lam_pos.le
      have hge := lam_le_pi_sub_triAng hlegal i
      linarith [hlegal.lam_pos]
    have htri : triAng c 0 + triAng c 1 + triAng c 2 = Real.pi := by
      have h10 : c 1 ≠ c 0 := fun h => absurd (hlegal.inj h) (by decide)
      have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
        (p₁ := c 0) (p₂ := c 1) (p₃ := c 2) h10
      have ht0 : triAng c 0 = ∠ (c 1) (c 0) (c 2) := rfl
      have ht1 : triAng c 1 = ∠ (c 0) (c 1) (c 2) := rfl
      have ht2 : triAng c 2 = ∠ (c 0) (c 2) (c 1) := rfl
      rw [ht0, ht1, ht2]
      have hc1 : ∠ (c 2) (c 0) (c 1) = ∠ (c 1) (c 0) (c 2) :=
        EuclideanGeometry.angle_comm _ _ _
      have hc2 : ∠ (c 1) (c 2) (c 0) = ∠ (c 0) (c 2) (c 1) :=
        EuclideanGeometry.angle_comm _ _ _
      linarith
    have harg : ∑ i : Fin 3, (Real.pi - triAng c i) = 2 * Real.pi := by
      rw [Fin.sum_univ_three]
      linarith [htri]
    have hsum : ∑ i : Fin 3, (Real.pi - triAng c i) / lam =
        2 * ((n : ℝ) + (Real.pi / lam - n)) := by
      rw [← Finset.sum_div, harg]
      ring_nf
    change ((∑ i : Fin 3, ⌊(Real.pi - triAng c i) / lam⌋₊ : ℕ) : ℝ) ≤
      2 * ((n : ℝ) + (Real.pi / lam - n))
    push_cast
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => h1 i
  k_le := by
    intro i
    have hge := lam_le_pi_sub_triAng hlegal i
    have hsum : ⌊triAng c i / lam⌋₊ + ⌊(Real.pi - triAng c i) / lam⌋₊
        ≤ n := by
      have hma_nonneg : 0 ≤ triAng c i / lam :=
        div_nonneg (EuclideanGeometry.angle_nonneg _ _ _)
          hlegal.lam_pos.le
      have hme_nonneg : 0 ≤ (Real.pi - triAng c i) / lam :=
        div_nonneg (by linarith [hlegal.lam_pos]) hlegal.lam_pos.le
      have h := Nat.floor_add_floor_le_floor_add hma_nonneg hme_nonneg
      have hdiv : triAng c i / lam + (Real.pi - triAng c i) / lam =
          Real.pi / lam := by
        rw [← add_div]; ring
      rwa [hdiv, hn] at h
    have hn1 : 1 ≤ n := by
      have h1pi : 1 ≤ Nat.floor (Real.pi / lam) := by
        rw [Nat.one_le_floor_iff, one_le_div_iff]
        exact Or.inl ⟨hlegal.lam_pos, le_of_lt hlampi⟩
      omega
    have hk : rowScore lam (directionRow o e c i) =
        (⌊triAng c i / lam⌋₊ - 1) +
          (⌊(Real.pi - triAng c i) / lam⌋₊ - 1) := by
      rw [rowScore_eq_gapScore_arcs hlegal he i]
      unfold gapScore; rfl
    change rowScore lam (directionRow o e c i) ≤ n - 1
    rw [hk]; omega

/-- **The `s = 3` potential bound, low-`δ` branch.** -/
theorem base3_potential_le {c : Fin 3 → Plane₂} {lam : ℝ}
    (hlegal : Section4Legality c lam) (he : e ≠ 0) (hlampi : lam < Real.pi)
    {n : ℕ} (hn : Nat.floor (Real.pi / lam) = n) (hn2 : 2 ≤ n)
    (hδ : Real.pi / lam - n < 1 / 2) :
    potential lam (directionRows o e c) ≤ 2 ^ n := by
  have h := base3_low
    (base3CellData (o := o) (e := e) hlegal he hn hlampi) hn2 hδ
  unfold potential exponentAt directionRows
  exact h

/-- **The `s = 3` potential bound, uniform (high-cap) branch.**
`5·2^{n-2} = 2^n + 2^{n-2}`. -/
theorem base3_potential_le_big {c : Fin 3 → Plane₂} {lam : ℝ}
    (hlegal : Section4Legality c lam) (he : e ≠ 0) (hlampi : lam < Real.pi)
    {n : ℕ} (hn : Nat.floor (Real.pi / lam) = n) (hn2 : 2 ≤ n) :
    potential lam (directionRows o e c) ≤ 5 * 2 ^ (n - 2) := by
  have hδ : Real.pi / lam - n < 1 := by
    have hlt := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn] at hlt
    linarith
  have h := base3_high
    (base3CellData (o := o) (e := e) hlegal he hn hlampi) hn2 hδ
  unfold potential exponentAt directionRows
  exact h

end Jsp404
