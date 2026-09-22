import Jsp000404.Deletion

/-!
# Three-gap arithmetic for two saturated anchors

These are proved components of the four-point argument recorded in
`notes/TWO_SATURATED_RESEARCH.md`.  This file does not assert the full
two-saturated-center theorem: the same-side / nesting argument and the
identification and restriction of actual direction rows are not yet connected.
-/

namespace Jsp404

open scoped EuclideanGeometry

private theorem three_floor_sum_le {lam x y z : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = Real.pi) :
    Nat.floor (x / lam) + Nat.floor (y / lam) + Nat.floor (z / lam) ≤ n := by
  rw [← hn]
  apply Nat.le_floor
  push_cast
  have hfx := Nat.floor_le (div_nonneg hx hlam.le)
  have hfy := Nat.floor_le (div_nonneg hy hlam.le)
  have hfz := Nat.floor_le (div_nonneg hz hlam.le)
  have hs : x / lam + y / lam + z / lam = Real.pi / lam := by
    rw [← add_div, ← add_div, hsum]
  linarith

/-- Three projective gaps, each at least `lam`, lose three full cells.
The conclusion also proves `3 ≤ n`, without a separate strip assumption. -/
theorem three_gapScore_add_three_le_of_ge {lam x y z : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hx : lam ≤ x) (hy : lam ≤ y) (hz : lam ≤ z)
    (hsum : x + y + z = Real.pi) :
    gapScore lam x + gapScore lam y + gapScore lam z + 3 ≤ n := by
  have hX : 1 ≤ Nat.floor (x / lam) := Nat.le_floor (by
    rw [Nat.cast_one, le_div_iff₀ hlam]; simpa using hx)
  have hY : 1 ≤ Nat.floor (y / lam) := Nat.le_floor (by
    rw [Nat.cast_one, le_div_iff₀ hlam]; simpa using hy)
  have hZ : 1 ≤ Nat.floor (z / lam) := Nat.le_floor (by
    rw [Nat.cast_one, le_div_iff₀ hlam]; simpa using hz)
  have ht := three_floor_sum_le hlam hn
    (hlam.le.trans hx) (hlam.le.trans hy) (hlam.le.trans hz) hsum
  unfold gapScore
  omega

/-- The outer point in a nested four-point configuration can have a small
gap.  The two pair-sum lower bounds still force the loss of three cells.
All relevant lower bounds are closed, including the boundary `z = lam`. -/
theorem three_gapScore_add_three_le_of_outer {lam x y z : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n) (hn3 : 3 ≤ n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : lam ≤ z) (hz2 : z < 2 * lam)
    (hxz : 2 * lam ≤ x + z) (hyz : 2 * lam ≤ y + z)
    (hsum : x + y + z = Real.pi) :
    gapScore lam x + gapScore lam y + gapScore lam z + 3 ≤ n := by
  have hZ : Nat.floor (z / lam) = 1 := by
    have hZl : 1 ≤ Nat.floor (z / lam) := Nat.le_floor (by
      rw [Nat.cast_one, le_div_iff₀ hlam]; simpa using hz)
    have hZu : Nat.floor (z / lam) < 2 := by
      apply (Nat.floor_lt (div_nonneg (hlam.le.trans hz) hlam.le)).mpr
      rw [Nat.cast_ofNat, div_lt_iff₀ hlam]
      exact hz2
    omega
  have hX2 : Nat.floor (x / lam) + 2 ≤ n := by
    rw [← hn]
    apply Nat.le_floor
    push_cast
    rw [le_div_iff₀ hlam]
    have hf := Nat.floor_le (div_nonneg hx hlam.le)
    rw [le_div_iff₀ hlam] at hf
    nlinarith
  have hY2 : Nat.floor (y / lam) + 2 ≤ n := by
    rw [← hn]
    apply Nat.le_floor
    push_cast
    rw [le_div_iff₀ hlam]
    have hf := Nat.floor_le (div_nonneg hy hlam.le)
    rw [le_div_iff₀ hlam] at hf
    nlinarith
  have ht := three_floor_sum_le hlam hn hx hy (hlam.le.trans hz) hsum
  unfold gapScore
  omega

/-- If a ray through the interior point continues to the opposite side of
a triangle, the three angles surrounding that point sum to `2*pi`.
The hypotheses are actual betweenness relations in the Euclidean plane. -/
theorem angle_sum_eq_two_pi_of_nested {A B C D E : Plane₂}
    (hE : Sbtw ℝ A E B) (hC : Sbtw ℝ D C E) :
    ∠ A C B + ∠ A C D + ∠ B C D = 2 * Real.pi := by
  have hsplit : ∠ A C E + ∠ E C B = ∠ A C B :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hE
  have hA := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi A
    hC.angle₁₂₃_eq_pi
  have hB := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi B
    hC.angle₁₂₃_eq_pi
  rw [EuclideanGeometry.angle_comm E C B] at hsplit
  linarith

/-- At an interior point of a triangle, the supplements of its three
surrounding angles have score at most `n-3` under the legal angle cap.
The full direction-row theorem additionally needs their identification as
the three cyclic projective gaps. -/
theorem inner_supplement_gapScore_add_three_le {A B C D E : Plane₂}
    {lam : ℝ} {n : ℕ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hE : Sbtw ℝ A E B) (hC : Sbtw ℝ D C E)
    (hAB : ∠ A C B ≤ Real.pi - lam)
    (hAD : ∠ A C D ≤ Real.pi - lam)
    (hBD : ∠ B C D ≤ Real.pi - lam) :
    gapScore lam (Real.pi - ∠ A C B) +
      gapScore lam (Real.pi - ∠ A C D) +
      gapScore lam (Real.pi - ∠ B C D) + 3 ≤ n := by
  apply three_gapScore_add_three_le_of_ge hlam hn
  · linarith
  · linarith
  · linarith
  · have hs := angle_sum_eq_two_pi_of_nested hE hC
    linarith

/-- The outer member of an explicitly nested pair also loses three cells.
Only the anchor angles of `ABD` need be less than `lam`; the three legal
angle bounds at the inner point supply the remaining inequalities.
This is an actual Euclidean statement, with no abstract angle-sum premise. -/
theorem outer_nested_gapScore_add_three_le {A B C D E : Plane₂}
    {lam : ℝ} {n : ℕ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hE : Sbtw ℝ A E B) (hC : Sbtw ℝ D C E)
    (hAD : A ≠ D) (hBD : B ≠ D)
    (hA : ∠ B A D < lam) (hB : ∠ A B D < lam)
    (hCAB : ∠ A C B ≤ Real.pi - lam)
    (hCAD : ∠ A C D ≤ Real.pi - lam)
    (hCBD : ∠ B C D ≤ Real.pi - lam) :
    gapScore lam (∠ A D C) + gapScore lam (∠ C D B) +
      gapScore lam (∠ B A D + ∠ A B D) + 3 ≤ n := by
  have hsplitA : ∠ B A C + ∠ C A D = ∠ B A D := by
    have h := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := A) hC
    rw [hE.angle_eq_right C, hE.angle_eq_right D] at h
    rw [EuclideanGeometry.angle_comm D A C,
      EuclideanGeometry.angle_comm C A B,
      EuclideanGeometry.angle_comm D A B] at h
    linarith
  have hsplitB : ∠ A B C + ∠ C B D = ∠ A B D := by
    have h := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := B) hC
    rw [hE.symm.angle_eq_right C, hE.symm.angle_eq_right D] at h
    rw [EuclideanGeometry.angle_comm D B C,
      EuclideanGeometry.angle_comm C B A,
      EuclideanGeometry.angle_comm D B A] at h
    linarith
  have hsplitD : ∠ A D C + ∠ C D B = ∠ A D B := by
    rw [hC.angle_eq_right A, hC.angle_eq_left B]
    exact EuclideanGeometry.angle_add_angle_eq_of_sbtw hE
  have hABC := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := A) (p₂ := B) C hE.left_ne_right.symm
  rw [EuclideanGeometry.angle_comm B C A,
    EuclideanGeometry.angle_comm C A B] at hABC
  have hbase : lam ≤ ∠ B A C + ∠ A B C := by linarith
  have hACD := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := A) (p₂ := D) C hAD.symm
  rw [EuclideanGeometry.angle_comm D C A] at hACD
  have hBCD := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := B) (p₂ := D) C hBD.symm
  rw [EuclideanGeometry.angle_comm B D C,
    EuclideanGeometry.angle_comm D C B] at hBCD
  have hABD := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := A) (p₂ := B) D hE.left_ne_right.symm
  rw [EuclideanGeometry.angle_comm B D A,
    EuclideanGeometry.angle_comm D A B] at hABD
  have hAmono : ∠ B A C ≤ ∠ B A D := by
    linarith [EuclideanGeometry.angle_nonneg C A D]
  have hBmono : ∠ A B C ≤ ∠ A B D := by
    linarith [EuclideanGeometry.angle_nonneg C B D]
  have hi := inner_supplement_gapScore_add_three_le hlam hn hE hC hCAB hCAD hCBD
  apply three_gapScore_add_three_le_of_outer hlam hn (by omega)
    (EuclideanGeometry.angle_nonneg A D C) (EuclideanGeometry.angle_nonneg C D B)
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

end Jsp404

#print axioms Jsp404.three_gapScore_add_three_le_of_ge
#print axioms Jsp404.three_gapScore_add_three_le_of_outer
#print axioms Jsp404.angle_sum_eq_two_pi_of_nested
#print axioms Jsp404.inner_supplement_gapScore_add_three_le
#print axioms Jsp404.outer_nested_gapScore_add_three_le
