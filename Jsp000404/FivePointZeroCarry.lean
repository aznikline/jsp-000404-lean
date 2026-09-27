import Jsp000404.MixedTwoInCentral

/-!
# Five-point `R = 3` — the zero-carry regime

`mixed_two_in_central` pins a mixed two-in receiver to defect `3` with the
third direction strictly outside the received directions.  In that regime
*every* relevant row has zero merge gain: the receiver row because its
defect `3 = c⁻ + μ` forces `μ = 0`, and the three defect-`2` source rows
by deletion rigidity (`five_point_merge_zero_{first,mid,last}`).

`mergeGain = 0` is more than "not both gaps big": when one merged gap is
already `≥ λ`, zero gain is exactly the *no-carry* condition
`x + (y − ⌊y/λ⌋·λ) < λ` — the small gap plus the big gap's remainder stays
in a single `λ`-cell.  This file exposes that remainder inequality in the
`q + r` vocabulary the rest of the development uses (`geomSkeleton`'s
`r x g = gapAfter g / λ − q g`), so that zero-gain constraints can be
summed across rows sharing chords.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- **No-carry characterization.**  Merging a small gap `x < λ` with a big
gap `y ≥ λ`: with `b = ⌊y/λ⌋`, `⌊x/λ⌋ = 0` and
`⌊(x+y)/λ⌋ = ⌊x/λ + (y/λ − b)⌋ + b`, so the merge gain is exactly the
carry bit `⌊x/λ + (y/λ − b)⌋`.  It vanishes iff the small gap plus the
big gap's `λ`-remainder stays below `λ`. -/
theorem mergeGain_eq_zero_iff_frac {lam x y : ℝ} (hlam : 0 < lam)
    (hx0 : 0 ≤ x) (hxl : x < lam) (hy : lam ≤ y) :
    mergeGain lam x y = 0 ↔ x + (y - (⌊y / lam⌋₊ : ℝ) * lam) < lam := by
  have hy0 : 0 ≤ y := hlam.le.trans hy
  have ha : ⌊x / lam⌋₊ = 0 := by
    rw [Nat.floor_eq_zero, div_lt_one hlam]
    exact hxl
  have hb : 1 ≤ ⌊y / lam⌋₊ := by
    rw [Nat.le_floor_iff' one_ne_zero, le_div_iff₀ hlam]
    simpa using hy
  set b : ℕ := ⌊y / lam⌋₊
  have hfrac0 : (0 : ℝ) ≤ y / lam - (b : ℝ) :=
    sub_nonneg.mpr (Nat.floor_le (div_nonneg hy0 hlam.le))
  have hsum : (x + y) / lam = x / lam + (y / lam - (b : ℝ)) + (b : ℝ) := by
    rw [add_div]
    ring
  have hcf : ⌊(x + y) / lam⌋₊ = ⌊x / lam + (y / lam - (b : ℝ))⌋₊ + b := by
    rw [hsum]
    exact Nat.floor_add_natCast (add_nonneg (div_nonneg hx0 hlam.le) hfrac0) b
  have hspec := mergeGain_spec hlam hx0 hy0
  unfold gapScore at hspec
  rw [hcf, ha] at hspec
  have hμ : mergeGain lam x y = ⌊x / lam + (y / lam - (b : ℝ))⌋₊ := by omega
  rw [hμ, Nat.floor_eq_zero]
  have hρmul : (x / lam + (y / lam - (b : ℝ))) * lam =
      x + (y - (b : ℝ) * lam) := by
    have hne : lam ≠ 0 := ne_of_gt hlam
    rw [add_mul, sub_mul, div_mul_cancel₀ x hne, div_mul_cancel₀ y hne]
  constructor
  · intro hρ1
    have hmul := mul_lt_mul_of_pos_right hρ1 hlam
    rw [hρmul, one_mul] at hmul
    linarith
  · intro h
    have hρlt : (x / lam + (y / lam - (b : ℝ))) * lam < 1 * lam := by linarith
    exact lt_of_mul_lt_mul_right hρlt hlam.le

/-- Packaged form used by the five-point analysis: a zero merge gain with
a big merged gap forces the complementary small gap plus the remainder
under `λ`. -/
theorem mergeGain_eq_zero_frac_lt {lam x y : ℝ} (hlam : 0 < lam)
    (hx0 : 0 ≤ x) (hxl : x < lam) (hy : lam ≤ y)
    (h0 : mergeGain lam x y = 0) :
    x + (y - (⌊y / lam⌋₊ : ℝ) * lam) < lam :=
  (mergeGain_eq_zero_iff_frac hlam hx0 hxl hy).mp h0

/-- Symmetric form with the big gap first. -/
theorem mergeGain_eq_zero_iff_frac' {lam x y : ℝ} (hlam : 0 < lam)
    (hx : lam ≤ x) (hy0 : 0 ≤ y) (hyl : y < lam) :
    mergeGain lam x y = 0 ↔ y + (x - (⌊x / lam⌋₊ : ℝ) * lam) < lam := by
  have hswap : mergeGain lam x y = mergeGain lam y x := by
    unfold mergeGain
    rw [add_comm x y]
    omega
  rw [hswap]
  exact mergeGain_eq_zero_iff_frac hlam hy0 hyl hx

/-- Symmetric consequence with the big gap first. -/
theorem mergeGain_eq_zero_frac_lt' {lam x y : ℝ} (hlam : 0 < lam)
    (hx : lam ≤ x) (hy0 : 0 ≤ y) (hyl : y < lam)
    (h0 : mergeGain lam x y = 0) :
    y + (x - (⌊x / lam⌋₊ : ℝ) * lam) < lam :=
  (mergeGain_eq_zero_iff_frac' hlam hx hy0 hyl).mp h0

end Jsp404
