import Jsp000404.IntervalPacking

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- Two gaps with zero merge gain are not both `≥ λ`. -/
theorem not_both_big_of_mergeGain_zero {lam x y : ℝ} (hlam : 0 < lam)
    (h : mergeGain lam x y = 0) : ¬ (lam ≤ x ∧ lam ≤ y) := by
  rintro ⟨hx, hy⟩
  have := mergeGain_pos_of_ge hlam hx hy
  omega

theorem sortedLE_three {a b d : ℝ} (h1 : a ≤ b) (h2 : b ≤ d) :
    [a, b, d].SortedLE := by
  refine List.Pairwise.sortedLE (List.pairwise_cons.mpr ⟨fun x hx => ?_,
    List.pairwise_cons.mpr ⟨fun x hx => ?_, List.pairwise_singleton _ _⟩⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl := hx <;> linarith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact h2

theorem sortedLE_four {a b d f : ℝ} (h1 : a ≤ b) (h2 : b ≤ d) (h3 : d ≤ f) :
    [a, b, d, f].SortedLE := by
  refine List.Pairwise.sortedLE (List.pairwise_cons.mpr ⟨fun x hx => ?_,
    (sortedLE_three h2 h3).pairwise⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain rfl | rfl | rfl := hx <;> linarith

/-- Splitting the first gap: `[θ, x, y]` vs `[θ, z, x, y]`. -/
theorem linScore_split_low {lam θ x y z R : ℝ} (hlam : 0 < lam)
    (hθz : θ ≤ z) (hzx : z ≤ x) :
    linearGapScore lam θ R [x, y] =
      linearGapScore lam θ R [z, x, y] + mergeGain lam (z - θ) (x - z) := by
  have hspec := mergeGain_spec hlam (sub_nonneg.mpr hθz) (sub_nonneg.mpr hzx)
  rw [show z - θ + (x - z) = x - θ by ring] at hspec
  simp only [linearGapScore]
  omega

/-- Splitting the middle gap: `[θ, x, y]` vs `[θ, x, z, y]`. -/
theorem linScore_split_mid {lam θ x y z R : ℝ} (hlam : 0 < lam)
    (hxz : x ≤ z) (hzy : z ≤ y) :
    linearGapScore lam θ R [x, y] =
      linearGapScore lam θ R [x, z, y] + mergeGain lam (z - x) (y - z) := by
  have hspec := mergeGain_spec hlam (sub_nonneg.mpr hxz) (sub_nonneg.mpr hzy)
  rw [show z - x + (y - z) = y - x by ring] at hspec
  simp only [linearGapScore]
  omega

/-- Splitting the last gap: `[θ, x, y]` vs `[θ, x, y, z]`. -/
theorem linScore_split_high {lam θ x y z R : ℝ} (hlam : 0 < lam)
    (hyz : y ≤ z) (hzR : z ≤ R) :
    linearGapScore lam θ R [x, y] =
      linearGapScore lam θ R [x, y, z] + mergeGain lam (z - y) (R - z) := by
  have hspec := mergeGain_spec hlam (sub_nonneg.mpr hyz) (sub_nonneg.mpr hzR)
  rw [show z - y + (R - z) = R - y by ring] at hspec
  simp only [linearGapScore]
  omega

/-- A merge gain of `2` forces both pieces `≥ λ` and a floor carry. -/
theorem mergeGain_eq_two {lam x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : mergeGain lam x y = 2) :
    lam ≤ x ∧ lam ≤ y ∧
      ⌊(x + y) / lam⌋₊ = ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 1 := by
  have hspec := mergeGain_spec hlam hx hy
  have hx' : 0 ≤ x / lam := div_nonneg hx hlam.le
  have hy' : 0 ≤ y / lam := div_nonneg hy hlam.le
  have hxy' : 0 ≤ (x + y) / lam := div_nonneg (add_nonneg hx hy) hlam.le
  have hdiv : (x + y) / lam = x / lam + y / lam := add_div x y lam
  have h1 : ⌊x / lam⌋₊ + ⌊y / lam⌋₊ ≤ ⌊(x + y) / lam⌋₊ := by
    rcases Nat.eq_zero_or_pos (⌊x / lam⌋₊ + ⌊y / lam⌋₊) with hh | hh
    · omega
    · rw [Nat.le_floor_iff' (Nat.ne_of_gt hh), hdiv]
      push_cast
      exact add_le_add (Nat.floor_le hx') (Nat.floor_le hy')
  have h2 : ⌊(x + y) / lam⌋₊ ≤ ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 1 := by
    have h3 : ⌊(x + y) / lam⌋₊ < ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 2 := by
      rw [Nat.floor_lt hxy', hdiv]
      push_cast
      linarith [Nat.lt_floor_add_one (x / lam), Nat.lt_floor_add_one (y / lam)]
    omega
  unfold mergeGain gapScore at h
  have hax : 1 ≤ ⌊x / lam⌋₊ := by omega
  have hay : 1 ≤ ⌊y / lam⌋₊ := by omega
  refine ⟨?_, ?_, by omega⟩
  · have := (Nat.le_floor_iff' one_ne_zero).mp hax
    rw [le_div_iff₀ hlam] at this; simpa using this
  · have := (Nat.le_floor_iff' one_ne_zero).mp hay
    rw [le_div_iff₀ hlam] at this; simpa using this


end Jsp404
