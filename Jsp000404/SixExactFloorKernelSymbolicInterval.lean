import Jsp000404.SixExactFloorKernelPrimitives

/-! A complete positive-score floor interval with a natural minimum indicator.
The indicator is computed from the actual score; it is not a model field. -/
namespace Jsp404.SixExactFloorKernel

theorem score_gap_min_interval (g : ℝ) (hzero : 0 ≤ g) :
    ((⌊g⌋₊ - 1 : ℕ) : ℝ) + ((min (⌊g⌋₊ - 1) 1 : ℕ) : ℝ) ≤ g ∧
      g < ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 2 := by
  rcases score_gap_dichotomy g hzero with ⟨hz, hu⟩ | ⟨hp, hl, hu⟩
  · simpa only [hz, Nat.zero_min, Nat.cast_zero, zero_add] using And.intro hzero hu
  · have hm : min (⌊g⌋₊ - 1) 1 = 1 := Nat.min_eq_right hp
    simpa only [hm, Nat.cast_one] using And.intro hl hu

#print axioms score_gap_min_interval
end Jsp404.SixExactFloorKernel
