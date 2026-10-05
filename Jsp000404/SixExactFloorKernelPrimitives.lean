import Jsp000404.SmallScoreGapBounds

/-! Exact natural positive scores are the bounded integer variables used by
the finite certificate exporter.  Zero-score gaps retain both floor 0 and 1;
positive scores have the exact half-open floor interval. -/

namespace Jsp404.SixExactFloorKernel

theorem zero_score_gap (g : ℝ) (hzero : 0 ≤ g) (hs : ⌊g⌋₊ - 1 = 0) : g < 2 := by
  have hq : ⌊g⌋₊ < 2 := by omega
  exact (Nat.floor_lt hzero).mp hq

theorem positive_score_gap (g : ℝ) (hzero : 0 ≤ g) (hs : 0 < ⌊g⌋₊ - 1) :
    ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 1 ≤ g ∧ g < ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 2 := by
  have hq : 2 ≤ ⌊g⌋₊ := by omega
  have he : ⌊g⌋₊ = (⌊g⌋₊ - 1) + 1 := by omega
  have heR : (⌊g⌋₊ : ℝ) = ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast he
  have hlow := Nat.floor_le hzero
  have hhigh := Nat.lt_floor_add_one g
  constructor <;> linarith

theorem score_gap_dichotomy (g : ℝ) (hzero : 0 ≤ g) :
    (⌊g⌋₊ - 1 = 0 ∧ g < 2) ∨
    (1 ≤ ⌊g⌋₊ - 1 ∧ ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 1 ≤ g ∧
      g < ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 2) := by
  by_cases hs : ⌊g⌋₊ - 1 = 0
  · exact Or.inl ⟨hs, zero_score_gap g hzero hs⟩
  · have hp : 0 < ⌊g⌋₊ - 1 := by omega
    exact Or.inr ⟨by omega, positive_score_gap g hzero hp⟩

#print axioms zero_score_gap
#print axioms positive_score_gap
#print axioms score_gap_dichotomy

end Jsp404.SixExactFloorKernel
