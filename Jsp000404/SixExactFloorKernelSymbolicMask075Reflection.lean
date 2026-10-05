import Jsp000404.SixExactFloorKernelSymbolicMask075Probe
import Jsp000404.SixModelReflection

/-! Actual ModelSix reflection transport. No original-point realization is assumed. -/
namespace Jsp404.SixExactFloorKernel
theorem symbolic_mask960_probe {n : ℕ} (M : SixModelCompression.ModelSix n)
    (hn4 : 4 ≤ n) (hhigh : (1/2 : ℝ) ≤ M.delta)
    (hdef0 : SixModelCompression.rowDefect M 0 = 2)
    (hdef1 : SixModelCompression.rowDefect M 1 = 3)
    (hdef3 : SixModelCompression.rowDefect M 3 = 3)
    (hdef4 : SixModelCompression.rowDefect M 4 = 2)
    (htri012 : M.d 0 1 + 1 ≤ M.d 1 2 ∧ M.d 0 1 < M.d 0 2 ∧ M.d 0 2 < M.d 1 2)
    (htri013 : M.d 0 1 + 1 ≤ M.d 1 3 ∧ M.d 0 1 < M.d 0 3 ∧ M.d 0 3 < M.d 1 3)
    (htri014 : M.d 0 1 + 1 ≤ M.d 1 4 ∧ M.d 0 1 < M.d 0 4 ∧ M.d 0 4 < M.d 1 4)
    (htri023 : M.d 0 2 + 1 ≤ M.d 2 3 ∧ M.d 0 2 < M.d 0 3 ∧ M.d 0 3 < M.d 2 3)
    (htri024 : M.d 0 2 + 1 ≤ M.d 2 4 ∧ M.d 0 2 < M.d 0 4 ∧ M.d 0 4 < M.d 2 4)
    (htri034 : M.d 0 3 + 1 ≤ M.d 3 4 ∧ M.d 0 3 < M.d 0 4 ∧ M.d 0 4 < M.d 3 4)
    (htri123 : M.d 2 3 + 1 ≤ M.d 1 2 ∧ M.d 2 3 < M.d 1 3 ∧ M.d 1 3 < M.d 1 2)
    (htri124 : M.d 2 4 + 1 ≤ M.d 1 2 ∧ M.d 2 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 2)
    (htri134 : M.d 3 4 + 1 ≤ M.d 1 3 ∧ M.d 3 4 < M.d 1 4 ∧ M.d 1 4 < M.d 1 3)
    (htri234 : M.d 3 4 + 1 ≤ M.d 2 3 ∧ M.d 3 4 < M.d 2 4 ∧ M.d 2 4 < M.d 2 3)
    : False := by
  let R := SixModelReflection.reflectedModel M
  have hhighR : (1/2 : ℝ) ≤ R.delta := hhigh
  have hdefR0 : SixModelCompression.rowDefect R 0 = 2 := by
    change SixModelCompression.rowDefect (SixModelReflection.reflectedModel M) 0 = 2
    rw [SixModelReflection.reflectedModel_rowDefect]
    change SixModelCompression.rowDefect M 4 = 2
    exact hdef4
  have hdefR1 : SixModelCompression.rowDefect R 1 = 3 := by
    change SixModelCompression.rowDefect (SixModelReflection.reflectedModel M) 1 = 3
    rw [SixModelReflection.reflectedModel_rowDefect]
    change SixModelCompression.rowDefect M 3 = 3
    exact hdef3
  have hdefR3 : SixModelCompression.rowDefect R 3 = 3 := by
    change SixModelCompression.rowDefect (SixModelReflection.reflectedModel M) 3 = 3
    rw [SixModelReflection.reflectedModel_rowDefect]
    change SixModelCompression.rowDefect M 1 = 3
    exact hdef1
  have hdefR4 : SixModelCompression.rowDefect R 4 = 2 := by
    change SixModelCompression.rowDefect (SixModelReflection.reflectedModel M) 4 = 2
    rw [SixModelReflection.reflectedModel_rowDefect]
    change SixModelCompression.rowDefect M 0 = 2
    exact hdef0
  have hs10 : M.d 1 0 = M.d 0 1 := M.symm 1 0 (by decide)
  have hs20 : M.d 2 0 = M.d 0 2 := M.symm 2 0 (by decide)
  have hs21 : M.d 2 1 = M.d 1 2 := M.symm 2 1 (by decide)
  have hs30 : M.d 3 0 = M.d 0 3 := M.symm 3 0 (by decide)
  have hs31 : M.d 3 1 = M.d 1 3 := M.symm 3 1 (by decide)
  have hs32 : M.d 3 2 = M.d 2 3 := M.symm 3 2 (by decide)
  have hs40 : M.d 4 0 = M.d 0 4 := M.symm 4 0 (by decide)
  have hs41 : M.d 4 1 = M.d 1 4 := M.symm 4 1 (by decide)
  have hs42 : M.d 4 2 = M.d 2 4 := M.symm 4 2 (by decide)
  have hs43 : M.d 4 3 = M.d 3 4 := M.symm 4 3 (by decide)
  have hr012 : R.d 1 2 + 1 ≤ R.d 0 1 ∧ R.d 1 2 < R.d 0 2 ∧ R.d 0 2 < R.d 0 1 := by
    change ((n : ℝ) + 2 * M.delta - M.d 3 2) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 4 3) ∧ ((n : ℝ) + 2 * M.delta - M.d 3 2) < ((n : ℝ) + 2 * M.delta - M.d 4 2) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 2) < ((n : ℝ) + 2 * M.delta - M.d 4 3)
    simp only [hs43, hs42, hs32]
    obtain ⟨ha, hb, hc⟩ := htri234
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr013 : R.d 1 3 + 1 ≤ R.d 0 1 ∧ R.d 1 3 < R.d 0 3 ∧ R.d 0 3 < R.d 0 1 := by
    change ((n : ℝ) + 2 * M.delta - M.d 3 1) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 4 3) ∧ ((n : ℝ) + 2 * M.delta - M.d 3 1) < ((n : ℝ) + 2 * M.delta - M.d 4 1) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 1) < ((n : ℝ) + 2 * M.delta - M.d 4 3)
    simp only [hs43, hs41, hs31]
    obtain ⟨ha, hb, hc⟩ := htri134
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr014 : R.d 0 1 + 1 ≤ R.d 1 4 ∧ R.d 0 1 < R.d 0 4 ∧ R.d 0 4 < R.d 1 4 := by
    change ((n : ℝ) + 2 * M.delta - M.d 4 3) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 3 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 3) < ((n : ℝ) + 2 * M.delta - M.d 4 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 0) < ((n : ℝ) + 2 * M.delta - M.d 3 0)
    simp only [hs43, hs40, hs30]
    obtain ⟨ha, hb, hc⟩ := htri034
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr023 : R.d 2 3 + 1 ≤ R.d 0 2 ∧ R.d 2 3 < R.d 0 3 ∧ R.d 0 3 < R.d 0 2 := by
    change ((n : ℝ) + 2 * M.delta - M.d 2 1) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 4 2) ∧ ((n : ℝ) + 2 * M.delta - M.d 2 1) < ((n : ℝ) + 2 * M.delta - M.d 4 1) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 1) < ((n : ℝ) + 2 * M.delta - M.d 4 2)
    simp only [hs42, hs41, hs21]
    obtain ⟨ha, hb, hc⟩ := htri124
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr024 : R.d 0 2 + 1 ≤ R.d 2 4 ∧ R.d 0 2 < R.d 0 4 ∧ R.d 0 4 < R.d 2 4 := by
    change ((n : ℝ) + 2 * M.delta - M.d 4 2) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 2 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 2) < ((n : ℝ) + 2 * M.delta - M.d 4 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 0) < ((n : ℝ) + 2 * M.delta - M.d 2 0)
    simp only [hs42, hs40, hs20]
    obtain ⟨ha, hb, hc⟩ := htri024
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr034 : R.d 0 3 + 1 ≤ R.d 3 4 ∧ R.d 0 3 < R.d 0 4 ∧ R.d 0 4 < R.d 3 4 := by
    change ((n : ℝ) + 2 * M.delta - M.d 4 1) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 1 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 1) < ((n : ℝ) + 2 * M.delta - M.d 4 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 4 0) < ((n : ℝ) + 2 * M.delta - M.d 1 0)
    simp only [hs41, hs40, hs10]
    obtain ⟨ha, hb, hc⟩ := htri014
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr123 : R.d 2 3 + 1 ≤ R.d 1 2 ∧ R.d 2 3 < R.d 1 3 ∧ R.d 1 3 < R.d 1 2 := by
    change ((n : ℝ) + 2 * M.delta - M.d 2 1) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 3 2) ∧ ((n : ℝ) + 2 * M.delta - M.d 2 1) < ((n : ℝ) + 2 * M.delta - M.d 3 1) ∧ ((n : ℝ) + 2 * M.delta - M.d 3 1) < ((n : ℝ) + 2 * M.delta - M.d 3 2)
    simp only [hs32, hs31, hs21]
    obtain ⟨ha, hb, hc⟩ := htri123
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr124 : R.d 1 2 + 1 ≤ R.d 2 4 ∧ R.d 1 2 < R.d 1 4 ∧ R.d 1 4 < R.d 2 4 := by
    change ((n : ℝ) + 2 * M.delta - M.d 3 2) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 2 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 3 2) < ((n : ℝ) + 2 * M.delta - M.d 3 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 3 0) < ((n : ℝ) + 2 * M.delta - M.d 2 0)
    simp only [hs32, hs30, hs20]
    obtain ⟨ha, hb, hc⟩ := htri023
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr134 : R.d 1 3 + 1 ≤ R.d 3 4 ∧ R.d 1 3 < R.d 1 4 ∧ R.d 1 4 < R.d 3 4 := by
    change ((n : ℝ) + 2 * M.delta - M.d 3 1) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 1 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 3 1) < ((n : ℝ) + 2 * M.delta - M.d 3 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 3 0) < ((n : ℝ) + 2 * M.delta - M.d 1 0)
    simp only [hs31, hs30, hs10]
    obtain ⟨ha, hb, hc⟩ := htri013
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  have hr234 : R.d 2 3 + 1 ≤ R.d 3 4 ∧ R.d 2 3 < R.d 2 4 ∧ R.d 2 4 < R.d 3 4 := by
    change ((n : ℝ) + 2 * M.delta - M.d 2 1) + 1 ≤ ((n : ℝ) + 2 * M.delta - M.d 1 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 2 1) < ((n : ℝ) + 2 * M.delta - M.d 2 0) ∧ ((n : ℝ) + 2 * M.delta - M.d 2 0) < ((n : ℝ) + 2 * M.delta - M.d 1 0)
    simp only [hs21, hs20, hs10]
    obtain ⟨ha, hb, hc⟩ := htri012
    constructor <;> try constructor
    all_goals linarith only [ha, hb, hc]
  exact symbolic_mask75_probe R hn4 hhighR hdefR0 hdefR1 hdefR3 hdefR4 hr012 hr013 hr014 hr023 hr024 hr034 hr123 hr124 hr134 hr234

#print axioms symbolic_mask960_probe
end Jsp404.SixExactFloorKernel
