import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A fractional row span bounds the integer count carried by its gap lower bounds. -/
set_option pp.fullNames true

namespace Jsp404.SixExactFloorKernel

theorem active_count_le_defect
    (n c s0 s1 s2 s3 s4 u0 u1 u2 u3 u4 : ℕ)
    (delta g0 g1 g2 g3 g4 : ℝ)
    (hscore : s0 + (s1 + (s2 + (s3 + s4))) + c = n)
    (hspan : g0 + g1 + g2 + g3 + g4 = (n : ℝ) + delta)
    (hg0 : (s0 : ℝ) + (u0 : ℝ) ≤ g0)
    (hg1 : (s1 : ℝ) + (u1 : ℝ) ≤ g1)
    (hg2 : (s2 : ℝ) + (u2 : ℝ) ≤ g2)
    (hg3 : (s3 : ℝ) + (u3 : ℝ) ≤ g3)
    (hg4 : (s4 : ℝ) + (u4 : ℝ) ≤ g4)
    (hdelta : delta < 1) :
    u0 + (u1 + (u2 + (u3 + u4))) ≤ c := by
  have hs : (s0 : ℝ) + ((s1 : ℝ) + ((s2 : ℝ) + ((s3 : ℝ) + (s4 : ℝ)))) +
      (c : ℝ) = (n : ℝ) := by
    exact_mod_cast hscore
  have hu : (u0 : ℝ) + ((u1 : ℝ) + ((u2 : ℝ) + ((u3 : ℝ) + (u4 : ℝ)))) <
      (c : ℝ) + 1 := by
    linarith only [hscore, hs, hspan, hg0, hg1, hg2, hg3, hg4, hdelta]
  have hlt : u0 + (u1 + (u2 + (u3 + u4))) < c + 1 := by
    exact_mod_cast hu
  exact Nat.lt_succ_iff.mp hlt

#print axioms active_count_le_defect

end Jsp404.SixExactFloorKernel
