import Jsp000404.SixSymbolicActiveCountBound
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! A forced unit endpoint spends one of a defect-two row's support slots. -/
set_option pp.fullNames true

namespace Jsp404.SixExactFloorKernel

theorem unit_gap_score_lower (g : ℝ) (hunit : 1 ≤ g) :
    ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 1 ≤ g := by
  have hfloor : 1 ≤ ⌊g⌋₊ := Nat.le_floor (by norm_num; exact hunit)
  have hcancel : ⌊g⌋₊ - 1 + 1 = ⌊g⌋₊ := Nat.sub_add_cancel hfloor
  have hcast : ((⌊g⌋₊ - 1 : ℕ) : ℝ) + 1 = (⌊g⌋₊ : ℝ) := by
    exact_mod_cast hcancel
  rw [hcast]
  exact Nat.floor_le (by linarith only [hunit])

theorem unit_first_active_count_le_one
    (n s0 s1 s2 s3 s4 u1 u2 u3 u4 : ℕ)
    (delta g0 g1 g2 g3 g4 : ℝ)
    (hscore : s0 + (s1 + (s2 + (s3 + s4))) + 2 = n)
    (hspan : g0 + g1 + g2 + g3 + g4 = (n : ℝ) + delta)
    (hunit : (s0 : ℝ) + 1 ≤ g0)
    (hg1 : (s1 : ℝ) + (u1 : ℝ) ≤ g1)
    (hg2 : (s2 : ℝ) + (u2 : ℝ) ≤ g2)
    (hg3 : (s3 : ℝ) + (u3 : ℝ) ≤ g3)
    (hg4 : (s4 : ℝ) + (u4 : ℝ) ≤ g4)
    (hdelta : delta < 1) :
    u1 + (u2 + (u3 + u4)) ≤ 1 := by
  have hs : (s0 : ℝ) + ((s1 : ℝ) + ((s2 : ℝ) + ((s3 : ℝ) + (s4 : ℝ)))) +
      2 = (n : ℝ) := by
    exact_mod_cast hscore
  have hu : (u1 : ℝ) + ((u2 : ℝ) + ((u3 : ℝ) + (u4 : ℝ))) < 2 := by
    linarith only [hs, hspan, hunit, hg1, hg2, hg3, hg4, hdelta]
  have hlt : u1 + (u2 + (u3 + u4)) < 2 := by exact_mod_cast hu
  exact Nat.lt_succ_iff.mp hlt

theorem unit_last_active_count_le_one
    (n s0 s1 s2 s3 s4 u0 u1 u2 u3 : ℕ)
    (delta g0 g1 g2 g3 g4 : ℝ)
    (hscore : s0 + (s1 + (s2 + (s3 + s4))) + 2 = n)
    (hspan : g0 + g1 + g2 + g3 + g4 = (n : ℝ) + delta)
    (hg0 : (s0 : ℝ) + (u0 : ℝ) ≤ g0)
    (hg1 : (s1 : ℝ) + (u1 : ℝ) ≤ g1)
    (hg2 : (s2 : ℝ) + (u2 : ℝ) ≤ g2)
    (hg3 : (s3 : ℝ) + (u3 : ℝ) ≤ g3)
    (hunit : (s4 : ℝ) + 1 ≤ g4)
    (hdelta : delta < 1) :
    u0 + (u1 + (u2 + u3)) ≤ 1 := by
  have hs : (s0 : ℝ) + ((s1 : ℝ) + ((s2 : ℝ) + ((s3 : ℝ) + (s4 : ℝ)))) +
      2 = (n : ℝ) := by
    exact_mod_cast hscore
  have hu : (u0 : ℝ) + ((u1 : ℝ) + ((u2 : ℝ) + (u3 : ℝ))) < 2 := by
    linarith only [hs, hspan, hg0, hg1, hg2, hg3, hunit, hdelta]
  have hlt : u0 + (u1 + (u2 + u3)) < 2 := by exact_mod_cast hu
  exact Nat.lt_succ_iff.mp hlt

#print axioms unit_gap_score_lower
#print axioms unit_first_active_count_le_one
#print axioms unit_last_active_count_le_one

end Jsp404.SixExactFloorKernel
