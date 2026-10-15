import Jsp000404.R3WitnessMidBottom

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section R3Dag

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}
  (C : SatChart o e n lam c v theta)
include C

/-- **Five-point `R = 3` closure.**  A `SatChart` on `s = 4` cannot have
one row of defect `≥ 3` with the other three rows of defect `2`: sorting
the four non-anchor rows by `theta`, whichever pair of defect-`2` rows
straddles the high row is killed by `pairkill_{outer,midtop,midbot}`. -/
theorem five_point_R3_impossible (h : Fin 4)
    (hdh : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h)))
    (hd : ∀ i : Fin 4, i ≠ h →
      rowDefect n lam (directionRow o e c (v.succAbove i)) = 2) : False := by
  classical
  have hθne : ∀ {i j : Fin 4}, i ≠ j → theta i ≠ theta j := by
    intro i j hij
    rcases up_or_up C hij with h1 | h1
    · exact ne_of_lt (up_theta_lt C hij h1)
    · exact (ne_of_lt (up_theta_lt C hij.symm h1)).symm
  fin_cases h
  · -- h = 0
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 2 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 2 (by decide)) (hd 1 (by decide))

  · -- h = 1
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 2 (by decide)) (hd 0 (by decide))

  · -- h = 2
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 3 (by decide)) (hd 1 (by decide))

  · -- h = 3
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 2 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 2 (by decide)) (hd 1 (by decide))

/-- **Five-point `R = 4` closure.**  A `SatChart` on `s = 4` cannot have
all four non-anchor rows of defect `2`: after sorting by `theta`, the
middle two defect-`2` rows have the extreme rows on opposite sides, and
`pairkill_outer` kills the configuration. -/
theorem five_point_R4_impossible
    (hd : ∀ i : Fin 4,
      rowDefect n lam (directionRow o e c (v.succAbove i)) = 2) : False := by
  classical
  have hθne : ∀ {i j : Fin 4}, i ≠ j → theta i ≠ theta j := by
    intro i j hij
    rcases up_or_up C hij with h1 | h1
    · exact ne_of_lt (up_theta_lt C hij h1)
    · exact (ne_of_lt (up_theta_lt C hij.symm h1)).symm
  rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
  rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
  rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
  rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
  rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
  rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c12 c23 (hd 1) (hd 2)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c13 c23 (hd 1) (hd 3)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c13 c12 (hd 3) (hd 1)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c12 c13 (hd 2) (hd 1)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c23 c13 (hd 2) (hd 3)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c23 c12 (hd 3) (hd 2)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c01 c12 (hd 0) (hd 1)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c02 c12 (hd 0) (hd 2)
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c01 c13 (hd 0) (hd 1)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c03 c13 (hd 0) (hd 3)
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c03 c01 (hd 3) (hd 0)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c02 c01 (hd 2) (hd 0)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c02 c23 (hd 0) (hd 2)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c03 c23 (hd 0) (hd 3)
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c03 c02 (hd 3) (hd 0)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c01 c02 (hd 1) (hd 0)
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c02 c03 (hd 2) (hd 0)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c01 c03 (hd 1) (hd 0)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c23 c03 (hd 2) (hd 3)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c23 c02 (hd 3) (hd 2)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c12 c02 (hd 1) (hd 2)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c13 c03 (hd 1) (hd 3)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c13 c01 (hd 3) (hd 1)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c12 c01 (hd 2) (hd 1)

/-- **Five-point `R ≥ 3` closure.**  On a five-point `SatChart`, at most
two non-anchor rows can have defect `2` when all remaining rows have
defect `≥ 3`: `T.card = 3` dispatches to `five_point_R3_impossible`,
`T.card = 4` to `five_point_R4_impossible`. -/
theorem five_point_R_ge_three_impossible (T : Finset (Fin 4))
    (hdef : ∀ i ∈ T, rowDefect n lam
      (directionRow o e c (v.succAbove i)) = 2)
    (hrest : ∀ i : Fin 4, i ∉ T → 3 ≤ rowDefect n lam
      (directionRow o e c (v.succAbove i)))
    (hT : 3 ≤ T.card) : False := by
  classical
  have hcard : T.card = 3 ∨ T.card = 4 := by
    have hle := T.card_le_univ
    rw [Fintype.card_fin] at hle
    omega
  rcases hcard with h3 | h4
  · have hcompl : (Finset.univ \ T).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ T),
        Finset.card_univ, Fintype.card_fin, h3]
    obtain ⟨h, hh⟩ := Finset.card_eq_one.mp hcompl
    have hnot : h ∉ T := by
      have : h ∈ Finset.univ \ T := by
        rw [hh]; exact Finset.mem_singleton_self h
      exact (Finset.mem_sdiff.mp this).2
    have hsub : ∀ i : Fin 4, i ≠ h → i ∈ T := by
      intro i hi2
      by_contra hi
      have hss : ({i, h} : Finset (Fin 4)) ⊆ Finset.univ \ T := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hi⟩
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hnot⟩
      have hcle := Finset.card_le_card hss
      rw [hcompl, Finset.card_pair hi2] at hcle
      omega
    exact five_point_R3_impossible C h (hrest h hnot)
      (fun i hi => hdef i (hsub i hi))
  · have hTuniv : T = Finset.univ :=
      Finset.eq_univ_of_card T (by rw [h4, Fintype.card_fin])
    exact five_point_R4_impossible C
      (fun i => hdef i (hTuniv ▸ Finset.mem_univ i))


end R3Dag

end Jsp404
