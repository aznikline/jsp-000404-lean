import Jsp000404.Deletion

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- The two complementary arcs between distinct points sum to `π`. -/
theorem cyclicDiff_add_rev {a b : ℝ} (h : a ≠ b) :
    cyclicDiff a b + cyclicDiff b a = Real.pi := by
  unfold cyclicDiff
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [if_neg h, if_pos hlt, if_neg h.symm,
      if_neg (not_lt.mpr hlt.le)]
    linarith [Real.pi_pos]
  · rw [if_neg h, if_neg (not_lt.mpr hgt.le), if_neg h.symm,
      if_pos hgt]
    linarith [Real.pi_pos]


end Jsp404
