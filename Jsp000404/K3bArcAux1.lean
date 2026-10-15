import Jsp000404.GeometricDeletion

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- Complement branch of the projective correspondence: a clockwise
sweep (`oangle.toReal < 0`) means the forward arc is `π − ∠uiv`. -/
theorem dirRep_arc_eq_pi_sub_angle {s : ℕ} {c : Fin s → Plane₂}
    (he : e ≠ 0) {i u v : Fin s}
    (hcu : c u ≠ c i) (hcv : c v ≠ c i)
    (hcw : (o.oangle (c u - c i) (c v - c i)).toReal < 0) :
    ∠ (c u) (c i) (c v) =
      Real.pi - cyclicDiff (dirRep o e c i u) (dirRep o e c i v) := by
  have hangle : ∠ (c u) (c i) (c v) =
      |(o.oangle (c u - c i) (c v - c i)).toReal| := by
    show InnerProductGeometry.angle (c u -ᵥ c i) (c v -ᵥ c i) = _
    rw [vsub_eq_sub, vsub_eq_sub]
    exact o.angle_eq_abs_oangle_toReal
      (sub_ne_zero.mpr hcu) (sub_ne_zero.mpr hcv)
  have hrep : linRep (o.oangle (c u - c i) (c v - c i)) =
      Real.pi - ∠ (c u) (c i) (c v) := by
    unfold linRep
    rw [if_pos hcw, hangle, abs_of_neg hcw]
    ring
  rw [cyclicDiff_dirRep o e c he hcu hcv, hrep]
  ring


end Jsp404
