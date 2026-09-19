import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped EuclideanGeometry
open Real

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Jsp404

/-- A finite plane configuration of N points in general position (no three collinear). -/
structure PlaneConfig (N : ℕ) where
  pt : Fin N → Plane
  gp : ∀ i j k : Fin N, i ≠ j → j ≠ k → i ≠ k →
    ¬ Collinear ℝ ({pt i, pt j, pt k} : Set Plane)

/-- Max angle over all ordered triples, vertex in the middle. -/
noncomputable def maxAngle {N : ℕ} (A : PlaneConfig N) : ℝ :=
  ⨆ (t : Fin N × Fin N × Fin N), ∠ (A.pt t.1) (A.pt t.2.1) (A.pt t.2.2)

end Jsp404
