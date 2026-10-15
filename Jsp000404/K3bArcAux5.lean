import Jsp000404.K3bArcAux3
import Jsp000404.K3bArcAux4

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- Four-term cyclic chain: with `x2, x3, x4` in that order on the
forward arc from `x1`, the four consecutive arcs telescope to `π`.
This is the model's `order` datum for a 4-gap fan. -/
theorem cyclicDiff_chain4 {x1 x2 x3 x4 : ℝ}
    (h1 : x1 ∈ Set.Ico 0 Real.pi) (h2 : x2 ∈ Set.Ico 0 Real.pi)
    (h3 : x3 ∈ Set.Ico 0 Real.pi) (h4 : x4 ∈ Set.Ico 0 Real.pi)
    (h23 : cyclicDiff x1 x2 ≤ cyclicDiff x1 x3)
    (h34 : cyclicDiff x1 x3 ≤ cyclicDiff x1 x4)
    (h14 : 0 < cyclicDiff x1 x4) :
    cyclicDiff x1 x2 + cyclicDiff x2 x3 + cyclicDiff x3 x4 +
      cyclicDiff x4 x1 = Real.pi := by
  have e1 := cyclicDiff_eq_add_of_le h1 h2 h3 h23
  have e2 := cyclicDiff_eq_add_of_le h1 h3 h4 h34
  have hne : x1 ≠ x4 := by
    intro he
    rw [he, show cyclicDiff x4 x4 = 0 from if_pos rfl] at h14
    exact lt_irrefl _ h14
  have e3 := cyclicDiff_add_rev hne
  linarith



end Jsp404
