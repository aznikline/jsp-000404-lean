import Jsp000404.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Generalized plane configurations of points (Sendov §2)

A *generalized configuration* (GC) is a plane configuration of points together
with a laminar family of circles: every point is the center of a primitive
circle, every non-primitive circle contains ≥ 2 subcircles, circumferences are
disjoint or nested, and no three circle centers are collinear.

We model a GC as an inductive tree. The leaves (`prim`) are the points; each
internal `node` is a circle. *Range* counts depth from the roots (range 1 =
outermost circles).

The separating circle `o(p; q)` of two points is the circle of the lowest
range containing `p` but not `q`; the generalized direction `GD p q` is the
direction of the vector `o(p;q) → o(q;p)`; the generalized angle `GA p q r`
is the angle between `GD q p` and `GD q r`.
-/

open scoped EuclideanGeometry

/-- The Euclidean plane. -/
abbrev Plane₂ := EuclideanSpace ℝ (Fin 2)

namespace Jsp404

/-- A generalized circle: `prim p` is a primitive circle at point `p`;
`node c r children` is a circle centered at `c` of radius `r` containing
`children` as immediate subcircles. -/
inductive GC where
  | prim (p : Plane₂) : GC
  | node (c : Plane₂) (r : ℝ) (children : List GC) : GC

namespace GC

/-- The center of a circle: a primitive circle is centered at its point. -/
def centerOf : GC → Plane₂
  | prim p => p
  | node c _ _ => c

/-- The points (primitive circle centers) of a GC. -/
def points : GC → List Plane₂
  | prim p => [p]
  | node _ _ ch => ch.flatMap points

/-- All circle centers of a GC. -/
def centers : GC → List Plane₂
  | prim p => [p]
  | node c _ ch => c :: ch.flatMap centers

/-- Descend `p`'s circle chain inside `g` (which contains `p`); return the
center of the outermost circle containing `p` but not `q`. Requires
`p ∈ g.points`. -/
noncomputable def sepWithin (p q : Plane₂) (g : GC) : Plane₂ :=
  match g with
  | .prim c => c
  | .node c _ ch =>
    match h : ch.find? (fun g' => p ∈ g'.points) with
    | none => c
    | some child => if q ∈ child.points then sepWithin p q child else child.centerOf
  termination_by g
  decreasing_by
    have hsz : sizeOf child < sizeOf ch :=
      List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some h)
    rw [GC.node.sizeOf_spec]
    omega

end GC

/-- A *generalized configuration* is a list of ≥ 2 range-1 circles. -/
structure GCfg where
  forest : List GC
  forest_len : 2 ≤ forest.length

namespace GCfg

/-- The points of a configuration. -/
def points (V : GCfg) : List Plane₂ := V.forest.flatMap GC.points

/-- All centers of a configuration. -/
def centers (V : GCfg) : List Plane₂ := V.forest.flatMap GC.centers

/-- The separating center `o(p; q)`: center of the outermost circle containing
`p` but not `q`. Defaults to `p` when `p` is not a point of `V`. -/
noncomputable def sepCenter (V : GCfg) (p q : Plane₂) : Plane₂ :=
  match V.forest.find? (fun g => p ∈ g.points) with
  | none => p
  | some g =>
    if q ∈ g.points then g.sepWithin p q else g.centerOf

/-- The generalized direction vector `o(q;p) - o(p;q)` of `p → q`. -/
noncomputable def GD (V : GCfg) (p q : Plane₂) : Plane₂ :=
  V.sepCenter q p - V.sepCenter p q

/-- The generalized angle `GA(p,q,r)`: angle between `GD q p` and `GD q r`. -/
noncomputable def GA (V : GCfg) (p q r : Plane₂) : ℝ :=
  InnerProductGeometry.angle (V.GD q p) (V.GD q r)

/-- The maximal generalized angle of a configuration, as a fold over triples. -/
noncomputable def maxGA (V : GCfg) : ℝ :=
  (V.points.flatMap fun a =>
    V.points.flatMap fun b =>
      V.points.map fun c => (a, b, c)).foldl
    (fun m t => max m (GA V t.1 t.2.1 t.2.2)) 0

/-- The *trivial GC* of a finite point list: every point a range-1 primitive
circle. Generalized directions and angles coincide with the ordinary ones. -/
def trivial (pts : List Plane₂) (h : 2 ≤ pts.length) : GCfg :=
  ⟨pts.map GC.prim, by simpa using h⟩

@[simp] lemma trivial_points (pts : List Plane₂) (h : 2 ≤ pts.length) :
    (trivial pts h).points = pts := by
  simp [points, trivial, GC.points, List.flatMap_map]

lemma trivial_find (p : Plane₂) (pts : List Plane₂) (hp : p ∈ pts) :
    (pts.map GC.prim).find? (fun g => p ∈ g.points) = some (GC.prim p) := by
  induction pts with
  | nil => simp at hp
  | cons a as ih =>
    rw [List.map_cons]
    by_cases hpa : p = a
    · subst hpa
      rw [List.find?_cons_of_pos (by simp [GC.points])]
    · rw [List.find?_cons_of_neg (by simp [GC.points]; exact hpa)]
      exact ih (List.mem_cons.mp hp |>.resolve_left hpa)

lemma trivial_sepCenter (pts : List Plane₂) (h : 2 ≤ pts.length)
    (p q : Plane₂) (hp : p ∈ pts) (hne : p ≠ q) :
    (trivial pts h).sepCenter p q = p := by
  rw [show (trivial pts h).sepCenter p q =
      (match (pts.map GC.prim).find? (fun g => p ∈ g.points) with
      | none => p
      | some g => if q ∈ g.points then GC.sepWithin p q g else g.centerOf) from rfl]
  rw [trivial_find p pts hp]
  show (if q ∈ (GC.prim p).points then GC.sepWithin p q (GC.prim p)
        else (GC.prim p).centerOf) = p
  simp [GC.points, GC.centerOf, hne.symm]

end GCfg

end Jsp404
