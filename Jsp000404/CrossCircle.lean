import Jsp000404.GC

/-!
# Cross-circle generalized angles (Sendov Lemma 3.5 cases)

For points lying in different range-1 circles of a GC, the separating
centers collapse to the circle centers, and generalized angles reduce to
ordinary angles between centers. This is the computational content of
Lemma 3.5:

- `p, q, r` in three different circles: `GA p q r = ∠ o_p o_q o_r`
  (contributes the `A(Q)` term).
- `p', p` in circle `i`, `q` in circle `j`: `GA p' p q` is the angle
  between the internal direction `GD p p'` and the center line
  `o_i → o_j` (contributes the `π - φ` term).
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

namespace GCfg

/-- `p` lies inside range-1 circle `g` of `V`. -/
def insideCircle (V : GCfg) (g : GC) (p : Plane₂) : Prop :=
  g ∈ V.forest ∧ p ∈ g.points

/-- If the tree containing `p` found by `find?` does not contain `q`, the
separating center `o(p;q)` is that tree's center. -/
lemma sepCenter_eq_centerOf (V : GCfg) {p q : Plane₂} {g : GC}
    (hfind : V.forest.find? (fun t => p ∈ t.points) = some g)
    (hq : q ∉ g.points) :
    V.sepCenter p q = g.centerOf := by
  show (match V.forest.find? (fun t => p ∈ t.points) with
    | none => p
    | some t => if q ∈ t.points then t.sepWithin p q else t.centerOf) = g.centerOf
  rw [hfind]
  simp [hq]

lemma find?_mem_of_mem_flatMap {F : List GC} {p : Plane₂}
    (hp : p ∈ F.flatMap GC.points) :
    ∃ g ∈ F, F.find? (fun t => p ∈ t.points) = some g ∧ p ∈ g.points := by
  rw [List.mem_flatMap] at hp
  obtain ⟨g, hg, hpg⟩ := hp
  induction F with
  | nil => simp at hg
  | cons a as ih =>
    by_cases ha : p ∈ a.points
    · exact ⟨a, List.mem_cons_self,
        List.find?_cons_of_pos (decide_eq_true_iff.mpr ha), ha⟩
    · rcases List.mem_cons.mp hg with rfl | hga
      · exact absurd hpg ha
      · obtain ⟨g', hg', hfind, hpg'⟩ := ih hga
        exact ⟨g', List.mem_cons_of_mem _ hg',
          by rw [List.find?_cons_of_neg (by simpa using ha)]; exact hfind, hpg'⟩

/-- `p` occurs in some range-1 circle whenever it is a point of `V`. -/
lemma find?_isSome (V : GCfg) {p : Plane₂} (hp : p ∈ V.points) :
    ∃ g ∈ V.forest, V.forest.find? (fun t => p ∈ t.points) = some g ∧
      p ∈ g.points :=
  find?_mem_of_mem_flatMap hp

/-- Well-formedness: distinct range-1 circles have disjoint point sets. -/
def DisjointCircles (V : GCfg) : Prop :=
  ∀ g₁ ∈ V.forest, ∀ g₂ ∈ V.forest, g₁ ≠ g₂ →
    ∀ p, p ∈ g₁.points → p ∉ g₂.points

lemma not_mem_of_disjoint (V : GCfg) (hd : V.DisjointCircles)
    {g₁ g₂ : GC} {p : Plane₂}
    (h1 : g₁ ∈ V.forest) (h2 : g₂ ∈ V.forest) (hne : g₁ ≠ g₂)
    (hp : p ∈ g₂.points) : p ∉ g₁.points :=
  hd g₂ h2 g₁ h1 hne.symm p hp

/-- The generalized direction between points of different range-1 circles is
the direction between the circle centers. -/
lemma GD_cross (V : GCfg) {g₁ g₂ : GC} {p q : Plane₂}
    (hf1 : V.forest.find? (fun t => p ∈ t.points) = some g₁)
    (hf2 : V.forest.find? (fun t => q ∈ t.points) = some g₂)
    (hq1 : q ∉ g₁.points) (hp2 : p ∉ g₂.points) :
    V.GD p q = g₂.centerOf - g₁.centerOf := by
  show V.sepCenter q p - V.sepCenter p q = g₂.centerOf - g₁.centerOf
  rw [sepCenter_eq_centerOf V hf1 hq1, sepCenter_eq_centerOf V hf2 hp2]

/-- **Lemma 3.5, case 1.** Three points in three different range-1 circles:
the generalized angle equals the angle of the center triangle. -/
lemma GA_three_circles (V : GCfg) {g₁ g₂ g₃ : GC} {p q r : Plane₂}
    (hf_p : V.forest.find? (fun t => p ∈ t.points) = some g₁)
    (hf_q : V.forest.find? (fun t => q ∈ t.points) = some g₂)
    (hf_r : V.forest.find? (fun t => r ∈ t.points) = some g₃)
    (hq1 : q ∉ g₁.points) (hp2 : p ∉ g₂.points)
    (hr2 : r ∉ g₂.points) (hq3 : q ∉ g₃.points) :
    V.GA p q r = ∠ g₁.centerOf g₂.centerOf g₃.centerOf := by
  show InnerProductGeometry.angle (V.GD q p) (V.GD q r) = _
  rw [GD_cross V hf_q hf_p hp2 hq1, GD_cross V hf_q hf_r hr2 hq3]
  rfl

/-- **Lemma 3.5, case 2.** Two points in circle `i`, the vertex point in the
same circle, the third point in circle `j`: the generalized angle is the
angle between the internal direction `GD p p'` and the center line
`o_i → o_j`. -/
lemma GA_two_in_one (V : GCfg) {g₁ g₂ : GC} {p' p q : Plane₂}
    (hf_p : V.forest.find? (fun t => p ∈ t.points) = some g₁)
    (hf_q : V.forest.find? (fun t => q ∈ t.points) = some g₂)
    (hq1 : q ∉ g₁.points) (hp2 : p ∉ g₂.points) :
    V.GA p' p q = InnerProductGeometry.angle (V.GD p p')
      (g₂.centerOf - g₁.centerOf) := by
  show InnerProductGeometry.angle (V.GD p p') (V.GD p q) = _
  rw [GD_cross V hf_p hf_q hq1 hp2]

end GCfg

end Jsp404
