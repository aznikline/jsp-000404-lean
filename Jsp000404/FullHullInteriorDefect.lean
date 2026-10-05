import Jsp000404.InteriorRowDefect
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.LocallyConvex.Separation

set_option autoImplicit false

/-! The full actual hull consequence of the interior row bound.
Finite-point separation connects the hull of all other original centers
to the extreme points of the entire original convex hull, not a subset hull.
-/

open scoped EuclideanGeometry

namespace Jsp404.FullHullInteriorDefect

/-- Separating the finite others' hull exposes q in the full original hull.
Injectivity is unnecessary in this geometric bridge. -/
theorem isHullVertex_of_not_mem_hull_others {s : ℕ}
    (c : Fin s → Plane₂) (q : Fin s)
    (hnot : c q ∉ convexHull ℝ (c '' ({q} : Set (Fin s))ᶜ)) :
    IsHullVertex c q := by
  classical
  let other : Set Plane₂ := c '' ({q} : Set (Fin s))ᶜ
  have hfinite : other.Finite := (Set.toFinite (({q} : Set (Fin s))ᶜ)).image c
  have hclosed : IsClosed (convexHull ℝ other) := hfinite.isClosed_convexHull ℝ
  obtain ⟨f, u, hfu, hufq⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ other) hclosed (by simpa only [other] using hnot)
  let T : Set Plane₂ := {x | f x ≤ f (c q) ∧ (f (c q) ≤ f x → x = c q)}
  have hT : Convex ℝ T := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb hab
    change f x ≤ f (c q) ∧ (f (c q) ≤ f x → x = c q) at hx
    change f y ≤ f (c q) ∧ (f (c q) ≤ f y → y = c q) at hy
    rcases hx with ⟨hxle, hxeq⟩
    rcases hy with ⟨hyle, hyeq⟩
    change f (a • x + b • y) ≤ f (c q) ∧
      (f (c q) ≤ f (a • x + b • y) → a • x + b • y = c q)
    have hcombo : f (a • x + b • y) = a * f x + b * f y := by
      simp only [f.map_add, f.map_smul, smul_eq_mul]
    have hrhs : a * f (c q) + b * f (c q) = f (c q) := by
      rw [← add_mul, hab, one_mul]
    have hle : a * f x + b * f y ≤ f (c q) := by
      calc
        a * f x + b * f y ≤ a * f (c q) + b * f (c q) :=
          add_le_add (mul_le_mul_of_nonneg_left hxle ha.le)
            (mul_le_mul_of_nonneg_left hyle hb.le)
        _ = f (c q) := hrhs
    refine ⟨by simpa only [hcombo] using hle, ?_⟩
    intro hge
    rw [hcombo] at hge
    have hxge : f (c q) ≤ f x := by
      by_contra hh
      have hxf : f x < f (c q) := lt_of_not_ge hh
      have hlt : a * f x + b * f y < f (c q) := by
        calc
          a * f x + b * f y < a * f (c q) + b * f (c q) :=
            add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxf ha)
              (mul_le_mul_of_nonneg_left hyle hb.le)
          _ = f (c q) := hrhs
      exact (not_lt_of_ge hge) hlt
    have hyge : f (c q) ≤ f y := by
      by_contra hh
      have hyf : f y < f (c q) := lt_of_not_ge hh
      have hlt : a * f x + b * f y < f (c q) := by
        calc
          a * f x + b * f y < a * f (c q) + b * f (c q) :=
            add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hxle ha.le)
              (mul_lt_mul_of_pos_left hyf hb)
          _ = f (c q) := hrhs
      exact (not_lt_of_ge hge) hlt
    rw [hxeq hxge, hyeq hyge, ← add_smul, hab, one_smul]
  have hrange : Set.range c ⊆ T := by
    rintro y ⟨i, rfl⟩
    change f (c i) ≤ f (c q) ∧ (f (c q) ≤ f (c i) → c i = c q)
    by_cases hi : i = q
    · subst i
      exact ⟨le_rfl, fun _ => rfl⟩
    · have hiother : c i ∈ other := ⟨i, by simpa using hi, rfl⟩
      have hlt : f (c i) < f (c q) :=
        (hfu (c i) (subset_convexHull ℝ other hiother)).trans hufq
      exact ⟨hlt.le, fun hh => False.elim ((not_le_of_gt hlt) hh)⟩
  have hfull : convexHull ℝ (Set.range c) ⊆ T := convexHull_min hrange hT
  have hqex : c q ∈ (convexHull ℝ (Set.range c)).exposedPoints ℝ := by
    refine exposed_point_def.mpr ⟨?_, f, ?_⟩
    · exact subset_convexHull ℝ _ (Set.mem_range_self q)
    · intro y hy
      exact hfull hy
  exact exposedPoints_subset_extremePoints hqex

/-- A nonvertex of the full actual hull has original row defect at least 3. -/
theorem rowDefect_ge_three_of_not_hull_vertex {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) (q : Fin s) (hnot : ¬ IsHullVertex c q) :
    3 ≤ rowDefect n lam (directionRow o e c q) := by
  have hmem : c q ∈ convexHull ℝ (c '' ({q} : Set (Fin s))ᶜ) := by
    by_contra hno
    exact hnot (isHullVertex_of_not_mem_hull_others c q hno)
  exact InteriorRowDefect.rowDefect_ge_three_of_mem_hull_others o e he hleg hn q hmem

/-- All original high-weight centers of defect at most two lie on the
full actual hull. No analogous statement is made for larger defects. -/
theorem low_defect_is_full_hull_vertex {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) (q : Fin s)
    (hsmall : rowDefect n lam (directionRow o e c q) ≤ 2) : IsHullVertex c q := by
  by_contra hnot
  have h := rowDefect_ge_three_of_not_hull_vertex o e he hleg hn q hnot
  omega

#print axioms isHullVertex_of_not_mem_hull_others
#print axioms rowDefect_ge_three_of_not_hull_vertex
#print axioms low_defect_is_full_hull_vertex

end Jsp404.FullHullInteriorDefect
