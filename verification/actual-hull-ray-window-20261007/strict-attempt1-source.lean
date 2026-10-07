import Jsp000404.FullHullInteriorDefect
import Jsp000404.ConeCorridor
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

/-!
Physical ray windows at a vertex of the full original convex hull.

The endpoint directions are actual original centers. The supporting normal
and the angular chart are produced internally from the full-hull hypothesis;
the caller supplies only original Section-4 legality and hull membership.
-/

open scoped EuclideanGeometry EuclideanSpace RealInnerProductSpace

namespace Jsp404.ActualHullRayWindow

/-- An injectively indexed full-hull vertex is outside the convex hull of
all other original centers. No subset hull replaces the full hull here. -/
theorem not_mem_hull_others_of_isHullVertex {s : ℕ}
    {c : Fin s → Plane₂} {p : Fin s}
    (hinj : Function.Injective c) (hp : IsHullVertex c p) :
    c p ∉ convexHull ℝ (c '' ({p} : Set (Fin s))ᶜ) := by
  classical
  let A : Set Plane₂ := convexHull ℝ (Set.range c)
  have hext : c p ∈ A.extremePoints ℝ := hp
  have hp' : c p ∈ A \ convexHull ℝ (A \ {c p}) :=
    (convex_convexHull ℝ (Set.range c)).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp
      hext
  have hsub : c '' ({p} : Set (Fin s))ᶜ ⊆ A \ {c p} := by
    rintro x ⟨i, hi, rfl⟩
    refine ⟨subset_convexHull ℝ (Set.range c) (Set.mem_range_self i), ?_⟩
    have hip : i ≠ p := by simpa using hi
    intro h
    exact hip (hinj (Set.mem_singleton_iff.mp h))
  exact fun hmem => hp'.2 ((convexHull_mono hsub) hmem)

/-- A strict inward supporting normal is produced from the full original
hull vertex. The only cardinality premise ensures that another center exists. -/
theorem exists_strict_supporting_normal {s : ℕ} (hs : 2 ≤ s)
    {c : Fin s → Plane₂} {p : Fin s}
    (hinj : Function.Injective c) (hp : IsHullVertex c p) :
    ∃ u : Plane₂, u ≠ 0 ∧ ∀ j, j ≠ p → 0 < ⟪u, c j - c p⟫ := by
  classical
  let other : Set Plane₂ := c '' ({p} : Set (Fin s))ᶜ
  have hnot : c p ∉ convexHull ℝ other := by
    simpa only [other] using not_mem_hull_others_of_isHullVertex hinj hp
  have hfinite : other.Finite := (Set.toFinite (({p} : Set (Fin s))ᶜ)).image c
  have hclosed : IsClosed (convexHull ℝ other) := hfinite.isClosed_convexHull ℝ
  obtain ⟨f, a, hfa, hafp⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ other) hclosed hnot
  let u : Plane₂ := (InnerProductSpace.toDual ℝ Plane₂).symm (-f)
  have hueval (x : Plane₂) : ⟪u, x⟫ = -f x := by
    simpa only [u, neg_apply] using
      (InnerProductSpace.toDual_symm_apply (x := x) (y := -f))
  have hsupport (j : Fin s) (hj : j ≠ p) : 0 < ⟪u, c j - c p⟫ := by
    have hjother : c j ∈ other := ⟨j, by simpa using hj, rfl⟩
    have hlt : f (c j) < f (c p) :=
      (hfa (c j) (subset_convexHull ℝ other hjother)).trans hafp
    rw [hueval, map_sub]
    linarith
  haveI : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr hs
  obtain ⟨j, hj⟩ := exists_ne p
  have hu : u ≠ 0 := by
    intro h
    have hpositive := hsupport j hj
    simpa only [h, inner_zero_left, lt_self_iff_false] using hpositive
  exact ⟨u, hu, hsupport⟩

/-- The real principal angle of a ray in a strict supporting half-plane is
strictly between `-pi/2` and `pi/2`. -/
private theorem signed_chart_of_inner_pos
    (o : Orientation ℝ Plane₂ (Fin 2)) {e u : Plane₂}
    (he : e ≠ 0) (hu : u ≠ 0) (hinner : 0 < ⟪e, u⟫) :
    (o.oangle e u).toReal ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hangle : InnerProductGeometry.angle e u < Real.pi / 2 := by
    by_contra h
    have hnonpos : ⟪e, u⟫ ≤ 0 :=
      InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr (le_of_not_gt h)
    exact (not_le_of_gt hinner) hnonpos
  rw [o.angle_eq_abs_oangle_toReal he hu] at hangle
  exact abs_lt.mp hangle

/-- Signed coordinates in one strict half-plane do not cross the principal
angle cut when taking a difference. -/
private theorem angle_eq_abs_sub_of_signed_chart
    (o : Orientation ℝ Plane₂ (Fin 2)) {e u v : Plane₂}
    (he : e ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) {a b : ℝ}
    (ha : a ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hua : o.oangle e u = (a : Real.Angle))
    (hvb : o.oangle e v = (b : Real.Angle)) :
    InnerProductGeometry.angle u v = |b - a| := by
  rw [o.angle_eq_abs_oangle_toReal hu hv,
    ← o.oangle_sub_left he hu hv, hua, hvb, ← Real.Angle.coe_sub]
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩]

/-- An actual physical window. Both boundary rays are actual original
indices different from the center, and its base is the left boundary ray.
Coordinates are only constrained on the other original indices. -/
structure Window {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (c : Fin s → Plane₂) (lam : ℝ) (p : Fin s) where
  left : Fin s
  right : Fin s
  left_ne_center : left ≠ p
  right_ne_center : right ≠ p
  boundary_distinct : left ≠ right
  base : Plane₂
  base_eq_left : base = c left - c p
  base_ne_zero : base ≠ 0
  width : ℝ
  width_pos : 0 < width
  width_lt_pi : width < Real.pi
  width_eq_actual_angle : width = ∠ (c left) (c p) (c right)
  width_le_legality : width ≤ Real.pi - lam
  theta : Fin s → ℝ
  theta_mem : ∀ j, j ≠ p → theta j ∈ Set.Icc 0 width
  actual_direction : ∀ j, j ≠ p → o.oangle base (c j - c p) = (theta j : Real.Angle)
  left_coordinate : theta left = 0
  right_coordinate : theta right = width

/-- Finite extrema turn a strict supporting half-plane into actual endpoint
rays. This helper is used below only with the internally produced support. -/
private theorem exists_window_of_strict_support {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 3 ≤ s)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (e : Plane₂) (he : e ≠ 0)
    (hsupport : ∀ j, j ≠ p → 0 < ⟪e, c j - c p⟫) :
    Nonempty (Window o c lam p) := by
  classical
  let other : Finset (Fin s) := Finset.univ.erase p
  have hother (j : Fin s) : j ∈ other ↔ j ≠ p := by simp [other]
  obtain ⟨j₀, hj₀, _⟩ := Fin.exists_ne_and_ne_of_two_lt p p (by omega)
  have hnonempty : other.Nonempty := ⟨j₀, (hother j₀).mpr hj₀⟩
  have hray (j : Fin s) (hj : j ≠ p) : c j - c p ≠ 0 :=
    sub_ne_zero.mpr (hleg.inj.ne hj)
  let t : Fin s → ℝ := fun j => (o.oangle e (c j - c p)).toReal
  have ht (j : Fin s) (hj : j ≠ p) :
      t j ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    signed_chart_of_inner_pos o he (hray j hj) (hsupport j hj)
  have hchart (j : Fin s) : o.oangle e (c j - c p) = (t j : Real.Angle) := by
    simp only [t, Real.Angle.coe_toReal]
  have hangle (a b : Fin s) (ha : a ≠ p) (hb : b ≠ p) :
      ∠ (c a) (c p) (c b) = |t b - t a| := by
    change InnerProductGeometry.angle (c a - c p) (c b - c p) = |t b - t a|
    exact angle_eq_abs_sub_of_signed_chart o he (hray a ha) (hray b hb)
      (ht a ha) (ht b hb) (hchart a) (hchart b)
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image other t hnonempty
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image other t hnonempty
  have hap : a ≠ p := (hother a).mp ha
  have hbp : b ≠ p := (hother b).mp hb
  have hab_le : t a ≤ t b := hmin b hb
  have hwidth_pos : 0 < t b - t a := by
    by_contra hnonpos
    have hba : t b ≤ t a := by linarith
    obtain ⟨k, hkp, hka⟩ := Fin.exists_ne_and_ne_of_two_lt p a (by omega)
    have htk : t k = t a := le_antisymm
      ((hmax k ((hother k).mpr hkp)).trans hba)
      (hmin k ((hother k).mpr hkp))
    have hzero := hangle a k hap hkp
    rw [htk, sub_self, abs_zero] at hzero
    have hpositive := EuclideanGeometry.angle_pos_of_not_collinear
      (legal_triple_not_collinear hleg hap hka.symm hkp.symm)
    linarith
  have hab : a ≠ b := by
    intro h
    subst b
    simpa using hwidth_pos
  have hwidth_lt : t b - t a < Real.pi := by
    linarith [(ht b hbp).2, (ht a hap).1]
  have hwidth_angle : t b - t a = ∠ (c a) (c p) (c b) := by
    rw [hangle a b hap hbp, abs_of_nonneg (sub_nonneg.mpr hab_le)]
  refine ⟨{
    left := a
    right := b
    left_ne_center := hap
    right_ne_center := hbp
    boundary_distinct := hab
    base := c a - c p
    base_eq_left := rfl
    base_ne_zero := hray a hap
    width := t b - t a
    width_pos := hwidth_pos
    width_lt_pi := hwidth_lt
    width_eq_actual_angle := hwidth_angle
    width_le_legality := by
      rw [hwidth_angle]
      exact hleg.triAngle a p b hap hbp.symm hab
    theta := fun j => t j - t a
    theta_mem := ?_
    actual_direction := ?_
    left_coordinate := by simp
    right_coordinate := rfl }⟩
  · intro j hj
    exact ⟨sub_nonneg.mpr (hmin j ((hother j).mpr hj)),
      sub_le_sub_right (hmax j ((hother j).mpr hj)) (t a)⟩
  · intro j hj
    change o.oangle (c a - c p) (c j - c p) = ((t j - t a : ℝ) : Real.Angle)
    rw [← o.oangle_sub_left he (hray a hap) (hray j hj), Real.Angle.coe_sub]
    simp only [t, Real.Angle.coe_toReal]

/-- Legality and a vertex of the full original hull internally produce an
actual ray window with two actual endpoints and width at most `pi - lam`.
There are no caller-supplied directions, normal, cone, or window coordinates. -/
theorem exists_actual_hull_ray_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 3 ≤ s)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hp : IsHullVertex c p) :
    Nonempty (Window o c lam p) := by
  obtain ⟨e, he, hsupport⟩ := exists_strict_supporting_normal (by omega) hleg.inj hp
  exact exists_window_of_strict_support o hs hleg p e he hsupport

#print axioms not_mem_hull_others_of_isHullVertex
#print axioms exists_strict_supporting_normal
#print axioms exists_actual_hull_ray_window

end Jsp404.ActualHullRayWindow
