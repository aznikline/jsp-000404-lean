import Jsp000404.ConeCorridor
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Inward bisectors for configurations with angles below 120 degrees

A finite family of rays of angular diameter alpha < 2*pi/3 lies in a
single oriented window of width alpha. Applying this to each point's ray
fan gives inward bisectors separated by at least pi-alpha. Circle packing
of those bisectors is a separate finite counting step.
-/

namespace Jsp404

open scoped EuclideanGeometry EuclideanSpace

/-- The finite-ray window lemma up to the sharp 120-degree threshold. -/
theorem exists_ray_window_of_three_mul_lt_two_pi
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (o : Orientation ℝ Plane₂ (Fin 2)) (u : ι → Plane₂)
    (hu : ∀ i, u i ≠ 0) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hsmall : 3 * alpha < 2 * Real.pi)
    (hang : ∀ i j, InnerProductGeometry.angle (u i) (u j) ≤ alpha) :
    ∃ e : Plane₂, e ≠ 0 ∧ ∃ theta : ι → ℝ,
      ∀ i, theta i ∈ Set.Icc 0 alpha ∧
        o.oangle e (u i) = (theta i : Real.Angle) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let a (i : ι) : ℝ := (o.oangle (u i₀) (u i)).toReal
  have ha (i : ι) : -alpha ≤ a i ∧ a i ≤ alpha := by
    have h := hang i₀ i
    rw [o.angle_eq_abs_oangle_toReal (hu i₀) (hu i)] at h
    exact abs_le.mp h
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  refine ⟨u j, hu j, fun i => a i-a j, ?_⟩
  intro i
  have hji : a j ≤ a i := hj i (Finset.mem_univ _)
  have hdir : o.oangle (u j) (u i) = ((a i-a j : ℝ) : Real.Angle) := by
    rw [← o.oangle_sub_left (hu i₀) (hu j) (hu i), Real.Angle.coe_sub]
    simp only [a, Real.Angle.coe_toReal]
  have hdpi : a i-a j ≤ Real.pi := by
    by_contra h
    have hgt : Real.pi < a i-a j := lt_of_not_ge h
    have hrep : (((a i-a j : ℝ) : Real.Angle)).toReal =
        a i-a j-2*Real.pi :=
      Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr
        ⟨hgt, by linarith [(ha i).2, (ha j).1, Real.pi_pos]⟩
    have hangle := hang j i
    rw [o.angle_eq_abs_oangle_toReal (hu j) (hu i), hdir, hrep,
      abs_of_neg (by linarith [(ha i).2, (ha j).1, Real.pi_pos])] at hangle
    linarith [(ha i).2, (ha j).1]
  have hrep : (((a i-a j : ℝ) : Real.Angle)).toReal = a i-a j :=
    Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], hdpi⟩
  have hangle := hang j i
  rw [o.angle_eq_abs_oangle_toReal (hu j) (hu i), hdir, hrep,
    abs_of_nonneg (sub_nonneg.mpr hji)] at hangle
  exact ⟨⟨sub_nonneg.mpr hji, hangle⟩, hdir⟩

/-- A fan contained in a width-alpha oriented window has a nonzero
inward bisector making angle at most alpha/2 with every ray. -/
theorem exists_inward_bisector_of_ray_window
    {ι : Type*} (o : Orientation ℝ Plane₂ (Fin 2)) (u : ι → Plane₂)
    (hu : ∀ i, u i ≠ 0) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hpi : alpha < Real.pi) (e : Plane₂) (he : e ≠ 0)
    (theta : ι → ℝ)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 alpha ∧
      o.oangle e (u i) = (theta i : Real.Angle)) :
    ∃ m : Plane₂, m ≠ 0 ∧
      ∀ i, InnerProductGeometry.angle m (u i) ≤ alpha/2 := by
  let m := o.rotation ((alpha/2 : ℝ) : Real.Angle) e
  have hm : m ≠ 0 := by
    intro h
    exact he ((o.rotation ((alpha/2 : ℝ) : Real.Angle)).injective (by simpa [m] using h))
  refine ⟨m, hm, ?_⟩
  intro i
  have hmangle : o.oangle e m = ((alpha/2 : ℝ) : Real.Angle) :=
    o.oangle_rotation_self_right he _
  rw [angle_eq_abs_of_half_plane_chart o he hm (hu i)
    ⟨by positivity, by linarith⟩
    ⟨(htheta i).1.1, (htheta i).1.2.trans_lt hpi⟩ hmangle (htheta i).2]
  exact abs_le.mpr ⟨by linarith [(htheta i).1.1], by linarith [(htheta i).1.2]⟩

/-- Every actual center fan below the 120-degree threshold has an inward
bisector, and distinct centers' bisectors are separated by pi-alpha. -/
theorem exists_separated_inward_bisectors
    (o : Orientation ℝ Plane₂ (Fin 2)) {s : ℕ} (hs : 2 ≤ s)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hsmall : 3*alpha < 2*Real.pi)
    (hcap : ∀ i j k : Fin s, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ alpha) :
    ∃ m : Fin s → Plane₂, (∀ i, m i ≠ 0) ∧
      ∀ i j, i ≠ j → Real.pi-alpha ≤ InnerProductGeometry.angle (m i) (m j) := by
  classical
  have hpi : alpha < Real.pi := by linarith [Real.pi_pos]
  have hlocal (i : Fin s) : ∃ m : Plane₂, m ≠ 0 ∧
      ∀ j : Fin s, j ≠ i → InnerProductGeometry.angle m (c j-c i) ≤ alpha/2 := by
    let : Nonempty {j : Fin s // j ≠ i} := by
      let z : Fin s := ⟨0, by omega⟩
      let one : Fin s := ⟨1, by omega⟩
      by_cases hi : z = i
      · exact ⟨⟨one, by intro h; have := congrArg Fin.val (h.trans hi.symm); simp [z, one] at this⟩⟩
      · exact ⟨⟨z, hi⟩⟩
    let u : {j : Fin s // j ≠ i} → Plane₂ := fun j => c j-c i
    have hu (j : {j : Fin s // j ≠ i}) : u j ≠ 0 :=
      sub_ne_zero.mpr (hinj.ne j.property)
    have hang (j k : {j : Fin s // j ≠ i}) :
        InnerProductGeometry.angle (u j) (u k) ≤ alpha := by
      by_cases hjk : j.val = k.val
      · have heq : j = k := Subtype.ext hjk
        subst k
        rw [InnerProductGeometry.angle_self (hu j)]
        exact halpha
      · exact hcap j i k j.property k.property.symm hjk
    obtain ⟨e, he, theta, htheta⟩ :=
      exists_ray_window_of_three_mul_lt_two_pi o u hu halpha hsmall hang
    obtain ⟨m, hm, hbound⟩ :=
      exists_inward_bisector_of_ray_window o u hu halpha hpi e he theta htheta
    exact ⟨m, hm, fun j hj => hbound ⟨j, hj⟩⟩
  choose m hm hbound using hlocal
  refine ⟨m, hm, ?_⟩
  intro i j hij
  have hi := hbound i j hij.symm
  have hj := hbound j i hij
  have hneg : InnerProductGeometry.angle (m j) (c j-c i) =
      Real.pi-InnerProductGeometry.angle (m j) (c i-c j) := by
    rw [show c j-c i = -(c i-c j) by abel, InnerProductGeometry.angle_neg_right]
  have htri := InnerProductGeometry.angle_le_angle_add_angle (m j) (m i) (c j-c i)
  rw [hneg, InnerProductGeometry.angle_comm (m j) (m i)] at htri
  linarith

#print axioms exists_ray_window_of_three_mul_lt_two_pi
#print axioms exists_inward_bisector_of_ray_window
#print axioms exists_separated_inward_bisectors

end Jsp404
