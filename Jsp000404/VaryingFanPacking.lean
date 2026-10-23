import Jsp000404.AcuteFanPacking

/-!
# Inward bisectors with a separate angle cap at each center

Each actual ray fan supplies its own bisector. Two centers' complementary
chord directions separate their bisectors by pi minus half the sum of
their local caps. No global cardinality or potential bound is assumed.
-/

namespace Jsp404

open scoped EuclideanGeometry EuclideanSpace

/-- Actual center fans, each of diameter below120 degrees, admit nonzero
inward bisectors with their respective half-cap bounds. -/
theorem exists_varying_inward_bisectors
    (o : Orientation ℝ Plane₂ (Fin 2)) {s : ℕ} (hs : 2 ≤ s)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    (a : Fin s → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsmall : ∀ i, 3*a i < 2*Real.pi)
    (hcap : ∀ i j k : Fin s, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ a j) :
    ∃ m : Fin s → Plane₂, (∀ i, m i ≠ 0) ∧
      ∀ i j, j ≠ i → InnerProductGeometry.angle (m i) (c j-c i) ≤ a i/2 := by
  classical
  have hlocal (i : Fin s) : ∃ m : Plane₂, m ≠ 0 ∧
      ∀ j : Fin s, j ≠ i → InnerProductGeometry.angle m (c j-c i) ≤ a i/2 := by
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
        InnerProductGeometry.angle (u j) (u k) ≤ a i := by
      by_cases hjk : j.val = k.val
      · have heq : j = k := Subtype.ext hjk
        subst k
        rw [InnerProductGeometry.angle_self (hu j)]
        exact ha i
      · exact hcap j i k j.property k.property.symm hjk
    obtain ⟨e, he, theta, htheta⟩ :=
      exists_ray_window_of_three_mul_lt_two_pi o u hu (ha i) (hsmall i) hang
    have hpi : a i < Real.pi := by linarith [hsmall i, Real.pi_pos]
    obtain ⟨m, hm, hbound⟩ :=
      exists_inward_bisector_of_ray_window o u hu (ha i) hpi e he theta htheta
    exact ⟨m, hm, fun j hj => hbound ⟨j, hj⟩⟩
  choose m hm hbound using hlocal
  exact ⟨m, hm, hbound⟩

/-- Distinct actual centers' inward bisectors are separated by pi minus
the average of their two local angle caps. -/
theorem exists_separated_varying_inward_bisectors
    (o : Orientation ℝ Plane₂ (Fin 2)) {s : ℕ} (hs : 2 ≤ s)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    (a : Fin s → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsmall : ∀ i, 3*a i < 2*Real.pi)
    (hcap : ∀ i j k : Fin s, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ a j) :
    ∃ m : Fin s → Plane₂, (∀ i, m i ≠ 0) ∧
      ∀ i j, i ≠ j →
        Real.pi-(a i+a j)/2 ≤ InnerProductGeometry.angle (m i) (m j) := by
  obtain ⟨m, hm, hbound⟩ := exists_varying_inward_bisectors o hs hinj a ha hsmall hcap
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

#print axioms exists_varying_inward_bisectors
#print axioms exists_separated_varying_inward_bisectors

end Jsp404
