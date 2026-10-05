import Jsp000404.ActualScorePreservingExpansion
import Mathlib.Algebra.Module.Submodule.Union

/-! Genuine safe references for finite families of nonzero plane vectors.
A finite union of kernels is avoided over the infinite real field. The
chosen reference avoids both projective seam directions, giving strict
chart coordinates and actual continuity at the limiting vectors.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.SafeFanReference

/-- Nonzero imaginary part excludes both endpoints of the projective cut. -/
theorem projective_arg_mem_Ioo {z : ℂ} (him : z.im ≠ 0) :
    linRep (z.arg : Real.Angle) ∈ Set.Ioo 0 Real.pi := by
  have ha := Complex.arg_mem_Ioc z
  have hzero : z.arg ≠ 0 := by
    intro h
    exact him (Complex.arg_eq_zero_iff.mp h).2
  have hpi : z.arg ≠ Real.pi := by
    intro h
    exact him (Complex.arg_eq_pi_iff.mp h).2
  simp only [linRep, Complex.arg_coe_angle_toReal_eq_arg]
  by_cases hneg : z.arg < 0
  · rw [ite_eq_left hneg]
    constructor <;> linarith [ha.1, ha.2]
  · rw [ite_eq_right hneg, ite_eq_right hpi]
    exact ⟨lt_of_le_of_ne (le_of_not_gt hneg) hzero.symm,
      lt_of_le_of_ne ha.2 hpi⟩

/-- A genuinely chosen reference avoids every vector in a nonempty finite
family. Each forbidden condition is the kernel of a nonzero real dual map. -/
theorem exists_safe_reference {α : Type*} [Finite α] [Nonempty α]
    (o : Orientation ℝ Plane₂ (Fin 2)) (v : α → Plane₂)
    (hv : ∀ i, v i ≠ 0) :
    ∃ e : Plane₂, e ≠ 0 ∧ ∀ i,
      (o.kahler e (v i)).im ≠ 0 ∧
        linRep (o.oangle e (v i)) ∈ Set.Ioo 0 Real.pi := by
  classical
  let f : α → Module.Dual ℝ Plane₂ := fun i => o.areaForm.flip (v i)
  have hf : ∀ i, ∃ x : Plane₂, f i x ≠ 0 := by
    intro i
    refine ⟨o.rightAngleRotation (v i), ?_⟩
    simpa only [f, LinearMap.flip_apply, o.areaForm_rightAngleRotation_left,
      neg_ne_zero] using (inner_self_ne_zero.mpr (hv i) : inner ℝ (v i) (v i) ≠ 0)
  obtain ⟨e, he⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  have henonzero : e ≠ 0 := by
    intro h
    subst e
    simpa using he (Classical.choice inferInstance)
  refine ⟨e, henonzero, ?_⟩
  intro i
  have him : (o.kahler e (v i)).im ≠ 0 := by
    simpa [f, Orientation.kahler_apply_apply] using he i
  exact ⟨him, by
    simpa only [Orientation.oangle] using projective_arg_mem_Ioo him⟩

/-- A safe reference is constructed internally for actual continuous
vector trajectories. No chart safety or projective coordinate continuity
is supplied by the caller. Limiting vector nonzeroness is indispensable. -/
theorem exists_safe_continuous_coordinates {α : Type*} [Finite α] [Nonempty α]
    (o : Orientation ℝ Plane₂ (Fin 2)) (B : ℝ → α → Plane₂)
    (hcont : ∀ i, ContinuousAt (fun eps => B eps i) 0)
    (hne : ∀ i, B 0 i ≠ 0) :
    ∃ e : Plane₂, e ≠ 0 ∧
      (∀ i, linRep (o.oangle e (B 0 i)) ∈ Set.Ioo 0 Real.pi) ∧
      ∀ i, ContinuousAt (fun eps => linRep (o.oangle e (B eps i))) 0 := by
  obtain ⟨e, he, hsafe⟩ := exists_safe_reference o (B 0) hne
  refine ⟨e, he, fun i => (hsafe i).2, ?_⟩
  intro i
  have hk : Continuous (o.kahler e) :=
    (o.kahler e).continuous_of_finiteDimensional
  have hc : ContinuousAt (fun eps => o.kahler e (B eps i)) 0 :=
    hk.continuousAt.comp (hcont i)
  simpa only [Orientation.oangle] using
    ActualScorePreservingExpansion.continuousAt_projective_arg hc (hsafe i).1

#print axioms projective_arg_mem_Ioo
#print axioms exists_safe_reference
#print axioms exists_safe_continuous_coordinates

end Jsp404.SafeFanReference
