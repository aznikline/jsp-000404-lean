import Jsp000404.ActualHullRayWindow
import Jsp000404.ConeDeletionProgress
import Jsp000404.AcuteFanPacking

/-!
The full original hull supplies physical boundary rays. An actual angular
bound at that vertex then supplies the common oriented cone needed for a
real incoming deletion gain. No bisector or abstract cone is a caller input.
-/

set_option autoImplicit false
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualHullConeDeletion

theorem exists_common_cone_of_actual_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2))
    {lam : ℝ} {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (p : Fin s) (W : ActualHullRayWindow.Window o c lam p)
    (hwidth : W.width ≤ Real.pi - 2 * lam) :
    ∃ u : Plane₂, u ≠ 0 ∧ ∀ j : Fin s, j ≠ p →
      InnerProductGeometry.angle (c j - c p) u ≤ Real.pi / 2 - lam := by
  classical
  let rays : {j : Fin s // j ≠ p} → Plane₂ := fun j => c j - c p
  have hrays (j : {j : Fin s // j ≠ p}) : rays j ≠ 0 :=
    sub_ne_zero.mpr (hleg.inj.ne j.property)
  obtain ⟨u, hu, hcone⟩ := exists_inward_bisector_of_ray_window o rays hrays
    W.width_pos.le W.width_lt_pi W.base W.base_ne_zero
    (fun j => W.theta j) (fun j => ⟨W.theta_mem j j.property, W.actual_direction j j.property⟩)
  refine ⟨u, hu, ?_⟩
  intro j hj
  have hc := hcone ⟨j, hj⟩
  dsimp only [rays] at hc
  rw [InnerProductGeometry.angle_comm]
  linarith

theorem exists_actual_hull_common_cone {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2))
    {lam : ℝ} {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (p : Fin s) (hp : IsHullVertex c p)
    (hangle : ∀ i j : Fin s, i ≠ p → j ≠ p → i ≠ j →
      ∠ (c i) (c p) (c j) ≤ Real.pi - 2 * lam) :
    ∃ u : Plane₂, u ≠ 0 ∧ ∀ j : Fin s, j ≠ p →
      InnerProductGeometry.angle (c j - c p) u ≤ Real.pi / 2 - lam := by
  classical
  obtain ⟨W⟩ := ActualHullRayWindow.exists_actual_hull_ray_window o hs hleg p hp
  have hwidth : W.width ≤ Real.pi - 2 * lam := by
    rw [W.width_eq_actual_angle]
    exact hangle W.left W.right W.left_ne_center W.right_ne_center W.boundary_distinct
  exact exists_common_cone_of_actual_window o hleg p W hwidth

theorem exists_emitter_of_actual_hull_angle_bound {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (p : Fin (s + 1)) (hp : IsHullVertex c p)
    (hangle : ∀ i j : Fin (s + 1), i ≠ p → j ≠ p → i ≠ j →
      ∠ (c i) (c p) (c j) ≤ Real.pi - 2 * lam) :
    ∃ i : Fin (s + 1), i ≠ p ∧
      1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c p i) := by
  obtain ⟨u, hu, hcone⟩ := exists_actual_hull_common_cone (by omega) o hleg p hp hangle
  exact ConeDeletionProgress.exists_emitter_of_common_cone hs o e he hleg p u hu hcone

theorem not_hull_angle_bound_of_actual_zero_incoming {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (p : Fin (s + 1)) (hp : IsHullVertex c p)
    (hzero : ∀ i : Fin (s + 1), i ≠ p →
      rowGain lam (directionRow o e c i) (deleteIndex o e c p i) = 0) :
    ¬ ∀ i j : Fin (s + 1), i ≠ p → j ≠ p → i ≠ j →
      ∠ (c i) (c p) (c j) ≤ Real.pi - 2 * lam := by
  intro hangle
  obtain ⟨i, hi, hg⟩ := exists_emitter_of_actual_hull_angle_bound hs o e he hleg p hp hangle
  rw [hzero i hi] at hg
  omega

#print axioms exists_common_cone_of_actual_window
#print axioms exists_actual_hull_common_cone
#print axioms exists_emitter_of_actual_hull_angle_bound
#print axioms not_hull_angle_bound_of_actual_zero_incoming

end Jsp404.ActualHullConeDeletion
