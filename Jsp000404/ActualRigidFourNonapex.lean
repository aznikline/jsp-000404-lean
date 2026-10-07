import Jsp000404.ActualRigidFourGeometry
import Jsp000404.ActualInteriorOnePartition

set_option autoImplicit false

/-! Original nonapex classes at a selected interior rigid-four center.
The original full configuration supplies the partition. The actual
four-point restriction supplies a wide complete hull window and doubled
legality. No lower bound on every selected triangle angle is assumed.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualRigidFourNonapex

/-- Output witnesses are selected original points, classified by an
internally produced original partition at pick i. -/
structure Data {s : ℕ} (c : Fin s → Plane₂) (lam : ℝ)
    (pick : Fin 4 → Fin s) (hpick : Function.Injective pick) (i : Fin 4) where
  partition : ActualInteriorOnePartition.Data c lam (pick i)
  no_apex : ∀ j : {j : Fin 4 // j ≠ i},
    partition.classOf ⟨pick j,hpick.ne j.property⟩ ≠ 1
  left : {j : Fin 4 // j ≠ i}
  right : {j : Fin 4 // j ≠ i}
  left_class : partition.classOf ⟨pick left,hpick.ne left.property⟩ = 0
  right_class : partition.classOf ⟨pick right,hpick.ne right.property⟩ = 2
  witnesses_distinct : left ≠ right

private theorem fin3_zero_of_ne_one_two (k : Fin 3) (h1 : k ≠ 1) (h2 : k ≠ 2) : k = 0 := by
  fin_cases k <;> simp_all

private theorem fin3_two_of_ne_zero_one (k : Fin 3) (h0 : k ≠ 0) (h1 : k ≠ 1) : k = 2 := by
  fin_cases k <;> simp_all

/-- At an original interior score-one center among four selected original
rigid points, the other three selected points avoid its original apex
class and occupy both original nonapex classes. -/
theorem actual_rigid_four_nonapex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (pick : Fin 4 → Fin s) (hpick : Function.Injective pick)
    (hselected : ∀ a : Fin 4,
      (¬ IsHullVertex c (pick a) ∧ rowScore lam (directionRow o e c (pick a)) = 1) ∨
      (rowScore lam (directionRow o e c (pick a)) = 2 ∧
        ∃ u v : Fin s, u ≠ pick a ∧ v ≠ pick a ∧ u ≠ v ∧
          2*lam ≤ ∠ (c u) (c (pick a)) (c v)))
    (i : Fin 4) (hnot : ¬ IsHullVertex c (pick i))
    (hscore : rowScore lam (directionRow o e c (pick i)) = 1) :
    Nonempty (Data c lam pick hpick i) := by
  classical
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  have hlo2 : 2*Real.pi/9 < lam := by rw [← hrho]; exact H.scale_lower
  have hlo5 : Real.pi/5 < lam := by linarith only [hlo2,Real.pi_pos]
  have hpi5 : Real.pi < 5*lam := by linarith only [hlo5]
  have hRsmall : Real.pi-4*lam < 2*lam := by
    linarith only [hlo5,H.legality.lam_pos]
  let P := ActualInteriorOnePartition.actualPartition
    (by have := H.card_ge_three; omega : 2 ≤ s) o e he H.legality hlo5 (pick i) hnot hscore
  obtain ⟨G⟩ := ActualRigidFourGeometry.actual_rigid_four_geometry
    o e he H pick hpick hselected
  let J := {j : Fin 4 // j ≠ i}
  let emb (j : J) : {p : Fin s // p ≠ pick i} := ⟨pick j,hpick.ne j.property⟩
  let cls (j : J) : Fin 3 := P.classOf (emb j)
  have hother (k : Fin 3) : ∃ j : J, cls j ≠ k := by
    by_contra hnone
    have hsame (j : J) : cls j = k := by
      by_contra hj
      exact hnone ⟨j,hj⟩
    let W := G.window i
    let l : J := ⟨W.left,W.left_ne_center⟩
    let r : J := ⟨W.right,W.right_ne_center⟩
    have hang := P.same_angle (emb l) (emb r) ((hsame l).trans (hsame r).symm)
    have hwidth : W.width ≤ Real.pi-4*lam := by
      rw [W.width_eq_actual_angle]
      exact hang
    have hwide : 2*lam ≤ W.width := G.window_lower i
    linarith only [hwidth,hwide,hRsmall]
  have hnoapex (j : J) : cls j ≠ 1 := by
    intro hj
    obtain ⟨k,hk⟩ := hother 1
    have hjk : (j : Fin 4) ≠ k := by
      intro h
      have heq : j = k := Subtype.ext h
      exact hk ((congrArg cls heq).symm.trans hj)
    have hbig := P.apex_angle (emb j) (emb k) hj hk
    change 3*lam ≤ ∠ ((c ∘ pick) (j : Fin 4)) ((c ∘ pick) i)
      ((c ∘ pick) (k : Fin 4)) at hbig
    have hcap := G.double_legality.triAngle (j : Fin 4) i (k : Fin 4)
      j.property k.property.symm hjk
    linarith only [hbig,hcap,hpi5]
  obtain ⟨left,hl2⟩ := hother 2
  obtain ⟨right,hr0⟩ := hother 0
  have hl : cls left = 0 := fin3_zero_of_ne_one_two (cls left) (hnoapex left) hl2
  have hr : cls right = 2 := fin3_two_of_ne_zero_one (cls right) hr0 (hnoapex right)
  have hne : left ≠ right := by
    intro h
    subst right
    exact (by decide : (0 : Fin 3) ≠ 2) (hl.symm.trans hr)
  exact ⟨{
    partition := P
    no_apex := hnoapex
    left := left
    right := right
    left_class := hl
    right_class := hr
    witnesses_distinct := hne }⟩

#print axioms actual_rigid_four_nonapex

end Jsp404.ActualRigidFourNonapex
