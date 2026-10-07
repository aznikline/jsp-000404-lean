import Jsp000404.ActualF18HeavyZeroGain
import Jsp000404.ActualMixedRigidCardinality
import Jsp000404.SharpNearestGeometry

set_option autoImplicit false

/-! Three distinct original nonacute heavy centers are impossible in an
actual n4 LOW minimum counter to cap sixteen. Every split is produced
from the original actual Types theorem. The contradiction uses only
original actual triangle angles and strict distances.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualNoThreeNonacuteHeavy

private structure WeakSplitData {s : ℕ} (c : Fin s → Plane₂) (lam : ℝ) (p : Fin s) where
  code : Fin s → Bool
  same_angle : ∀ i j, i ≠ p → j ≠ p → code i = code j →
    ∠ (c i) (c p) (c j) ≤ Real.pi-4*lam
  different_angle : ∀ i j, i ≠ p → j ≠ p → code i ≠ code j →
    2*lam ≤ ∠ (c i) (c p) (c j)

private theorem low_scale {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam) :
    2*Real.pi/9 < lam := by
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  rw [← hrho]
  exact H.scale_lower

private noncomputable def splitOfClumps {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} {W : ActualHullRayWindow.Window o c lam p}
    {score : ℕ} {sep : ℝ}
    (hleg : Section4Legality c lam)
    (D : ActualHullSmallScoreTypes.Clumps W score sep (Real.pi-4*lam))
    (hsep : 2*lam ≤ sep) : WeakSplitData c lam p where
  code := D.code
  same_angle := D.same_angle_le hleg
  different_angle := fun i j hi hj hne =>
    hsep.trans (D.different_angle_ge hleg i j hi hj hne)

private theorem actual_nonacute_split {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (hwide : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2*lam ≤ ∠ (c a) (c p) (c b)) :
    Nonempty (WeakSplitData c lam p) := by
  obtain ⟨hn,_,_⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by have := H.card_ge_three; omega) hn
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
  have hsmall : rowDefect 4 lam (directionRow o e c p) ≤ 2 := by omega
  have hhull := FullHullInteriorDefect.low_defect_is_full_hull_vertex
    o e he H.legality hn p hsmall
  obtain ⟨⟨W,K⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    H.card_ge_three o e he H.legality (low_scale o e H) p hhull hp
  cases K with
  | HA _hout hcone =>
      obtain ⟨a,b,ha,hb,_hab,hbig⟩ := hwide
      have hangle := ActualMixedRigidCardinality.actual_window_angle_le_width
        W H.legality a b ha hb
      have hlo := low_scale o e H
      exact False.elim (by linarith [Real.pi_pos])
  | HM _hout _hlo _hhi D =>
      exact ⟨splitOfClumps H.legality D le_rfl⟩
  | HO _hout _hcone D =>
      exact ⟨splitOfClumps H.legality D (by linarith [H.legality.lam_pos])⟩

private theorem actual_split_companion {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (D : WeakSplitData c lam p) (q : Fin s) (hqp : q ≠ p) :
    ∃ r : Fin s, r ≠ p ∧ r ≠ q ∧ D.code r = D.code q := by
  have hzero := ActualF18HeavyZeroGain.actual_low_four_heavy_observer_gain_eq_zero
    o e he H p hp q hqp.symm
  obtain ⟨r,hrp,hrq,hsmall⟩ :=
    (emit_or_near_collinear o e c H.legality he hqp.symm H.card_ge_three).resolve_left (by
      intro hpos
      rw [hzero] at hpos
      omega)
  by_cases hsame : D.code r = D.code q
  · exact ⟨r,hrp,hrq,hsame⟩
  · have hlarge := D.different_angle r q hrp hqp hsame
    rw [EuclideanGeometry.angle_comm (c r) (c p) (c q)] at hlarge
    exact False.elim (by linarith [H.legality.lam_pos])

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

private theorem two_small_false {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2*Real.pi/9 < lam)
    (A B C : Fin s) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hA : ∠ (c B) (c A) (c C) ≤ Real.pi-4*lam)
    (hB : ∠ (c A) (c B) (c C) ≤ Real.pi-4*lam) : False := by
  have hsum := actual_triangle_sum hleg A B C hAB
  have hcap := hleg.triAngle A C B hAC hBC.symm hAB
  linarith

private theorem bool_eq_of_two_ne {a b d : Bool} (hab : a ≠ b) (hbd : b ≠ d) : a = d := by
  cases a <;> cases b <;> cases d <;> simp_all

private theorem no_three_of_small_at_first {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (A B C : Fin s) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hB : rowScore lam (directionRow o e c B) = 2)
    (DA : WeakSplitData c lam A) (DB : WeakSplitData c lam B) (DC : WeakSplitData c lam C)
    (hsmallA : ∠ (c B) (c A) (c C) ≤ Real.pi-4*lam) : False := by
  have hlo := low_scale o e H
  have hhalf : Real.pi-4*lam < lam/2 := by linarith
  have hsmallA' : ∠ (c C) (c A) (c B) ≤ Real.pi-4*lam := by
    rw [EuclideanGeometry.angle_comm (c C) (c A) (c B)]
    exact hsmallA
  have hBAC : DB.code A ≠ DB.code C := by
    intro h
    exact two_small_false H.legality hlo A B C hAB hAC hBC hsmallA
      (DB.same_angle A C hAB hBC.symm h)
  have hCAB : DC.code A ≠ DC.code B := by
    intro h
    exact two_small_false H.legality hlo A C B hAC hAB hBC.symm hsmallA'
      (DC.same_angle A B hAC hBC h)
  obtain ⟨u,huB,huC,hBuC⟩ := actual_split_companion o e he H B hB DB C hBC.symm
  have huA : u ≠ A := by
    intro h
    apply hBAC
    simpa only [h] using hBuC
  have hsmallB : ∠ (c C) (c B) (c u) ≤ Real.pi-4*lam :=
    DB.same_angle C u hBC.symm huB hBuC.symm
  have hCBu : DC.code B ≠ DC.code u := by
    intro h
    have hsmallC := DC.same_angle B u hBC huC h
    exact two_small_false H.legality hlo B C u hBC huB.symm huC.symm hsmallB hsmallC
  have hCAu : DC.code A = DC.code u := bool_eq_of_two_ne hCAB hCBu
  have hsmallC : ∠ (c A) (c C) (c u) ≤ Real.pi-4*lam :=
    DC.same_angle A u hAC huC hCAu
  have hABC : DA.code B = DA.code C := by
    by_contra h
    have hbig := DA.different_angle B C hAB.symm hAC.symm h
    linarith [H.legality.lam_pos]
  by_cases hAu : DA.code u = DA.code B
  · have hsmallAu : ∠ (c C) (c A) (c u) ≤ Real.pi-4*lam :=
      DA.same_angle C u hAC.symm huA (hABC.symm.trans hAu.symm)
    exact two_small_false H.legality hlo A C u hAC huA.symm huC.symm hsmallAu hsmallC
  · have hlargeA := DA.different_angle B u hAB.symm huA (Ne.symm hAu)
    have hlargeB := DB.different_angle A u hAB huB (by
      intro h
      exact hBAC (h.trans hBuC))
    have hsumU := actual_triangle_sum H.legality A B u hAB
    have hsmallU : ∠ (c A) (c u) (c B) ≤ Real.pi-4*lam := by linarith
    have hsmallC' : ∠ (c u) (c C) (c A) ≤ Real.pi-4*lam :=
      DC.same_angle u A huC hAC hCAu.symm
    have h1 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
      H.legality hAB hAC hBC (hsmallA.trans_lt hhalf)
    have h2 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
      H.legality huA huB hAB (hsmallU.trans_lt hhalf)
    have h3 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
      H.legality huC.symm hAC.symm huA (hsmallC'.trans_lt hhalf)
    have h4 := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
      H.legality hBC huB.symm huC.symm (hsmallB.trans_lt hhalf)
    rw [dist_comm (c B) (c A)] at h1
    rw [dist_comm (c u) (c A),dist_comm (c u) (c C)] at h3
    rw [dist_comm (c C) (c B)] at h4
    linarith

/-- Three injectively selected original score-two centers, each with an
actual original angle at least twice lambda, contradict the original
triangle legality and strict distances. No potential-value premise is needed. -/
theorem no_three_nonacute_heavy {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (pick : Fin 3 → Fin s) (hpick : Function.Injective pick)
    (hheavy : ∀ i : Fin 3, rowScore lam (directionRow o e c (pick i)) = 2)
    (hwide : ∀ i : Fin 3, ∃ a b : Fin s, a ≠ pick i ∧ b ≠ pick i ∧ a ≠ b ∧
      2*lam ≤ ∠ (c a) (c (pick i)) (c b)) : False := by
  let A := pick 0
  let B := pick 1
  let C := pick 2
  have hAB : A ≠ B := hpick.ne (by decide : (0 : Fin 3) ≠ 1)
  have hAC : A ≠ C := hpick.ne (by decide : (0 : Fin 3) ≠ 2)
  have hBC : B ≠ C := hpick.ne (by decide : (1 : Fin 3) ≠ 2)
  obtain ⟨DA⟩ := actual_nonacute_split o e he H A (hheavy 0) (hwide 0)
  obtain ⟨DB⟩ := actual_nonacute_split o e he H B (hheavy 1) (hwide 1)
  obtain ⟨DC⟩ := actual_nonacute_split o e he H C (hheavy 2) (hwide 2)
  by_cases hA : DA.code B = DA.code C
  · exact no_three_of_small_at_first o e he H A B C hAB hAC hBC
      (hheavy 1) DA DB DC
      (DA.same_angle B C hAB.symm hAC.symm hA)
  by_cases hB : DB.code A = DB.code C
  · exact no_three_of_small_at_first o e he H B A C hAB.symm hBC hAC
      (hheavy 0) DB DA DC
      (DB.same_angle A C hAB hBC.symm hB)
  by_cases hC : DC.code A = DC.code B
  · exact no_three_of_small_at_first o e he H C A B hAC.symm hBC.symm hAB
      (hheavy 0) DC DA DB
      (DC.same_angle A B hAC hBC hC)
  have hsum := actual_triangle_sum H.legality A B C hAB
  have hbigA := DA.different_angle B C hAB.symm hAC.symm hA
  have hbigB := DB.different_angle A C hAB hBC.symm hB
  have hbigC := DC.different_angle A B hAC hBC hC
  have hlo := low_scale o e H
  linarith [Real.pi_pos]

#print axioms no_three_nonacute_heavy

end Jsp404.ActualNoThreeNonacuteHeavy
