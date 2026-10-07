import Jsp000404.ActualInteriorOnePartition

set_option autoImplicit false

/-! Actual class sizes from original deletion budgets.
A light target cannot be a singleton. Heavy singleton classes are allowed;
no theorem below turns the light-only budget into an all-target budget.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators
open Jsp404.ActualInteriorOnePartition

namespace Jsp404.ActualInteriorOneClassSize

/-- The finite fiber of an actual partition output. All geometric theorems
below use the fixed partition produced from the original configuration. -/
noncomputable def members {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : Data c lam p) (k : Fin 3) : Finset {i : Fin s // i ≠ p} :=
  Finset.univ.filter (fun i => D.classOf i = k)

private theorem two_le_members_card {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (D : Data c lam p) (k : Fin 3)
    (hcomp : ∀ q : {i : Fin s // i ≠ p}, D.classOf q = k →
      ∃ j : {i : Fin s // i ≠ p}, j ≠ q ∧ D.classOf j = k) :
    2 ≤ (members D k).card := by
  classical
  obtain ⟨j,hjq,hjk⟩ := hcomp (D.witness k) (D.witness_class k)
  have hnon : (members D k).Nontrivial :=
    ⟨D.witness k,by simp [members,D.witness_class k],
      j,by simp [members,hjk],hjq.symm⟩
  exact hnon.two_le_card

private theorem low_model_scale {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam) :
    Real.pi/5 < lam := by
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  have hlo : 2*Real.pi/9 < lam := by rw [← hrho]; exact H.scale_lower
  linarith [Real.pi_pos]

/-- The original F18 LOW model selects a minimum score internally;
its exact critical form forces every original score to be at least one. -/
theorem actual_low_four_F18_score_ge_one {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18) :
    ∀ i : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c i) := by
  classical
  obtain ⟨m,hmin⟩ := Finite.exists_min
    (fun i : Fin (s+1) => rowScore lam (directionRow o e c i))
  have hcrit := ActualMinimalBandCounterexample.low_minimum_score_critical_form
    (n := 4) hs (by decide : 2 ≤ 4) o e H m hmin
  have hpow : 2 ^ rowScore lam (directionRow o e c m) = 2 := by
    have h := hcrit.1
    rw [hF] at h
    norm_num at h
    omega
  have hm : rowScore lam (directionRow o e c m) = 1 :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (by simpa using hpow)
  intro i
  simpa only [hm] using hmin i

/-- Deleting any original light target has zero gain at every other
original row. The target's minimum-score property is derived internally. -/
theorem actual_low_four_F18_light_incoming_gain_zero {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (q : Fin (s+1)) (hq : rowScore lam (directionRow o e c q) = 1) :
    ∀ i : Fin (s+1), i ≠ q →
      rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0 := by
  have hall := actual_low_four_F18_score_ge_one hs o e H hF
  have hmin (i : Fin (s+1)) : rowScore lam (directionRow o e c q) ≤
      rowScore lam (directionRow o e c i) := by simpa only [hq] using hall i
  exact (ActualMinimalBandCounterexample.low_minimum_score_critical_form
    (n := 4) hs (by decide : 2 ≤ 4) o e H q hmin).2.2

/-- At an original interior score-one row, zero actual gain toward q
forces a second original point in q's internally produced class. -/
theorem actual_class_companion_of_zero_gain {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : Real.pi/5 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hp : rowScore lam (directionRow o e c p) = 1)
    (q : {i : Fin s // i ≠ p})
    (hzero : rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0) :
    ∃ j : {i : Fin s // i ≠ p}, j ≠ q ∧
      (actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hp).classOf j =
        (actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hp).classOf q := by
  classical
  by_contra hno
  have hsingle : ∀ j : {i : Fin s // i ≠ p},
      (actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hp).classOf j =
        (actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hp).classOf q → j = q := by
    intro j hj
    by_contra hne
    exact hno ⟨j,hne,hj⟩
  have hpos := singleton_in_class_actual_gain hs o e he hleg hlo p hnot hp q hsingle
  rw [hzero] at hpos
  omega

/-- In the original F18 model, each light target has a distinct companion
in its class at every original interior light center. -/
theorem actual_low_four_F18_light_class_companion {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s+1)) (hnot : ¬ IsHullVertex c p)
    (hp : rowScore lam (directionRow o e c p) = 1)
    (q : {i : Fin (s+1) // i ≠ p})
    (hq : rowScore lam (directionRow o e c q) = 1) :
    ∃ j : {i : Fin (s+1) // i ≠ p}, j ≠ q ∧
      (actualPartition (by omega : 2 ≤ s+1) o e he H.legality
        (low_model_scale o e H) p hnot hp).classOf j =
      (actualPartition (by omega : 2 ≤ s+1) o e he H.legality
        (low_model_scale o e H) p hnot hp).classOf q := by
  apply actual_class_companion_of_zero_gain (by omega : 3 ≤ s+1)
    o e he H.legality (low_model_scale o e H) p hnot hp q
  exact actual_low_four_F18_light_incoming_gain_zero hs o e H hF q hq p q.property.symm

/-- A class consisting entirely of original light points has at least
two members. This does not assert the same for a heavy singleton class. -/
theorem actual_low_four_F18_pure_light_class_card_ge_two {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s+1)) (hnot : ¬ IsHullVertex c p)
    (hp : rowScore lam (directionRow o e c p) = 1) (k : Fin 3)
    (hlight : ∀ q : {i : Fin (s+1) // i ≠ p},
      (actualPartition (by omega : 2 ≤ s+1) o e he H.legality
        (low_model_scale o e H) p hnot hp).classOf q = k →
      rowScore lam (directionRow o e c q) = 1) :
    2 ≤ (members (actualPartition (by omega : 2 ≤ s+1) o e he H.legality
      (low_model_scale o e H) p hnot hp) k).card := by
  apply two_le_members_card
  intro q hqk
  obtain ⟨j,hjq,hclass⟩ := actual_low_four_F18_light_class_companion
    hs o e he H hF p hnot hp q (hlight q hqk)
  exact ⟨j,hjq,hclass.trans hqk⟩

/-- If all actual targets have zero gain at the original center, then
all three internally produced classes have at least two original points. -/
theorem actual_interior_one_all_zero_class_card_ge_two {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : Real.pi/5 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hp : rowScore lam (directionRow o e c p) = 1)
    (hzero : ∀ q : Fin s, q ≠ p →
      rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0) :
    ∀ k : Fin 3, 2 ≤ (members
      (actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hp) k).card := by
  intro k
  apply two_le_members_card
  intro q hqk
  obtain ⟨j,hjq,hclass⟩ := actual_class_companion_of_zero_gain
    hs o e he hleg hlo p hnot hp q (hzero q q.property)
  exact ⟨j,hjq,hclass.trans hqk⟩

/-- Three nonempty classes with no singleton need six other original
points. Thus the full configuration has at least seven, allowing equality. -/
theorem actual_interior_one_all_zero_card_ge_seven {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : Real.pi/5 < lam) (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hp : rowScore lam (directionRow o e c p) = 1)
    (hzero : ∀ q : Fin s, q ≠ p →
      rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0) :
    7 ≤ s := by
  classical
  let D := actualPartition (by omega : 2 ≤ s) o e he hleg hlo p hnot hp
  have hclasses : ∀ k : Fin 3, 2 ≤ (members D k).card :=
    actual_interior_one_all_zero_class_card_ge_two hs o e he hleg hlo p hnot hp hzero
  have hsum : (Finset.univ : Finset {i : Fin s // i ≠ p}).card =
      ∑ k : Fin 3, (members D k).card := by
    simpa only [members] using
      (Finset.card_eq_sum_card_fiberwise (f := D.classOf)
        (s := Finset.univ) (t := Finset.univ) (by intro i hi; simp))
  have hsum_lower : 6 ≤ ∑ k : Fin 3, (members D k).card := by
    calc
      6 = ∑ k : Fin 3, (2 : ℕ) := by simp
      _ ≤ ∑ k : Fin 3, (members D k).card :=
        Finset.sum_le_sum (fun k _ => hclasses k)
  have hothers : Fintype.card {i : Fin s // i ≠ p} = s-1 := by
    simpa only [Fintype.card_fin,Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : Fin s => i = p)
  rw [Finset.card_univ,hothers] at hsum
  omega

/-- The same-class companion can be chosen strictly closer to the light
target than the original interior center, with the target endpoint fixed. -/
theorem actual_low_four_F18_light_class_closer {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s+1)) (hnot : ¬ IsHullVertex c p)
    (hp : rowScore lam (directionRow o e c p) = 1)
    (q : {i : Fin (s+1) // i ≠ p})
    (hq : rowScore lam (directionRow o e c q) = 1) :
    ∃ j : {i : Fin (s+1) // i ≠ p}, j ≠ q ∧
      (actualPartition (by omega : 2 ≤ s+1) o e he H.legality
        (low_model_scale o e H) p hnot hp).classOf j =
      (actualPartition (by omega : 2 ≤ s+1) o e he H.legality
        (low_model_scale o e H) p hnot hp).classOf q ∧
      dist (c q) (c j) < dist (c q) (c p) := by
  obtain ⟨j,hjq,hclass⟩ := actual_low_four_F18_light_class_companion
    hs o e he H hF p hnot hp q hq
  let D := actualPartition (by omega : 2 ≤ s+1) o e he H.legality
    (low_model_scale o e H) p hnot hp
  have hang := D.same_angle q j hclass.symm
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  have hlo : 2*Real.pi/9 < lam := by rw [← hrho]; exact H.scale_lower
  have hsmall : ∠ (c q) (c p) (c j) < lam/2 := by linarith
  have hqj : (q : Fin (s+1)) ≠ j := by
    intro heq
    exact hjq (Subtype.ext heq.symm)
  exact ⟨j,hjq,hclass,SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
    H.legality q.property.symm j.property.symm hqj hsmall⟩

#print axioms actual_low_four_F18_score_ge_one
#print axioms actual_low_four_F18_light_incoming_gain_zero
#print axioms actual_class_companion_of_zero_gain
#print axioms actual_low_four_F18_light_class_companion
#print axioms actual_low_four_F18_pure_light_class_card_ge_two
#print axioms actual_interior_one_all_zero_class_card_ge_two
#print axioms actual_interior_one_all_zero_card_ge_seven
#print axioms actual_low_four_F18_light_class_closer

end Jsp404.ActualInteriorOneClassSize
