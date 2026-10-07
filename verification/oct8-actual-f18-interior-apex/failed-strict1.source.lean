import Jsp000404.ActualF18ClassWeight

set_option autoImplicit false

/-!
SOURCE_ONLY: original F18 interior apex constraints.
The weighted actual partitions are produced internally. No all-light
profile, number of interior points, supplied classes or mass budget is
accepted by the public declarations.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18InteriorApex

open ActualF18ClassWeight

private theorem actual_triangle_sum {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (p q r : Fin t) (hpq : p ≠ q) :
    ∠ (c q) (c p) (c r) + ∠ (c p) (c q) (c r) +
      ∠ (c p) (c r) (c q) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c p) (p₂ := c q) (c r) (hleg.inj.ne hpq.symm)
  rw [EuclideanGeometry.angle_comm (c q) (c r) (c p),
    EuclideanGeometry.angle_comm (c r) (c p) (c q)] at hsum
  linarith only [hsum]

private theorem class_weight_le_eight {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (W : Data o e c lam p) (k : Fin 3) :
    originalWeight o e c lam (W.classMembers k) ≤ 8 := by
  have hsum : originalWeight o e c lam (W.classMembers 0) +
      originalWeight o e c lam (W.classMembers 1) +
      originalWeight o e c lam (W.classMembers 2) = 16 := by
    simpa only [Fin.sum_univ_three,Nat.add_assoc] using W.weight_sum
  have h0 := W.weight_ge_four 0
  have h1 := W.weight_ge_four 1
  have h2 := W.weight_ge_four 2
  fin_cases k <;> omega

private theorem no_apex_of_class_weights {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : Real.pi/5 < lam)
    (p q : Fin t) (hpq : p ≠ q)
    (P : Data o e c lam p) (Q : Data o e c lam q) :
    P.partition.classOf ⟨q,hpq.symm⟩ ≠ 1 := by
  classical
  intro hqapex
  let k : Fin 3 := Q.partition.classOf ⟨p,hpq⟩
  have hsame (a : Fin 3) (ha : a ≠ 1) (r : Fin t)
      (hr : r ∈ P.classMembers a) : r ∈ Q.classMembers k := by
    have hrp := P.ne_center a r hr
    have hrc := (P.mem_iff a r hrp).mp hr
    have hrq : r ≠ q := by
      intro h
      subst r
      exact ha (hrc.symm.trans hqapex)
    have hbig := P.partition.apex_angle ⟨q,hpq.symm⟩ ⟨r,hrp⟩ hqapex
      (fun h => ha (hrc.symm.trans h))
    apply (Q.mem_iff k r hrq).mpr
    by_contra hdiff
    have hlarge := Q.partition.different_angle ⟨r,hrq⟩ ⟨p,hpq⟩ hdiff
    rw [EuclideanGeometry.angle_comm (c r) (c q) (c p)] at hlarge
    have hsum := actual_triangle_sum hleg p q r hpq
    have hthird := EuclideanGeometry.angle_nonneg (c p) (c r) (c q)
    linarith only [hbig,hlarge,hsum,hthird,hlo]
  have hpnot : p ∉ P.classMembers 0 ∪ P.classMembers 2 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact P.ne_center 0 p h rfl
    · exact P.ne_center 2 p h rfl
  have hsub : insert p (P.classMembers 0 ∪ P.classMembers 2) ⊆ Q.classMembers k := by
    intro r hr
    rcases Finset.mem_insert.mp hr with h | h
    · subst r
      exact (Q.mem_iff k p hpq).mpr rfl
    · rcases Finset.mem_union.mp h with h | h
      · exact hsame 0 (by decide : (0 : Fin 3) ≠ 1) r h
      · exact hsame 2 (by decide : (2 : Fin 3) ≠ 1) r h
  have hmass : originalWeight o e c lam
      (insert p (P.classMembers 0 ∪ P.classMembers 2)) =
      2 + originalWeight o e c lam (P.classMembers 0) +
        originalWeight o e c lam (P.classMembers 2) := by
    unfold originalWeight
    rw [Finset.sum_insert hpnot,
      Finset.sum_union (P.disjoint (by decide : (0 : Fin 3) ≠ 2)),P.score_one]
    simp only [pow_one,Nat.add_assoc]
  have hmono : originalWeight o e c lam
      (insert p (P.classMembers 0 ∪ P.classMembers 2)) ≤
      originalWeight o e c lam (Q.classMembers k) := by
    unfold originalWeight
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have h0 := P.weight_ge_four 0
  have h2 := P.weight_ge_four 2
  have hcap := class_weight_le_eight Q k
  omega

/-- A fixed choice of an actual weighted partition produced from an
original F18 interior point. Its score-one property is derived internally. -/
noncomputable def actualClassWeight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p) : Data o e c lam p :=
  Classical.choice (exists_actual_F18_interior_class_weight o e he H hF p hp)

/-- Any two distinct original interior points avoid each other's
internally produced original apex classes in an F18 model. -/
theorem actual_two_interior_not_apex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p q : Fin (s+1)) (hp : ¬ IsHullVertex c p) (hq : ¬ IsHullVertex c q)
    (hpq : p ≠ q) :
    (actualClassWeight o e he H hF p hp).partition.classOf ⟨q,hpq.symm⟩ ≠ 1 := by
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hlo : Real.pi/5 < lam := by linarith only [F.scale_lower,Real.pi_pos]
  exact no_apex_of_class_weights H.legality hlo p q hpq
    (actualClassWeight o e he H hF p hp) (actualClassWeight o e he H hF q hq)

/-- Every actual member of an original interior apex class is an
original full-configuration hull point. -/
theorem actual_interior_apex_full_hull {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p) :
    ∀ q ∈ (actualClassWeight o e he H hF p hp).classMembers 1,
      IsHullVertex c q := by
  intro q hmem
  by_contra hq
  let P := actualClassWeight o e he H hF p hp
  have hqp := P.ne_center 1 q hmem
  have hno := actual_two_interior_not_apex o e he H hF p q hp hq hqp.symm
  exact hno ((P.mem_iff 1 q hqp).mp hmem)

/-- Distinct original interior points have disjoint internally
produced actual apex blocks in every original F18 model. -/
theorem actual_two_interior_apex_disjoint {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p q : Fin (s+1)) (hp : ¬ IsHullVertex c p) (hq : ¬ IsHullVertex c q)
    (hpq : p ≠ q) :
    Disjoint ((actualClassWeight o e he H hF p hp).classMembers 1)
      ((actualClassWeight o e he H hF q hq).classMembers 1) := by
  classical
  let P := actualClassWeight o e he H hF p hp
  let Q := actualClassWeight o e he H hF q hq
  have hpqno := actual_two_interior_not_apex o e he H hF p q hp hq hpq
  have hqpno := actual_two_interior_not_apex o e he H hF q p hq hp hpq.symm
  apply Finset.disjoint_left.mpr
  intro r hrP hrQ
  have hrp := P.ne_center 1 r hrP
  have hrq := Q.ne_center 1 r hrQ
  have hcP := (P.mem_iff 1 r hrp).mp hrP
  have hcQ := (Q.mem_iff 1 r hrq).mp hrQ
  have hbigP := P.partition.apex_angle ⟨r,hrp⟩ ⟨q,hpq.symm⟩ hcP hpqno
  have hbigQ := Q.partition.apex_angle ⟨r,hrq⟩ ⟨p,hpq⟩ hcQ hqpno
  rw [EuclideanGeometry.angle_comm (c r) (c p) (c q)] at hbigP
  rw [EuclideanGeometry.angle_comm (c r) (c q) (c p)] at hbigQ
  have hsum := actual_triangle_sum H.legality p q r hpq
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c r) (c q)
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  linarith only [hbigP,hbigQ,hsum,hthird,F.scale_lower,Real.pi_pos]

#print axioms actualClassWeight
#print axioms actual_two_interior_not_apex
#print axioms actual_interior_apex_full_hull
#print axioms actual_two_interior_apex_disjoint

end Jsp404.ActualF18InteriorApex
