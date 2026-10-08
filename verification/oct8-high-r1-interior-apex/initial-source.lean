import Jsp000404.ActualHighR1InteriorClassWeight
import Jsp000404.FullHullInteriorDefect

set_option autoImplicit false

/-!
SOURCE_ONLY positive HIGH4 R1 interior-apex constraints. Every actual
partition and original class weight is produced internally. The physical
SAT-pair angle bound is extracted from a genuine actual SAT chart.
No LOW half-scale bound, nearest-point fact, caller classes, gain budget,
potential or cardinality assumption is used. This does not prove R1 capacity.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualHighR1InteriorApex

open ActualF18ClassWeight
open ActualHighR1InteriorClassWeight

private theorem actual_triangle_sum {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (p q r : Fin t) (hpq : p ≠ q) :
    ∠ (c q) (c p) (c r) + ∠ (c p) (c q) (c r) +
      ∠ (c p) (c r) (c q) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c p) (p₂ := c q) (c r) (hleg.inj.ne hpq.symm)
  rw [EuclideanGeometry.angle_comm (c q) (c r) (c p),
    EuclideanGeometry.angle_comm (c r) (c p) (c q)] at hsum
  linarith only [hsum]

/-- This is an unsigned physical angle bound, not a projective claim. -/
private theorem sat_chart_pair_angle_le {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin (s+1) → Plane₂} {v : Fin (s+1)} {theta : Fin s → ℝ}
    (C : SatChart o e 4 lam c v theta) (p q : Fin (s+1))
    (hpv : p ≠ v) (hqv : q ≠ v) :
    ∠ (c p) (c v) (c q) ≤ Real.pi-4*lam := by
  obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq hpv
  obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hqv
  have hico (k : Fin s) : theta k ∈ Set.Ico 0 Real.pi := by
    refine ⟨(C.htheta k).1.1, ?_⟩
    have hk := (C.htheta k).1.2
    linarith only [hk,C.hlam]
  change InnerProductGeometry.angle (c (v.succAbove i)-c v)
    (c (v.succAbove j)-c v) ≤ Real.pi-4*lam
  rw [angle_eq_abs_of_half_plane_chart o C.he
    (sub_ne_zero.mpr (C.hleg.inj.ne (Fin.succAbove_ne v i)))
    (sub_ne_zero.mpr (C.hleg.inj.ne (Fin.succAbove_ne v j)))
    (hico i) (hico j) (C.htheta i).2 (C.htheta j).2]
  exact abs_le.mpr
    ⟨by linarith only [(C.htheta j).1.1,(C.htheta i).1.2],
      by linarith only [(C.htheta j).1.2,(C.htheta i).1.1]⟩

private theorem interior_score_one {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p) :
    rowScore lam (directionRow o e c p) = 1 := by
  have F := ActualHighR1PositiveCriticalProfile.actual_high_r1_positive_critical_profile
    o e he H v hsat a ha hpositive
  have hd := FullHullInteriorDefect.rowDefect_ge_three_of_not_hull_vertex
    o e he H.legality F.floor_four p hp
  have hc := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by have := H.card_ge_three; omega) F.floor_four
  have hs := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hc
  have hpos := hpositive p
  omega

/-- Canonical actual class choice. Its score-one premise is internal. -/
noncomputable def actualClassWeight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p) : ActualHighR1InteriorClassWeight.Data o e c lam v p :=
  Classical.choice (exists_actual_high_r1_interior_class_weight o e he H v hsat a ha
    hpositive p (interior_score_one o e he H v hsat a ha hpositive p hp) hp)

private theorem no_apex_of_actual_weights {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin t → Plane₂} {v : Fin t}
    (hleg : Section4Legality c lam) (hlo : Real.pi/5 < lam)
    (hsatAngle : ∀ p q : Fin t, p ≠ v → q ≠ v →
      ∠ (c p) (c v) (c q) ≤ Real.pi-4*lam)
    (p q : Fin t) (hpq : p ≠ q)
    (P : ActualHighR1InteriorClassWeight.Data o e c lam v p) (Q : ActualHighR1InteriorClassWeight.Data o e c lam v q) :
    P.partition.classOf ⟨q,hpq.symm⟩ ≠ 1 := by
  classical
  intro hqapex
  let k : Fin 3 := Q.partition.classOf ⟨p,hpq⟩
  have hvp := P.ne_center P.satClass v P.sat_mem
  have hvq := Q.ne_center Q.satClass v Q.sat_mem
  have hsame (b : Fin 3) (hb : b ≠ 1) (r : Fin t)
      (hr : r ∈ P.classMembers b) : r ∈ Q.classMembers k := by
    have hrp := P.ne_center b r hr
    have hrc := (P.mem_iff b r hrp).mp hr
    have hrq : r ≠ q := by
      intro h
      subst r
      exact hb (hrc.symm.trans hqapex)
    have hbig := P.partition.apex_angle ⟨q,hpq.symm⟩ ⟨r,hrp⟩ hqapex
      (fun h => hb (hrc.symm.trans h))
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
  have hvsat := (P.mem_iff P.satClass v hvp).mp P.sat_mem
  by_cases hvapex : P.partition.classOf ⟨v,hvp⟩ = 1
  · have hsmallP := P.partition.same_angle ⟨q,hpq.symm⟩ ⟨v,hvp⟩
      (hqapex.trans hvapex.symm)
    have hsmallV := hsatAngle p q hvp.symm hvq.symm
    have hvnot : v ∉ Q.classMembers k := by
      intro hmem
      have hvclass := (Q.mem_iff k v hvq).mp hmem
      have hsmallQ := Q.partition.same_angle ⟨p,hpq⟩ ⟨v,hvq⟩ hvclass.symm
      have hsum := actual_triangle_sum hleg p q v hpq
      linarith only [hsmallP,hsmallV,hsmallQ,hsum,hlo,Real.pi_pos]
    have hcap := Q.weight_le_eight_of_sat_not_mem k hvnot
    omega
  · have hnot1 : P.satClass ≠ 1 := fun h => hvapex (hvsat.trans h)
    have hlabels (b : Fin 3) : b = 0 ∨ b = 1 ∨ b = 2 := by
      fin_cases b <;> simp
    have height := P.sat_weight_ge_eight
    have hcap := Q.weight_le_twelve k
    rcases hlabels P.satClass with hv0 | hv1 | hv2
    · rw [hv0] at height
      omega
    · exact False.elim (hnot1 hv1)
    · rw [hv2] at height
      omega

/-- Two original interiors avoid each other's canonical apex classes. -/
theorem actual_two_interior_not_apex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q))
    (p q : Fin (s+1)) (hp : ¬ IsHullVertex c p) (hq : ¬ IsHullVertex c q)
    (hpq : p ≠ q) :
    (actualClassWeight o e he H v hsat a ha hpositive p hp).partition.classOf
      ⟨q,hpq.symm⟩ ≠ 1 := by
  obtain ⟨E⟩ := ActualHighR1PositiveCriticalProfile.exists_actual_high_r1_positive_critical_endpoint
    o e he H v hsat a ha hpositive
  exact no_apex_of_actual_weights H.legality H.scale_lower
    (sat_chart_pair_angle_le E.chart) p q hpq
    (actualClassWeight o e he H v hsat a ha hpositive p hp)
    (actualClassWeight o e he H v hsat a ha hpositive q hq)

/-- An interior's canonical actual apex contains only original hull points. -/
theorem actual_interior_apex_full_hull {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p) :
    ∀ q ∈ (actualClassWeight o e he H v hsat a ha hpositive p hp).classMembers 1,
      IsHullVertex c q := by
  intro q hmem
  by_contra hq
  let P := actualClassWeight o e he H v hsat a ha hpositive p hp
  have hqp := P.ne_center 1 q hmem
  have hno := actual_two_interior_not_apex o e he H v hsat a ha hpositive p q hp hq hqp.symm
  exact hno ((P.mem_iff 1 q hqp).mp hmem)

/-- Distinct original interiors have disjoint actual canonical apex blocks. -/
theorem actual_two_interior_apex_disjoint {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q))
    (p q : Fin (s+1)) (hp : ¬ IsHullVertex c p) (hq : ¬ IsHullVertex c q)
    (hpq : p ≠ q) :
    Disjoint ((actualClassWeight o e he H v hsat a ha hpositive p hp).classMembers 1)
      ((actualClassWeight o e he H v hsat a ha hpositive q hq).classMembers 1) := by
  classical
  let P := actualClassWeight o e he H v hsat a ha hpositive p hp
  let Q := actualClassWeight o e he H v hsat a ha hpositive q hq
  have hpqno := actual_two_interior_not_apex o e he H v hsat a ha hpositive p q hp hq hpq
  have hqpno := actual_two_interior_not_apex o e he H v hsat a ha hpositive q p hq hp hpq.symm
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
  linarith only [hbigP,hbigQ,hsum,hthird,H.scale_lower,Real.pi_pos]

/-- Original non-hull indices; no selected subset hull is used. -/
noncomputable def interiorIndices {t : ℕ} (c : Fin t → Plane₂) : Finset (Fin t) := by
  classical
  exact Finset.univ.filter (fun p => ¬ IsHullVertex c p)

/-- Weighted disjoint original apex blocks bound the original interiors. -/
theorem actual_interior_count_le_three {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q)) :
    (interiorIndices c).card ≤ 3 := by
  classical
  let I := interiorIndices c
  let A (p : Fin (s+1)) : Finset (Fin (s+1)) :=
    if hp : ¬ IsHullVertex c p then
      (actualClassWeight o e he H v hsat a ha hpositive p hp).classMembers 1 else ∅
  have hnot (p : Fin (s+1)) (hp : p ∈ I) : ¬ IsHullVertex c p :=
    (Finset.mem_filter.mp hp).2
  have hA (p : Fin (s+1)) (hp : p ∈ I) : A p =
      (actualClassWeight o e he H v hsat a ha hpositive p (hnot p hp)).classMembers 1 := by
    simp only [A,dif_pos (hnot p hp)]
  have hpair : Set.PairwiseDisjoint (↑I : Set (Fin (s+1))) A := by
    intro p hp q hq hpq
    rw [hA p hp,hA q hq]
    exact actual_two_interior_apex_disjoint o e he H v hsat a ha hpositive
      p q (hnot p hp) (hnot q hq) hpq
  let U := I.biUnion A
  have hdisjoint : Disjoint U I := by
    apply Finset.disjoint_left.mpr
    intro r hr hri
    obtain ⟨p,hp,hrp⟩ := Finset.mem_biUnion.mp hr
    rw [hA p hp] at hrp
    have hrHull := actual_interior_apex_full_hull o e he H v hsat a ha hpositive
      p (hnot p hp) r hrp
    exact hnot r hri hrHull
  have hmassU : originalWeight o e c lam U = ∑ p ∈ I, originalWeight o e c lam (A p) := by
    unfold originalWeight
    exact Finset.sum_biUnion hpair
  have hfour : 4*I.card ≤ originalWeight o e c lam U := by
    rw [hmassU]
    have h : (∑ _p ∈ I, (4 : ℕ)) ≤ ∑ p ∈ I, originalWeight o e c lam (A p) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [hA p hp]
      exact (actualClassWeight o e he H v hsat a ha hpositive p (hnot p hp)).weight_ge_four 1
    simpa only [Finset.sum_const,smul_eq_mul,Nat.mul_comm] using h
  have hmassI : originalWeight o e c lam I = 2*I.card := by
    unfold originalWeight
    calc
      (∑ p ∈ I, 2 ^ rowScore lam (directionRow o e c p)) = ∑ _p ∈ I, (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [interior_score_one o e he H v hsat a ha hpositive p (hnot p hp),pow_one]
      _ = 2*I.card := by simp only [Finset.sum_const,smul_eq_mul,Nat.mul_comm]
  have hbudget : originalWeight o e c lam U + originalWeight o e c lam I ≤ 22 := by
    have hmono : originalWeight o e c lam (U ∪ I) ≤
        originalWeight o e c lam Finset.univ := by
      unfold originalWeight
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    have F := ActualHighR1PositiveCriticalProfile.actual_high_r1_positive_critical_profile
      o e he H v hsat a ha hpositive
    have htotal : originalWeight o e c lam Finset.univ = 22 := by
      simpa only [originalWeight,potential,exponentAt,directionRows] using F.potential_eq
    have hunion : originalWeight o e c lam (U ∪ I) =
        originalWeight o e c lam U + originalWeight o e c lam I := by
      unfold originalWeight
      exact Finset.sum_union hdisjoint
    rw [hunion,htotal] at hmono
    exact hmono
  change I.card ≤ 3
  omega

#print axioms actualClassWeight
#print axioms actual_two_interior_not_apex
#print axioms actual_interior_apex_full_hull
#print axioms actual_two_interior_apex_disjoint
#print axioms actual_interior_count_le_three

end Jsp404.ActualHighR1InteriorApex
