import Jsp000404.ActualF18Frame
import Jsp000404.ActualInteriorOneClassSize

set_option autoImplicit false

/-! SOURCE_ONLY. Original weighted classes at an original F18 interior
center. The actual partition and original-index class sets are selected
internally. A heavy singleton is permitted; only a light singleton is
excluded by the original target's incoming-zero conclusion.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18ClassWeight

noncomputable def originalWeight {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) (S : Finset (Fin t)) : ℕ :=
  ∑ q ∈ S, 2 ^ rowScore lam (directionRow o e c q)

/-- Original point indices in an actual partition class. -/
noncomputable def classMembers {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) : Finset (Fin t) :=
  (ActualInteriorOneClassSize.members D k).image
    (fun q : {q : Fin t // q ≠ p} => q.val)

theorem classMembers_ne_center {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3)
    {q : Fin t} (hq : q ∈ classMembers D k) : q ≠ p := by
  classical
  obtain ⟨v,_hv,hvq⟩ := Finset.mem_image.mp hq
  intro hqp
  exact v.property (hvq.trans hqp)

theorem classMembers_mem_iff {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3)
    (q : Fin t) (hqp : q ≠ p) :
    q ∈ classMembers D k ↔ D.classOf ⟨q,hqp⟩ = k := by
  classical
  constructor
  · intro hq
    obtain ⟨v,hv,hvq⟩ := Finset.mem_image.mp hq
    have hc := (Finset.mem_filter.mp hv).2
    have heq : v = ⟨q,hqp⟩ := Subtype.ext hvq
    simpa only [heq] using hc
  · intro hc
    exact Finset.mem_image.mpr
      ⟨⟨q,hqp⟩,by simp [ActualInteriorOneClassSize.members,hc],rfl⟩

theorem classMembers_nonempty {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    (classMembers D k).Nonempty := by
  classical
  exact ⟨D.witness k,(classMembers_mem_iff D k _ (D.witness k).property).2
    (D.witness_class k)⟩

theorem classMembers_disjoint {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (D : ActualInteriorOnePartition.Data c lam p) {k l : Fin 3} (hkl : k ≠ l) :
    Disjoint (classMembers D k) (classMembers D l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hq hk
  have hqp := classMembers_ne_center D k hq
  exact hkl (((classMembers_mem_iff D k q hqp).mp hq).symm.trans
    ((classMembers_mem_iff D l q hqp).mp hk))

theorem classMembers_cover {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (D : ActualInteriorOnePartition.Data c lam p) :
    (classMembers D 0 ∪ classMembers D 1) ∪ classMembers D 2 = Finset.univ.erase p := by
  classical
  have hlabels (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  ext q
  constructor
  · intro hq
    have hqp : q ≠ p := by
      rcases Finset.mem_union.mp hq with hq | hq
      · rcases Finset.mem_union.mp hq with hq | hq
        · exact classMembers_ne_center D 0 hq
        · exact classMembers_ne_center D 1 hq
      · exact classMembers_ne_center D 2 hq
    simp [hqp]
  · intro hq
    have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
    rcases hlabels (D.classOf ⟨q,hqp⟩) with hc | hc | hc
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((classMembers_mem_iff D 0 q hqp).2 hc))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((classMembers_mem_iff D 1 q hqp).2 hc))
    · exact Finset.mem_union_right _ ((classMembers_mem_iff D 2 q hqp).2 hc)

theorem originalWeight_classMembers_sum {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (D : ActualInteriorOnePartition.Data c lam p) :
    (∑ k : Fin 3, originalWeight o e c lam (classMembers D k)) =
      originalWeight o e c lam (Finset.univ.erase p) := by
  classical
  have h01 := classMembers_disjoint D (by decide : (0 : Fin 3) ≠ 1)
  have h02 := classMembers_disjoint D (by decide : (0 : Fin 3) ≠ 2)
  have h12 := classMembers_disjoint D (by decide : (1 : Fin 3) ≠ 2)
  have h012 : Disjoint (classMembers D 0 ∪ classMembers D 1) (classMembers D 2) := by
    apply Finset.disjoint_left.mpr
    intro q hq hq2
    rcases Finset.mem_union.mp hq with hq0 | hq1
    · exact Finset.disjoint_left.mp h02 hq0 hq2
    · exact Finset.disjoint_left.mp h12 hq1 hq2
  unfold originalWeight
  rw [Fin.sum_univ_three,← Finset.sum_union h01,← Finset.sum_union h012,classMembers_cover D]

/-- Actual original partition, plain original-index classes, and weights.
These fields are all internally produced by the public theorem below. -/
structure Data {t : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) (p : Fin t) where
  partition : ActualInteriorOnePartition.Data c lam p
  score_one : rowScore lam (directionRow o e c p) = 1
  classMembers : Fin 3 → Finset (Fin t)
  mem_iff : ∀ k q (hqp : q ≠ p), q ∈ classMembers k ↔ partition.classOf ⟨q,hqp⟩ = k
  ne_center : ∀ k q, q ∈ classMembers k → q ≠ p
  disjoint : ∀ {k l : Fin 3}, k ≠ l → Disjoint (classMembers k) (classMembers l)
  weight_ge_four : ∀ k, 4 ≤ originalWeight o e c lam (classMembers k)
  weight_sum : (∑ k : Fin 3, originalWeight o e c lam (classMembers k)) = 16

/-- A singleton light class emits at the original observer. Heavy
singleton classes have weight four and are deliberately allowed. -/
private theorem class_weight_ge_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (F : ActualF18Frame.Frame o e c lam)
    (p : Fin (s+1)) (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    4 ≤ originalWeight o e c lam (classMembers D k) := by
  classical
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  have hpoint (q : Fin (s+1)) : 2 ≤ 2 ^ rowScore lam (directionRow o e c q) := by
    rcases F.score_one_or_two q with hq | hq <;> simp [hq]
  have hmass : 2 * (classMembers D k).card ≤ originalWeight o e c lam (classMembers D k) := by
    have h := Finset.sum_le_sum (fun q (_hq : q ∈ classMembers D k) => hpoint q)
    simpa only [originalWeight,Finset.sum_const,smul_eq_mul,Nat.mul_comm] using h
  by_cases hcard : 2 ≤ (classMembers D k).card
  · omega
  have hpos : 0 < (classMembers D k).card := (classMembers_nonempty D k).card_pos
  have hone : (classMembers D k).card = 1 := by omega
  obtain ⟨q,hset⟩ := Finset.card_eq_one.mp hone
  have hqmem : q ∈ classMembers D k := by rw [hset]; simp
  have hqp := classMembers_ne_center D k hqmem
  have hqclass := (classMembers_mem_iff D k q hqp).mp hqmem
  rcases F.score_one_or_two q with hqone | hqtwo
  · have hgain : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
      apply rowGain_pos_of_forall_angle_ge o e c H.legality he hqp.symm H.card_ge_three
      intro j hjp hjq
      have hdiff : D.classOf ⟨q,hqp⟩ ≠ D.classOf ⟨j,hjp⟩ := by
        intro hsame
        have hjmem : j ∈ classMembers D k :=
          (classMembers_mem_iff D k j hjp).2 (hsame.symm.trans hqclass)
        have hjeq : j = q := by simpa only [hset,Finset.mem_singleton] using hjmem
        exact hjq hjeq
      have hangle := D.different_angle ⟨q,hqp⟩ ⟨j,hjp⟩ hdiff
      linarith [H.legality.lam_pos]
    have hzero := ActualInteriorOneClassSize.actual_low_four_F18_light_incoming_gain_zero
      hs o e H hF q hqone p hqp.symm
    omega
  · simp [originalWeight,hset,hqtwo]

/-- The original F18 Model internally produces its interior point's
actual score-one partition and all original class weights. -/
theorem exists_actual_F18_interior_class_weight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s+1)) (hnot : ¬ IsHullVertex c p) :
    Nonempty (Data o e c lam p) := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hp : rowScore lam (directionRow o e c p) = 1 := by
    rcases F.score_one_or_two p with hp | hp
    · exact hp
    · exact False.elim (hnot (F.heavy_full_hull p hp))
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  have h5 : Real.pi/5 < lam := by linarith [F.scale_lower,Real.pi_pos]
  let D := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s+1)
    o e he H.legality h5 p hnot hp
  have hweight : ∀ k, 4 ≤ originalWeight o e c lam (classMembers D k) :=
    class_weight_ge_four o e he H hF F p D
  have hmass : originalWeight o e c lam (Finset.univ.erase p) + 2 = 18 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (s+1)))
      (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ p)
    have hfull : (∑ q : Fin (s+1), 2 ^ rowScore lam (directionRow o e c q)) = 18 := by
      simpa only [potential,exponentAt,directionRows] using hF
    rw [hp,pow_one,hfull] at h
    exact h
  have hsum : (∑ k : Fin 3, originalWeight o e c lam (classMembers D k)) = 16 := by
    rw [originalWeight_classMembers_sum o e D]
    omega
  exact ⟨{
    partition := D
    score_one := hp
    classMembers := classMembers D
    mem_iff := classMembers_mem_iff D
    ne_center := fun k q hq => classMembers_ne_center D k hq
    disjoint := fun {k l} hkl => classMembers_disjoint D hkl
    weight_ge_four := hweight
    weight_sum := hsum }⟩

#print axioms classMembers_ne_center
#print axioms classMembers_mem_iff
#print axioms classMembers_nonempty
#print axioms classMembers_disjoint
#print axioms classMembers_cover
#print axioms originalWeight_classMembers_sum
#print axioms exists_actual_F18_interior_class_weight

end Jsp404.ActualF18ClassWeight
