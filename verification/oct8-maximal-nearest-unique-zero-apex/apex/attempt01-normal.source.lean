import Jsp000404.ActualF17UniqueZeroClassWeight
import Jsp000404.ActualHeavyClumpWeight

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY original unique-zero F17 apex consumers. All actual weighted
partitions and heavy clumps are produced internally from the original
Model. Class masses use the checked 3/4/7/8 unique-zero bounds, not the
F18 four-per-class bound. The unique zero may remain an original interior.

The local triangle and finite-weight arguments are adapted from the
checked ActualF18InteriorApex/ActualF18NonacuteApex proofs, with the
different original masses made explicit. No private declaration is used.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF17UniqueZeroInteriorApex

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

private theorem actual_scale_lower {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    {c : Fin t → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 t c lam) :
    2 * Real.pi / 9 < lam := by
  have hrho : Real.pi / ((4 : ℝ) + 1 / 2) = 2 * Real.pi / 9 := by ring
  rw [← hrho]
  exact H.scale_lower

private theorem nonapex_original_mass_ge_nine {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    {c : Fin t → Plane₂} {lam : ℝ} {z p : Fin t}
    (P : ActualF17UniqueZeroClassWeight.Data o e c lam z p) :
    9 ≤ originalWeight o e c lam (insert p (P.classMembers 0 ∪ P.classMembers 2)) := by
  classical
  have hpnot : p ∉ P.classMembers 0 ∪ P.classMembers 2 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact P.ne_center 0 p h rfl
    · exact P.ne_center 2 p h rfl
  have hmass : originalWeight o e c lam
      (insert p (P.classMembers 0 ∪ P.classMembers 2)) =
      2 + originalWeight o e c lam (P.classMembers 0) +
        originalWeight o e c lam (P.classMembers 2) := by
    unfold originalWeight
    rw [Finset.sum_insert hpnot,
      Finset.sum_union (P.disjoint (by decide : (0 : Fin 3) ≠ 2)), P.score_one]
    simp only [pow_one, Nat.add_assoc]
  have hpair := P.pair_weight_ge_seven 0 2 (by decide : (0 : Fin 3) ≠ 2)
  omega

private theorem weight_mono {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin t → Plane₂) (lam : ℝ)
    {S T : Finset (Fin t)} (hST : S ⊆ T) :
    originalWeight o e c lam S ≤ originalWeight o e c lam T := by
  classical
  unfold originalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => Nat.zero_le _)

private theorem no_apex_of_class_weights {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    {c : Fin t → Plane₂} {lam : ℝ} {z : Fin t}
    (hleg : Section4Legality c lam) (hlo : Real.pi / 5 < lam)
    (p q : Fin t) (hpq : p ≠ q)
    (P : ActualF17UniqueZeroClassWeight.Data o e c lam z p)
    (Q : ActualF17UniqueZeroClassWeight.Data o e c lam z q) :
    P.partition.classOf ⟨q, hpq.symm⟩ ≠ 1 := by
  classical
  intro hqapex
  let k : Fin 3 := Q.partition.classOf ⟨p, hpq⟩
  have hsame (a : Fin 3) (ha : a ≠ 1) (r : Fin t)
      (hr : r ∈ P.classMembers a) : r ∈ Q.classMembers k := by
    have hrp := P.ne_center a r hr
    have hrc := (P.mem_iff a r hrp).mp hr
    have hrq : r ≠ q := by
      intro h
      subst r
      exact ha (hrc.symm.trans hqapex)
    have hbig := P.partition.apex_angle ⟨q, hpq.symm⟩ ⟨r, hrp⟩ hqapex
      (fun h => ha (hrc.symm.trans h))
    apply (Q.mem_iff k r hrq).mpr
    by_contra hdiff
    have hlarge := Q.partition.different_angle ⟨r, hrq⟩ ⟨p, hpq⟩ hdiff
    rw [EuclideanGeometry.angle_comm (c r) (c q) (c p)] at hlarge
    have hsum := actual_triangle_sum hleg p q r hpq
    have hthird := EuclideanGeometry.angle_nonneg (c p) (c r) (c q)
    linarith only [hbig, hlarge, hsum, hthird, hlo]
  have hsub : insert p (P.classMembers 0 ∪ P.classMembers 2) ⊆ Q.classMembers k := by
    intro r hr
    rcases Finset.mem_insert.mp hr with h | h
    · subst r
      exact (Q.mem_iff k p hpq).mpr rfl
    · rcases Finset.mem_union.mp h with h | h
      · exact hsame 0 (by decide : (0 : Fin 3) ≠ 1) r h
      · exact hsame 2 (by decide : (2 : Fin 3) ≠ 1) r h
  have hmass := nonapex_original_mass_ge_nine P
  have hmono := weight_mono o e c lam hsub
  have hcap := Q.weight_le_eight k
  omega

/-- A fixed choice of the checked actual unique-zero weighted producer.
No classes, original weight bounds or partition are caller inputs. -/
noncomputable def actualClassWeight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ q : Fin (s + 1), q ≠ z → 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hnot : ¬ IsHullVertex c p) : ActualF17UniqueZeroClassWeight.Data o e c lam z p :=
  Classical.choice (ActualF17UniqueZeroClassWeight.exists_actual_unique_zero_interior_class_weight
    o e he H z hz hpositive p hp hnot)

/-- Two distinct original score-one interior centers avoid each other's
internally produced apexes in the unique-original-zero subcase. -/
theorem actual_two_interior_not_apex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p q : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hq : rowScore lam (directionRow o e c q) = 1)
    (hpnot : ¬ IsHullVertex c p) (hqnot : ¬ IsHullVertex c q) (hpq : p ≠ q) :
    (actualClassWeight o e he H z hz hpositive p hp hpnot).partition.classOf
      ⟨q, hpq.symm⟩ ≠ 1 := by
  have hscale := actual_scale_lower H
  have hlo : Real.pi / 5 < lam := by linarith only [hscale, Real.pi_pos]
  exact no_apex_of_class_weights H.legality hlo p q hpq
    (actualClassWeight o e he H z hz hpositive p hp hpnot)
    (actualClassWeight o e he H z hz hpositive q hq hqnot)

/-- An original score-one interior apex contains only original hull
vertices and possibly the unique zero itself, even when that zero is interior. -/
theorem actual_interior_apex_full_hull_or_zero {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hpnot : ¬ IsHullVertex c p) :
    ∀ q ∈ (actualClassWeight o e he H z hz hpositive p hp hpnot).classMembers 1,
      IsHullVertex c q ∨ q = z := by
  intro q hmem
  by_cases hqz : q = z
  · exact Or.inr hqz
  · apply Or.inl
    by_contra hqnot
    let P := actualClassWeight o e he H z hz hpositive p hp hpnot
    have hqp := P.ne_center 1 q hmem
    obtain ⟨hn, _hlow, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
      (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
    have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos q
      (by have := H.card_ge_three; omega : 2 ≤ s + 1) hn
    have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
    have hdef := FullHullInteriorDefect.rowDefect_ge_three_of_not_hull_vertex
      o e he H.legality hn q hqnot
    have hqpos := hpositive q hqz
    have hqone : rowScore lam (directionRow o e c q) = 1 := by omega
    have hno := actual_two_interior_not_apex o e he H z hz hpositive
      p q hp hqone hpnot hqnot hqp.symm
    exact hno ((P.mem_iff 1 q hqp).mp hmem)

/-- Distinct original score-one interior centers have disjoint actual
apex sets. In particular at most one of them can contain the unique zero. -/
theorem actual_two_interior_apex_disjoint {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p q : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hq : rowScore lam (directionRow o e c q) = 1)
    (hpnot : ¬ IsHullVertex c p) (hqnot : ¬ IsHullVertex c q) (hpq : p ≠ q) :
    Disjoint ((actualClassWeight o e he H z hz hpositive p hp hpnot).classMembers 1)
      ((actualClassWeight o e he H z hz hpositive q hq hqnot).classMembers 1) := by
  classical
  let P := actualClassWeight o e he H z hz hpositive p hp hpnot
  let Q := actualClassWeight o e he H z hz hpositive q hq hqnot
  have hpqno := actual_two_interior_not_apex o e he H z hz hpositive
    p q hp hq hpnot hqnot hpq
  have hqpno := actual_two_interior_not_apex o e he H z hz hpositive
    q p hq hp hqnot hpnot hpq.symm
  apply Finset.disjoint_left.mpr
  intro r hrP hrQ
  have hrp := P.ne_center 1 r hrP
  have hrq := Q.ne_center 1 r hrQ
  have hcP := (P.mem_iff 1 r hrp).mp hrP
  have hcQ := (Q.mem_iff 1 r hrq).mp hrQ
  have hbigP := P.partition.apex_angle ⟨r, hrp⟩ ⟨q, hpq.symm⟩ hcP hpqno
  have hbigQ := Q.partition.apex_angle ⟨r, hrq⟩ ⟨p, hpq⟩ hcQ hqpno
  rw [EuclideanGeometry.angle_comm (c r) (c p) (c q)] at hbigP
  rw [EuclideanGeometry.angle_comm (c r) (c q) (c p)] at hbigQ
  have hsum := actual_triangle_sum H.legality p q r hpq
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c r) (c q)
  have hscale := actual_scale_lower H
  linarith only [hbigP, hbigQ, hsum, hthird, hscale, Real.pi_pos]

private theorem bool_not_ne_self (b : Bool) : (!b) ≠ b := by cases b <;> decide

private theorem clump_code_eq_of_three_scale {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (p h q : Fin t) (hph : p ≠ h) (hqh : q ≠ h)
    (G : ActualMaximalLowRowClumps.Data 4 o c lam h)
    (hbig : 3 * lam ≤ ∠ (c h) (c p) (c q)) :
    G.clumps.code q = G.clumps.code p := by
  by_contra hdiff
  have hlarge := G.clumps.different_angle_ge hleg q p hqh hph hdiff
  rw [EuclideanGeometry.angle_comm (c q) (c h) (c p)] at hlarge
  have hsum := actual_triangle_sum hleg p h q hph
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c q) (c h)
  linarith only [hbig, hlarge, hsum, hthird, hlo, Real.pi_pos]

private theorem clump_weights_sum {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin t → Plane₂} {lam : ℝ} {h : Fin t}
    (G : ActualMaximalLowRowClumps.Data 4 o c lam h) (b : Bool) :
    originalWeight o e c lam (ActualHeavyClumpWeight.members G b) +
      originalWeight o e c lam (ActualHeavyClumpWeight.members G (!b)) =
      originalWeight o e c lam (Finset.univ.erase h) := by
  classical
  have hd : Disjoint (ActualHeavyClumpWeight.members G b)
      (ActualHeavyClumpWeight.members G (!b)) := by
    apply Finset.disjoint_left.mpr
    intro q hqb hqnb
    have hcb := (Finset.mem_filter.mp hqb).2.2
    have hcnb := (Finset.mem_filter.mp hqnb).2.2
    exact bool_not_ne_self b (hcnb.symm.trans hcb)
  have hcover : ActualHeavyClumpWeight.members G b ∪
      ActualHeavyClumpWeight.members G (!b) = Finset.univ.erase h := by
    ext q
    cases b <;> cases hcode : G.clumps.code q <;>
      simp [ActualHeavyClumpWeight.members, hcode]
  unfold originalWeight
  rw [← Finset.sum_union hd, hcover]

/-- An original actual-wide score-two center is not in an original
score-one interior apex in the unique-zero subcase. Original heavy clumps
are produced internally; mass nine plus opposite mass five exceeds thirteen. -/
theorem actual_nonacute_heavy_not_in_interior_apex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ r : Fin (s + 1), r ≠ z → 1 ≤ rowScore lam (directionRow o e c r))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hpnot : ¬ IsHullVertex c p)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hwide : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c h) (c b)) :
    h ∉ (actualClassWeight o e he H z hz hpositive p hp hpnot).classMembers 1 := by
  classical
  let P := actualClassWeight o e he H z hz hpositive p hp hpnot
  change h ∉ P.classMembers 1
  intro hmem
  have hhp := P.ne_center 1 h hmem
  have hph := hhp.symm
  have hhclass := (P.mem_iff 1 h hhp).mp hmem
  obtain ⟨B⟩ := ActualHeavyClumpWeight.exists_actual_heavy_clump_weight o e he H h hh hwide
  let b := B.geometry.clumps.code p
  have hsub : insert p (P.classMembers 0 ∪ P.classMembers 2) ⊆
      ActualHeavyClumpWeight.members B.geometry b := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hrp | hr
    · subst r
      simp [ActualHeavyClumpWeight.members, b, hph]
    · have hsame (k : Fin 3) (hk : k ≠ 1) (hrk : r ∈ P.classMembers k) :
          B.geometry.clumps.code r = B.geometry.clumps.code p := by
        have hrp := P.ne_center k r hrk
        have hrclass := (P.mem_iff k r hrp).mp hrk
        have hrh : r ≠ h := by
          intro heq
          subst r
          exact hk (hrclass.symm.trans hhclass)
        have hrnon : P.partition.classOf ⟨r, hrp⟩ ≠ 1 := by
          intro heq
          exact hk (hrclass.symm.trans heq)
        have hbig := P.partition.apex_angle ⟨h, hhp⟩ ⟨r, hrp⟩ hhclass hrnon
        exact clump_code_eq_of_three_scale H.legality (actual_scale_lower H)
          p h r hph hrh B.geometry hbig
      have hrh : r ≠ h := by
        intro heq
        subst r
        rcases Finset.mem_union.mp hr with hr0 | hr2
        · exact (by decide : (0 : Fin 3) ≠ 1)
            (((P.mem_iff 0 h hhp).mp hr0).symm.trans hhclass)
        · exact (by decide : (2 : Fin 3) ≠ 1)
            (((P.mem_iff 2 h hhp).mp hr2).symm.trans hhclass)
      have hcode : B.geometry.clumps.code r = b := by
        rcases Finset.mem_union.mp hr with hr0 | hr2
        · exact hsame 0 (by decide : (0 : Fin 3) ≠ 1) hr0
        · exact hsame 2 (by decide : (2 : Fin 3) ≠ 1) hr2
      simp [ActualHeavyClumpWeight.members, hrh, hcode]
  have hmass := nonapex_original_mass_ge_nine P
  have hmono := weight_mono o e c lam hsub
  have hside : 9 ≤ originalWeight o e c lam (ActualHeavyClumpWeight.members B.geometry b) := by
    omega
  have hF := ActualN4LowCriticalReduction.actual_n4_low_model_potential_eq_seventeen o e he H
  have hother : 5 ≤ originalWeight o e c lam (ActualHeavyClumpWeight.members B.geometry (!b)) := by
    have hw := B.weight_lower (!b)
    change (potential lam (directionRows o e c) - 16) + 4 ≤
      originalWeight o e c lam (ActualHeavyClumpWeight.members B.geometry (!b)) at hw
    simpa only [hF, show (17 : ℕ) - 16 + 4 = 5 by decide] using hw
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin (s + 1)))
    (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ h)
  have hfull : (∑ q : Fin (s + 1), 2 ^ rowScore lam (directionRow o e c q)) = 17 := by
    simpa only [potential, exponentAt, directionRows] using hF
  rw [hh, show (2 : ℕ) ^ 2 = 4 by decide, hfull] at hsplit
  have herased : originalWeight o e c lam (Finset.univ.erase h) = 13 := by
    unfold originalWeight
    omega
  have htotal := clump_weights_sum o e B.geometry b
  rw [herased] at htotal
  omega

#print axioms actualClassWeight
#print axioms actual_two_interior_not_apex
#print axioms actual_interior_apex_full_hull_or_zero
#print axioms actual_two_interior_apex_disjoint
#print axioms actual_nonacute_heavy_not_in_interior_apex

end Jsp404.ActualF17UniqueZeroInteriorApex
