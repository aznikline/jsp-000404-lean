import Jsp000404.ActualF18NonacuteApex
import Jsp000404.ActualMixedRigidCardinality
import Jsp000404.ActualHullTurnBudget

set_option autoImplicit false

/-!
Original F18 two-heavy consumers. Every partition, class weight, heavy
clump, hull window and turn budget is produced internally from the
original actual minimum-counter Model. No class data, clump, cover,
capacity or budget is a caller premise.

* `actual_interior_apex_has_heavy_of_nonacute`: any F18 profile. If some
  original heavy is nonacute, every original interior apex contains a
  different original heavy point.
* `actual_obtuse_heavy_interior_false`: any F18 profile. A heavy point with
  an actual angle above `pi - 2*lam` (necessarily HO) and an original interior
  point cannot coexist.
* `actual_F18_two_heavy_nonacute_interior_false`: exactly two original heavy
  points, one of them nonacute, and an original interior point is impossible.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.DevinF18TwoHeavyApex

open Jsp404.ActualF18ClassWeight

private theorem bool_not_ne_self (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

private theorem weight_mono {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ)
    {S T : Finset (Fin s)} (hST : S ⊆ T) :
    originalWeight o e c lam S ≤ originalWeight o e c lam T := by
  classical
  unfold originalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => Nat.zero_le _)

private theorem weight_insert {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ)
    (q : Fin s) (S : Finset (Fin s)) (hq : q ∉ S) :
    originalWeight o e c lam (insert q S) =
      2 ^ rowScore lam (directionRow o e c q) + originalWeight o e c lam S := by
  classical
  unfold originalWeight
  exact Finset.sum_insert hq

private theorem clump_code_eq_of_three_scale {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (p h q : Fin s) (hph : p ≠ h) (hqh : q ≠ h)
    (G : ActualMaximalLowRowClumps.Data 4 o c lam h)
    (hbig : 3 * lam ≤ ∠ (c h) (c p) (c q)) :
    G.clumps.code q = G.clumps.code p := by
  by_contra hdiff
  have hlarge := G.clumps.different_angle_ge hleg q p hqh hph hdiff
  rw [EuclideanGeometry.angle_comm (c q) (c h) (c p)] at hlarge
  have hsum := actual_triangle_sum hleg p h q hph
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c q) (c h)
  linarith [Real.pi_pos]

private theorem clump_weights_sum {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ} {h : Fin s}
    (G : ActualMaximalLowRowClumps.Data 4 o c lam h) (b : Bool) :
    originalWeight o e c lam (ActualHeavyClumpWeight.members G b) +
      originalWeight o e c lam (ActualHeavyClumpWeight.members G (!b)) =
      originalWeight o e c lam (Finset.univ.erase h) := by
  classical
  have hdisjoint : Disjoint (ActualHeavyClumpWeight.members G b)
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
  rw [← Finset.sum_union hdisjoint, hcover]

private theorem class_weight_le_eight {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (W : Data o e c lam p) (k : Fin 3) :
    originalWeight o e c lam (W.classMembers k) ≤ 8 := by
  have hsum : originalWeight o e c lam (W.classMembers 0) +
      originalWeight o e c lam (W.classMembers 1) +
      originalWeight o e c lam (W.classMembers 2) = 16 := by
    simpa only [Fin.sum_univ_three, Nat.add_assoc] using W.weight_sum
  have h0 := W.weight_ge_four 0
  have h1 := W.weight_ge_four 1
  have h2 := W.weight_ge_four 2
  fin_cases k
  · change originalWeight o e c lam (W.classMembers 0) ≤ 8
    omega
  · change originalWeight o e c lam (W.classMembers 1) ≤ 8
    omega
  · change originalWeight o e c lam (W.classMembers 2) ≤ 8
    omega

private theorem erased_heavy_weight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin s) (hh : rowScore lam (directionRow o e c h) = 2) :
    originalWeight o e c lam (Finset.univ.erase h) = 14 := by
  classical
  have hmass := Finset.sum_erase_add (Finset.univ : Finset (Fin s))
    (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ h)
  have hfull : (∑ q : Fin s, 2 ^ rowScore lam (directionRow o e c q)) = 18 := by
    simpa only [potential, exponentAt, directionRows] using hF
  rw [hh, show (2 : ℕ) ^ 2 = 4 by decide, hfull] at hmass
  unfold originalWeight
  omega

private theorem wide_of_window_lower {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p) (hlower : 2 * lam ≤ W.width) :
    ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b) :=
  ⟨W.left, W.right, W.left_ne_center, W.right_ne_center,
    W.boundary_distinct, W.width_eq_actual_angle ▸ hlower⟩

/-- Any original F18 profile: if an original heavy point is nonacute, the
internally produced apex of every original interior point contains a
different original heavy point. The apex cannot be pure light, because the
checked pure-light block bound and the heavy clump weights overflow the
original mass fourteen around the nonacute heavy. -/
theorem actual_interior_apex_has_heavy_of_nonacute {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s + 1)) (hp : ¬ IsHullVertex c p)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hwide : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c h) (c b)) :
    ∃ C ∈ (ActualF18InteriorApex.actualClassWeight o e he H hF p hp).classMembers 1,
      C ≠ h ∧ rowScore lam (directionRow o e c C) = 2 := by
  classical
  let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
  let U := P.classMembers 1
  change ∃ C ∈ U, C ≠ h ∧ rowScore lam (directionRow o e c C) = 2
  by_contra hnone
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hph : p ≠ h := by
    intro heq
    exact hp (by simpa only [heq] using F.heavy_full_hull h hh)
  have hNoH : h ∉ U :=
    ActualF18NonacuteApex.actual_nonacute_heavy_not_in_interior_apex
      o e he H hF p hp h hh hwide
  have hqp (q : Fin (s + 1)) (hq : q ∈ U) : q ≠ p := P.ne_center 1 q hq
  have hqh (q : Fin (s + 1)) (hq : q ∈ U) : q ≠ h := by
    intro heq
    exact hNoH (by simpa only [heq] using hq)
  have hlight (q : Fin (s + 1)) (hq : q ∈ U) :
      rowScore lam (directionRow o e c q) = 1 :=
    (F.score_one_or_two q).resolve_right (fun h2 => hnone ⟨q, hq, hqh q hq, h2⟩)
  have hnonempty : U.Nonempty := by
    refine ⟨P.partition.witness 1, (P.mem_iff 1 _ (P.partition.witness 1).property).mpr ?_⟩
    exact P.partition.witness_class 1
  have hUfour : 4 ≤ U.card := by
    apply ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four
      o e he H hF U hnonempty p
    · intro hpmem
      exact hqp p hpmem rfl
    · intro q hq
      exact ActualF18InteriorApex.actual_interior_apex_full_hull o e he H hF p hp q hq
    · exact hlight
    · intro q hq v hv hvp
      have hq1 := (P.mem_iff 1 q (hqp q hq)).mp hq
      have hv1 : P.partition.classOf ⟨v, hvp⟩ ≠ 1 := by
        intro hvclass
        exact hv ((P.mem_iff 1 v hvp).mpr hvclass)
      exact P.partition.apex_angle ⟨q, hqp q hq⟩ ⟨v, hvp⟩ hq1 hv1
  have hUweight : 8 ≤ originalWeight o e c lam U := by
    have hsum : originalWeight o e c lam U = 2 * U.card := by
      unfold originalWeight
      calc
        _ = ∑ _q ∈ U, (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro q hq
          simp only [hlight q hq, pow_one]
        _ = _ := by simp [Nat.mul_comm]
    omega
  obtain ⟨B⟩ := ActualHeavyClumpWeight.exists_actual_heavy_clump_weight o e he H h hh hwide
  let b := B.geometry.clumps.code p
  have hHclass : P.partition.classOf ⟨h, hph.symm⟩ ≠ 1 := by
    intro hc
    exact hNoH ((P.mem_iff 1 h hph.symm).mpr hc)
  have hsub : insert p U ⊆ ActualHeavyClumpWeight.members B.geometry b := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqp' | hq
    · subst q
      simp [ActualHeavyClumpWeight.members, b, hph]
    · have hqclass := (P.mem_iff 1 q (hqp q hq)).mp hq
      have hbig := P.partition.apex_angle ⟨q, hqp q hq⟩ ⟨h, hph.symm⟩ hqclass hHclass
      rw [EuclideanGeometry.angle_comm (c q) (c p) (c h)] at hbig
      have hcode := clump_code_eq_of_three_scale H.legality F.scale_lower
        p h q hph (hqh q hq) B.geometry hbig
      simp [ActualHeavyClumpWeight.members, hqh q hq, hcode, b]
  have hpU : p ∉ U := by intro hpmem; exact hqp p hpmem rfl
  have hinsert : originalWeight o e c lam (insert p U) =
      2 + originalWeight o e c lam U := by
    rw [weight_insert o e c lam p U hpU, P.score_one, pow_one]
  have hmono := weight_mono o e c lam hsub
  rw [hinsert] at hmono
  have hotherWeight : 6 ≤ originalWeight o e c lam
      (ActualHeavyClumpWeight.members B.geometry (!b)) := by
    have hw := B.weight_lower (!b)
    change (potential lam (directionRows o e c) - 16) + 4 ≤
      originalWeight o e c lam (ActualHeavyClumpWeight.members B.geometry (!b)) at hw
    simpa only [hF, show (18 : ℕ) - 16 + 4 = 6 by decide] using hw
  have htotal := clump_weights_sum o e B.geometry b
  rw [erased_heavy_weight o e hF h hh] at htotal
  omega

/-- Any original F18 profile: an original heavy point with an actual angle
strictly above `pi - 2*lam` cannot coexist with an original interior point.
The HO type and both clump structures are produced internally. The far
heavy clump has original weight at least six and is forced, together with
the heavy itself, into one actual class of the interior point. -/
theorem actual_obtuse_heavy_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s + 1)) (hp : ¬ IsHullVertex c p)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hobtuse : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      Real.pi - 2 * lam < ∠ (c a) (c h) (c b)) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hleg := H.legality
  obtain ⟨a0, b0, ha0, hb0, _hab0, hangle0⟩ := hobtuse
  obtain ⟨⟨W, K⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    H.card_ge_three o e he hleg F.scale_lower h (F.heavy_full_hull h hh) hh
  have hle := ActualMixedRigidCardinality.actual_window_angle_le_width W hleg a0 b0 ha0 hb0
  cases K with
  | HA _hout hcone => linarith [hleg.lam_pos]
  | HM _hout _hlo hhi _D => linarith
  | HO _hout hlo D =>
    have hwide := wide_of_window_lower W (by linarith [hleg.lam_pos])
    have hph : p ≠ h := by
      intro heq
      exact hp (by simpa only [heq] using F.heavy_full_hull h hh)
    let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
    obtain ⟨B⟩ := ActualHeavyClumpWeight.exists_actual_heavy_clump_weight o e he H h hh hwide
    let G := B.geometry
    let b := G.clumps.code p
    let T := ActualHeavyClumpWeight.members G (!b)
    let k := P.partition.classOf ⟨h, hph.symm⟩
    have hTsub : T ⊆ P.classMembers k := by
      intro v hv
      have hvd := (Finset.mem_filter.mp hv).2
      have hvh : v ≠ h := hvd.1
      have hvp : v ≠ p := by
        intro heq
        subst v
        exact bool_not_ne_self b hvd.2.symm
      have hcodes : G.clumps.code v ≠ G.clumps.code p := by
        intro heq
        exact bool_not_ne_self b (hvd.2.symm.trans heq)
      have h2 := G.clumps.different_angle_ge hleg v p hvh hph hcodes
      have h3 : 3 * lam ≤ ∠ (c v) (c h) (c p) := by
        by_cases hsame : D.code v = D.code p
        · have hsmall := D.same_angle_le hleg v p hvh hph hsame
          linarith [F.scale_lower, Real.pi_pos]
        · exact D.different_angle_ge hleg v p hvh hph hsame
      apply (P.mem_iff k v hvp).mpr
      by_contra hdiff
      have hat := P.partition.different_angle ⟨v, hvp⟩ ⟨h, hph.symm⟩ hdiff
      have hsum := actual_triangle_sum hleg h p v hph.symm
      rw [EuclideanGeometry.angle_comm (c p) (c h) (c v),
        EuclideanGeometry.angle_comm (c h) (c p) (c v)] at hsum
      have hthird := EuclideanGeometry.angle_nonneg (c h) (c v) (c p)
      linarith [F.scale_lower, Real.pi_pos]
    have hhT : h ∉ T := by simp [T, ActualHeavyClumpWeight.members]
    have hsub : insert h T ⊆ P.classMembers k := by
      intro q hq
      rcases Finset.mem_insert.mp hq with hqh | hq
      · subst q
        exact (P.mem_iff k h hph.symm).mpr rfl
      · exact hTsub hq
    have hTweight : 6 ≤ originalWeight o e c lam T := by
      have hw := B.weight_lower (!b)
      change (potential lam (directionRows o e c) - 16) + 4 ≤
        originalWeight o e c lam T at hw
      simpa only [hF, show (18 : ℕ) - 16 + 4 = 6 by decide] using hw
    have hinsert : originalWeight o e c lam (insert h T) =
        4 + originalWeight o e c lam T := by
      rw [weight_insert o e c lam h T hhT, hh]
      norm_num
    have hmono := weight_mono o e c lam hsub
    rw [hinsert] at hmono
    have hcap := class_weight_le_eight P k
    omega

/-- At most two original heavy points and a nonacute heavy: two distinct
original interior points are impossible. Their disjoint apex sets would
need two distinct heavy points other than the nonacute one. -/
theorem actual_two_interior_nonacute_heavy_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (ht : (ActualF18Frame.heavyIndices o e c lam).card ≤ 2)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hwide : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c h) (c b))
    (p q : Fin (s + 1)) (hp : ¬ IsHullVertex c p) (hq : ¬ IsHullVertex c q)
    (hpq : p ≠ q) : False := by
  classical
  obtain ⟨Cp, hCp, hCph, hCps⟩ :=
    actual_interior_apex_has_heavy_of_nonacute o e he H hF p hp h hh hwide
  obtain ⟨Cq, hCq, hCqh, hCqs⟩ :=
    actual_interior_apex_has_heavy_of_nonacute o e he H hF q hq h hh hwide
  have hdisj := ActualF18InteriorApex.actual_two_interior_apex_disjoint
    o e he H hF p q hp hq hpq
  have hCpq : Cp ≠ Cq := by
    intro heq
    subst heq
    exact Finset.disjoint_left.mp hdisj hCp hCq
  have hsub : ({h, Cp, Cq} : Finset (Fin (s + 1))) ⊆
      ActualF18Frame.heavyIndices o e c lam := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      simp [ActualF18Frame.heavyIndices, hh, hCps, hCqs]
  have hcard : ({h, Cp, Cq} : Finset (Fin (s + 1))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hCph.symm, hCqh.symm]),
      Finset.card_pair hCpq]
  have := Finset.card_le_card hsub
  omega

/-- Every original heavy point nonacute and some original interior point:
impossible in any original F18 profile with at least one heavy point. -/
theorem actual_all_heavy_nonacute_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hallwide : ∀ g : Fin (s + 1), rowScore lam (directionRow o e c g) = 2 →
      ∃ a b : Fin (s + 1), a ≠ g ∧ b ≠ g ∧ a ≠ b ∧
        2 * lam ≤ ∠ (c a) (c g) (c b))
    (p : Fin (s + 1)) (hp : ¬ IsHullVertex c p) : False := by
  obtain ⟨C, hC, _hCh, hCs⟩ :=
    actual_interior_apex_has_heavy_of_nonacute o e he H hF p hp h hh (hallwide h hh)
  exact ActualF18NonacuteApex.actual_nonacute_heavy_not_in_interior_apex
    o e he H hF p hp C hCs (hallwide C hCs) hC

/-- The whole original two-heavy F18 branch with a nonacute heavy point and
an original interior point is impossible. If the nonacute heavy has no angle
above `pi - 2*lam`, the unique interior point leaves six original hull
vertices whose checked integer turn budget is at least nine. Otherwise the
obtuse-heavy theorem applies. -/
theorem actual_F18_two_heavy_nonacute_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (ht : (ActualF18Frame.heavyIndices o e c lam).card = 2)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hwide : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c h) (c b))
    (p : Fin (s + 1)) (hp : ¬ IsHullVertex c p) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hleg := H.legality
  by_cases hobtuse : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      Real.pi - 2 * lam < ∠ (c a) (c h) (c b)
  · exact actual_obtuse_heavy_interior_false o e he H hF p hp h hh hobtuse
  have hhcap : ∀ a b : Fin (s + 1), a ≠ h → b ≠ h → a ≠ b →
      ∠ (c a) (c h) (c b) ≤ Real.pi - 2 * lam := by
    intro a b ha hb hab
    by_contra hlt
    exact hobtuse ⟨a, b, ha, hb, hab, lt_of_not_ge hlt⟩
  obtain ⟨C, hCapex, hCh, hCs⟩ :=
    actual_interior_apex_has_heavy_of_nonacute o e he H hF p hp h hh hwide
  have hCnotwide : ¬ ∃ a b : Fin (s + 1), a ≠ C ∧ b ≠ C ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c C) (c b) := by
    intro hCw
    exact ActualF18NonacuteApex.actual_nonacute_heavy_not_in_interior_apex
      o e he H hF p hp C hCs hCw hCapex
  obtain ⟨⟨WC, KC⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    H.card_ge_three o e he hleg F.scale_lower C (F.heavy_full_hull C hCs) hCs
  have hCcap : WC.width ≤ Real.pi - 3 * lam := by
    cases KC with
    | HA _hout hcone => exact hcone
    | HM _hout hlo _hhi _D => exact False.elim (hCnotwide (wide_of_window_lower WC hlo))
    | HO _hout hlo _D =>
        exact False.elim (hCnotwide (wide_of_window_lower WC (by linarith [hleg.lam_pos])))
  have hheavy (g : Fin (s + 1)) (hg : rowScore lam (directionRow o e c g) = 2) :
      g = h ∨ g = C := by
    by_contra hne
    have hgh : g ≠ h := fun heq => hne (Or.inl heq)
    have hgC : g ≠ C := fun heq => hne (Or.inr heq)
    have hsub : ({g, h, C} : Finset (Fin (s + 1))) ⊆
        ActualF18Frame.heavyIndices o e c lam := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;>
        simp [ActualF18Frame.heavyIndices, hh, hCs, hg]
    have hcard : ({g, h, C} : Finset (Fin (s + 1))).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hgh, hgC]),
        Finset.card_pair hCh.symm]
    have := Finset.card_le_card hsub
    omega
  have hhull (q : Fin (s + 1)) (hqp : q ≠ p) : IsHullVertex c q := by
    by_contra hq
    exact actual_two_interior_nonacute_heavy_false o e he H hF ht.le h hh hwide
      p q hp hq hqp.symm
  have hsize : s + 1 = 7 := by have := F.card_eq_nine_sub_heavy; omega
  let S : Finset (Fin (s + 1)) := Finset.univ.erase p
  have hS : S.card = 6 := by
    simp only [S, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    omega
  let E := S.orderIsoOfFin hS
  let pick : Fin 6 → Fin (s + 1) := fun i => (E i).val
  have hpick : Function.Injective pick := Subtype.val_injective.comp E.injective
  have hpickp (i : Fin 6) : pick i ≠ p := (Finset.mem_erase.mp (E i).property).1
  let kq : Fin (s + 1) → ℕ := fun q => if q = h then 2 else if q = C then 3 else 1
  have hbudget := ActualHullTurnBudget.selected_hull_integer_budget_le_eight
    o H.card_ge_three (by decide : 2 ≤ 6) hleg F.scale_lower
    pick hpick (fun i => hhull (pick i) (hpickp i)) (fun i => kq (pick i)) (by
      intro i a b ha hb hab
      by_cases hih : pick i = h
      · have hk : kq (pick i) = 2 := by simp [kq, hih]
        rw [hk]
        rw [hih] at ha hb ⊢
        have := hhcap a b ha hb hab
        push_cast
        linarith
      · by_cases hiC : pick i = C
        · have hk : kq (pick i) = 3 := by simp [kq, hih, hiC]
          rw [hk]
          rw [hiC] at ha hb ⊢
          have := (ActualMixedRigidCardinality.actual_window_angle_le_width WC hleg
            a b ha hb).trans hCcap
          push_cast
          linarith
        · have hk : kq (pick i) = 1 := by simp [kq, hih, hiC]
          rw [hk]
          have := hleg.triAngle a (pick i) b ha.symm hb hab
          push_cast
          linarith)
  have hsumS : (∑ i : Fin 6, kq (pick i)) = ∑ q ∈ S, kq q := by
    rw [← Finset.sum_coe_sort S kq]
    exact Fintype.sum_equiv E.toEquiv _ _ (fun _ => rfl)
  have hpoint (q : Fin (s + 1)) : kq q =
      1 + (if q = h then 1 else 0) + (if q = C then 2 else 0) := by
    by_cases hqh : q = h
    · subst q
      simp [kq, hCh.symm]
    · by_cases hqC : q = C <;> simp [kq, hqh, hqC]
  have hhS : h ∈ S := Finset.mem_erase.mpr ⟨fun heq => hp (heq ▸ F.heavy_full_hull h hh),
    Finset.mem_univ h⟩
  have hCS : C ∈ S := Finset.mem_erase.mpr ⟨fun heq => hp (heq ▸ F.heavy_full_hull C hCs),
    Finset.mem_univ C⟩
  have hnine : (∑ q ∈ S, kq q) = 9 := by
    rw [Finset.sum_congr rfl (fun q _ => hpoint q), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq' S h, Finset.sum_ite_eq' S C]
    simp [hhS, hCS, hS]
  have hcount := hbudget.2
  rw [hsumS, hnine] at hcount
  omega

#print axioms actual_interior_apex_has_heavy_of_nonacute
#print axioms actual_obtuse_heavy_interior_false
#print axioms actual_two_interior_nonacute_heavy_false
#print axioms actual_all_heavy_nonacute_interior_false
#print axioms actual_F18_two_heavy_nonacute_interior_false

end Jsp404.DevinF18TwoHeavyApex
