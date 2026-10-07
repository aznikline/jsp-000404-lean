import Jsp000404.ActualHeavyClumpWeight
import Jsp000404.ActualF18InteriorApex
import Jsp000404.ActualF18OneHeavyAllHull

set_option autoImplicit false

/-!
SOURCE_ONLY weighted nonacute-apex consumers.
Every partition, class weight and heavy clump is internally generated
from the original actual Model. No caller supplies class data or budgets.
The first theorem permits any original F18 heavy profile; the second
closes the complete unique-nonacute-heavy profile without an interior count.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18NonacuteApex

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

/-- In any original F18 profile, an actual-wide score-two heavy cannot
belong to the internally produced apex of an original interior point.
The weighted partition and heavy clumps are not caller premises. -/
theorem actual_nonacute_heavy_not_in_interior_apex {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s + 1)) (hp : ¬ IsHullVertex c p)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hwide : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c h) (c b)) :
    h ∉ (ActualF18InteriorApex.actualClassWeight o e he H hF p hp).classMembers 1 := by
  classical
  let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
  change h ∉ P.classMembers 1
  intro hmem
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hhp := P.ne_center 1 h hmem
  have hph : p ≠ h := hhp.symm
  have hhclass := (P.mem_iff 1 h hhp).mp hmem
  obtain ⟨B⟩ := ActualHeavyClumpWeight.exists_actual_heavy_clump_weight o e he H h hh hwide
  let b := B.geometry.clumps.code p
  let C := ActualHeavyClumpWeight.members B.geometry (!b)
  have hCsub : C ⊆ P.classMembers 1 := by
    intro q hq
    have hqd := (Finset.mem_filter.mp hq).2
    have hqp : q ≠ p := by
      intro h
      subst q
      exact bool_not_ne_self b hqd.2.symm
    apply (P.mem_iff 1 q hqp).mpr
    by_contra hnon
    have hbig := P.partition.apex_angle ⟨h, hhp⟩ ⟨q, hqp⟩ hhclass hnon
    have hsame := clump_code_eq_of_three_scale H.legality F.scale_lower
      p h q hph hqd.1 B.geometry hbig
    exact bool_not_ne_self b (hqd.2.symm.trans hsame)
  have hsub : insert h C ⊆ P.classMembers 1 := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqh | hq
    · simpa only [hqh] using hmem
    · exact hCsub hq
  have hhC : h ∉ C := by simp [C, ActualHeavyClumpWeight.members]
  have hCweight : 6 ≤ originalWeight o e c lam C := by
    have hw := B.weight_lower (!b)
    change (potential lam (directionRows o e c) - 16) + 4 ≤
      originalWeight o e c lam C at hw
    simpa only [hF, show (18 : ℕ) - 16 + 4 = 6 by decide] using hw
  have hinsert : originalWeight o e c lam (insert h C) =
      4 + originalWeight o e c lam C := by
    rw [weight_insert o e c lam h C hhC, hh]
    norm_num
  have hmono := weight_mono o e c lam hsub
  rw [hinsert] at hmono
  have hsum := P.weight_sum
  rw [Fin.sum_univ_three] at hsum
  have h0 := P.weight_ge_four 0
  have h2 := P.weight_ge_four 2
  omega

/-- The entire original unique-nonacute-heavy F18 profile is impossible,
without supplying the number or position of original interior points. -/
theorem actual_F18_unique_nonacute_heavy_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s + 1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ q : Fin (s + 1), q ≠ h → rowScore lam (directionRow o e c q) = 1)
    (hwide : ∃ a b : Fin (s + 1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c h) (c b)) : False := by
  classical
  by_cases hAllHull : ∀ q : Fin (s + 1), IsHullVertex c q
  · exact ActualF18OneHeavyAllHull.actual_F18_one_heavy_all_hull_false
      o e he H hF h hh (fun q hq => ⟨hlight q hq, hAllHull q⟩)
  push Not at hAllHull
  obtain ⟨p, hp⟩ := hAllHull
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
  let U := P.classMembers 1
  have hph : p ≠ h := by
    intro heq
    exact hp (by simpa only [heq] using F.heavy_full_hull h hh)
  have hNoH : h ∉ U :=
    actual_nonacute_heavy_not_in_interior_apex o e he H hF p hp h hh hwide
  have hqp (q : Fin (s + 1)) (hq : q ∈ U) : q ≠ p := P.ne_center 1 q hq
  have hqh (q : Fin (s + 1)) (hq : q ∈ U) : q ≠ h := by
    intro heq
    exact hNoH (by simpa only [heq] using hq)
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
    · intro q hq
      exact hlight q (hqh q hq)
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
          simp only [hlight q (hqh q hq), pow_one]
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
  have hbigWeight : 10 ≤ originalWeight o e c lam
      (ActualHeavyClumpWeight.members B.geometry b) := by omega
  have hotherWeight : 6 ≤ originalWeight o e c lam
      (ActualHeavyClumpWeight.members B.geometry (!b)) := by
    have hw := B.weight_lower (!b)
    change (potential lam (directionRows o e c) - 16) + 4 ≤
      originalWeight o e c lam (ActualHeavyClumpWeight.members B.geometry (!b)) at hw
    simpa only [hF, show (18 : ℕ) - 16 + 4 = 6 by decide] using hw
  have hmass := Finset.sum_erase_add (Finset.univ : Finset (Fin (s + 1)))
    (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ h)
  have hfull : (∑ q : Fin (s + 1), 2 ^ rowScore lam (directionRow o e c q)) = 18 := by
    simpa only [potential, exponentAt, directionRows] using hF
  rw [hh, show (2 : ℕ) ^ 2 = 4 by decide, hfull] at hmass
  have herased : originalWeight o e c lam (Finset.univ.erase h) = 14 := by
    unfold originalWeight
    omega
  have htotal := clump_weights_sum o e B.geometry b
  rw [herased] at htotal
  omega

#print axioms actual_nonacute_heavy_not_in_interior_apex
#print axioms actual_F18_unique_nonacute_heavy_false

end Jsp404.ActualF18NonacuteApex
