import Jsp000404.ActualF18InteriorApex
import Jsp000404.ActualPureLightBlock

set_option autoImplicit false

/-! SOURCE_ONLY. In an original unique-heavy F18 profile, a heavy point
outside an original interior apex is the only point in its actual class.
Only original light-target incoming zero is used by the imported block
bound; no heavy singleton is ruled out without the actual weight ledger.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18UniqueHeavySingleton

open ActualF18ClassWeight

private theorem nonapex_weight_le_four {t : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (P : Data o e c lam p)
    (hlarge : 8 ≤ originalWeight o e c lam (P.classMembers 1))
    (k : Fin 3) (hk : k ≠ 1) :
    originalWeight o e c lam (P.classMembers k) ≤ 4 := by
  have hsum : originalWeight o e c lam (P.classMembers 0) +
      originalWeight o e c lam (P.classMembers 1) +
      originalWeight o e c lam (P.classMembers 2) = 16 := by
    simpa only [Fin.sum_univ_three,Nat.add_assoc] using P.weight_sum
  have h0 := P.weight_ge_four 0
  have h2 := P.weight_ge_four 2
  fin_cases k
  · change originalWeight o e c lam (P.classMembers 0) ≤ 4
    omega
  · exact False.elim (hk rfl)
  · change originalWeight o e c lam (P.classMembers 2) ≤ 4
    omega

/-- The heavy's nonapex class has original weight four and cannot
contain a second original point. The conclusion uses actual angles. -/
theorem actual_unique_heavy_nonapex_angle_ge_two {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ q : Fin (s+1), q ≠ h → rowScore lam (directionRow o e c q) = 1)
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p)
    (hNoH : h ∉ (ActualF18InteriorApex.actualClassWeight o e he H hF p hp).classMembers 1) :
    ∀ j : Fin (s+1), j ≠ p → j ≠ h → 2*lam ≤ ∠ (c h) (c p) (c j) := by
  classical
  let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
  have hhp : h ≠ p := by
    intro hEq
    have hpone := P.score_one
    rw [← hEq,hh] at hpone
    omega
  have hnonempty : (P.classMembers 1).Nonempty := by
    refine ⟨P.partition.witness 1,?_⟩
    exact (P.mem_iff 1 _ (P.partition.witness 1).property).mpr
      (P.partition.witness_class 1)
  have hapex_light (q : Fin (s+1)) (hq : q ∈ P.classMembers 1) :
      rowScore lam (directionRow o e c q) = 1 := by
    apply hlight q
    intro hEq
    subst q
    exact hNoH hq
  have hfour : 4 ≤ (P.classMembers 1).card := by
    apply ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four
      o e he H hF (P.classMembers 1) hnonempty p
    · intro hmem
      exact P.ne_center 1 p hmem rfl
    · intro q hq
      exact ActualF18InteriorApex.actual_interior_apex_full_hull o e he H hF p hp q hq
    · exact hapex_light
    · intro q hq v hv hvp
      have hqp := P.ne_center 1 q hq
      have hq1 := (P.mem_iff 1 q hqp).mp hq
      have hv1 : P.partition.classOf ⟨v,hvp⟩ ≠ 1 := by
        intro hvclass
        exact hv ((P.mem_iff 1 v hvp).mpr hvclass)
      exact P.partition.apex_angle ⟨q,hqp⟩ ⟨v,hvp⟩ hq1 hv1
  have hpoint (q : Fin (s+1)) : 2 ≤ 2 ^ rowScore lam (directionRow o e c q) := by
    by_cases hq : q = h
    · simp [hq,hh]
    · simp [hlight q hq]
  have hmass : 2 * (P.classMembers 1).card ≤
      originalWeight o e c lam (P.classMembers 1) := by
    have hle := Finset.sum_le_sum (fun q (_hq : q ∈ P.classMembers 1) => hpoint q)
    simpa only [originalWeight,Finset.sum_const,smul_eq_mul,Nat.mul_comm] using hle
  have hlarge : 8 ≤ originalWeight o e c lam (P.classMembers 1) := by omega
  let k : Fin 3 := P.partition.classOf ⟨h,hhp⟩
  have hk : k ≠ 1 := by
    intro hk1
    exact hNoH ((P.mem_iff 1 h hhp).mpr hk1)
  have hcap : originalWeight o e c lam (P.classMembers k) ≤ 4 :=
    nonapex_weight_le_four P hlarge k hk
  have hHmem : h ∈ P.classMembers k := (P.mem_iff k h hhp).mpr rfl
  intro j hjp hjh
  have hdiff : P.partition.classOf ⟨h,hhp⟩ ≠ P.partition.classOf ⟨j,hjp⟩ := by
    intro hsame
    have hjmem : j ∈ P.classMembers k := (P.mem_iff k j hjp).mpr hsame.symm
    have hsub : ({h,j} : Finset (Fin (s+1))) ⊆ P.classMembers k := by
      intro q hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · simpa only [hq] using hHmem
      · have hqj : q = j := Finset.mem_singleton.mp hq
        simpa only [hqj] using hjmem
    have hpair : originalWeight o e c lam ({h,j} : Finset (Fin (s+1))) = 6 := by
      unfold originalWeight
      rw [Finset.sum_pair hjh.symm,hh,hlight j hjh]
      norm_num
    have hmono : originalWeight o e c lam ({h,j} : Finset (Fin (s+1))) ≤
        originalWeight o e c lam (P.classMembers k) := by
      unfold originalWeight
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    omega
  exact P.partition.different_angle ⟨h,hhp⟩ ⟨j,hjp⟩ hdiff

/-- Actual positive gain on deleting the original heavy follows from
its internally forced singleton class; the target need not be light. -/
theorem actual_unique_heavy_nonapex_gain {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ q : Fin (s+1), q ≠ h → rowScore lam (directionRow o e c q) = 1)
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p)
    (hNoH : h ∉ (ActualF18InteriorApex.actualClassWeight o e he H hF p hp).classMembers 1) :
    1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c h p) := by
  let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
  have hhp : h ≠ p := by
    intro hEq
    have hpone := P.score_one
    rw [← hEq,hh] at hpone
    omega
  apply rowGain_pos_of_forall_angle_ge o e c H.legality he hhp.symm H.card_ge_three
  intro j hjp hjh
  have hangle := actual_unique_heavy_nonapex_angle_ge_two o e he H hF h hh hlight p hp hNoH j hjp hjh
  linarith [H.legality.lam_pos]

#print axioms actual_unique_heavy_nonapex_angle_ge_two
#print axioms actual_unique_heavy_nonapex_gain

end Jsp404.ActualF18UniqueHeavySingleton
