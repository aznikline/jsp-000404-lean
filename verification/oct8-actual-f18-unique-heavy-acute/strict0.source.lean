import Jsp000404.ActualF18UniqueHeavySingleton
import Jsp000404.ActualF18NonacuteApex
import Jsp000404.ActualHullTurnBudget
import Jsp000404.ActualMinimumDeletionNormalForm

set_option autoImplicit false

/-! SOURCE_ONLY: original unique-heavy F18 closure.
Two original interior points are excluded by actual singleton emission
and the original single-deletion budget. The remaining acute heavy is
excluded by the actual original hull-turn budget. -/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18UniqueHeavyAcute

private theorem actual_triangle_sum {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (p q r : Fin t) (hpq : p ≠ q) :
    ∠ (c q) (c p) (c r) + ∠ (c p) (c q) (c r) +
      ∠ (c p) (c r) (c q) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c p) (p₂ := c q) (c r) (hleg.inj.ne hpq.symm)
  rw [EuclideanGeometry.angle_comm (c q) (c r) (c p),
    EuclideanGeometry.angle_comm (c r) (c p) (c q)] at hsum
  linarith only [hsum]

private theorem original_card_eq_eight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ q : Fin (s+1), q ≠ h → rowScore lam (directionRow o e c q) = 1) :
    s+1 = 8 := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hheavy : ActualF18Frame.heavyIndices o e c lam = {h} := by
    ext q
    simp only [ActualF18Frame.heavyIndices,Finset.mem_filter,
      Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hq
      by_contra hqh
      have hqone := hlight q hqh
      omega
    · intro hqh
      simpa only [hqh] using hh
  have hcard := F.card_plus_heavy
  rw [hheavy,Finset.card_singleton] at hcard
  omega

private theorem apex_nonapex_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ r : Fin (s+1), r ≠ h → rowScore lam (directionRow o e c r) = 1)
    (p q : Fin (s+1)) (hp : ¬ IsHullVertex c p) (hq : ¬ IsHullVertex c q)
    (hpq : p ≠ q)
    (hP : h ∈ (ActualF18InteriorApex.actualClassWeight o e he H hF p hp).classMembers 1)
    (hQ : h ∉ (ActualF18InteriorApex.actualClassWeight o e he H hF q hq).classMembers 1) :
    False := by
  let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hhp := P.ne_center 1 h hP
  have hph : p ≠ h := hhp.symm
  have hHclass := (P.mem_iff 1 h hhp).mp hP
  have hQclass := ActualF18InteriorApex.actual_two_interior_not_apex
    o e he H hF p q hp hq hpq
  have hlargeP := P.partition.apex_angle ⟨h,hhp⟩ ⟨q,hpq.symm⟩ hHclass hQclass
  have hlargeQ := ActualF18UniqueHeavySingleton.actual_unique_heavy_nonapex_angle_ge_two
    o e he H hF h hh hlight q hq hQ p hpq hph
  rw [EuclideanGeometry.angle_comm (c h) (c p) (c q)] at hlargeP
  rw [EuclideanGeometry.angle_comm (c h) (c q) (c p)] at hlargeQ
  have hsum := actual_triangle_sum H.legality p q h hpq
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c h) (c q)
  linarith only [hlargeP,hlargeQ,hsum,hthird,F.scale_lower,Real.pi_pos]

private theorem two_incoming_gains_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ q : Fin (s+1), q ≠ h → rowScore lam (directionRow o e c q) = 1)
    (p q : Fin (s+1)) (hpq : p ≠ q) (hph : p ≠ h) (hqh : q ≠ h)
    (hpGain : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c h p))
    (hqGain : 1 ≤ rowGain lam (directionRow o e c q) (deleteIndex o e c h q)) : False := by
  classical
  have hN := original_card_eq_eight o e he H hF h hh hlight
  have hs : 3 ≤ s := by omega
  have hterm (i : Fin (s+1)) (hi : i ∈ Finset.univ.erase h) :
      2 + (if i = p then 2 else 0) + (if i = q then 2 else 0) ≤
      2 ^ rowScore lam (directionRow o e c i) *
        2 ^ rowGain lam (directionRow o e c i) (deleteIndex o e c h i) := by
    have hih : i ≠ h := (Finset.mem_erase.mp hi).1
    rw [hlight i hih,pow_one]
    by_cases hip : i = p
    · subst i
      have hpow : 2 ≤ 2 ^ rowGain lam (directionRow o e c p) (deleteIndex o e c h p) := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hpGain
      simp only [ite_true,ite_eq_right hpq]
      omega
    · by_cases hiq : i = q
      · subst i
        have hpow : 2 ≤ 2 ^ rowGain lam (directionRow o e c q) (deleteIndex o e c h q) := by
          simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hqGain
        simp only [ite_eq_right hpq.symm,ite_true]
        omega
      · have hpow : 1 ≤ 2 ^ rowGain lam (directionRow o e c i) (deleteIndex o e c h i) :=
          Nat.one_le_pow _ 2 (by decide)
        simp only [ite_eq_right hip,ite_eq_right hiq,Nat.add_zero]
        omega
  have hsum := Finset.sum_le_sum hterm
  have hleft : (∑ i ∈ Finset.univ.erase h,
      (2 + (if i = p then 2 else 0) + (if i = q then 2 else 0))) = 2*s+4 := by
    simp [Finset.sum_add_distrib,hph,hqh,Nat.mul_comm,Nat.add_assoc]
  rw [hleft] at hsum
  have hcap := ActualMinimalBandCounterexample.actual_delete_potential_le_cap hs o e H h
  rw [ActualMinimumDeletionNormalForm.actual_delete_potential_eq_sum_pow_gain
    (by omega : 2 ≤ s) o e H.legality.lam_pos h] at hcap
  omega

/-- A unique original heavy F18 profile cannot have two distinct
original interior points. No acute or nonacute angle premise is needed. -/
theorem actual_unique_heavy_two_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ r : Fin (s+1), r ≠ h → rowScore lam (directionRow o e c r) = 1)
    (p q : Fin (s+1)) (hp : ¬ IsHullVertex c p) (hq : ¬ IsHullVertex c q)
    (hpq : p ≠ q) : False := by
  classical
  let P := ActualF18InteriorApex.actualClassWeight o e he H hF p hp
  let Q := ActualF18InteriorApex.actualClassWeight o e he H hF q hq
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hph : p ≠ h := by
    intro heq
    exact hp (by simpa only [heq] using F.heavy_full_hull h hh)
  have hqh : q ≠ h := by
    intro heq
    exact hq (by simpa only [heq] using F.heavy_full_hull h hh)
  by_cases hP : h ∈ P.classMembers 1
  · by_cases hQ : h ∈ Q.classMembers 1
    · have hd := ActualF18InteriorApex.actual_two_interior_apex_disjoint
        o e he H hF p q hp hq hpq
      exact Finset.disjoint_left.mp hd hP hQ
    · exact apex_nonapex_false o e he H hF h hh hlight p q hp hq hpq hP hQ
  · by_cases hQ : h ∈ Q.classMembers 1
    · exact apex_nonapex_false o e he H hF h hh hlight q p hq hp hpq.symm hQ hP
    · have hpGain := ActualF18UniqueHeavySingleton.actual_unique_heavy_nonapex_gain
        o e he H hF h hh hlight p hp hP
      have hqGain := ActualF18UniqueHeavySingleton.actual_unique_heavy_nonapex_gain
        o e he H hF h hh hlight q hq hQ
      exact two_incoming_gains_false o e he H hF h hh hlight p q hpq hph hqh hpGain hqGain

private theorem exceptional_sum {s : ℕ} (i : Fin s) :
    (∑ j : Fin s, if j = i then (3 : ℕ) else 1) = s+2 := by
  classical
  have hterm (j : Fin s) : (if j = i then (3 : ℕ) else 1) =
      1 + if j = i then 2 else 0 := by
    by_cases hji : j = i <;> simp [hji]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

private theorem acute_one_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ r : Fin (s+1), r ≠ h → rowScore lam (directionRow o e c r) = 1)
    (p : Fin (s+1)) (hp : ¬ IsHullVertex c p)
    (hstrong : ∀ a b : Fin (s+1), a ≠ h → b ≠ h → a ≠ b →
      ∠ (c a) (c h) (c b) ≤ Real.pi-3*lam) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hN := original_card_eq_eight o e he H hF h hh hlight
  have hhp : h ≠ p := by
    intro heq
    exact hp (by simpa only [heq] using F.heavy_full_hull h hh)
  obtain ⟨ih,hih⟩ := Fin.exists_succAbove_eq hhp
  have hhull (i : Fin s) : IsHullVertex c (p.succAbove i) := by
    by_contra hnot
    exact actual_unique_heavy_two_interior_false o e he H hF h hh hlight
      p (p.succAbove i) hp hnot (Fin.succAbove_ne p i).symm
  let k : Fin s → ℕ := fun i => if i = ih then 3 else 1
  have hbudget := ActualHullTurnBudget.selected_hull_integer_budget_le_eight
    o H.card_ge_three (by omega : 2 ≤ s) H.legality F.scale_lower
    p.succAbove Fin.succAbove_right_injective hhull k (by
      intro i a b hai hbi hab
      by_cases hi : i = ih
      · subst i
        have hah : a ≠ h := by simpa only [hih] using hai
        have hbh : b ≠ h := by simpa only [hih] using hbi
        have ha := hstrong a b hah hbh hab
        simpa [k,hih] using ha
      · have ha := H.legality.triAngle a (p.succAbove i) b hai hbi.symm hab
        simpa [k,hi] using ha)
  have hsum : (∑ i : Fin s, k i) = s+2 := by
    simpa only [k] using exceptional_sum ih
  have hcount := hbudget.2
  rw [hsum] at hcount
  omega

/-- The whole original unique-heavy F18 profile is impossible. The
nonacute case uses its verified consumer; the actual HA case is selected
internally and excludes the remaining seven-hull-point configuration. -/
theorem actual_F18_unique_heavy_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (h : Fin (s+1)) (hh : rowScore lam (directionRow o e c h) = 2)
    (hlight : ∀ r : Fin (s+1), r ≠ h → rowScore lam (directionRow o e c r) = 1) :
    False := by
  classical
  by_cases hwide : ∃ a b : Fin (s+1), a ≠ h ∧ b ≠ h ∧ a ≠ b ∧
      2*lam ≤ ∠ (c a) (c h) (c b)
  · exact ActualF18NonacuteApex.actual_F18_unique_nonacute_heavy_false
      o e he H hF h hh hlight hwide
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  by_cases hall : ∀ q : Fin (s+1), IsHullVertex c q
  · exact ActualF18OneHeavyAllHull.actual_F18_one_heavy_all_hull_false
      o e he H hF h hh (fun q hq => ⟨hlight q hq,hall q⟩)
  push Not at hall
  obtain ⟨p,hp⟩ := hall
  obtain ⟨⟨W,kind⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    H.card_ge_three o e he H.legality F.scale_lower h (F.heavy_full_hull h hh) hh
  cases kind with
  | HA _hout hcone =>
      apply acute_one_interior_false o e he H hF h hh hlight p hp
      intro a b hah hbh _hab
      exact (ActualMixedRigidCardinality.actual_window_angle_le_width
        W H.legality a b hah hbh).trans hcone
  | HM _hout hcone _hupper _D =>
      exact hwide ⟨W.left,W.right,W.left_ne_center,W.right_ne_center,
        W.boundary_distinct,W.width_eq_actual_angle ▸ hcone⟩
  | HO _hout hcone _D =>
      apply hwide
      refine ⟨W.left,W.right,W.left_ne_center,W.right_ne_center,W.boundary_distinct,?_⟩
      have hbig : 3*lam ≤ ∠ (c W.left) (c h) (c W.right) :=
        W.width_eq_actual_angle ▸ hcone
      linarith only [hbig,H.legality.lam_pos]

#print axioms actual_unique_heavy_two_interior_false
#print axioms actual_F18_unique_heavy_false

end Jsp404.ActualF18UniqueHeavyAcute
