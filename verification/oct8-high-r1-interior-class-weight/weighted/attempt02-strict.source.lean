import Jsp000404.ActualHighR1PositiveCriticalProfile
import Jsp000404.ActualF18ClassWeight

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY actual weighted interior classes in the positive HIGH4 R1 branch.
The new positive critical-profile dependency is validated separately. This
candidate has not been compiled. Its generic class-set helpers are reused
from ActualF18ClassWeight; no F18 Model or mass16 theorem is applied.

All weights and sets refer to the original configuration. SAT mass8 is
retained explicitly: the total outside the interior light is20, the SAT
class can have mass12, and only SAT-free classes have upper bound8.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualHighR1InteriorClassWeight

open ActualF18ClassWeight

/-- Actual original-index classes, with the SAT-sensitive HIGH bounds. -/
structure Data {t : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) (v p : Fin t) where
  partition : ActualInteriorOnePartition.Data c lam p
  score_one : rowScore lam (directionRow o e c p) = 1
  saturated_score : rowScore lam (directionRow o e c v) = 3
  card_eq : t = 7
  potential_eq : potential lam (directionRows o e c) = 22
  classMembers : Fin 3 → Finset (Fin t)
  mem_iff : ∀ k q (hqp : q ≠ p),
    q ∈ classMembers k ↔ partition.classOf ⟨q, hqp⟩ = k
  ne_center : ∀ k q, q ∈ classMembers k → q ≠ p
  nonempty : ∀ k, (classMembers k).Nonempty
  disjoint : ∀ {k l : Fin 3}, k ≠ l → Disjoint (classMembers k) (classMembers l)
  cover : (classMembers 0 ∪ classMembers 1) ∪ classMembers 2 = Finset.univ.erase p
  satClass : Fin 3
  sat_mem : v ∈ classMembers satClass
  weight_sum : (∑ k : Fin 3, originalWeight o e c lam (classMembers k)) = 20
  weight_ge_four : ∀ k, 4 ≤ originalWeight o e c lam (classMembers k)
  sat_weight_ge_eight : 8 ≤ originalWeight o e c lam (classMembers satClass)
  weight_le_twelve : ∀ k, originalWeight o e c lam (classMembers k) ≤ 12
  weight_le_eight_of_sat_not_mem : ∀ k, v ∉ classMembers k →
    originalWeight o e c lam (classMembers k) ≤ 8

private theorem light_incoming_gain_zero {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / 5) (Real.pi / ((4 : ℝ) + 1 / 2)) 20 (s + 1) c lam)
    (hpositive : ∀ q : Fin (s + 1), 1 ≤ rowScore lam (directionRow o e c q))
    (q : Fin (s + 1)) (hq : rowScore lam (directionRow o e c q) = 1) :
    ∀ i : Fin (s + 1), i ≠ q →
      rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0 := by
  have hmin (i : Fin (s + 1)) : rowScore lam (directionRow o e c q) ≤
      rowScore lam (directionRow o e c i) := by
    simpa only [hq] using hpositive i
  have hdiv : 2 ^ rowScore lam (directionRow o e c q) ∣ 20 := by
    norm_num [hq]
  obtain ⟨_, _, hzero, _⟩ :=
    ActualMinimalBandCounterexample.actual_minimum_score_critical_form
      hs o e H q hmin hdiv
  exact hzero

private theorem class_weight_ge_four {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / 5) (Real.pi / ((4 : ℝ) + 1 / 2)) 20 (s + 1) c lam)
    (hpositive : ∀ q : Fin (s + 1), 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s + 1)) (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    4 ≤ originalWeight o e c lam (classMembers D k) := by
  classical
  let S := classMembers D k
  change 4 ≤ originalWeight o e c lam S
  have hpoint (q : Fin (s + 1)) : 2 ≤ 2 ^ rowScore lam (directionRow o e c q) := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (hpositive q)
  have hmass : 2 * S.card ≤ originalWeight o e c lam S := by
    have h := Finset.sum_le_sum (fun q (_hq : q ∈ S) => hpoint q)
    simpa only [originalWeight, Finset.sum_const, smul_eq_mul, Nat.mul_comm] using h
  by_cases hcard : 2 ≤ S.card
  · omega
  · have hpos : 0 < S.card := (classMembers_nonempty D k).card_pos
    have hone : S.card = 1 := by omega
    obtain ⟨q, hset⟩ := Finset.card_eq_one.mp hone
    have hqmem : q ∈ classMembers D k := by
      change q ∈ S
      rw [hset]
      simp
    have hqp := classMembers_ne_center D k hqmem
    have hqclass := (classMembers_mem_iff D k q hqp).mp hqmem
    by_cases hqone : rowScore lam (directionRow o e c q) = 1
    · have hgain : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
        apply rowGain_pos_of_forall_angle_ge o e c H.legality he hqp.symm H.card_ge_three
        intro j hjp hjq
        have hdiff : D.classOf ⟨q, hqp⟩ ≠ D.classOf ⟨j, hjp⟩ := by
          intro hsame
          have hjmem : j ∈ classMembers D k :=
            (classMembers_mem_iff D k j hjp).mpr (hsame.symm.trans hqclass)
          have hjeq : j = q := by
            change j ∈ S at hjmem
            simpa only [hset, Finset.mem_singleton] using hjmem
          exact hjq hjeq
        have hangle := D.different_angle ⟨q, hqp⟩ ⟨j, hjp⟩ hdiff
        linarith [H.legality.lam_pos]
      have hzero := light_incoming_gain_zero hs o e H hpositive q hqone p hqp.symm
      omega
    · have hqtwo : 2 ≤ rowScore lam (directionRow o e c q) := by
        have := hpositive q
        omega
      have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hqtwo
      simpa only [originalWeight, hset, Finset.sum_singleton,
        show (2 : ℕ) ^ 2 = 4 by decide] using hpow

private theorem three_mass_bounds (w : Fin 3 → ℕ)
    (hsum : (∑ k : Fin 3, w k) = 20) (hfour : ∀ k, 4 ≤ w k)
    (j : Fin 3) (height : 8 ≤ w j) :
    (∀ k, w k ≤ 12) ∧ (∀ k, k ≠ j → w k ≤ 8) := by
  have h0 := hfour 0
  have h1 := hfour 1
  have h2 := hfour 2
  rw [Fin.sum_univ_three] at hsum
  constructor
  · intro k
    fin_cases k
    · change w 0 ≤ 12
      omega
    · change w 1 ≤ 12
      omega
    · change w 2 ≤ 12
      omega
  · intro k hkj
    fin_cases k <;> fin_cases j
    · exact False.elim (hkj rfl)
    · change w 0 ≤ 8
      change 8 ≤ w 1 at height
      omega
    · change w 0 ≤ 8
      change 8 ≤ w 2 at height
      omega
    · change w 1 ≤ 8
      change 8 ≤ w 0 at height
      omega
    · exact False.elim (hkj rfl)
    · change w 1 ≤ 8
      change 8 ≤ w 2 at height
      omega
    · change w 2 ≤ 8
      change 8 ≤ w 0 at height
      omega
    · change w 2 ≤ 8
      change 8 ≤ w 1 at height
      omega
    · exact False.elim (hkj rfl)

/-- The original positive HIGH R1 model internally supplies its actual
interior-light partition and all original SAT-sensitive class weights.
Original non-hull membership specifies the interior case. No caller gives
potential22, card7, a partition, class masses, gain bounds or other hull data. -/
theorem exists_actual_high_r1_interior_class_weight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / 5) (Real.pi / ((4 : ℝ) + 1 / 2)) 20 (s + 1) c lam)
    (v : Fin (s + 1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s + 1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s + 1), 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hpnot : ¬ IsHullVertex c p) : Nonempty (Data o e c lam v p) := by
  classical
  have P := ActualHighR1PositiveCriticalProfile.actual_high_r1_positive_critical_profile
    o e he H v hsat a ha hpositive
  have hs : 3 ≤ s := by have := P.card_eq; omega
  have hvp : v ≠ p := by
    intro h
    have hv := P.saturated_score
    rw [h, hp] at hv
    omega
  let D := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s + 1)
    o e he H.legality H.scale_lower p hpnot hp
  have hfour : ∀ k, 4 ≤ originalWeight o e c lam (classMembers D k) :=
    class_weight_ge_four hs o e he H hpositive p D
  have hmass : originalWeight o e c lam (Finset.univ.erase p) + 2 = 22 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin (s + 1)))
      (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ p)
    have hfull : (∑ q : Fin (s + 1), 2 ^ rowScore lam (directionRow o e c q)) = 22 := by
      simpa only [potential, exponentAt, directionRows] using P.potential_eq
    rw [hp, pow_one, hfull] at h
    exact h
  have hsum : (∑ k : Fin 3, originalWeight o e c lam (classMembers D k)) = 20 := by
    rw [originalWeight_classMembers_sum o e D]
    omega
  let j : Fin 3 := D.classOf ⟨v, hvp⟩
  have hvmem : v ∈ classMembers D j := (classMembers_mem_iff D j v hvp).mpr rfl
  have height : 8 ≤ originalWeight o e c lam (classMembers D j) := by
    have h := Finset.single_le_sum
      (fun q (_hq : q ∈ classMembers D j) => Nat.zero_le
        (2 ^ rowScore lam (directionRow o e c q))) hvmem
    change 8 ≤ ∑ q ∈ classMembers D j, 2 ^ rowScore lam (directionRow o e c q)
    simpa only [P.saturated_score, show (2 : ℕ) ^ 3 = 8 by decide] using h
  obtain ⟨hupper, hfree⟩ := three_mass_bounds
    (fun k => originalWeight o e c lam (classMembers D k)) hsum hfour j height
  refine ⟨{
    partition := D
    score_one := hp
    saturated_score := P.saturated_score
    card_eq := by have := P.card_eq; omega
    potential_eq := P.potential_eq
    classMembers := classMembers D
    mem_iff := classMembers_mem_iff D
    ne_center := fun k q hq => classMembers_ne_center D k hq
    nonempty := classMembers_nonempty D
    disjoint := fun {_ _} hkl => classMembers_disjoint D hkl
    cover := classMembers_cover D
    satClass := j
    sat_mem := hvmem
    weight_sum := hsum
    weight_ge_four := hfour
    sat_weight_ge_eight := height
    weight_le_twelve := hupper
    weight_le_eight_of_sat_not_mem := ?_ }⟩
  intro k hnot
  apply hfree k
  intro hkj
  apply hnot
  rw [hkj]
  exact hvmem

#print axioms exists_actual_high_r1_interior_class_weight

end Jsp404.ActualHighR1InteriorClassWeight
