import Jsp000404.ActualF17PositiveObserverZeroGain
import Jsp000404.ActualF18ClassWeight

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY actual original F17 classes with one original zero.
The general score-one actual partition is produced internally. Its
original class masses sum to fifteen, not sixteen. The class containing
the unique zero may have mass three; a heavy singleton remains allowed.
Only generic original-index helpers are used from ActualF18ClassWeight.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF17UniqueZeroClassWeight

open ActualF18ClassWeight

/-- Original-index classes and the exact unique-zero mass bounds. This
structure is generic in the original index count; its public producer
below supplies all fields from the actual original Model. -/
structure Data {t : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) (z p : Fin t) where
  partition : ActualInteriorOnePartition.Data c lam p
  score_one : rowScore lam (directionRow o e c p) = 1
  classMembers : Fin 3 → Finset (Fin t)
  mem_iff : ∀ k q (hqp : q ≠ p),
    q ∈ classMembers k ↔ partition.classOf ⟨q, hqp⟩ = k
  ne_center : ∀ k q, q ∈ classMembers k → q ≠ p
  disjoint : ∀ {k l : Fin 3}, k ≠ l → Disjoint (classMembers k) (classMembers l)
  weight_sum : (∑ k : Fin 3, originalWeight o e c lam (classMembers k)) = 15
  weight_ge_three : ∀ k, 3 ≤ originalWeight o e c lam (classMembers k)
  weight_ge_four_of_zero_not_mem : ∀ k, z ∉ classMembers k →
    4 ≤ originalWeight o e c lam (classMembers k)
  pair_weight_ge_seven : ∀ k l : Fin 3, k ≠ l →
    7 ≤ originalWeight o e c lam (classMembers k) +
      originalWeight o e c lam (classMembers l)
  weight_le_eight : ∀ k, originalWeight o e c lam (classMembers k) ≤ 8

private theorem zero_gain_of_target_score_le_one {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (q : Fin (s + 1)) (hpq : p ≠ q)
    (hq : rowScore lam (directionRow o e c q) ≤ 1) :
    rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0 := by
  by_cases hzero : rowScore lam (directionRow o e c q) = 0
  · have hmin (j : Fin (s + 1)) :
        rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c j) := by
      rw [hzero]
      exact Nat.zero_le _
    exact (ActualMinimalBandCounterexample.low_minimum_score_critical_form
      (n := 4) hs (by decide : 2 ≤ 4) o e H q hmin).2.2 p hpq
  · have hone : rowScore lam (directionRow o e c q) = 1 := by omega
    exact ActualF17PositiveObserverZeroGain.actual_positive_observer_light_target_gain_zero
      o e he H q hone p hpq (by omega)

private theorem class_weight_bounds {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ q : Fin (s + 1), q ≠ z → 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    3 ≤ originalWeight o e c lam (classMembers D k) ∧
      (z ∉ classMembers D k → 4 ≤ originalWeight o e c lam (classMembers D k)) := by
  classical
  let S := classMembers D k
  have hpoint (q : Fin (s + 1)) :
      2 ≤ 2 ^ rowScore lam (directionRow o e c q) + if q = z then 1 else 0 := by
    by_cases hqz : q = z
    · simp only [hqz, hz, pow_zero, if_pos rfl]
    · have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (hpositive q hqz)
      simpa only [pow_one, if_neg hqz, Nat.add_zero] using hpow
  have hmass : 2 * S.card ≤ originalWeight o e c lam S + if z ∈ S then 1 else 0 := by
    have hsum := Finset.sum_le_sum (fun q (_hq : q ∈ S) => hpoint q)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_const,
      smul_eq_mul, mul_one, originalWeight, Nat.mul_comm] using hsum
  by_cases hcard : 2 ≤ S.card
  · by_cases hzS : z ∈ S
    · simp only [if_pos hzS] at hmass
      exact ⟨by omega, fun h => False.elim (h hzS)⟩
    · simp only [if_neg hzS, Nat.add_zero] at hmass
      exact ⟨by omega, fun _ => by omega⟩
  · have hpos : 0 < S.card := (classMembers_nonempty D k).card_pos
    have hone : S.card = 1 := by omega
    obtain ⟨q, hset⟩ := Finset.card_eq_one.mp hone
    have hqmem : q ∈ classMembers D k := by change q ∈ S; rw [hset]; simp
    have hqp := classMembers_ne_center D k hqmem
    have hqclass := (classMembers_mem_iff D k q hqp).mp hqmem
    have hgain : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
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
      linarith only [hangle, H.legality.lam_pos]
    have hqscore : 2 ≤ rowScore lam (directionRow o e c q) := by
      by_contra hnot
      have hzero := zero_gain_of_target_score_le_one hs o e he H p hp q hqp.symm
        (by omega : rowScore lam (directionRow o e c q) ≤ 1)
      omega
    have hpow : 4 ≤ 2 ^ rowScore lam (directionRow o e c q) := by
      simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using
        Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hqscore
    have hfour : 4 ≤ originalWeight o e c lam S := by
      simpa only [originalWeight, hset, Finset.sum_singleton] using hpow
    exact ⟨by omega, fun _ => hfour⟩

/-- One original zero and an original score-one interior subcase internally
produce their actual classes and all original mass bounds. A singleton
heavy is allowed; no F18 four-per-class assumption is used. -/
theorem exists_actual_unique_zero_interior_class_weight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (z : Fin (s + 1)) (hz : rowScore lam (directionRow o e c z) = 0)
    (hpositive : ∀ q : Fin (s + 1), q ≠ z → 1 ≤ rowScore lam (directionRow o e c q))
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 1)
    (hnot : ¬ IsHullVertex c p) : Nonempty (Data o e c lam z p) := by
  classical
  have hF := ActualN4LowCriticalReduction.actual_n4_low_model_potential_eq_seventeen
    o e he H
  have hs : 3 ≤ s := by
    by_contra hnot
    obtain ⟨hn, hlow, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
      (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
    have hcap : potential lam (directionRows o e c) ≤ 16 := by
      simpa using GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low
        o e he H.card_ge_three (by omega : s + 1 ≤ 5) (by decide : 3 ≤ 4)
        H.legality.lam_pos hn hlow H.legality
    omega
  have hrho : Real.pi / ((4 : ℝ) + 1 / 2) = 2 * Real.pi / 9 := by ring
  have hscale : 2 * Real.pi / 9 < lam := by rw [← hrho]; exact H.scale_lower
  have h5 : Real.pi / 5 < lam := by linarith only [hscale, Real.pi_pos]
  let D := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s + 1)
    o e he H.legality h5 p hnot hp
  have hbounds (k : Fin 3) := class_weight_bounds hs o e he H z hz hpositive p hp D k
  have hthree (k : Fin 3) : 3 ≤ originalWeight o e c lam (classMembers D k) :=
    (hbounds k).1
  have hfour (k : Fin 3) : z ∉ classMembers D k →
      4 ≤ originalWeight o e c lam (classMembers D k) := (hbounds k).2
  have hmass : originalWeight o e c lam (Finset.univ.erase p) + 2 = 17 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin (s + 1)))
      (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ p)
    have hfull : (∑ q : Fin (s + 1), 2 ^ rowScore lam (directionRow o e c q)) = 17 := by
      simpa only [potential, exponentAt, directionRows] using hF
    rw [hp, pow_one, hfull] at hsplit
    exact hsplit
  have hsum : (∑ k : Fin 3, originalWeight o e c lam (classMembers D k)) = 15 := by
    rw [originalWeight_classMembers_sum o e D]
    omega
  have hpairs (k l : Fin 3) (hkl : k ≠ l) :
      7 ≤ originalWeight o e c lam (classMembers D k) +
        originalWeight o e c lam (classMembers D l) := by
    have hk3 := hthree k
    have hl3 := hthree l
    by_cases hzk : z ∈ classMembers D k
    · have hzl : z ∉ classMembers D l := by
        intro hzl
        exact Finset.disjoint_left.mp (classMembers_disjoint D hkl) hzk hzl
      have hl4 := hfour l hzl
      omega
    · have hk4 := hfour k hzk
      omega
  have hupper (k : Fin 3) : originalWeight o e c lam (classMembers D k) ≤ 8 := by
    have hsum3 : originalWeight o e c lam (classMembers D 0) +
        originalWeight o e c lam (classMembers D 1) +
        originalWeight o e c lam (classMembers D 2) = 15 := by
      simpa only [Fin.sum_univ_three, Nat.add_assoc] using hsum
    have h01 := hpairs 0 1 (by decide : (0 : Fin 3) ≠ 1)
    have h02 := hpairs 0 2 (by decide : (0 : Fin 3) ≠ 2)
    have h12 := hpairs 1 2 (by decide : (1 : Fin 3) ≠ 2)
    fin_cases k
    · change originalWeight o e c lam (classMembers D 0) ≤ 8
      omega
    · change originalWeight o e c lam (classMembers D 1) ≤ 8
      omega
    · change originalWeight o e c lam (classMembers D 2) ≤ 8
      omega
  exact ⟨{
    partition := D
    score_one := hp
    classMembers := classMembers D
    mem_iff := classMembers_mem_iff D
    ne_center := fun k q hq => classMembers_ne_center D k hq
    disjoint := fun {k l} hkl => classMembers_disjoint D hkl
    weight_sum := hsum
    weight_ge_three := hthree
    weight_ge_four_of_zero_not_mem := hfour
    pair_weight_ge_seven := hpairs
    weight_le_eight := hupper }⟩

#print axioms exists_actual_unique_zero_interior_class_weight

end Jsp404.ActualF17UniqueZeroClassWeight
