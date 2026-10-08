import Jsp000404.ActualHighR1PositiveClosure
import Jsp000404.N3SaturatedBounds

set_option autoImplicit false

/-!
SOURCE_ONLY arbitrary-size actual positive HIGH4 SAT/heavy capacity.
The final seven-point provider and closure are pending their own checks.
Actual injective restrictions preserve scores and the saturated anchor;
no restricted Model or caller seven-subset/profile/capacity is assumed.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualHighR1PositiveCapacity

private theorem exact_profile_of_overfull {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (ht3 : 3 ≤ t) {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 4)
    (hhigh : (1/2 : ℝ) ≤ Real.pi/lam-4)
    (v a : Fin t) (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (ha : 2 ≤ rowScore lam (directionRow o e c a))
    (hpositive : ∀ q : Fin t, 1 ≤ rowScore lam (directionRow o e c q))
    (hover : 20 < potential lam (directionRows o e c)) :
    rowScore lam (directionRow o e c v) = 3 ∧
    rowScore lam (directionRow o e c a) = 2 ∧
      ∀ q : Fin t, q ≠ v → q ≠ a → rowScore lam (directionRow o e c q) = 1 := by
  have hcells (q : Fin t) := rowCells_directionRow_le_of_floor_eq
    o e c hleg.lam_pos q (by omega : 2 ≤ t) hn
  have hscore (q : Fin t) := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ (hcells q)
  have hv : rowScore lam (directionRow o e c v) = 3 := by
    have h := hscore v
    rw [hsat] at h
    exact h
  have hnonSat (q : Fin t) (hqv : q ≠ v) : rowScore lam (directionRow o e c q) ≤ 2 := by
    have hd := one_le_rowDefect lam hleg.lam_pos 4 _ (by decide : 1 ≤ 4) (hcells q)
    have hs := hscore q
    have hnot : rowDefect 4 lam (directionRow o e c q) ≠ 1 := by
      intro hq
      have hcap := potential_le_high_of_two_saturated o e he ht3
        (by decide : 2 ≤ 4) hleg.lam_pos hn hleg hqv.symm hsat hq
      norm_num at hcap
      omega
    omega
  have ha2 : rowScore lam (directionRow o e c a) = 2 := by
    have h := hnonSat a hva.symm
    omega
  have hda : rowDefect 4 lam (directionRow o e c a) = 2 := by
    have h := hscore a
    omega
  refine ⟨hv,ha2,?_⟩
  intro q hqv hqa
  have hqle := hnonSat q hqv
  have hqpos := hpositive q
  have hnot2 : rowScore lam (directionRow o e c q) ≠ 2 := by
    intro hq
    have hdq : rowDefect 4 lam (directionRow o e c q) = 2 := by
      have h := hscore q
      omega
    have hcap := ActualN4R2Capacity.actual_r2_capacity o e he hn hhigh
      hleg v hsat hva.symm hqv hqa.symm hda hdq
    omega
  omega

/-- A weak actual seven-point profile suffices; exactness is internal. -/
private theorem weak_seven_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 7 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 4)
    (hhigh : (1/2 : ℝ) ≤ Real.pi/lam-4)
    (v a : Fin 7) (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (ha : 2 ≤ rowScore lam (directionRow o e c a))
    (hpositive : ∀ q : Fin 7, 1 ≤ rowScore lam (directionRow o e c q)) : False := by
  classical
  have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos v (by decide : 2 ≤ 7) hn
  have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
  have hv : rowScore lam (directionRow o e c v) = 3 := by omega
  have hweight (q : Fin 7) : ((2 + if q = v then 6 else 0) + (if q = a then 2 else 0)) ≤
      2 ^ rowScore lam (directionRow o e c q) := by
    by_cases hqv : q = v
    · subst q
      simp [hv,hva]
    · by_cases hqa : q = a
      · subst q
        have h := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ha
        simpa only [if_neg hva.symm,ite_true,show (2 : ℕ)^2 = 4 by decide,Nat.add_zero] using h
      · have h := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (hpositive q)
        simpa only [if_neg hqv,if_neg hqa,Nat.add_zero,pow_one] using h
  have hsum : (∑ q : Fin 7, ((2 + if q = v then 6 else 0) + if q = a then 2 else 0)) = 22 := by
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hlower : 22 ≤ potential lam (directionRows o e c) := by
    rw [← hsum]
    unfold potential exponentAt directionRows
    exact Finset.sum_le_sum (fun q _ => hweight q)
  obtain ⟨_,ha2,htail⟩ := exact_profile_of_overfull o e he (by decide : 3 ≤ 7)
    hleg hn hhigh v a hva hsat ha hpositive (by omega)
  exact ActualHighR1PositiveClosure.actual_seven_positive_r1_false
    o e he hleg hn hhigh v a hva hsat ha2 htail

/-- Any actual positive HIGH4 configuration with SAT and a distinct heavy
has at most six points. No counter-Model or potential premise is needed. -/
theorem actual_positive_sat_heavy_card_le_six {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 4)
    (hhigh : (1/2 : ℝ) ≤ Real.pi/lam-4)
    (v a : Fin t) (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (ha : 2 ≤ rowScore lam (directionRow o e c a))
    (hpositive : ∀ q : Fin t, 1 ≤ rowScore lam (directionRow o e c q)) : t ≤ 6 := by
  classical
  by_contra hnot
  have ht7 : 7 ≤ t := by omega
  obtain ⟨pick,hpick,hkeep⟩ := N3SaturatedBounds.exists_restriction_containing
    ({v,a} : Finset (Fin t))
    (by simp [hva] : ({v,a} : Finset (Fin t)).card ≤ 7) ht7
  obtain ⟨v',hv'⟩ := hkeep v (by simp)
  obtain ⟨a',ha'⟩ := hkeep a (by simp)
  have hva' : v' ≠ a' := by
    intro h
    apply hva
    exact hv'.symm.trans ((congrArg pick h).trans ha')
  let d : Fin 7 → Plane₂ := c ∘ pick
  have hd : Section4Legality d lam := hleg.restrict_injective pick hpick
  have hvold : rowScore lam (directionRow o e c v) = 3 := by
    have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos v (by omega : 2 ≤ t) hn
    have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
    omega
  have hvnew : rowScore lam (directionRow o e d v') = 3 := by
    have hmono := PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos
      (by decide : 2 ≤ 7) pick hpick v'
    rw [hv',hvold] at hmono
    have hc := rowCells_directionRow_le_of_floor_eq o e d hleg.lam_pos v' (by decide : 2 ≤ 7) hn
    have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
    have hb := one_le_rowDefect lam hleg.lam_pos 4 _ (by decide : 1 ≤ 4) hc
    change 3 ≤ rowScore lam (directionRow o e d v') at hmono
    omega
  have hsat' : rowDefect 4 lam (directionRow o e d v') = 1 := by
    have hc := rowCells_directionRow_le_of_floor_eq o e d hleg.lam_pos v' (by decide : 2 ≤ 7) hn
    have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
    omega
  have hheavy : 2 ≤ rowScore lam (directionRow o e d a') := by
    have hmono := PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos
      (by decide : 2 ≤ 7) pick hpick a'
    rw [ha'] at hmono
    exact ha.trans hmono
  have hpos (q : Fin 7) : 1 ≤ rowScore lam (directionRow o e d q) :=
    (hpositive (pick q)).trans (PositiveRowCount.rowScore_le_restrict
      o e c hleg.lam_pos (by decide : 2 ≤ 7) pick hpick q)
  exact weak_seven_impossible o e he hd hn hhigh v' a' hva' hsat' hheavy hpos

/-- Arbitrary-size actual positive HIGH4 SAT/heavy capacity. There is no
minimal Model, exact heavy score, tail profile, seven-subset or capacity
certificate supplied by the caller. Positivity is explicitly retained. -/
theorem actual_positive_sat_heavy_capacity {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi/lam) = 4)
    (hhigh : (1/2 : ℝ) ≤ Real.pi/lam-4)
    (v a : Fin t) (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (ha : 2 ≤ rowScore lam (directionRow o e c a))
    (hpositive : ∀ q : Fin t, 1 ≤ rowScore lam (directionRow o e c q)) :
    potential lam (directionRows o e c) ≤ 20 := by
  classical
  have hcard := actual_positive_sat_heavy_card_le_six o e he hleg hn hhigh v a hva hsat ha hpositive
  by_cases ht3 : 3 ≤ t
  · by_contra hnot
    have hover : 20 < potential lam (directionRows o e c) := by omega
    obtain ⟨hv,ha2,htail⟩ := exact_profile_of_overfull o e he ht3 hleg hn hhigh
      v a hva hsat ha hpositive hover
    have hweight (q : Fin t) : 2 ^ rowScore lam (directionRow o e c q) =
        (2 + if q = v then 6 else 0) + if q = a then 2 else 0 := by
      by_cases hqv : q = v
      · subst q
        simp [hv,hva]
      · by_cases hqa : q = a
        · subst q
          simp [ha2,hva.symm]
        · simp [htail q hqv hqa,hqv,hqa]
    have hmass : potential lam (directionRows o e c) = 2*t+8 := by
      unfold potential exponentAt directionRows
      simp_rw [hweight]
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      omega
    omega
  · have hpair : ({v,a} : Finset (Fin t)).card = 2 := Finset.card_pair hva
    have hle := Finset.card_le_card (Finset.subset_univ ({v,a} : Finset (Fin t)))
    have ht2 : 2 ≤ t := by simpa only [hpair,Finset.card_univ,Fintype.card_fin] using hle
    have hweight (q : Fin t) : 2 ^ rowScore lam (directionRow o e c q) ≤ 8 := by
      have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos q ht2 hn
      have hs := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hc
      have hb := one_le_rowDefect lam hleg.lam_pos 4 _ (by decide : 1 ≤ 4) hc
      have hq : rowScore lam (directionRow o e c q) ≤ 3 := by omega
      simpa only [show (2 : ℕ)^3 = 8 by decide] using
        Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hq
    have hmass : potential lam (directionRows o e c) ≤ 8*t := by
      unfold potential exponentAt directionRows
      have h := Finset.sum_le_sum (fun q (_hq : q ∈ (Finset.univ : Finset (Fin t))) => hweight q)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm] using h
    omega

#print axioms actual_positive_sat_heavy_card_le_six
#print axioms actual_positive_sat_heavy_capacity

end Jsp404.ActualHighR1PositiveCapacity
