import Jsp000404.ActualMaximalLowRowClumps
import Jsp000404.ActualF18HeavyZeroGain
import Jsp000404.ActualProperSubsetDeletionBudget
import Jsp000404.ActualHullWindowScoreLower
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-!
SOURCE_ONLY original-model heavy-clump weight producer.
Whole-clump deletion uses only the original proper-subset ledger. The
retained heavy's new hull window is produced from its inherited extreme
point, and its width is bounded through its actual two endpoint rays.
No restricted counter-model, clump, gain, or capacity is a caller input.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualHeavyClumpWeight

private theorem bool_eq_of_two_ne {a b d : Bool} (ha : a ≠ d) (hb : b ≠ d) : a = b := by
  cases a <;> cases b <;> cases d <;> simp_all

noncomputable def members {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (G : ActualMaximalLowRowClumps.Data 4 o c lam p) (b : Bool) : Finset (Fin s) :=
  Finset.univ.filter (fun q => q ≠ p ∧ G.clumps.code q = b)

private theorem members_nonempty {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (G : ActualMaximalLowRowClumps.Data 4 o c lam p) (b : Bool) :
    (members G b).Nonempty := by
  classical
  obtain ⟨left, right, hlp, hrp, _hlr, hl, hr⟩ := G.clumps.actual_witnesses
  cases b with
  | false => exact ⟨right, by simp [members, hrp, hr]⟩
  | true => exact ⟨left, by simp [members, hlp, hl]⟩

private theorem actual_companion {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (G : ActualMaximalLowRowClumps.Data 4 o c lam p)
    (q : Fin s) (hqp : q ≠ p) :
    ∃ r : Fin s, r ≠ p ∧ r ≠ q ∧ G.clumps.code r = G.clumps.code q := by
  classical
  by_contra hnone
  push Not at hnone
  have hgain : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
    apply rowGain_pos_of_forall_angle_ge o e c H.legality he hqp.symm H.card_ge_three
    intro j hjp hjq
    have hangle := G.clumps.different_angle_ge H.legality q j hqp hjp
      (Ne.symm (hnone j hjp hjq))
    linarith [H.legality.lam_pos]
  have hzero := ActualF18HeavyZeroGain.actual_low_four_heavy_observer_gain_eq_zero
    o e he H p hp q hqp.symm
  rw [hzero] at hgain
  omega

private theorem members_card_ge_two {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (G : ActualMaximalLowRowClumps.Data 4 o c lam p) (b : Bool) :
    2 ≤ (members G b).card := by
  classical
  obtain ⟨q, hq⟩ := members_nonempty G b
  have hqdata := (Finset.mem_filter.mp hq).2
  obtain ⟨r, hrp, hrq, hrqcode⟩ := actual_companion o e he H p hp G q hqdata.1
  have hr : r ∈ members G b := by
    simp [members, hrp, hrqcode.trans hqdata.2]
  have hnontrivial : (members G b).Nontrivial := ⟨q, hq, r, hr, hrq.symm⟩
  exact hnontrivial.two_le_card

/-- A retained original extreme point is extreme in the actual
restriction. This is only hull inheritance, never model inheritance. -/
private theorem hull_of_injective_restriction {s r : ℕ}
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    (keep : Fin r → Fin s) (hkeep : Function.Injective keep) (i : Fin r)
    (hhull : IsHullVertex c (keep i)) : IsHullVertex (c ∘ keep) i := by
  classical
  have hnot := ActualHullRayWindow.not_mem_hull_others_of_isHullVertex hinj hhull
  apply FullHullInteriorDefect.isHullVertex_of_not_mem_hull_others (c ∘ keep) i
  intro hmem
  apply hnot
  have hsub : (c ∘ keep) '' ({i} : Set (Fin r))ᶜ ⊆
      c '' ({keep i} : Set (Fin s))ᶜ := by
    rintro x ⟨j, hj, rfl⟩
    refine ⟨keep j, ?_, rfl⟩
    have hji : j ≠ i := by simpa using hj
    simpa using hkeep.ne hji
  exact (convexHull_mono hsub) hmem

private theorem whole_clump_weight_lower {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (hpHull : IsHullVertex c p)
    (G : ActualMaximalLowRowClumps.Data 4 o c lam p)
    (hcards : ∀ b, 2 ≤ (members G b).card) (b : Bool) :
    (potential lam (directionRows o e c) - 16) + 4 ≤
      ∑ q ∈ members G b, 2 ^ rowScore lam (directionRow o e c q) := by
  classical
  let C := members G b
  let S : Finset (Fin s) := Cᶜ
  have hpS : p ∈ S := by simp [S, C, members]
  have hpOther : p ∉ members G (!b) := by simp [members]
  have hotherSub : insert p (members G (!b)) ⊆ S := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqp | hq
    · simpa only [hqp] using hpS
    · apply Finset.mem_compl.mpr
      intro hqC
      have ho := (Finset.mem_filter.mp hq).2.2
      have hc := (Finset.mem_filter.mp hqC).2.2
      have hne : (!b) ≠ b := by cases b <;> decide
      exact hne (ho.symm.trans hc)
  have hr : 3 ≤ S.card := by
    have hle := Finset.card_le_card hotherSub
    rw [Finset.card_insert_of_notMem hpOther] at hle
    have htwo := hcards (!b)
    omega
  have hproper : S.card < s := by
    have hsum : S.card + C.card = s := by
      simpa only [S, Fintype.card_fin] using Finset.card_compl_add_card C
    have htwo := hcards b
    change 2 ≤ C.card at htwo
    omega
  let E : Fin S.card ≃o ↥S := S.orderIsoOfFin rfl
  let keep : Fin S.card → Fin s := fun i => (E i).val
  have hkeep : Function.Injective keep := Subtype.val_injective.comp E.injective
  have hkeepMem (i : Fin S.card) : keep i ∈ S := (E i).property
  have hImage : (Finset.univ.image keep) = S := by
    ext q
    constructor
    · intro hq
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hq
      exact hkeepMem i
    · intro hq
      exact Finset.mem_image.mpr ⟨E.symm ⟨q, hq⟩, Finset.mem_univ _,
        by simp [keep]⟩
  let center : Fin S.card := E.symm ⟨p, hpS⟩
  have hcenter : keep center = p := by simp [keep, center]
  have hnewLeg := H.legality.restrict_injective keep hkeep
  have hnewHull : IsHullVertex (c ∘ keep) center :=
    hull_of_injective_restriction H.legality.inj keep hkeep center
      (by simpa only [hcenter] using hpHull)
  obtain ⟨W⟩ := ActualHullRayWindow.exists_actual_hull_ray_window
    o hr hnewLeg center hnewHull
  have hleft : keep W.left ≠ p := by
    simpa only [hcenter] using hkeep.ne W.left_ne_center
  have hright : keep W.right ≠ p := by
    simpa only [hcenter] using hkeep.ne W.right_ne_center
  have hcode (i : Fin S.card) (hip : keep i ≠ p) : G.clumps.code (keep i) ≠ b := by
    intro hib
    have hnotC : keep i ∉ C := Finset.mem_compl.mp (hkeepMem i)
    exact hnotC (by simp [C, members, hip, hib])
  have hsame : G.clumps.code (keep W.left) = G.clumps.code (keep W.right) :=
    bool_eq_of_two_ne (hcode W.left hleft) (hcode W.right hright)
  have hangle := G.clumps.same_angle_le H.legality
    (keep W.left) (keep W.right) hleft hright hsame
  have hwidth : W.width ≤ Real.pi - 4 * lam := by
    rw [W.width_eq_actual_angle]
    simpa only [Function.comp_apply, hcenter] using hangle
  have hnew : 3 ≤ rowScore lam (directionRow o e (c ∘ keep) center) :=
    ActualHullWindowScoreLower.rowScore_ge_three_of_remainder_window
      o e he hnewLeg W H.legality.lam_pos hwidth
  have hold : rowScore lam (directionRow o e c (keep center)) = 2 := by
    simpa only [hcenter] using hp
  have hgain : 1 ≤ ActualProperSubsetDeletionBudget.restrictionGain
      o e c lam keep center := by
    unfold ActualProperSubsetDeletionBudget.restrictionGain
    omega
  have hpow : 2 ≤ 2 ^ ActualProperSubsetDeletionBudget.restrictionGain
      o e c lam keep center := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hgain
  have hfactor : 1 ≤ 2 ^ ActualProperSubsetDeletionBudget.restrictionGain
      o e c lam keep center - 1 := by omega
  have hterm : 4 ≤ 2 ^ rowScore lam (directionRow o e c (keep center)) *
      (2 ^ ActualProperSubsetDeletionBudget.restrictionGain o e c lam keep center - 1) := by
    have hmul := Nat.mul_le_mul_left 4 hfactor
    simpa only [hold, show (2 : ℕ) ^ 2 = 4 by decide, Nat.mul_one] using hmul
  have htermLe : 2 ^ rowScore lam (directionRow o e c (keep center)) *
      (2 ^ ActualProperSubsetDeletionBudget.restrictionGain o e c lam keep center - 1) ≤
      ActualProperSubsetDeletionBudget.restrictionExpense o e c lam keep :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ center)
  have hexpense : 4 ≤ ActualProperSubsetDeletionBudget.restrictionExpense
      o e c lam keep := hterm.trans htermLe
  have hremoved : ActualProperSubsetDeletionBudget.removedWeight o e c lam keep =
      ∑ q ∈ members G b, 2 ^ rowScore lam (directionRow o e c q) := by
    unfold ActualProperSubsetDeletionBudget.removedWeight
    rw [hImage]
    simp only [S, C, compl_compl]
  have hbudget := ActualProperSubsetDeletionBudget.actual_proper_subset_gain_budget
    o e H hr hproper keep hkeep
  rw [hremoved] at hbudget
  omega

/-- Both sides and their weights are actual original-configuration
outputs. The original excess is retained even for potential seventeen. -/
structure Data {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (lam : ℝ) (p : Fin s) where
  geometry : ActualMaximalLowRowClumps.Data 4 o c lam p
  card_ge_two : ∀ b : Bool, 2 ≤ (members geometry b).card
  weight_lower : ∀ b : Bool,
    (potential lam (directionRows o e c) - 16) + 4 ≤
      ∑ q ∈ members geometry b, 2 ^ rowScore lam (directionRow o e c q)

/-- Main original-model producer: no clump, restriction, score-growth
certificate or supplied proper-subset budget is an input. -/
theorem exists_actual_heavy_clump_weight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (hwide : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b)) : Nonempty (Data o e c lam p) := by
  classical
  obtain ⟨hfloor, _hdelta, _hpi⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by have := H.card_ge_three; omega : 2 ≤ s) hfloor
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4
    (directionRow o e c p) hcells
  have hdef : rowDefect 4 lam (directionRow o e c p) ≤ 2 := by omega
  have hpHull := FullHullInteriorDefect.low_defect_is_full_hull_vertex
    o e he H.legality hfloor p hdef
  obtain ⟨G⟩ := ActualMaximalLowRowClumps.exists_actual_maximal_low_row_clumps
    H.card_ge_three (by decide : 4 ≤ 4) o e he H.legality
    (by simpa using H.scale_lower) (by simpa using H.scale_upper) p hpHull hp hwide
  have hcards : ∀ b : Bool, 2 ≤ (members G b).card :=
    members_card_ge_two o e he H p hp G
  exact ⟨{
    geometry := G
    card_ge_two := hcards
    weight_lower := whole_clump_weight_lower o e he H p hp hpHull G hcards }⟩

/-- In F18, either internally produced side consisting entirely of
original light points has at least three members. -/
theorem exists_actual_F18_heavy_clumps_pure_light_card_ge_three {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (hwide : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b)) :
    ∃ D : Data o e c lam p, ∀ b : Bool,
      (∀ q ∈ members D.geometry b, rowScore lam (directionRow o e c q) = 1) →
      3 ≤ (members D.geometry b).card := by
  classical
  obtain ⟨D⟩ := exists_actual_heavy_clump_weight o e he H p hp hwide
  refine ⟨D, ?_⟩
  intro b hlight
  have hweight := D.weight_lower b
  have hsum : (∑ q ∈ members D.geometry b,
      2 ^ rowScore lam (directionRow o e c q)) = 2 * (members D.geometry b).card := by
    calc
      _ = ∑ _q ∈ members D.geometry b, (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [hlight q hq, pow_one]
      _ = _ := by simp [Nat.mul_comm]
  rw [hF, hsum] at hweight
  omega

/-- In F17, either internally produced pure original-zero side has
at least five members. Its support is not restricted to interior points. -/
theorem exists_actual_F17_heavy_clumps_pure_zero_card_ge_five {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hF : potential lam (directionRows o e c) = 17)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2)
    (hwide : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b)) :
    ∃ D : Data o e c lam p, ∀ b : Bool,
      (∀ q ∈ members D.geometry b, rowScore lam (directionRow o e c q) = 0) →
      5 ≤ (members D.geometry b).card := by
  classical
  obtain ⟨D⟩ := exists_actual_heavy_clump_weight o e he H p hp hwide
  refine ⟨D, ?_⟩
  intro b hzero
  have hweight := D.weight_lower b
  have hsum : (∑ q ∈ members D.geometry b,
      2 ^ rowScore lam (directionRow o e c q)) = (members D.geometry b).card := by
    calc
      _ = ∑ _q ∈ members D.geometry b, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [hzero q hq, pow_zero]
      _ = _ := by simp
  rw [hF, hsum] at hweight
  omega

#print axioms exists_actual_heavy_clump_weight
#print axioms exists_actual_F18_heavy_clumps_pure_light_card_ge_three
#print axioms exists_actual_F17_heavy_clumps_pure_zero_card_ge_five

end Jsp404.ActualHeavyClumpWeight
