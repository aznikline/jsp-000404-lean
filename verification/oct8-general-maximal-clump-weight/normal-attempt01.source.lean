import Jsp000404.ActualMaximalLowRowClumps
import Jsp000404.ActualMinimalBandCounterexample
import Jsp000404.ActualProperSubsetDeletionBudget
import Jsp000404.ActualHullWindowScoreLower
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-! SOURCE_ONLY uniform maximal nonsaturated LOW-row clump weights.

This new module parameterizes the separately verified n4 clump ledger.
The public inputs are n>=4, the original LOW minimum-counter Model with
cap2^n, an original score n-2 row, and a genuine nonacute original angle.
All zero gains, full-hull membership, actual cuts, side cardinalities and
proper-subset costs are derived internally. No restricted Model is used.
This source is not a kernel receipt or a general capacity conclusion.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualMaximalLowClumpWeight

private theorem bool_eq_of_two_ne {a b d : Bool} (ha : a ≠ d) (hb : b ≠ d) : a = b := by
  cases a <;> cases b <;> cases d <;> simp_all

noncomputable def members {s n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (G : ActualMaximalLowRowClumps.Data n o c lam p) (b : Bool) : Finset (Fin s) :=
  Finset.univ.filter (fun q => q ≠ p ∧ G.clumps.code q = b)

private theorem members_nonempty {s n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (G : ActualMaximalLowRowClumps.Data n o c lam p) (b : Bool) :
    (members G b).Nonempty := by
  classical
  obtain ⟨left, right, hlp, hrp, _hlr, hl, hr⟩ := G.clumps.actual_witnesses
  cases b with
  | false => exact ⟨right, by simp [members, hrp, hr]⟩
  | true => exact ⟨left, by simp [members, hlp, hl]⟩

/-- The original LOW model supplies nonsaturation and hence score at most
n-2. Positive gain at a maximal-score observer p would cover the original
weight of any distinct deleted target q and make q actually removable.
No fixed potential value or caller-supplied score/gain cap is needed. -/
theorem actual_maximal_observer_gain_eq_zero {s n : ℕ}
    (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (q : Fin s) (hpq : p ≠ q) :
    rowGain lam (directionRow o e c p) (deleteIndex o e c q p) = 0 := by
  obtain ⟨hfloor,hdelta,hpi⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by omega : 2 ≤ n) H.legality.lam_pos H.scale_lower H.scale_upper
  have hdef := ActualMinimalBandCounterexample.low_model_nonsaturated
    (n := n) (by omega : 2 ≤ n) o e he H
  have hupper (i : Fin s) : rowScore lam (directionRow o e c i) ≤ n - 2 := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos i
      (by have := H.card_ge_three; omega) hfloor
    have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos n _ hcells
    have hi := hdef i
    omega
  have hs4 : 4 ≤ s := by
    by_contra hnot
    have hs3 : s = 3 := by have := H.card_ge_three; omega
    subst s
    have hcap : potential lam (directionRows o e c) ≤ 2 ^ n := by
      simpa using base3_potential_le (o := o) (e := e) H.legality he hpi hfloor
        (by omega : 2 ≤ n) hdelta
    have hover := H.over_cap
    omega
  obtain ⟨u,rfl⟩ : ∃ u : ℕ, s = u+1 := ⟨s-1,by omega⟩
  have hs3 : 3 ≤ u := by omega
  by_contra hnot
  have hpos : 1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by omega
  have hrem : Removable lam (fun v i => deleteIndex o e c v i)
      (directionRows o e c) q := by
    apply removable_of_gain1_ge H.legality.lam_pos
      (fun v i => deleteIndex o e c v i) (directionRows o e c) q
      (fun i => directionRow_sorted o e c i)
      (fun i x hx => Set.mem_Ico.mp (directionRow_mem_Ico o e c hx))
      (fun i => by change 2 ≤ (directionRow o e c i).length
                   rw [directionRow_length]; omega)
      (fun i hi => deleteIndex_lt o e c hi) p hpq hpos
    change rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c p)
    rw [hp]
    exact hupper q
  exact ActualMinimalBandCounterexample.not_actual_removable hs3 o e H q hrem


private theorem actual_companion {s n : ℕ}
    (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (G : ActualMaximalLowRowClumps.Data n o c lam p)
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
  have hzero := actual_maximal_observer_gain_eq_zero
    hn4 o e he H p hp q hqp.symm
  rw [hzero] at hgain
  omega

private theorem members_card_ge_two {s n : ℕ}
    (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (G : ActualMaximalLowRowClumps.Data n o c lam p) (b : Bool) :
    2 ≤ (members G b).card := by
  classical
  obtain ⟨q, hq⟩ := members_nonempty G b
  have hqdata := (Finset.mem_filter.mp hq).2
  obtain ⟨r, hrp, hrq, hrqcode⟩ := actual_companion hn4 o e he H p hp G q hqdata.1
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

set_option maxHeartbeats 600000 in
private theorem whole_clump_weight_lower {s n : ℕ}
    (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (hpHull : IsHullVertex c p)
    (G : ActualMaximalLowRowClumps.Data n o c lam p)
    (hcards : ∀ b, 2 ≤ (members G b).card) (b : Bool) :
    (potential lam (directionRows o e c) - 2 ^ n) + 2 ^ (n - 2) ≤
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
  have hwidth : W.width ≤ Real.pi - (n : ℝ) * lam := by
    rw [W.width_eq_actual_angle]
    simpa only [Function.comp_apply, hcenter] using hangle
  have hnew : n - 1 ≤ rowScore lam (directionRow o e (c ∘ keep) center) :=
    ActualHullWindowScoreLower.rowScore_ge_sub_one_of_actual_window
      o e he hnewLeg W H.legality.lam_pos n (by omega : 1 ≤ n) hwidth
  have hold : rowScore lam (directionRow o e c (keep center)) = n - 2 := by
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
  have hterm : 2 ^ (n - 2) ≤ 2 ^ rowScore lam (directionRow o e c (keep center)) *
      (2 ^ ActualProperSubsetDeletionBudget.restrictionGain o e c lam keep center - 1) := by
    have hmul := Nat.mul_le_mul_left (2 ^ (n - 2)) hfactor
    simpa only [hold, Nat.mul_one] using hmul
  have htermLe : 2 ^ rowScore lam (directionRow o e c (keep center)) *
      (2 ^ ActualProperSubsetDeletionBudget.restrictionGain o e c lam keep center - 1) ≤
      ActualProperSubsetDeletionBudget.restrictionExpense o e c lam keep := by
    unfold ActualProperSubsetDeletionBudget.restrictionExpense
    exact Finset.single_le_sum
      (f := fun i : Fin S.card =>
        2 ^ rowScore lam (directionRow o e c (keep i)) *
          (2 ^ ActualProperSubsetDeletionBudget.restrictionGain o e c lam keep i - 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ center)
  have hexpense : 2 ^ (n - 2) ≤ ActualProperSubsetDeletionBudget.restrictionExpense
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
outputs. The entire original excess above the power cap is retained. -/
structure Data {s : ℕ} (n : ℕ) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (lam : ℝ) (p : Fin s) where
  geometry : ActualMaximalLowRowClumps.Data n o c lam p
  card_ge_two : ∀ b : Bool, 2 ≤ (members geometry b).card
  weight_lower : ∀ b : Bool,
    (potential lam (directionRows o e c) - 2 ^ n) + 2 ^ (n - 2) ≤
      ∑ q ∈ members geometry b, 2 ^ rowScore lam (directionRow o e c q)

/-- Main original-model producer: no clump, restriction, score-growth
certificate or supplied proper-subset budget is an input. -/
theorem exists_actual_maximal_low_clump_weight {s n : ℕ}
    (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = n - 2)
    (hwide : ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b)) : Nonempty (Data n o e c lam p) := by
  classical
  obtain ⟨hfloor, _hdelta, _hpi⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by omega : 2 ≤ n) H.legality.lam_pos H.scale_lower H.scale_upper
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by have := H.card_ge_three; omega : 2 ≤ s) hfloor
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos n
    (directionRow o e c p) hcells
  have hdef : rowDefect n lam (directionRow o e c p) ≤ 2 := by omega
  have hpHull := FullHullInteriorDefect.low_defect_is_full_hull_vertex
    o e he H.legality hfloor p hdef
  obtain ⟨G⟩ := ActualMaximalLowRowClumps.exists_actual_maximal_low_row_clumps
    H.card_ge_three hn4 o e he H.legality
    (by simpa using H.scale_lower) (by simpa using H.scale_upper) p hpHull hp hwide
  have hcards : ∀ b : Bool, 2 ≤ (members G b).card :=
    members_card_ge_two hn4 o e he H p hp G
  exact ⟨{
    geometry := G
    card_ge_two := hcards
    weight_lower := whole_clump_weight_lower hn4 o e he H p hp hpHull G hcards }⟩


#print axioms actual_maximal_observer_gain_eq_zero
#print axioms exists_actual_maximal_low_clump_weight

end Jsp404.ActualMaximalLowClumpWeight
