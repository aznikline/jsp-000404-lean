import Jsp000404.TwoSaturatedDeficit
import Jsp000404.ConeCorridor

/-!
# Geometry for the corridor between two saturated anchors

The common innermost point is selected from the actual finite
configuration. Its two base angles are simultaneous minima, as forced
by the strict nested-triangle theorem.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- A strictly nested pair increases both base angles. The positive
angle increments are derived from noncollinearity. -/
theorem nested_base_angles_lt {A B C D E : Plane₂}
    (hE : Sbtw ℝ A E B) (hC : Sbtw ℝ D C E)
    (hCAD : ¬ Collinear ℝ ({C, A, D} : Set Plane₂))
    (hCBD : ¬ Collinear ℝ ({C, B, D} : Set Plane₂)) :
    ∠ B A C < ∠ B A D ∧ ∠ A B C < ∠ A B D := by
  have hA := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := A) hC
  rw [hE.angle_eq_right C, hE.angle_eq_right D] at hA
  rw [EuclideanGeometry.angle_comm D A C,
    EuclideanGeometry.angle_comm C A B,
    EuclideanGeometry.angle_comm D A B] at hA
  have hB := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := B) hC
  rw [hE.symm.angle_eq_right C, hE.symm.angle_eq_right D] at hB
  rw [EuclideanGeometry.angle_comm D B C,
    EuclideanGeometry.angle_comm C B A,
    EuclideanGeometry.angle_comm D B A] at hB
  constructor
  · linarith [EuclideanGeometry.angle_pos_of_not_collinear hCAD]
  · linarith [EuclideanGeometry.angle_pos_of_not_collinear hCBD]

/-- There is one remaining center inside every triangle formed by the
two saturated anchors and any other remaining center. -/
theorem two_saturated_exists_innermost {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs3 : 3 ≤ s)
    {i j : Fin s} (hij : i ≠ j)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    ∃ k : Fin s, i ≠ k ∧ j ≠ k ∧
      ∀ l : Fin s, i ≠ l → j ≠ l → k ≠ l →
        ∃ E : Plane₂, Sbtw ℝ (c i) E (c j) ∧ Sbtw ℝ (c l) (c k) E := by
  classical
  have hcard : ({i, j} : Finset (Fin s)).card <
      (Finset.univ : Finset (Fin s)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    have htwo : ({i, j} : Finset (Fin s)).card = 2 := by simp [hij]
    omega
  obtain ⟨k₀, _, hk₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hk₀i : k₀ ≠ i := by simpa only [Finset.mem_insert, Finset.mem_singleton,
    not_or] using (show k₀ ≠ i ∧ k₀ ≠ j by simpa using hk₀) |>.1
  have hk₀j : k₀ ≠ j := by simpa only [Finset.mem_insert, Finset.mem_singleton,
    not_or] using (show k₀ ≠ i ∧ k₀ ≠ j by simpa using hk₀) |>.2
  let R := {k : Fin s // k ≠ i ∧ k ≠ j}
  letI : Nonempty R := ⟨⟨k₀, hk₀i, hk₀j⟩⟩
  let a : R → ℝ := fun k => ∠ (c j) (c i) (c k)
  obtain ⟨k, _, hkmin⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  refine ⟨k, k.property.1.symm, k.property.2.symm, ?_⟩
  intro l hil hjl hkl
  obtain ⟨E, hE, hinner | houter⟩ :=
    two_saturated_nested o e he hn2 hlam hn hleg (by omega)
      hij k.property.1.symm hil k.property.2.symm hjl hkl hi hj
  · exact ⟨E, hE, hinner⟩
  · have hlt := (nested_base_angles_lt hE houter
      (legal_triple_not_collinear hleg hil.symm hkl.symm k.property.1.symm)
      (legal_triple_not_collinear hleg hjl.symm hkl.symm k.property.2.symm)).1
    have hmin := hkmin ⟨l, hil.symm, hjl.symm⟩ (Finset.mem_univ _)
    dsimp [a] at hmin
    linarith

/-- The actual innermost center simultaneously minimizes both base
angles. The minimum-angle sum still satisfies the legal facing bound. -/
theorem two_saturated_exists_common_base_minimum {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs3 : 3 ≤ s)
    {i j : Fin s} (hij : i ≠ j)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    ∃ k : Fin s, i ≠ k ∧ j ≠ k ∧
      lam ≤ ∠ (c j) (c i) (c k) + ∠ (c i) (c j) (c k) ∧
      ∀ l : Fin s, i ≠ l → j ≠ l →
        ∠ (c j) (c i) (c k) ≤ ∠ (c j) (c i) (c l) ∧
        ∠ (c i) (c j) (c k) ≤ ∠ (c i) (c j) (c l) := by
  obtain ⟨k, hik, hjk, hk⟩ :=
    two_saturated_exists_innermost o e he hn2 hlam hn hleg hs3 hij hi hj
  refine ⟨k, hik, hjk, hleg.facing_lower hij hjk hik, ?_⟩
  intro l hil hjl
  by_cases hkl : k = l
  · subst l
    exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨E, hE, hC⟩ := hk l hil hjl hkl
    have hlt := nested_base_angles_lt hE hC
      (legal_triple_not_collinear hleg hik.symm hkl hil)
      (legal_triple_not_collinear hleg hjk.symm hkl hjl)
    exact ⟨hlt.1.le, hlt.2.le⟩

private theorem linRep_coe_of_mem {x : ℝ} (hx : x ∈ Set.Ico 0 Real.pi) :
    linRep (x : Real.Angle) = x :=
  (eq_linRep_of_int_pi hx ⟨0, by simp⟩).symm

private theorem linRep_neg_coe_of_pos_lt {x : ℝ} (hx : 0 < x) (hxpi : x < Real.pi) :
    linRep (-(x : Real.Angle)) = Real.pi - x := by
  apply Eq.symm
  apply eq_linRep_of_int_pi ⟨by linarith, by linarith⟩
  refine ⟨1, ?_⟩
  simp only [Real.Angle.coe_sub, one_zsmul]
  abel

/-- In the base-line reference chart, the anchor directions are the
base angles or their supplements according to the sign at the first
anchor. This explicitly fixes the possible reflection of the chart. -/
theorem base_anchor_reps_of_sign
    (o : Orientation ℝ Plane₂ (Fin 2)) {A B P : Plane₂}
    (hAB : A ≠ B) (hPA : P ≠ A) (hPB : P ≠ B)
    (ha : 0 < ∠ B A P) (hapi : ∠ B A P < Real.pi)
    (hb : 0 < ∠ A B P) (hbpi : ∠ A B P < Real.pi) :
    ((o.oangle (B - A) (P - A)).sign = 1 →
      linRep (o.oangle (B - A) (A - P)) = ∠ B A P ∧
      linRep (o.oangle (B - A) (B - P)) = Real.pi - ∠ A B P) ∧
    ((o.oangle (B - A) (P - A)).sign = -1 →
      linRep (o.oangle (B - A) (A - P)) = Real.pi - ∠ B A P ∧
      linRep (o.oangle (B - A) (B - P)) = ∠ A B P) := by
  letI : Module.Oriented ℝ Plane₂ (Fin 2) := ⟨o⟩
  have hswap := EuclideanGeometry.oangle_swap₁₂_sign B A P
  change -(o.oangle (B - A) (P - A)).sign =
    (o.oangle (A - B) (P - B)).sign at hswap
  have hArep : linRep (o.oangle (B - A) (A - P)) =
      linRep (o.oangle (B - A) (P - A)) := by
    rw [show A - P = -(P - A) by abel,
      o.oangle_neg_right (sub_ne_zero.mpr hAB.symm) (sub_ne_zero.mpr hPA), linRep_add_pi]
  have hBrep : linRep (o.oangle (B - A) (B - P)) =
      linRep (o.oangle (A - B) (P - B)) := by
    rw [show B - A = -(A - B) by abel, show B - P = -(P - B) by abel,
      o.oangle_neg_neg]
  constructor
  · intro hsign
    have hsignB : (o.oangle (A - B) (P - B)).sign = -1 := by simpa [hsign] using hswap.symm
    rw [hArep, hBrep, o.oangle_eq_angle_of_sign_eq_one hsign,
      o.oangle_eq_neg_angle_of_sign_eq_neg_one hsignB]
    change linRep (∠ B A P : Real.Angle) = ∠ B A P ∧
      linRep (-(∠ A B P : Real.Angle)) = Real.pi - ∠ A B P
    exact ⟨linRep_coe_of_mem ⟨ha.le, hapi⟩, linRep_neg_coe_of_pos_lt hb hbpi⟩
  · intro hsign
    have hsignB : (o.oangle (A - B) (P - B)).sign = 1 := by simpa [hsign] using hswap.symm
    rw [hArep, hBrep, o.oangle_eq_neg_angle_of_sign_eq_neg_one hsign,
      o.oangle_eq_angle_of_sign_eq_one hsignB]
    change linRep (-(∠ B A P : Real.Angle)) = Real.pi - ∠ B A P ∧
      linRep (∠ A B P : Real.Angle) = ∠ A B P
    exact ⟨linRep_neg_coe_of_pos_lt ha hapi, linRep_coe_of_mem ⟨hb.le, hbpi⟩⟩

/-- At the inner point of a nested pair, the chord direction is at
least `lam` away from both anchor directions. The narrow end margins
force the chord into the ordinary interval between those anchors. -/
theorem inner_chord_corridor_of_anchor_reps
    (o : Orientation ℝ Plane₂ (Fin 2)) {e A B C D E : Plane₂}
    (he : e ≠ 0) (hAC : A ≠ C) (hBC : B ≠ C) (hDC : D ≠ C)
    {lam a b : ℝ} (hlam : 0 < lam) (ha : a < lam) (hb : b < lam)
    (hE : Sbtw ℝ A E B) (hC : Sbtw ℝ D C E)
    (hABcap : ∠ A C B ≤ Real.pi - lam)
    (hADcap : ∠ A C D ≤ Real.pi - lam)
    (hBDcap : ∠ B C D ≤ Real.pi - lam)
    (hArep : linRep (o.oangle e (A - C)) = a)
    (hBrep : linRep (o.oangle e (B - C)) = Real.pi - b) :
    linRep (o.oangle e (D - C)) ∈ Set.Icc (lam + a) (Real.pi - lam - b) := by
  have hsum := angle_sum_eq_two_pi_of_nested hE hC
  have hADlow : lam ≤ ∠ A C D := by linarith
  have hBDlow : lam ≤ ∠ B C D := by linarith
  have hAsep := (linRep_sub_mem_Icc (o := o) he
    (sub_ne_zero.mpr hAC) (sub_ne_zero.mpr hDC) ⟨hADlow, hADcap⟩).1
  have hBsep := (linRep_sub_mem_Icc (o := o) he
    (sub_ne_zero.mpr hBC) (sub_ne_zero.mpr hDC) ⟨hBDlow, hBDcap⟩).1
  rw [hArep] at hAsep
  rw [hBrep] at hBsep
  have hr := linRep_mem_Ico (o.oangle e (D - C))
  have hlow : a ≤ linRep (o.oangle e (D - C)) := by
    by_contra h
    have hpos : 0 < a - linRep (o.oangle e (D - C)) := by linarith
    rw [abs_of_pos hpos] at hAsep
    linarith [hr.1]
  have hhigh : linRep (o.oangle e (D - C)) ≤ Real.pi - b := by
    by_contra h
    have hneg : Real.pi - b - linRep (o.oangle e (D - C)) < 0 := by linarith
    rw [abs_of_neg hneg] at hBsep
    linarith [hr.2]
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)] at hAsep
  rw [abs_of_nonneg (sub_nonneg.mpr hhigh)] at hBsep
  constructor <;> linarith

/-- One global sign choice fixes which anchor is the first endpoint in
the base-line projective chart. The order cannot vary between rows. -/
theorem two_saturated_base_anchor_rep_branches {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k₀ : Fin s} (hij : i ≠ j) (hik₀ : i ≠ k₀) (hjk₀ : j ≠ k₀)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    (∀ k : Fin s, i ≠ k → j ≠ k →
      dirRep o (c j - c i) c k i = ∠ (c j) (c i) (c k) ∧
      dirRep o (c j - c i) c k j = Real.pi - ∠ (c i) (c j) (c k)) ∨
    (∀ k : Fin s, i ≠ k → j ≠ k →
      dirRep o (c j - c i) c k i = Real.pi - ∠ (c j) (c i) (c k) ∧
      dirRep o (c j - c i) c k j = ∠ (c i) (c j) (c k)) := by
  letI : Module.Oriented ℝ Plane₂ (Fin 2) := ⟨o⟩
  let sig : Fin s → SignType := fun k => (∡ (c j) (c i) (c k)).sign
  have hsame k (hik : i ≠ k) (hjk : j ≠ k) : sig k = sig k₀ := by
    by_cases hkk : k = k₀
    · subst k
      rfl
    · have hside := two_saturated_sSameSide o e he hn2 hlam hn hleg hs2
        hij hik₀ hik hjk₀ hjk (Ne.symm hkk) hi hj
      have h := hside.oangle_sign_eq
        (left_mem_affineSpan_pair ℝ (c i) (c j))
        (right_mem_affineSpan_pair ℝ (c i) (c j))
      rw [EuclideanGeometry.oangle_rotate_sign (c j) (c i) (c k),
        EuclideanGeometry.oangle_rotate_sign (c j) (c i) (c k₀)] at h
      exact h
  have hnz : sig k₀ ≠ 0 := by
    intro hz
    exact (legal_triple_not_collinear hleg hij.symm hjk₀ hik₀)
      (EuclideanGeometry.oangle_sign_eq_zero_iff_collinear.mp hz)
  have hchart k (hik : i ≠ k) (hjk : j ≠ k) :=
    base_anchor_reps_of_sign o (hleg.inj.ne hij)
      (hleg.inj.ne hik.symm) (hleg.inj.ne hjk.symm)
      (EuclideanGeometry.angle_pos_of_not_collinear
        (legal_triple_not_collinear hleg hij.symm hjk hik))
      (lt_of_le_of_lt (hleg.triAngle j i k hij.symm hik hjk) (sub_lt_self _ hlam))
      (EuclideanGeometry.angle_pos_of_not_collinear
        (legal_triple_not_collinear hleg hij hik hjk))
      (lt_of_le_of_lt (hleg.triAngle i j k hij hjk hik) (sub_lt_self _ hlam))
  rcases SignType.trichotomy (sig k₀) with hneg | hzero | hpos
  · right
    intro k hik hjk
    exact (hchart k hik hjk).2 ((hsame k hik hjk).trans hneg)
  · exact False.elim (hnz hzero)
  · left
    intro k hik hjk
    exact (hchart k hik hjk).1 ((hsame k hik hjk).trans hpos)

/-- Endpoint data for the two-anchor bin cover. The anchor pair may be
exchanged globally; its permutation is all row assembly needs. -/
structure TwoAnchorCorridorData {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (eref : Plane₂)
    (c : Fin s → Plane₂) (i j : Fin s) (lam beta : ℝ) where
  a : Fin s → ℝ
  b : Fin s → ℝ
  amin : ℝ
  bmin : ℝ
  amin_pos : 0 < amin
  bmin_pos : 0 < bmin
  min_sum_lower : lam ≤ amin + bmin
  min_sum_upper : amin + bmin ≤ 2 * beta
  row_bounds : ∀ k, i ≠ k → j ≠ k →
    0 < a k ∧ a k ≤ beta ∧ 0 < b k ∧ b k ≤ beta ∧
      lam ≤ a k + b k ∧ amin ≤ a k ∧ bmin ≤ b k
  anchor_reps : ∀ k, i ≠ k → j ≠ k →
    ([dirRep o eref c k i, dirRep o eref c k j] : List ℝ).Perm
      [a k, Real.pi - b k]
  chords : ∀ k l, i ≠ k → j ≠ k → i ≠ l → j ≠ l → k ≠ l →
    dirRep o eref c k l ∈ Set.Icc (lam + amin) (Real.pi - lam - bmin)

private theorem chord_corridor_of_two_saturated_charts {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e eref : Plane₂)
    (he : e ≠ 0) (href : eref ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j : Fin s} (hij : i ≠ j)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1)
    (a b : Fin s → ℝ) (amin bmin : ℝ)
    (hchart : ∀ k, i ≠ k → j ≠ k →
      dirRep o eref c k i = a k ∧ dirRep o eref c k j = Real.pi - b k ∧
      a k < lam ∧ b k < lam ∧ amin ≤ a k ∧ bmin ≤ b k)
    {k l : Fin s} (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) :
    dirRep o eref c k l ∈ Set.Icc (lam + amin) (Real.pi - lam - bmin) := by
  obtain ⟨E, hE, hinner | hinner⟩ :=
    two_saturated_nested o e he hn2 hlam hn hleg hs2
      hij hik hil hjk hjl hkl hi hj
  · obtain ⟨hA, hB, ha, hb, hamin, hbmin⟩ := hchart k hik hjk
    have h := inner_chord_corridor_of_anchor_reps o href
      (hleg.inj.ne hik) (hleg.inj.ne hjk) (hleg.inj.ne hkl.symm)
      hlam ha hb hE hinner
      (hleg.triAngle i k j hik hjk.symm hij)
      (hleg.triAngle i k l hik hkl hil)
      (hleg.triAngle j k l hjk hkl hjl) hA hB
    change dirRep o eref c k l ∈ _ at h
    constructor <;> linarith [h.1, h.2]
  · obtain ⟨hA, hB, ha, hb, hamin, hbmin⟩ := hchart l hil hjl
    have h := inner_chord_corridor_of_anchor_reps o href
      (hleg.inj.ne hil) (hleg.inj.ne hjl) (hleg.inj.ne hkl)
      hlam ha hb hE hinner
      (hleg.triAngle i l j hil hjl.symm hij)
      (hleg.triAngle i l k hil hkl.symm hik)
      (hleg.triAngle j l k hjl hkl.symm hjk) hA hB
    change dirRep o eref c l k ∈ _ at h
    rw [dirRep_comm o eref c href (hleg.inj.ne hkl)]
    constructor <;> linarith [h.1, h.2]

/-- Actual two-saturated geometry supplies the complete corridor data
in the base-line reference. The chart's possible global reversal is
absorbed by exchanging the two endpoint functions. -/
theorem two_saturated_corridor_data {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs3 : 3 ≤ s)
    {i j : Fin s} (hij : i ≠ j)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    Nonempty (TwoAnchorCorridorData o (c j - c i) c i j lam (Real.pi - n * lam)) := by
  classical
  let a : Fin s → ℝ := fun k => ∠ (c j) (c i) (c k)
  let b : Fin s → ℝ := fun k => ∠ (c i) (c j) (c k)
  let beta := Real.pi - n * lam
  have href : c j - c i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hij.symm)
  have hf := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hf
  have hbeta : beta < lam := by dsimp [beta]; linarith
  have hbound k (hik : i ≠ k) (hjk : j ≠ k) :
      0 < a k ∧ a k ≤ beta ∧ 0 < b k ∧ b k ≤ beta ∧ lam ≤ a k + b k := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact EuclideanGeometry.angle_pos_of_not_collinear
        (legal_triple_not_collinear hleg hij.symm hjk hik)
    · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he (by omega)
        hij hik hjk hi
    · exact EuclideanGeometry.angle_pos_of_not_collinear
        (legal_triple_not_collinear hleg hij hik hjk)
    · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he (by omega)
        hij.symm hjk hik hj
    · exact hleg.facing_lower hij hjk hik
  obtain ⟨k₀, hik₀, hjk₀, hminsum, hmin⟩ :=
    two_saturated_exists_common_base_minimum o e he hn2 hlam hn hleg hs3 hij hi hj
  have hk₀ := hbound k₀ hik₀ hjk₀
  rcases two_saturated_base_anchor_rep_branches o e he hn2 hlam hn hleg (by omega)
    hij hik₀ hjk₀ hi hj with hpos | hneg
  · refine ⟨{
      a := a
      b := b
      amin := a k₀
      bmin := b k₀
      amin_pos := hk₀.1
      bmin_pos := hk₀.2.2.1
      min_sum_lower := hminsum
      min_sum_upper := by linarith [hk₀.2.1, hk₀.2.2.2.1]
      row_bounds := ?_
      anchor_reps := ?_
      chords := ?_ }⟩
    · intro k hik hjk
      obtain ⟨ha0, ha, hb0, hb, hsum⟩ := hbound k hik hjk
      exact ⟨ha0, ha, hb0, hb, hsum, (hmin k hik hjk).1, (hmin k hik hjk).2⟩
    · intro k hik hjk
      rw [(hpos k hik hjk).1, (hpos k hik hjk).2]
    · intro k l hik hjk hil hjl hkl
      apply chord_corridor_of_two_saturated_charts o e (c j - c i) he href hn2 hlam hn
        hleg (by omega) hij hi hj a b (a k₀) (b k₀) _ hik hjk hil hjl hkl
      intro q hiq hjq
      obtain ⟨_, haq, _, hbq, _⟩ := hbound q hiq hjq
      exact ⟨(hpos q hiq hjq).1, (hpos q hiq hjq).2,
        haq.trans_lt hbeta, hbq.trans_lt hbeta, (hmin q hiq hjq).1, (hmin q hiq hjq).2⟩
  · refine ⟨{
      a := b
      b := a
      amin := b k₀
      bmin := a k₀
      amin_pos := hk₀.2.2.1
      bmin_pos := hk₀.1
      min_sum_lower := by linarith
      min_sum_upper := by linarith [hk₀.2.1, hk₀.2.2.2.1]
      row_bounds := ?_
      anchor_reps := ?_
      chords := ?_ }⟩
    · intro k hik hjk
      obtain ⟨ha0, ha, hb0, hb, hsum⟩ := hbound k hik hjk
      exact ⟨hb0, hb, ha0, ha, by linarith, (hmin k hik hjk).2, (hmin k hik hjk).1⟩
    · intro k hik hjk
      rw [(hneg k hik hjk).1, (hneg k hik hjk).2]
      exact List.Perm.swap _ _ []
    · intro k l hik hjk hil hjl hkl
      apply chord_corridor_of_two_saturated_charts o e (c j - c i) he href hn2 hlam hn
        hleg (by omega) hij.symm hj hi b a (b k₀) (a k₀) _ hjk hik hjl hil hkl
      intro q hjq hiq
      obtain ⟨_, haq, _, hbq, _⟩ := hbound q hiq hjq
      exact ⟨(hneg q hiq hjq).2, (hneg q hiq hjq).1,
        hbq.trans_lt hbeta, haq.trans_lt hbeta, (hmin q hiq hjq).2, (hmin q hiq hjq).1⟩

end Jsp404

#print axioms Jsp404.nested_base_angles_lt
#print axioms Jsp404.two_saturated_exists_innermost
#print axioms Jsp404.two_saturated_exists_common_base_minimum
#print axioms Jsp404.base_anchor_reps_of_sign
#print axioms Jsp404.inner_chord_corridor_of_anchor_reps
#print axioms Jsp404.two_saturated_base_anchor_rep_branches
#print axioms Jsp404.two_saturated_corridor_data
