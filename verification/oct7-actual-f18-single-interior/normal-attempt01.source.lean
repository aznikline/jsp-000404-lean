import Jsp000404.ActualPureLightBlock
import Jsp000404.ActualInteriorOneClassSize
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

/-!
SOURCE_ONLY actual F18 single-interior consumer.
The original partition, cardinalities and strict mutual nearest pair are
constructed internally. No caller supplies nearest-neighbor information.
The radial minimum used below ranges only over the two nonapex classes.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18SingleInterior

private noncomputable def block {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) : Finset (Fin s) :=
  (ActualInteriorOneClassSize.members D k).image
    (fun i : {i : Fin s // i ≠ p} => i.val)

private theorem block_ne_center {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3)
    {i : Fin s} (hi : i ∈ block D k) : i ≠ p := by
  classical
  obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp hi
  intro hip
  exact j.property (hji.trans hip)

private theorem block_mem_iff {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3)
    (i : Fin s) (hip : i ≠ p) :
    i ∈ block D k ↔ D.classOf ⟨i, hip⟩ = k := by
  classical
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hjk := (Finset.mem_filter.mp hj).2
    have heq : j = ⟨i, hip⟩ := Subtype.ext hji
    simpa only [heq] using hjk
  · intro hik
    exact Finset.mem_image.mpr
      ⟨⟨i, hip⟩, by simp [ActualInteriorOneClassSize.members, hik], rfl⟩

private theorem block_card {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    (block D k).card = (ActualInteriorOneClassSize.members D k).card := by
  classical
  exact Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)

private theorem different_block_ne {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) {k l : Fin 3} (hkl : k ≠ l)
    {i j : Fin s} (hi : i ∈ block D k) (hj : j ∈ block D l) : i ≠ j := by
  intro h
  subst j
  have hip := block_ne_center D k hi
  exact hkl (((block_mem_iff D k i hip).mp hi).symm.trans
    ((block_mem_iff D l i hip).mp hj))

private theorem pair_of_mem_card_two {s : ℕ} (S : Finset (Fin s))
    (hcard : S.card = 2) (w : Fin s) (hw : w ∈ S) :
    ∃ w' : Fin s, w' ≠ w ∧ S = {w, w'} := by
  classical
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hcard
  have hwab : w = a ∨ w = b := by simpa only [hS, Finset.mem_insert,
    Finset.mem_singleton] using hw
  rcases hwab with h | h
  · subst a
    exact ⟨b, hab.symm, hS⟩
  · subst b
    exact ⟨a, hab, by simpa only [Finset.pair_comm] using hS⟩

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

private theorem actual_cosine_identity {s : ℕ} (c : Fin s → Plane₂)
    (p a b : Fin s) :
    dist (c a) (c b) ^ 2 =
      dist (c p) (c a) ^ 2 + dist (c p) (c b) ^ 2 -
      2 * dist (c p) (c a) * dist (c p) (c b) *
        Real.cos (∠ (c a) (c p) (c b)) := by
  have h := EuclideanGeometry.law_cos (c a) (c p) (c b)
  rw [dist_comm (c a) (c p), dist_comm (c b) (c p)] at h
  nlinarith

private theorem cos_lt_half_of_two_scale {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hlo : 2 * Real.pi / 9 < lam) (p a b : Fin s)
    (hangle : 2 * lam ≤ ∠ (c a) (c p) (c b)) :
    Real.cos (∠ (c a) (c p) (c b)) < 1 / 2 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ Real.pi / 3)
    (EuclideanGeometry.angle_le_pi (c a) (c p) (c b))
    (by linarith [Real.pi_pos] : Real.pi / 3 < ∠ (c a) (c p) (c b))
  simpa only [Real.cos_pi_div_three] using h

private theorem radius_lt_cross_of_apex {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (p a b : Fin s) (hap : a ≠ p) (hbp : b ≠ p)
    (hangle : 3 * lam ≤ ∠ (c a) (c p) (c b)) :
    dist (c p) (c a) < dist (c a) (c b) := by
  have ha : 0 < dist (c p) (c a) := dist_pos.mpr (hleg.inj.ne hap.symm)
  have hb : 0 < dist (c p) (c b) := dist_pos.mpr (hleg.inj.ne hbp.symm)
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ Real.pi / 2)
    (EuclideanGeometry.angle_le_pi (c a) (c p) (c b))
    (by linarith [Real.pi_pos] : Real.pi / 2 < ∠ (c a) (c p) (c b))
  rw [Real.cos_pi_div_two] at hc
  have hprod : 2 * dist (c p) (c a) * dist (c p) (c b) *
      Real.cos (∠ (c a) (c p) (c b)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hc.le
  have hcos := actual_cosine_identity c p a b
  nlinarith [show 0 ≤ dist (c a) (c b) from dist_nonneg]

private theorem radius_lt_cross_of_min {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (p a b : Fin s) (hap : a ≠ p)
    (hmin : dist (c p) (c a) ≤ dist (c p) (c b))
    (hangle : 2 * lam ≤ ∠ (c a) (c p) (c b)) :
    dist (c p) (c a) < dist (c a) (c b) := by
  have ha : 0 < dist (c p) (c a) := dist_pos.mpr (hleg.inj.ne hap.symm)
  have hb : 0 < dist (c p) (c b) := ha.trans_le hmin
  have hc := cos_lt_half_of_two_scale hlo p a b hangle
  have hm := mul_lt_mul_of_pos_left hc ha
  have hfactor : 0 < dist (c p) (c b) -
      2 * dist (c p) (c a) * Real.cos (∠ (c a) (c p) (c b)) := by
    nlinarith
  have hpositive := mul_pos hb hfactor
  have hcos := actual_cosine_identity c p a b
  nlinarith [show 0 ≤ dist (c a) (c b) from dist_nonneg]

/-- The reverse comparison uses the frozen cosine difference identity.
Only b has a radius lower bound; apex radii are not involved. -/
private theorem pair_lt_cross_of_min {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (p w w' b : Fin s) (hwp : w ≠ p) (hw'p : w' ≠ p)
    (hshort : dist (c w) (c w') < dist (c p) (c w))
    (hmin : dist (c p) (c w) ≤ dist (c p) (c b))
    (hsmall : ∠ (c w') (c p) (c w) ≤ Real.pi - 4 * lam)
    (hlarge : 2 * lam ≤ ∠ (c w') (c p) (c b)) :
    dist (c w) (c w') < dist (c w') (c b) := by
  have hw : 0 < dist (c p) (c w) := dist_pos.mpr (hleg.inj.ne hwp.symm)
  have hw' : 0 < dist (c p) (c w') := dist_pos.mpr (hleg.inj.ne hw'p.symm)
  have htri := dist_triangle (c p) (c w) (c w')
  have hrad : dist (c p) (c w') < 2 * dist (c p) (c w) := by linarith
  have hc := cos_lt_half_of_two_scale hlo p w' b hlarge
  have hmul := mul_lt_mul_of_pos_left hc hw'
  have hprod : dist (c p) (c w') * Real.cos (∠ (c w') (c p) (c b)) <
      dist (c p) (c w) := by nlinarith
  have hcosdiff := Real.cos_lt_cos_of_nonneg_of_le_pi
    (EuclideanGeometry.angle_nonneg (c w') (c p) (c w))
    (EuclideanGeometry.angle_le_pi (c w') (c p) (c b))
    (by linarith [Real.pi_pos] :
      ∠ (c w') (c p) (c w) < ∠ (c w') (c p) (c b))
  have hfirst : 0 ≤ (dist (c p) (c b) - dist (c p) (c w)) *
      (dist (c p) (c b) + dist (c p) (c w) -
        2 * dist (c p) (c w') * Real.cos (∠ (c w') (c p) (c b))) :=
    mul_nonneg (sub_nonneg.mpr hmin) (by linarith)
  have hsecond : 0 < 2 * dist (c p) (c w') * dist (c p) (c w) *
      (Real.cos (∠ (c w') (c p) (c w)) -
        Real.cos (∠ (c w') (c p) (c b))) := by
    exact mul_pos (by positivity) (sub_pos.mpr hcosdiff)
  have hcross := actual_cosine_identity c p w' b
  have hpair := actual_cosine_identity c p w' w
  rw [dist_comm (c w') (c w)] at hpair
  nlinarith [show 0 ≤ dist (c w) (c w') from dist_nonneg,
    show 0 ≤ dist (c w') (c b) from dist_nonneg]

private theorem strict_mutual_angle_le {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (w w' v : Fin s)
    (hww' : w ≠ w') (hwv : w ≠ v) (hw'v : w' ≠ v)
    (h1 : dist (c w) (c w') < dist (c w) (c v))
    (h2 : dist (c w) (c w') < dist (c w') (c v)) :
    ∠ (c w) (c v) (c w') ≤ Real.pi / 3 := by
  have ha := (EuclideanGeometry.angle_le_iff_dist_le
    (legal_triple_not_collinear hleg hww' hwv hw'v)).mpr h1.le
  have hb := (EuclideanGeometry.angle_le_iff_dist_le
    (legal_triple_not_collinear hleg hww'.symm hw'v hwv)).mpr
      (by simpa only [dist_comm] using h2.le)
  rw [EuclideanGeometry.angle_comm (c w') (c v) (c w),
    EuclideanGeometry.angle_comm (c w') (c w) (c v)] at hb
  have hsum := actual_triangle_sum hleg w v w' hwv
  linarith

private theorem li_code_eq_of_three_scale {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (p v u : Fin s) (hpv : p ≠ v) (huv : u ≠ v)
    {W : ActualHullRayWindow.Window o c lam v}
    (E : ActualHullSmallScoreTypes.Clumps W 1 (2 * lam) (Real.pi - 3 * lam))
    (hbig : 3 * lam ≤ ∠ (c u) (c p) (c v)) : E.code u = E.code p := by
  by_contra hdiff
  have hlarge := E.different_angle_ge hleg u p huv hpv hdiff
  rw [EuclideanGeometry.angle_comm (c u) (c v) (c p)] at hlarge
  rw [EuclideanGeometry.angle_comm (c u) (c p) (c v)] at hbig
  have hsum := actual_triangle_sum hleg p v u hpv
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c u) (c v)
  linarith [Real.pi_pos]

private theorem li_not_all_but_one_same {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hs : 3 ≤ s) (v p q : Fin s) (hqv : q ≠ v)
    {W : ActualHullRayWindow.Window o c lam v}
    (E : ActualHullSmallScoreTypes.Clumps W 1 (2 * lam) (Real.pi - 3 * lam))
    (hzero : rowGain lam (directionRow o e c v) (deleteIndex o e c q v) = 0)
    (hcodes : ∀ j : Fin s, j ≠ v → j ≠ q → E.code j = E.code p) : False := by
  classical
  by_cases hqp : E.code q = E.code p
  · have hall (j : Fin s) (hj : j ≠ v) : E.code j = E.code p := by
      by_cases hjq : j = q
      · simpa only [hjq] using hqp
      · exact hcodes j hj hjq
    obtain ⟨a, b, hav, hbv, _hab, ha, hb⟩ := E.actual_witnesses
    have hsame := (hall a hav).trans (hall b hbv).symm
    rw [ha, hb] at hsame
    cases hsame
  · have hgain : 1 ≤ rowGain lam (directionRow o e c v) (deleteIndex o e c q v) := by
      apply rowGain_pos_of_forall_angle_ge o e c hleg he hqv.symm hs
      intro j hjv hjq
      have hdiff : E.code q ≠ E.code j := by
        rw [hcodes j hjv hjq]
        exact hqp
      have hlarge := E.different_angle_ge hleg q j hqv hjv hdiff
      linarith [hleg.lam_pos]
    rw [hzero] at hgain
    omega

private theorem strict_mutual_nonapex_pair {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    {p : Fin s} (D : ActualInteriorOnePartition.Data c lam p)
    (k : Fin 3) (hk : k ≠ 1) (w w' : Fin s)
    (hwp : w ≠ p) (hw'p : w' ≠ p) (hww' : w ≠ w')
    (hwk : D.classOf ⟨w, hwp⟩ = k) (hw'k : D.classOf ⟨w', hw'p⟩ = k)
    (hexhaust : ∀ j (hjp : j ≠ p), D.classOf ⟨j, hjp⟩ = k → j = w ∨ j = w')
    (hmin : ∀ j (hjp : j ≠ p), D.classOf ⟨j, hjp⟩ ≠ 1 →
      dist (c p) (c w) ≤ dist (c p) (c j)) :
    ∀ j : Fin s, j ≠ w → j ≠ w' →
      dist (c w) (c w') < dist (c w) (c j) ∧
      dist (c w) (c w') < dist (c w') (c j) := by
  have hhalf : Real.pi - 4 * lam < lam / 2 := by linarith
  have hs := D.same_angle ⟨w, hwp⟩ ⟨w', hw'p⟩ (hwk.trans hw'k.symm)
  have hs' := D.same_angle ⟨w', hw'p⟩ ⟨w, hwp⟩ (hw'k.trans hwk.symm)
  have hshort : dist (c w) (c w') < dist (c p) (c w) := by
    have h := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
      hleg hwp.symm hw'p.symm hww' (hs.trans_lt hhalf)
    simpa only [dist_comm (c w) (c p)] using h
  have hshort' : dist (c w) (c w') < dist (c p) (c w') := by
    have h := SharpNearestGeometry.actual_third_point_closer_of_half_scale_angle
      hleg hw'p.symm hwp.symm hww'.symm (hs'.trans_lt hhalf)
    simpa only [dist_comm (c w') (c w), dist_comm (c w') (c p)] using h
  intro j hjw hjw'
  by_cases hjp : j = p
  · subst j
    exact ⟨by simpa only [dist_comm (c w) (c p)] using hshort,
      by simpa only [dist_comm (c w') (c p)] using hshort'⟩
  by_cases hjapex : D.classOf ⟨j, hjp⟩ = 1
  · have hwne : D.classOf ⟨w, hwp⟩ ≠ 1 := by simpa only [hwk] using hk
    have hw'ne : D.classOf ⟨w', hw'p⟩ ≠ 1 := by simpa only [hw'k] using hk
    have ha := D.apex_angle ⟨j, hjp⟩ ⟨w, hwp⟩ hjapex hwne
    have ha' := D.apex_angle ⟨j, hjp⟩ ⟨w', hw'p⟩ hjapex hw'ne
    rw [EuclideanGeometry.angle_comm (c j) (c p) (c w)] at ha
    rw [EuclideanGeometry.angle_comm (c j) (c p) (c w')] at ha'
    exact ⟨hshort.trans (radius_lt_cross_of_apex hleg hlo p w j hwp hjp ha),
      hshort'.trans (radius_lt_cross_of_apex hleg hlo p w' j hw'p hjp ha')⟩
  by_cases hjk : D.classOf ⟨j, hjp⟩ = k
  · rcases hexhaust j hjp hjk with h | h
    · exact False.elim (hjw h)
    · exact False.elim (hjw' h)
  have hwj : D.classOf ⟨w, hwp⟩ ≠ D.classOf ⟨j, hjp⟩ := by
    rw [hwk]
    exact Ne.symm hjk
  have hw'j : D.classOf ⟨w', hw'p⟩ ≠ D.classOf ⟨j, hjp⟩ := by
    rw [hw'k]
    exact Ne.symm hjk
  have hl := D.different_angle ⟨w, hwp⟩ ⟨j, hjp⟩ hwj
  have hl' := D.different_angle ⟨w', hw'p⟩ ⟨j, hjp⟩ hw'j
  exact ⟨hshort.trans (radius_lt_cross_of_min hleg hlo p w j hwp
      (hmin j hjp hjapex) hl),
    pair_lt_cross_of_min hleg hlo p w w' j hwp hw'p hshort
      (hmin j hjp hjapex) hs' hl'⟩

/-- Two nonapex doubletons force a contradiction once every original
target other than the interior center is hull light. -/
private theorem nonapex_doubletons_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (hall : ∀ i, rowScore lam (directionRow o e c i) = 1)
    (p : Fin (s + 1)) (hhull : ∀ i, i ≠ p → IsHullVertex c i)
    (D : ActualInteriorOnePartition.Data c lam p)
    (k l : Fin 3) (hk : k ≠ 1) (hl : l ≠ 1) (hkl : k ≠ l)
    (hcover : ∀ r : Fin 3, r = 1 ∨ r = k ∨ r = l)
    (hK : (block D k).card = 2) (hL : (block D l).card = 2)
    (w : Fin (s + 1)) (hw : w ∈ block D k)
    (hmin : ∀ j ∈ block D k ∪ block D l,
      dist (c p) (c w) ≤ dist (c p) (c j)) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  obtain ⟨w', hw'w, hW⟩ := pair_of_mem_card_two (block D k) hK w hw
  have hw' : w' ∈ block D k := by rw [hW]; simp
  have hwp := block_ne_center D k hw
  have hw'p := block_ne_center D k hw'
  have hwk := (block_mem_iff D k w hwp).mp hw
  have hw'k := (block_mem_iff D k w' hw'p).mp hw'
  have hexhaust (j : Fin (s + 1)) (hjp : j ≠ p)
      (hjk : D.classOf ⟨j, hjp⟩ = k) : j = w ∨ j = w' := by
    have hj := (block_mem_iff D k j hjp).mpr hjk
    simpa only [hW, Finset.mem_insert, Finset.mem_singleton] using hj
  have hradial (j : Fin (s + 1)) (hjp : j ≠ p)
      (hj1 : D.classOf ⟨j, hjp⟩ ≠ 1) :
      dist (c p) (c w) ≤ dist (c p) (c j) := by
    rcases hcover (D.classOf ⟨j, hjp⟩) with h | h | h
    · exact False.elim (hj1 h)
    · exact hmin j (Finset.mem_union.mpr (Or.inl ((block_mem_iff D k j hjp).mpr h)))
    · exact hmin j (Finset.mem_union.mpr (Or.inr ((block_mem_iff D l j hjp).mpr h)))
  have hmut := strict_mutual_nonapex_pair H.legality F.scale_lower D k hk w w'
    hwp hw'p hw'w.symm hwk hw'k hexhaust hradial
  have hzero (q v : Fin (s + 1)) (hvq : v ≠ q) :
      rowGain lam (directionRow o e c v) (deleteIndex o e c q v) = 0 :=
    ActualInteriorOneClassSize.actual_low_four_F18_light_incoming_gain_zero
      hs o e H hF q (hall q) v hvq
  have hWopposite (v : Fin (s + 1)) (hv : v ∈ block D l)
      (Wnd : ActualHullRayWindow.Window o c lam v)
      (E : ActualHullSmallScoreTypes.Clumps Wnd 1 (2 * lam) (Real.pi - 3 * lam)) :
      E.code w ≠ E.code p := by
    have hvp := block_ne_center D l hv
    have hvl := (block_mem_iff D l v hvp).mp hv
    have hv1 : D.classOf ⟨v, hvp⟩ ≠ 1 := by simpa only [hvl] using hl
    have hvw := different_block_ne D hkl.symm hv hw
    have hvw' := different_block_ne D hkl.symm hv hw'
    have hma := hmut v hvw hvw'
    have hang := strict_mutual_angle_le H.legality w w' v hw'w.symm
      hvw.symm hvw'.symm hma.1 hma.2
    have hsame : E.code w = E.code w' := by
      by_contra hdiff
      have hb := E.different_angle_ge H.legality w w' hvw.symm hvw'.symm hdiff
      linarith [F.scale_lower, Real.pi_pos]
    intro hwpcode
    obtain ⟨v', hv'v, hV⟩ := pair_of_mem_card_two (block D l) hL v hv
    have hcodes (j : Fin (s + 1)) (hjv : j ≠ v) (hjv' : j ≠ v') :
        E.code j = E.code p := by
      by_cases hjp : j = p
      · subst j; rfl
      rcases hcover (D.classOf ⟨j, hjp⟩) with hj1 | hjk | hjl
      · exact li_code_eq_of_three_scale H.legality F.scale_lower p v j hvp.symm hjv E
          (D.apex_angle ⟨j, hjp⟩ ⟨v, hvp⟩ hj1 hv1)
      · rcases hexhaust j hjp hjk with h | h
        · simpa only [h] using hwpcode
        · simpa only [h] using hsame.symm.trans hwpcode
      · have hj := (block_mem_iff D l j hjp).mpr hjl
        have hc : j = v ∨ j = v' := by
          simpa only [hV, Finset.mem_insert, Finset.mem_singleton] using hj
        rcases hc with h | h
        · exact False.elim (hjv h)
        · exact False.elim (hjv' h)
    exact li_not_all_but_one_same o e he H.legality H.card_ge_three
      v p v' hv'v E (hzero v' v hv'v.symm) hcodes
  obtain ⟨⟨Wnd, E⟩⟩ :=
    ActualF18LightHullClumps.exists_actual_F18_hull_light_clumps
      o e he H hF w (hhull w hwp) (hall w)
  have hVsame (v : Fin (s + 1)) (hv : v ∈ block D l) : E.code v = E.code p := by
    have hvp := block_ne_center D l hv
    have hvl := (block_mem_iff D l v hvp).mp hv
    have hvw := different_block_ne D hkl.symm hv hw
    obtain ⟨⟨Vnd, Ev⟩⟩ :=
      ActualF18LightHullClumps.exists_actual_F18_hull_light_clumps
        o e he H hF v (hhull v hvp) (hall v)
    have hcross := Ev.different_angle_ge H.legality w p hvw.symm hvp.symm
      (hWopposite v hv Vnd Ev)
    rw [EuclideanGeometry.angle_comm (c w) (c v) (c p)] at hcross
    have hclasses : D.classOf ⟨v, hvp⟩ ≠ D.classOf ⟨w, hwp⟩ := by
      rw [hvl, hwk]
      exact hkl.symm
    have hangle := D.different_angle ⟨v, hvp⟩ ⟨w, hwp⟩ hclasses
    have hsum := actual_triangle_sum H.legality p v w hvp.symm
    have hsmall : ∠ (c p) (c w) (c v) ≤ Real.pi - 4 * lam := by linarith
    by_contra hdiff
    have hlarge := E.different_angle_ge H.legality v p hvw hwp.symm hdiff
    rw [EuclideanGeometry.angle_comm (c v) (c w) (c p)] at hlarge
    linarith [F.scale_lower, Real.pi_pos]
  have hw1 : D.classOf ⟨w, hwp⟩ ≠ 1 := by simpa only [hwk] using hk
  have hcodes (j : Fin (s + 1)) (hjw : j ≠ w) (hjw' : j ≠ w') :
      E.code j = E.code p := by
    by_cases hjp : j = p
    · subst j; rfl
    rcases hcover (D.classOf ⟨j, hjp⟩) with hj1 | hjk | hjl
    · exact li_code_eq_of_three_scale H.legality F.scale_lower p w j hwp.symm hjw E
        (D.apex_angle ⟨j, hjp⟩ ⟨w, hwp⟩ hj1 hw1)
    · rcases hexhaust j hjp hjk with h | h
      · exact False.elim (hjw h)
      · exact False.elim (hjw' h)
    · exact hVsame j ((block_mem_iff D l j hjp).mpr hjl)
  exact li_not_all_but_one_same o e he H.legality H.card_ge_three
    w p w' hw'w E (hzero w' w hw'w.symm) hcodes

/-- The all-light original F18 model cannot have exactly one original
interior point. No nearest pair, clump, class cardinality, or restricted
counter-model is a caller premise. -/
theorem actual_F18_all_light_single_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (hall : ∀ i : Fin (s + 1), rowScore lam (directionRow o e c i) = 1)
    (p : Fin (s + 1)) (hnot : ¬ IsHullVertex c p)
    (hhull : ∀ q : Fin (s + 1), q ≠ p → IsHullVertex c q) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  have hheavy : ActualF18Frame.heavyIndices o e c lam = ∅ := by
    ext i
    simp [ActualF18Frame.heavyIndices, hall i]
  have hN : s + 1 = 9 := by
    have h := F.card_plus_heavy
    rw [hheavy, Finset.card_empty] at h
    omega
  have hlo : Real.pi / 5 < lam := by linarith [F.scale_lower, Real.pi_pos]
  let D := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s + 1)
    o e he H.legality hlo p hnot (hall p)
  have htwo (k : Fin 3) : 2 ≤ (block D k).card := by
    have h := ActualInteriorOneClassSize.actual_low_four_F18_pure_light_class_card_ge_two
      hs o e he H hF p hnot (hall p) k (fun q _ => hall q)
    simpa only [block_card, D] using h
  have hothers : Fintype.card {i : Fin (s + 1) // i ≠ p} = (s + 1) - 1 := by
    simpa only [Fintype.card_fin, Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : Fin (s + 1) => i = p)
  have huniv : (Finset.univ : Finset {i : Fin (s + 1) // i ≠ p}).card = 8 := by
    rw [Finset.card_univ, hothers]
    omega
  have hsumMembers : 8 = ∑ k : Fin 3, (ActualInteriorOneClassSize.members D k).card := by
    calc
      8 = (Finset.univ : Finset {i : Fin (s + 1) // i ≠ p}).card := huniv.symm
      _ = ∑ k : Fin 3, (ActualInteriorOneClassSize.members D k).card := by
        simpa only [ActualInteriorOneClassSize.members] using
          (Finset.card_eq_sum_card_fiberwise (f := D.classOf)
            (s := Finset.univ) (t := Finset.univ) (by intro i hi; simp))
  have hsumPhysical : (∑ k : Fin 3, (block D k).card) = 8 := by
    simpa only [block_card] using hsumMembers.symm
  have hsum : (block D 0).card + (block D 1).card + (block D 2).card = 8 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsumPhysical
  have hapex : 4 ≤ (block D 1).card := by
    have hnonempty : (block D 1).Nonempty :=
      Finset.card_pos.mp (by have := htwo 1; omega)
    apply ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four
      o e he H hF (block D 1) hnonempty p
    · intro hp
      exact (block_ne_center D 1 hp) rfl
    · intro u hu
      exact hhull u (block_ne_center D 1 hu)
    · intro u hu
      exact hall u
    · intro u hu v hv hvp
      have hup := block_ne_center D 1 hu
      have huc := (block_mem_iff D 1 u hup).mp hu
      have hvc : D.classOf ⟨v, hvp⟩ ≠ 1 := by
        intro h
        exact hv ((block_mem_iff D 1 v hvp).mpr h)
      exact D.apex_angle ⟨u, hup⟩ ⟨v, hvp⟩ huc hvc
  have hzero : (block D 0).card = 2 := by
    have h0 := htwo 0
    have h2 := htwo 2
    omega
  have _hone : (block D 1).card = 4 := by
    have h0 := htwo 0
    have h2 := htwo 2
    omega
  have htwoCard : (block D 2).card = 2 := by
    have h0 := htwo 0
    have h2 := htwo 2
    omega
  let N := block D 0 ∪ block D 2
  have hNnonempty : N.Nonempty := by
    have hw : (D.witness 0 : Fin (s + 1)) ∈ block D 0 :=
      (block_mem_iff D 0 (D.witness 0) (D.witness 0).property).mpr (D.witness_class 0)
    exact ⟨D.witness 0, Finset.mem_union.mpr (Or.inl hw)⟩
  obtain ⟨w, hw, hmin⟩ :=
    Finset.exists_min_image N (fun i => dist (c p) (c i)) hNnonempty
  rcases Finset.mem_union.mp hw with hw0 | hw2
  · apply nonapex_doubletons_false o e he H hF hall p hhull D
      0 2 (by decide) (by decide) (by decide) _ hzero htwoCard w hw0 hmin
    intro r
    fin_cases r <;> simp
  · have hcover : ∀ r : Fin 3, r = 1 ∨ r = 2 ∨ r = 0 := by
      intro r
      fin_cases r <;> simp
    apply nonapex_doubletons_false o e he H hF hall p hhull D
      2 0 (by decide) (by decide) (by decide) hcover htwoCard hzero w hw2
    intro j hj
    exact hmin j (by simpa only [N, Finset.union_comm] using hj)

#print axioms actual_F18_all_light_single_interior_false

end Jsp404.ActualF18SingleInterior
