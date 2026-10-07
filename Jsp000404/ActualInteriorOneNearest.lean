import Jsp000404.FullHullInteriorDefect

set_option autoImplicit false

/-! Actual nested fans required by the interior-one nearest-neighbor route.
The containing triangle is chosen from the original full hull. Its selected
score and angles follow from the original row score, never from an assumed
three-cluster model. The actual four-center emission theorem verifies the
singleton base case. The general full-row twisted-run extraction is still
missing, so this file does not assert the general nearest-neighbor exclusion.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualInteriorOneNearest

private theorem low_four_floor {lam : ℝ} (hlam : 0 < lam)
    (hlo : 2 * Real.pi / 9 < lam) (hup : lam ≤ Real.pi / 4) :
    Nat.floor (Real.pi / lam) = 4 := by
  apply (Nat.floor_eq_iff (div_nonneg Real.pi_pos.le hlam.le)).mpr
  constructor
  · rw [le_div_iff₀ hlam]
    norm_num
    linarith
  · rw [div_lt_iff₀ hlam]
    norm_num
    linarith

private theorem gapScore_eq_zero_of_lt_two {lam x : ℝ}
    (hlam : 0 < lam) (hsmall : x < 2 * lam) : gapScore lam x = 0 := by
  by_cases hx : 0 ≤ x
  · have hf : Nat.floor (x / lam) < 2 := by
      apply (Nat.floor_lt (div_nonneg hx hlam.le)).mpr
      rw [div_lt_iff₀ hlam]
      norm_num
      exact hsmall
    unfold gapScore
    omega
  · have hf : Nat.floor (x / lam) = 0 :=
      Nat.floor_eq_zero.mpr (by rw [div_lt_iff₀ hlam]; linarith)
    simp only [gapScore, hf, Nat.zero_sub]

/-- Any actual nested legal three-ray fan has all its surrounding angles
at least twice the scale. This is an actual triangle-sum statement. -/
theorem actual_nested_angles_ge_twice {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hleg : Section4Legality c lam) {p a b d : Fin s}
    (hpa : p ≠ a) (hpb : p ≠ b) (hpd : p ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    {E : Plane₂} (hE : Sbtw ℝ (c a) E (c b))
    (hp : Sbtw ℝ (c d) (c p) E) :
    2 * lam ≤ ∠ (c a) (c p) (c b) ∧
      2 * lam ≤ ∠ (c a) (c p) (c d) ∧
      2 * lam ≤ ∠ (c b) (c p) (c d) := by
  have hsum := angle_sum_eq_two_pi_of_nested hE hp
  have hAB := hleg.triAngle a p b hpa.symm hpb hab
  have hAD := hleg.triAngle a p d hpa.symm hpd had
  have hBD := hleg.triAngle b p d hpb.symm hpd hbd
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Restriction to a real containing triangle retains exactly score one
when the full original interior row has score one in the n4 LOW band. -/
theorem actual_nested_selected_score_one {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hup : lam ≤ Real.pi / 4)
    {p a b d : Fin s} (hpa : p ≠ a) (hpb : p ≠ b) (hpd : p ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    {E : Plane₂} (hE : Sbtw ℝ (c a) E (c b))
    (hp : Sbtw ℝ (c d) (c p) E)
    (hscore : rowScore lam (directionRow o e c p) = 1) :
    rowScore lam ([dirRep o e c p a, dirRep o e c p b,
      dirRep o e c p d].insertionSort (· ≤ ·)) = 1 ∧
      (∠ (c a) (c p) (c b) ≤ Real.pi - 2 * lam ∨
        ∠ (c a) (c p) (c d) ≤ Real.pi - 2 * lam ∨
        ∠ (c b) (c p) (c d) ≤ Real.pi - 2 * lam) := by
  have hn := low_four_floor hleg.lam_pos hlo hup
  have hAB := hleg.triAngle a p b hpa.symm hpb hab
  have hAD := hleg.triAngle a p d hpa.symm hpd had
  have hBD := hleg.triAngle b p d hpb.symm hpd hbd
  have hid := rowScore_inner_nested_three_directions o e c he hleg.inj
    hpa.symm hpb.symm hpd.symm hE hp
    (by linarith [hleg.lam_pos]) (by linarith [hleg.lam_pos])
    (by linarith [hleg.lam_pos]) lam
  have hrestrict := rowScore_le_sorted_three_directions o e c hleg.lam_pos
    hpa hpb hpd hab had hbd
  have hbound := inner_supplement_gapScore_add_three_le
    hleg.lam_pos hn hE hp hAB hAD hBD
  rw [hscore, hid] at hrestrict
  have hsum : gapScore lam (Real.pi - ∠ (c a) (c p) (c b)) +
      gapScore lam (Real.pi - ∠ (c a) (c p) (c d)) +
      gapScore lam (Real.pi - ∠ (c b) (c p) (c d)) = 1 := by omega
  refine ⟨by rw [hid, hsum], ?_⟩
  by_contra hnot
  push Not at hnot
  have h0 := gapScore_eq_zero_of_lt_two hleg.lam_pos
    (show Real.pi - ∠ (c a) (c p) (c b) < 2 * lam by linarith)
  have h1 := gapScore_eq_zero_of_lt_two hleg.lam_pos
    (show Real.pi - ∠ (c a) (c p) (c d) < 2 * lam by linarith)
  have h2 := gapScore_eq_zero_of_lt_two hleg.lam_pos
    (show Real.pi - ∠ (c b) (c p) (c d) < 2 * lam by linarith)
  omega

/-- The actual full-hull nonvertex internally supplies a containing
triangle, nested fan, exact selected score, and necessary real angles. -/
theorem exists_actual_interior_one_fan {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hup : lam ≤ Real.pi / 4)
    (p : Fin s) (hnot : ¬ IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1) :
    ∃ a b d : Fin s, ∃ E : Plane₂,
      p ≠ a ∧ p ≠ b ∧ p ≠ d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      Sbtw ℝ (c a) E (c b) ∧ Sbtw ℝ (c d) (c p) E ∧
      rowScore lam ([dirRep o e c p a, dirRep o e c p b,
        dirRep o e c p d].insertionSort (· ≤ ·)) = 1 ∧
      (2 * lam ≤ ∠ (c a) (c p) (c b) ∧
        2 * lam ≤ ∠ (c a) (c p) (c d) ∧
        2 * lam ≤ ∠ (c b) (c p) (c d)) ∧
      ((∠ (c a) (c p) (c b) ≤ Real.pi - 2 * lam ∧
          3 * lam ≤ ∠ (c a) (c p) (c d) ∧
          3 * lam ≤ ∠ (c b) (c p) (c d)) ∨
        (∠ (c a) (c p) (c d) ≤ Real.pi - 2 * lam ∧
          3 * lam ≤ ∠ (c a) (c p) (c b) ∧
          3 * lam ≤ ∠ (c b) (c p) (c d)) ∨
        (∠ (c b) (c p) (c d) ≤ Real.pi - 2 * lam ∧
          3 * lam ≤ ∠ (c a) (c p) (c b) ∧
          3 * lam ≤ ∠ (c a) (c p) (c d))) := by
  have hmem : c p ∈ convexHull ℝ (c '' ({p} : Set (Fin s))ᶜ) := by
    by_contra hno
    exact hnot (FullHullInteriorDefect.isHullVertex_of_not_mem_hull_others c p hno)
  obtain ⟨a, b, d, hpa, hpb, hpd, hab, had, hbd, htri⟩ :=
    InteriorRowDefect.exists_containing_actual_triangle hleg p hmem
  obtain ⟨E, hE, hp⟩ := strict_nested_of_mem_convexHull htri (hleg.inj.ne hpd)
    (legal_triple_not_collinear hleg hpd.symm had.symm hpa)
    (legal_triple_not_collinear hleg hpd.symm hbd.symm hpb)
    (legal_triple_not_collinear hleg hpa.symm hab hpb)
  have hselected := actual_nested_selected_score_one o e he hleg hlo hup
    hpa hpb hpd hab had hbd hE hp hscore
  refine ⟨a, b, d, E, hpa, hpb, hpd, hab, had, hbd, hE, hp,
    hselected.1, actual_nested_angles_ge_twice hleg hpa hpb hpd hab had hbd hE hp, ?_⟩
  have hsum := angle_sum_eq_two_pi_of_nested hE hp
  have hAB := hleg.triAngle a p b hpa.symm hpb hab
  have hAD := hleg.triAngle a p d hpa.symm hpd had
  have hBD := hleg.triAngle b p d hpb.symm hpd hbd
  rcases hselected.2 with hablo | hadlo | hbdlo
  · exact Or.inl ⟨hablo, by linarith, by linarith⟩
  · exact Or.inr (Or.inl ⟨hadlo, by linarith, by linarith⟩)
  · exact Or.inr (Or.inr ⟨hbdlo, by linarith, by linarith⟩)

/-- In a genuine four-center interior fan, each run has one actual ray.
Deleting any of the three other centers therefore gives positive actual
gain in the interior row. No abstract adjacent-gap certificate is supplied. -/
theorem actual_four_center_interior_emits
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 4 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin 4) (hnot : ¬ IsHullVertex c p) :
    ∀ q : Fin 4, p ≠ q →
      1 ≤ rowGain lam (directionRow o e c p) (deleteIndex o e c q p) := by
  classical
  have hmem : c p ∈ convexHull ℝ (c '' ({p} : Set (Fin 4))ᶜ) := by
    by_contra hno
    exact hnot (FullHullInteriorDefect.isHullVertex_of_not_mem_hull_others c p hno)
  obtain ⟨a, b, d, hpa, hpb, hpd, hab, had, hbd, htri⟩ :=
    InteriorRowDefect.exists_containing_actual_triangle hleg p hmem
  obtain ⟨E, hE, hp⟩ := strict_nested_of_mem_convexHull htri (hleg.inj.ne hpd)
    (legal_triple_not_collinear hleg hpd.symm had.symm hpa)
    (legal_triple_not_collinear hleg hpd.symm hbd.symm hpb)
    (legal_triple_not_collinear hleg hpa.symm hab hpb)
  have hwide := actual_nested_angles_ge_twice hleg hpa hpb hpd hab had hbd hE hp
  have hset : ({a, b, d} : Finset (Fin 4)) = Finset.univ.erase p := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [hpa.symm, hpb.symm, hpd.symm]
    · simp [hab, had, hbd]
  have hother (x : Fin 4) (hxp : x ≠ p) : x = a ∨ x = b ∨ x = d := by
    have hm : x ∈ Finset.univ.erase p := by simp [hxp]
    rw [← hset] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  intro q hpq
  apply rowGain_pos_of_forall_angle_ge o e c hleg he hpq (by decide)
  intro j hjp hjq
  have hq := hother q hpq.symm
  have hj := hother j hjp
  rcases hq with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  · exact False.elim (hjq rfl)
  · linarith [hwide.1, hleg.lam_pos]
  · linarith [hwide.2.1, hleg.lam_pos]
  · rw [EuclideanGeometry.angle_comm]
    linarith [hwide.1, hleg.lam_pos]
  · exact False.elim (hjq rfl)
  · linarith [hwide.2.2, hleg.lam_pos]
  · rw [EuclideanGeometry.angle_comm]
    linarith [hwide.2.1, hleg.lam_pos]
  · rw [EuclideanGeometry.angle_comm]
    linarith [hwide.2.2, hleg.lam_pos]
  · exact False.elim (hjq rfl)

#print axioms actual_nested_angles_ge_twice
#print axioms actual_nested_selected_score_one
#print axioms exists_actual_interior_one_fan
#print axioms actual_four_center_interior_emits

end Jsp404.ActualInteriorOneNearest
