import Jsp000404.SaturationPacking
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Join

/-!
# Actual nesting from two saturated anchors

The angle-sum obstruction derives same-side and non-crossing conclusions
from the saturated angle bounds. Radon's theorem then gives a strict
nested betweenness witness for any four selected centers of an arbitrary
legal configuration. Saturation is used only on the original full rows.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Jsp404

/-- Intersecting open diagonals give the usual quadrilateral angle sum.
All angle additions are derived from actual betweenness. -/
theorem four_angle_sum_of_crossing {A B C D E : Plane₂}
    (hAB : A ≠ B) (hBC : B ≠ C)
    (hAC : Sbtw ℝ A E C) (hBD : Sbtw ℝ B E D) :
    ∠ B A D + ∠ A B C + ∠ B C D + ∠ A D C = 2 * Real.pi := by
  have hB := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := B) hAC
  rw [hBD.angle_eq_right A, hBD.angle_eq_left C] at hB
  have hD := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := D) hAC
  rw [hBD.symm.angle_eq_right A, hBD.symm.angle_eq_left C] at hD
  have hABD := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := A) (p₂ := B) D hAB.symm
  rw [EuclideanGeometry.angle_comm B D A,
    EuclideanGeometry.angle_comm D A B] at hABD
  have hBCD := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := B) (p₂ := C) D hBC.symm
  rw [EuclideanGeometry.angle_comm C D B] at hBCD
  linarith

/-- If two corner angles are bounded by `beta < lam`, and the other
two by `pi-lam`, the opposite open segments cannot intersect. -/
theorem not_crossing_of_two_small_angles {A B C D E : Plane₂}
    {lam beta : ℝ} (hbeta : beta < lam)
    (hAB : A ≠ B) (hBC : B ≠ C)
    (hA : ∠ B A D ≤ beta) (hB : ∠ A B C ≤ beta)
    (hC : ∠ B C D ≤ Real.pi - lam)
    (hD : ∠ A D C ≤ Real.pi - lam)
    (hAC : Sbtw ℝ A E C) (hBD : Sbtw ℝ B E D) : False := by
  have hs := four_angle_sum_of_crossing hAB hBC hAC hBD
  linarith

/-- The same non-crossing obstruction when the small corner angles
belong to opposite vertices of the quadrilateral. -/
theorem not_crossing_of_opposite_small_angles {A B C D E : Plane₂}
    {lam beta : ℝ} (hbeta : beta < lam)
    (hAB : A ≠ B) (hBC : B ≠ C)
    (hA : ∠ B A D ≤ beta) (hC : ∠ B C D ≤ beta)
    (hB : ∠ A B C ≤ Real.pi - lam)
    (hD : ∠ A D C ≤ Real.pi - lam)
    (hAC : Sbtw ℝ A E C) (hBD : Sbtw ℝ B E D) : False := by
  have hs := four_angle_sum_of_crossing hAB hBC hAC hBD
  linarith

/-- A one-sided acute fan suffices to keep its anchor out of the convex
hull of the other points. No acute-angle assumption elsewhere is needed. -/
theorem anchor_outside_convexHull_of_acute {ι : Type*} (p : ι → Plane₂)
    (hp : Function.Injective p) {i : ι}
    (hacute : ∀ j k, j ≠ i → k ≠ i → j ≠ k →
      ∠ (p j) (p i) (p k) < Real.pi / 2)
    {S : Set ι} (hi : i ∉ S) : p i ∉ convexHull ℝ (p '' S) := by
  intro h
  obtain ⟨j, hj⟩ := Set.image_nonempty.mp
    (convexHull_nonempty_iff.mp ⟨p i, h⟩)
  have hji : j ≠ i := fun he => hi (he ▸ hj)
  let f : Plane₂ → ℝ := fun x => ⟪p j - p i, x⟫
  have hconv : Convex ℝ {x | f (p i) < f x} :=
    convex_halfSpace_gt
      (show IsLinearMap ℝ f from
        ⟨fun x y => inner_add_right _ x y,
          fun r x => real_inner_smul_right _ x r⟩) _
  have hpoints : p '' S ⊆ {x | f (p i) < f x} := by
    rintro x ⟨k, hk, rfl⟩
    have hki : k ≠ i := fun he => hi (he ▸ hk)
    have hpos : 0 < ⟪p j - p i, p k - p i⟫ := by
      by_cases hjk : j = k
      · subst k
        exact real_inner_self_pos.mpr (sub_ne_zero.mpr (fun he => hji (hp he)))
      · apply lt_of_not_ge
        intro hinner
        exact (not_le_of_gt (hacute j k hji hki hjk))
          (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp hinner)
    simpa only [Set.mem_ofPred_eq, f, inner_sub_right, sub_pos] using hpos
  exact (lt_irrefl (f (p i))) ((convexHull_min hpoints hconv) h)

/-- Narrow anchors rule out opposite sides of their line. The line's
intersection with `CD` is obtained from the side relation; its position
between `A` and `B` is proved, rather than assumed. -/
theorem not_sOppSide_of_small_anchor_angles {A B C D : Plane₂}
    {lam beta : ℝ} (hbeta : beta < lam) (hbeta2 : beta < Real.pi / 2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hCB : C ≠ B)
    (hAref : ∠ C A B ≤ beta) (hBref : ∠ C B A ≤ beta)
    (hApair : ∠ C A D ≤ beta) (hBpair : ∠ C B D ≤ beta)
    (hC : ∠ A C B ≤ Real.pi - lam)
    (hD : ∠ A D B ≤ Real.pi - lam) :
    ¬ (affineSpan ℝ ({A, B} : Set Plane₂)).SOppSide C D := by
  intro hopp
  obtain ⟨E, hEline, hECD⟩ := hopp.exists_sbtw
  have hEA : E ≠ A := by
    intro he
    rw [he] at hECD
    have heq := hECD.angle₁₂₃_eq_pi
    linarith [Real.pi_pos]
  have hEB : E ≠ B := by
    intro he
    rw [he] at hECD
    have heq := hECD.angle₁₂₃_eq_pi
    linarith [Real.pi_pos]
  have hcol : Collinear ℝ ({E, A, B} : Set Plane₂) :=
    collinear_insert_of_mem_affineSpan_pair hEline
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · have hEAB : Sbtw ℝ E A B := ⟨h, hEA.symm, hAB⟩
    have hs := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := A) hECD
    have hp := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi C
      hEAB.angle₁₂₃_eq_pi
    linarith [EuclideanGeometry.angle_nonneg E A D]
  · have hABE : Sbtw ℝ A B E := ⟨h, hAB.symm, hEB.symm⟩
    have hs := EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := B) hECD
    have hp := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi C
      hABE.angle₁₂₃_eq_pi
    linarith [EuclideanGeometry.angle_nonneg E B D]
  · have hBEA : Sbtw ℝ B E A := ⟨h, hEB, hEA⟩
    exact not_crossing_of_opposite_small_angles hbeta hAC hCB
      hApair hBpair hC hD hBEA.symm hECD

private theorem saturated_beta_lt {n : ℕ} {lam : ℝ}
    (hn2 : 2 ≤ n) (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n) :
    Real.pi - n * lam < lam ∧ Real.pi - n * lam < Real.pi / 2 := by
  have hf := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hf
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hm := mul_le_mul_of_nonneg_right hnreal hlam.le
  constructor <;> nlinarith

/-- Every actual saturated center is outside the convex hull of every
collection of the other centers. Only its own angle fan is used. -/
theorem saturated_anchor_outside_convexHull {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i : Fin s} (hi : rowDefect n lam (directionRow o e c i) = 1)
    {S : Set (Fin s)} (hiS : i ∉ S) :
    c i ∉ convexHull ℝ (c '' S) := by
  apply anchor_outside_convexHull_of_acute c hleg.inj _ hiS
  intro j k hji hki hjk
  exact lt_of_le_of_lt
    (angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hji.symm hki.symm hjk hi)
    (saturated_beta_lt hn2 hlam hn).2

/-- Two actual saturated anchors exclude opposite sides of their line.
The statement has no same-side, nesting, or intersection premise. -/
theorem two_saturated_not_sOppSide {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k l : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    ¬ (affineSpan ℝ ({c i, c j} : Set Plane₂)).SOppSide (c k) (c l) := by
  obtain ⟨hbeta, hbeta2⟩ := saturated_beta_lt hn2 hlam hn
  apply not_sOppSide_of_small_anchor_angles hbeta hbeta2
    (hleg.inj.ne hij) (hleg.inj.ne hik) (hleg.inj.ne hjk.symm)
  · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hik hij hjk.symm hi
  · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hjk hij.symm hik.symm hj
  · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hik hil hkl hi
  · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hjk hjl hkl hj
  · exact hleg.triAngle i k j hik hjk.symm hij
  · exact hleg.triAngle i l j hil hjl.symm hij

/-- The other possible pairing of diagonals is likewise excluded by
two actual saturated anchors. Together with the symmetric instance,
this handles both convex-quadrilateral orders with adjacent anchors. -/
theorem two_saturated_not_crossing {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k l : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1)
    {E : Plane₂} (h₁ : Sbtw ℝ (c i) E (c k))
    (h₂ : Sbtw ℝ (c j) E (c l)) : False := by
  apply not_crossing_of_two_small_angles (saturated_beta_lt hn2 hlam hn).1
    (hleg.inj.ne hij) (hleg.inj.ne hjk) _ _ _ _ h₁ h₂
  · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hij hil hjl hi
  · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hij.symm hjk hik hj
  · exact hleg.triAngle j k l hjk hkl hjl
  · exact hleg.triAngle i l k hil hkl.symm hik

/-- Legal distinct triples cannot be collinear: the middle point would
have angle `pi`, contrary to the positive angular margin. -/
theorem legal_triple_not_collinear {s : ℕ} {lam : ℝ}
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Collinear ℝ ({c i, c j, c k} : Set Plane₂) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · have hb : Sbtw ℝ (c i) (c j) (c k) :=
      ⟨h, hleg.inj.ne hij.symm, hleg.inj.ne hjk⟩
    have hc := hleg.triAngle i j k hij hjk hik
    rw [hb.angle₁₂₃_eq_pi] at hc
    linarith [hleg.lam_pos]
  · have hb : Sbtw ℝ (c j) (c k) (c i) :=
      ⟨h, hleg.inj.ne hjk.symm, hleg.inj.ne hik.symm⟩
    have hc := hleg.triAngle j k i hjk hik.symm hij.symm
    rw [hb.angle₁₂₃_eq_pi] at hc
    linarith [hleg.lam_pos]
  · have hb : Sbtw ℝ (c k) (c i) (c j) :=
      ⟨h, hleg.inj.ne hik, hleg.inj.ne hij⟩
    have hc := hleg.triAngle k i j hik.symm hij hjk.symm
    rw [hb.angle₁₂₃_eq_pi] at hc
    linarith [hleg.lam_pos]

/-- In the plane, two points off a line that are not on opposite sides
are on the same strict side. The dimension argument is explicit. -/
theorem plane_sSameSide_of_not_sOppSide {A B C D : Plane₂}
    (hC : ¬ Collinear ℝ ({C, A, B} : Set Plane₂))
    (hD : ¬ Collinear ℝ ({D, A, B} : Set Plane₂))
    (hnot : ¬ (affineSpan ℝ ({A, B} : Set Plane₂)).SOppSide C D) :
    (affineSpan ℝ ({A, B} : Set Plane₂)).SSameSide C D := by
  have hCline : C ∉ affineSpan ℝ ({A, B} : Set Plane₂) :=
    fun h => hC (collinear_insert_of_mem_affineSpan_pair h)
  have hDline : D ∉ affineSpan ℝ ({A, B} : Set Plane₂) :=
    fun h => hD (collinear_insert_of_mem_affineSpan_pair h)
  have hi : AffineIndependent ℝ ![C, A, B] :=
    affineIndependent_iff_not_collinear_set.mpr hC
  have htop : affineSpan ℝ ({C, A, B} : Set Plane₂) = ⊤ := by
    have h := hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
      insert_empty_eq] using h
  have hspan : D ∈ affineSpan ℝ
      (insert C (affineSpan ℝ ({A, B} : Set Plane₂) : Set Plane₂)) := by
    rw [affineSpan_insert_affineSpan, htop]
    trivial
  have hA : A ∈ affineSpan ℝ ({A, B} : Set Plane₂) :=
    left_mem_affineSpan_pair ℝ A B
  obtain ⟨t, q, hq, hEq⟩ :=
    (AffineSubspace.mem_affineSpan_insert_iff hA C D).mp hspan
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨?_, hCline, hDline⟩
    rw [hEq]
    exact AffineSubspace.wSameSide_smul_vsub_vadd_right C hA hq ht
  · exfalso
    apply hnot
    rw [hEq]
    exact AffineSubspace.sOppSide_smul_vsub_vadd_right hCline hA hq ht

/-- Every pair of centers other than two saturated anchors lies on the
same strict side of the anchor line, derived from actual legal geometry. -/
theorem two_saturated_sSameSide {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k l : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    (affineSpan ℝ ({c i, c j} : Set Plane₂)).SSameSide (c k) (c l) := by
  apply plane_sSameSide_of_not_sOppSide
    (legal_triple_not_collinear hleg hik.symm hjk.symm hij)
    (legal_triple_not_collinear hleg hil.symm hjl.symm hij)
  exact two_saturated_not_sOppSide o e he hn2 hlam hn hleg hs2
    hij hik hil hjk hjl hkl hi hj

/-- Four local angle caps with total below `2*pi` force a point into
the convex hull of the other three. Radon's theorem supplies the
intersection; all singleton and endpoint cases are handled in the proof. -/
theorem exists_mem_convexHull_of_four_angle_caps
    (p : Fin 4 → Plane₂) (hp : Function.Injective p) (cap : Fin 4 → ℝ)
    (hcap : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      ∠ (p i) (p j) (p k) ≤ cap j)
    (hsum : ∑ i : Fin 4, cap i < 2 * Real.pi) :
    ∃ i : Fin 4, p i ∈ convexHull ℝ (p '' ({i} : Set (Fin 4))ᶜ) := by
  classical
  by_contra hnested
  push Not at hnested
  have hout (i : Fin 4) (S : Set (Fin 4)) (hi : i ∉ S) :
      p i ∉ convexHull ℝ (p '' S) := by
    intro h
    apply hnested i
    apply (convexHull_mono (Set.image_mono ?_)) h
    intro j hj
    simpa using (show j ≠ i from fun he => hi (he ▸ hj))
  have hdep : ¬ AffineIndependent ℝ p := by
    intro hind
    have hc := hind.card_le_finrank_succ
    have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range p))
    have he : Module.finrank ℝ Plane₂ = 2 := by simp
    rw [he] at hd
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨S, z, hzS, hzC⟩ := Convex.radon_partition hdep
  have hcard (T : Set (Fin 4)) (hzT : z ∈ convexHull ℝ (p '' T))
      (hzTc : z ∈ convexHull ℝ (p '' Tᶜ)) : 2 ≤ T.toFinset.card := by
    by_contra hsmall
    have hle : T.toFinset.card ≤ 1 := by omega
    obtain ⟨i, hi⟩ := Set.image_nonempty.mp
      (convexHull_nonempty_iff.mp ⟨z, hzT⟩)
    have hsub : p '' T ⊆ {p i} := by
      rintro x ⟨j, hj, rfl⟩
      have he := Finset.card_le_one.mp hle j (by simpa using hj)
        i (by simpa using hi)
      simp [he]
    have hzi : z = p i := (convexHull_min hsub (convex_singleton _)) hzT
    rw [hzi] at hzTc
    exact hout i Tᶜ (by simpa) hzTc
  have hs := hcard S hzS hzC
  have hc := hcard Sᶜ hzC (by simpa using hzS)
  rw [Set.toFinset_compl, Finset.card_compl] at hc
  simp only [Fintype.card_fin] at hc
  have hs2 : S.toFinset.card = 2 := by omega
  have hc2 : Sᶜ.toFinset.card = 2 := by
    rw [Set.toFinset_compl, Finset.card_compl, hs2]
    decide
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hs2
  obtain ⟨c, d, hcd, hscd⟩ := Finset.card_eq_two.mp hc2
  have hsab' : S = {a, b} := by
    simpa using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) hsab
  have hscd' : Sᶜ = {c, d} := by
    simpa using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) hscd
  have hne : ∀ i ∈ S, ∀ j ∈ Sᶜ, i ≠ j := by
    intro i hi j hj he
    exact hj (he ▸ hi)
  have hac := hne a (by simp [hsab']) c (by simp [hscd'])
  have had := hne a (by simp [hsab']) d (by simp [hscd'])
  have hbc := hne b (by simp [hsab']) c (by simp [hscd'])
  have hbd := hne b (by simp [hsab']) d (by simp [hscd'])
  have hzane : z ≠ p a := by
    intro he
    apply hout a Sᶜ (by simp [hsab'])
    simpa [he] using hzC
  have hzbne : z ≠ p b := by
    intro he
    apply hout b Sᶜ (by simp [hsab'])
    simpa [he] using hzC
  have hzcne : z ≠ p c := by
    intro he
    apply hout c S (show c ∈ Sᶜ by simp [hscd'])
    simpa [he] using hzS
  have hzdne : z ≠ p d := by
    intro he
    apply hout d S (show d ∈ Sᶜ by simp [hscd'])
    simpa [he] using hzS
  have hsumcap : cap a + cap b + (cap c + cap d) = ∑ i : Fin 4, cap i := by
    have h := S.toFinset.sum_add_sum_compl cap
    rw [← Set.toFinset_compl, hsab, hscd] at h
    simpa only [Finset.sum_pair hab, Finset.sum_pair hcd] using h
  rw [hsab', Set.image_pair, convexHull_pair] at hzS
  rw [hscd', Set.image_pair, convexHull_pair] at hzC
  have hcross₁ : Sbtw ℝ (p a) z (p b) :=
    ⟨mem_segment_iff_wbtw.mp hzS, hzane, hzbne⟩
  have hcross₂ : Sbtw ℝ (p c) z (p d) :=
    ⟨mem_segment_iff_wbtw.mp hzC, hzcne, hzdne⟩
  have hsangle := four_angle_sum_of_crossing (hp.ne hac) (hp.ne hbc.symm)
    hcross₁ hcross₂
  have hA := hcap c a d hac.symm had hcd
  have hC := hcap a c b hac hbc.symm hab
  have hB := hcap c b d hbc.symm hbd hcd
  have hD := hcap a d b had hbd.symm hab
  linarith

/-- Membership in a triangle's convex hull becomes a strict nested
betweenness witness when the relevant triples are noncollinear. -/
theorem strict_nested_of_mem_convexHull {A B C D : Plane₂}
    (hmem : C ∈ convexHull ℝ ({A, B, D} : Set Plane₂)) (hCD : C ≠ D)
    (hDCA : ¬ Collinear ℝ ({D, C, A} : Set Plane₂))
    (hDCB : ¬ Collinear ℝ ({D, C, B} : Set Plane₂))
    (hACB : ¬ Collinear ℝ ({A, C, B} : Set Plane₂)) :
    ∃ E : Plane₂, Sbtw ℝ A E B ∧ Sbtw ℝ D C E := by
  rw [← convexJoin_segment_singleton A B D] at hmem
  obtain ⟨E, hE, F, hF, hCF⟩ := mem_convexJoin.mp hmem
  have hFD : F = D := Set.mem_singleton_iff.mp hF
  subst F
  have hAB : Wbtw ℝ A E B := mem_segment_iff_wbtw.mp hE
  have hDC : Wbtw ℝ D C E := (mem_segment_iff_wbtw.mp hCF).symm
  have hEA : E ≠ A := by
    intro he
    subst E
    exact hDCA hDC.collinear
  have hEB : E ≠ B := by
    intro he
    subst E
    exact hDCB hDC.collinear
  have hCE : C ≠ E := by
    intro he
    subst E
    exact hACB hAB.collinear
  exact ⟨E, ⟨hAB, hEA, hEB⟩, ⟨hDC, hCD, hCE⟩⟩

/-- Small anchor fans in a legal four-point configuration force one of
the other points strictly inside the triangle of the other three.
This local version permits direct restriction from larger configurations. -/
theorem nested_four_of_small_anchor_angles {lam beta : ℝ}
    (hbeta : beta < lam) (hbeta2 : beta < Real.pi / 2)
    {p : Fin 4 → Plane₂} (hleg : Section4Legality p lam)
    (h₀ : ∀ j k, j ≠ 0 → k ≠ 0 → j ≠ k → ∠ (p j) (p 0) (p k) ≤ beta)
    (h₁ : ∀ j k, j ≠ 1 → k ≠ 1 → j ≠ k → ∠ (p j) (p 1) (p k) ≤ beta) :
    ∃ E : Plane₂, Sbtw ℝ (p 0) E (p 1) ∧
      (Sbtw ℝ (p 3) (p 2) E ∨ Sbtw ℝ (p 2) (p 3) E) := by
  classical
  let cap : Fin 4 → ℝ := fun i =>
    if i = 0 ∨ i = 1 then beta else Real.pi - lam
  have hcap : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      ∠ (p i) (p j) (p k) ≤ cap j := by
    intro i j k hij hjk hik
    fin_cases j
    · simpa [cap] using h₀ i k hij hjk.symm hik
    · simpa [cap] using h₁ i k hij hjk.symm hik
    · simpa [cap] using hleg.triAngle i 2 k hij hjk hik
    · simpa [cap] using hleg.triAngle i 3 k hij hjk hik
  have hsum : ∑ i : Fin 4, cap i < 2 * Real.pi := by
    simp [cap, Fin.sum_univ_succ]
    linarith
  obtain ⟨i, hi⟩ := exists_mem_convexHull_of_four_angle_caps p hleg.inj cap hcap hsum
  fin_cases i
  · exact False.elim ((anchor_outside_convexHull_of_acute p hleg.inj
      (fun j k hj hk hjk => lt_of_le_of_lt (h₀ j k hj hk hjk) hbeta2)
      (by simp)) hi)
  · exact False.elim ((anchor_outside_convexHull_of_acute p hleg.inj
      (fun j k hj hk hjk => lt_of_le_of_lt (h₁ j k hj hk hjk) hbeta2)
      (by simp)) hi)
  · have hsub : p '' ({2} : Set (Fin 4))ᶜ ⊆ {p 0, p 1, p 3} := by
      rintro x ⟨v, hv, rfl⟩
      fin_cases v <;> simp_all
    have hmem := (convexHull_mono hsub) hi
    obtain ⟨E, hE, hinner⟩ := strict_nested_of_mem_convexHull hmem
      (hleg.inj.ne (by decide : (2 : Fin 4) ≠ 3))
      (legal_triple_not_collinear hleg (by decide : (3 : Fin 4) ≠ 2)
        (by decide : (3 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 0))
      (legal_triple_not_collinear hleg (by decide : (3 : Fin 4) ≠ 2)
        (by decide : (3 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 1))
      (legal_triple_not_collinear hleg (by decide : (0 : Fin 4) ≠ 2)
        (by decide : (0 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 1))
    exact ⟨E, hE, Or.inl hinner⟩
  · have hsub : p '' ({3} : Set (Fin 4))ᶜ ⊆ {p 0, p 1, p 2} := by
      rintro x ⟨v, hv, rfl⟩
      fin_cases v <;> simp_all
    have hmem := (convexHull_mono hsub) hi
    obtain ⟨E, hE, hinner⟩ := strict_nested_of_mem_convexHull hmem
      (hleg.inj.ne (by decide : (3 : Fin 4) ≠ 2))
      (legal_triple_not_collinear hleg (by decide : (2 : Fin 4) ≠ 3)
        (by decide : (2 : Fin 4) ≠ 0) (by decide : (3 : Fin 4) ≠ 0))
      (legal_triple_not_collinear hleg (by decide : (2 : Fin 4) ≠ 3)
        (by decide : (2 : Fin 4) ≠ 1) (by decide : (3 : Fin 4) ≠ 1))
      (legal_triple_not_collinear hleg (by decide : (0 : Fin 4) ≠ 3)
        (by decide : (0 : Fin 4) ≠ 1) (by decide : (3 : Fin 4) ≠ 1))
    exact ⟨E, hE, Or.inr hinner⟩

/-- Two saturated anchors in a legal four-point configuration give an
actual strict nesting witness. -/
theorem two_saturated_nested_four {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {p : Fin 4 → Plane₂} (hleg : Section4Legality p lam)
    (h₀ : rowDefect n lam (directionRow o e p 0) = 1)
    (h₁ : rowDefect n lam (directionRow o e p 1) = 1) :
    ∃ E : Plane₂, Sbtw ℝ (p 0) E (p 1) ∧
      (Sbtw ℝ (p 3) (p 2) E ∨ Sbtw ℝ (p 2) (p 3) E) := by
  obtain ⟨hbeta, hbeta2⟩ := saturated_beta_lt hn2 hlam hn
  apply nested_four_of_small_anchor_angles hbeta hbeta2 hleg
  · intro j k hj hk hjk
    exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he (by decide)
      hj.symm hk.symm hjk h₀
  · intro j k hj hk hjk
    exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he (by decide)
      hj.symm hk.symm hjk h₁

/-- The full nesting connection for any four selected centers in a
larger legal configuration with two saturated anchors. Saturation is
used only on the original full rows, never assumed after restriction. -/
theorem two_saturated_nested {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k l : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    ∃ E : Plane₂, Sbtw ℝ (c i) E (c j) ∧
      (Sbtw ℝ (c l) (c k) E ∨ Sbtw ℝ (c k) (c l) E) := by
  let f : Fin 4 → Fin s := ![i, j, k, l]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  let p : Fin 4 → Plane₂ := c ∘ f
  have hp : Section4Legality p lam := {
    lam_pos := hlam
    inj := hleg.inj.comp hf
    triAngle := fun a b d hab hbd had =>
      hleg.triAngle (f a) (f b) (f d) (hf.ne hab) (hf.ne hbd) (hf.ne had) }
  obtain ⟨hbeta, hbeta2⟩ := saturated_beta_lt hn2 hlam hn
  change ∃ E : Plane₂, Sbtw ℝ (p 0) E (p 1) ∧
    (Sbtw ℝ (p 3) (p 2) E ∨ Sbtw ℝ (p 2) (p 3) E)
  apply nested_four_of_small_anchor_angles hbeta hbeta2 hp
  · intro a b ha hb hab
    have hia : i ≠ f a := by
      change f 0 ≠ f a
      exact hf.ne ha.symm
    have hib : i ≠ f b := by
      change f 0 ≠ f b
      exact hf.ne hb.symm
    exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hia hib (hf.ne hab) hi
  · intro a b ha hb hab
    have hja : j ≠ f a := by
      change f 1 ≠ f a
      exact hf.ne ha.symm
    have hjb : j ≠ f b := by
      change f 1 ≠ f b
      exact hf.ne hb.symm
    exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
      hja hjb (hf.ne hab) hj

end Jsp404

#print axioms Jsp404.four_angle_sum_of_crossing
#print axioms Jsp404.not_crossing_of_two_small_angles
#print axioms Jsp404.not_crossing_of_opposite_small_angles
#print axioms Jsp404.anchor_outside_convexHull_of_acute
#print axioms Jsp404.not_sOppSide_of_small_anchor_angles
#print axioms Jsp404.saturated_anchor_outside_convexHull
#print axioms Jsp404.two_saturated_not_sOppSide
#print axioms Jsp404.two_saturated_not_crossing
#print axioms Jsp404.legal_triple_not_collinear
#print axioms Jsp404.plane_sSameSide_of_not_sOppSide
#print axioms Jsp404.two_saturated_sSameSide
#print axioms Jsp404.exists_mem_convexHull_of_four_angle_caps
#print axioms Jsp404.strict_nested_of_mem_convexHull
#print axioms Jsp404.nested_four_of_small_anchor_angles
#print axioms Jsp404.two_saturated_nested_four
#print axioms Jsp404.two_saturated_nested
