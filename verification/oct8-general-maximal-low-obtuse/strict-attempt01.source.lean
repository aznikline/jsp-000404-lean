import Jsp000404.ActualMaximalLowClumpWeight

/-! SOURCE_ONLY uniform maximal-obtuse / other-nonacute exclusion.

The needed (n-1)*lambda separation is derived from the actual paid gap of
an internally produced clump, not supplied by the caller. The two-gap list
argument keeps multiplicities. Whole-row scores and weights always refer
to the original actual Model. No restricted Model or capacity certificate
is constructed. The physical window support repackaging below is copied
from the verified ActualHullWindowScoreLower producer, without editing it.
-/

set_option autoImplicit false
set_option pp.fullNames true
open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualMaximalLowObtuseExclusion

private noncomputable def supportOfWindow {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (hlam : 0 < lam) : ActualHullSmallScoreTypes.Support o c lam p := by
  classical
  let l := directionRow o W.base c p
  have hdir (j : Fin s) (hj : j ≠ p) :
      dirRep o W.base c p j = W.theta j := by
    unfold dirRep
    rw [W.actual_direction j hj]
    exact (eq_linRep_of_int_pi
      ⟨(W.theta_mem j hj).1, ((W.theta_mem j hj).2).trans_lt W.width_lt_pi⟩
      ⟨0, by simp⟩).symm
  have hmem : ∀ x ∈ l, x ∈ Set.Icc 0 W.width := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_directionRow o W.base c).mp hx
    rw [hdir j hj]
    exact W.theta_mem j hj
  have hzero : (0 : ℝ) ∈ l := by
    apply (mem_directionRow o W.base c).mpr
    refine ⟨W.left, W.left_ne_center, ?_⟩
    rw [hdir W.left W.left_ne_center, W.left_coordinate]
  have hwidth : W.width ∈ l := by
    apply (mem_directionRow o W.base c).mpr
    refine ⟨W.right, W.right_ne_center, ?_⟩
    rw [hdir W.right W.right_ne_center, W.right_coordinate]
  have hne : l ≠ [] := List.ne_nil_of_mem hzero
  have hsort : l.SortedLE := directionRow_sorted o W.base c p
  have hhead : l.head hne = 0 := by
    have hlow := (hmem _ (List.head_mem hne)).1
    have hhigh : l.head hne ≤ 0 := by simpa using hsort.pairwise.rel_head hzero
    exact le_antisymm hhigh hlow
  have hlast : l.getLast hne = W.width := by
    have hhigh := (hmem _ (List.getLast_mem hne)).2
    have hlow : W.width ≤ l.getLast hne := by
      simpa using hsort.pairwise.rel_getLast hwidth
    exact le_antisymm hhigh hlow
  have hwrap : wrapGap l hne = Real.pi - W.width := by
    have hnot : ¬ ∀ x ∈ l, x = l.head hne := by
      intro h
      have h := h W.width hwidth
      rw [hhead] at h
      linarith [W.width_pos]
    rw [wrapGap, if_neg hnot, hhead, hlast]
    simp [cyclicDiff, ne_of_gt W.width_pos, not_lt_of_ge W.width_pos.le]
  exact {
    window := W
    nonempty := hne
    dirRep_eq := hdir
    head_eq := hhead
    last_eq := hlast
    wrap_eq := hwrap
    wrap_mem := by
      change Real.pi - W.width ∈ cycGaps l
      rw [cycGaps_eq_map_append_wrap l hne, hwrap]
      exact List.mem_append_right _ (by simp)
    outside_ge_scale := by linarith [W.width_le_legality]
    outside_floor_pos := (one_le_floor_iff_ge lam _ hlam).mpr
      (by linarith [W.width_le_legality]) }

private theorem score_zero_of_lt_two {lam g : ℝ} (hlam : 0 < lam)
    (hg : 0 ≤ g) (hsmall : g < 2 * lam) : gapScore lam g = 0 := by
  have hratio : g / lam < 2 := (div_lt_iff₀ hlam).mpr (by linarith)
  have hfloor : ⌊g / lam⌋₊ < 2 := (Nat.floor_lt (div_nonneg hg hlam.le)).mpr hratio
  unfold gapScore
  omega

/-- Erase one paid gap and one distinct exterior gap. The remaining real
length is below lambda/2, so all its scores vanish, with multiplicity. -/
private theorem score_concentrated_in_paid_gap {lam g E : ℝ}
    (hlam : 0 < lam) (l : List ℝ) (hnonneg : ∀ x ∈ l, 0 ≤ x)
    (hg : g ∈ l) (hE : E ∈ l) (hgbig : 2 * lam ≤ g) (hEsmall : E < 2 * lam)
    (hrest : l.sum - g - E < lam / 2) :
    (l.map (gapScore lam)).sum = gapScore lam g := by
  classical
  have hEg : E ≠ g := by intro h; rw [h] at hEsmall; linarith
  let l1 := l.erase g
  have hE1 : E ∈ l1 := (List.mem_erase_of_ne hEg).mpr hE
  let l2 := l1.erase E
  have hsum1 : l.sum = g + l1.sum := by
    simpa only [List.sum_cons] using (List.perm_cons_erase hg).sum_eq
  have hsum2 : l1.sum = E + l2.sum := by
    simpa only [List.sum_cons] using (List.perm_cons_erase hE1).sum_eq
  have hrestsmall : l2.sum < lam / 2 := by linarith
  have hnn2 (x : ℝ) (hx : x ∈ l2) : 0 ≤ x :=
    hnonneg x (List.mem_of_mem_erase (List.mem_of_mem_erase hx))
  have hz (x : ℝ) (hx : x ∈ l2) : gapScore lam x = 0 := by
    have hle := le_sum_of_mem_of_nonneg l2 hnn2 hx
    exact score_zero_of_lt_two hlam (hnn2 x hx) (by linarith)
  have hzero : (l2.map (gapScore lam)).sum = 0 := by
    have hm : l2.map (gapScore lam) = l2.map (fun _ : ℝ => (0 : ℕ)) :=
      List.map_congr_left hz
    rw [hm]
    simp
  have hEzero : gapScore lam E = 0 :=
    score_zero_of_lt_two hlam (hnonneg E hE) hEsmall
  have hs1 := ((List.perm_cons_erase hg).map (gapScore lam)).sum_eq
  have hs2 := ((List.perm_cons_erase hE1).map (gapScore lam)).sum_eq
  simp only [List.map_cons, List.sum_cons] at hs1 hs2
  change (l.map (gapScore lam)).sum = gapScore lam g + (l1.map (gapScore lam)).sum at hs1
  change (l1.map (gapScore lam)).sum = gapScore lam E + (l2.map (gapScore lam)).sum at hs2
  omega

/-- The chosen generic paid cut itself has the full original score n-2.
Thus its actual cross-clump separation is (n-1)*lambda. No second cut or
assumed equality of independently chosen labels is used. -/
private theorem obtuse_clump_different_angle_ge {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (B : Fin s) (hB : rowScore lam (directionRow o e c B) = n - 2)
    (hobtuse : ∃ a b : Fin s, a ≠ B ∧ b ≠ B ∧ a ≠ b ∧
      Real.pi - 2 * lam < ∠ (c a) (c B) (c b))
    (G : ActualMaximalLowRowClumps.Data n o c lam B) :
    ∀ i j : Fin s, i ≠ B → j ≠ B → G.clumps.code i ≠ G.clumps.code j →
      ((n : ℝ) - 1) * lam ≤ ∠ (c i) (c B) (c j) := by
  classical
  let S := supportOfWindow G.window hleg.lam_pos
  let l := cycGaps (directionRow o G.window.base c B)
  let g := G.window.theta G.clumps.rightRay - G.window.theta G.clumps.leftRay
  let E := Real.pi - G.window.width
  have hnonneg : ∀ x ∈ l, 0 ≤ x :=
    cycGaps_nonneg (directionRow_sorted o G.window.base c B)
      (fun x hx => directionRow_mem_Ico o G.window.base c hx) S.nonempty
  have hg : g ∈ l := G.clumps.actual_gap
  have hE : E ∈ l := S.wrap_mem
  have hgbig : 2 * lam ≤ g := G.clumps.gap_lower
  obtain ⟨a,b,ha,hb,_hab,hangle⟩ := hobtuse
  have hcap := ActualMixedRigidCardinality.actual_window_angle_le_width G.window hleg a b ha hb
  have hEsmall : E < 2 * lam := by dsimp [E]; linarith
  have hsum : l.sum = Real.pi :=
    cycGaps_sum_eq_pi (directionRow_sorted o G.window.base c B) S.nonempty
  have hrest : l.sum - g - E < lam / 2 := by
    have hwidth := G.clumps.remaining_width
    have hrem := G.remainder_lt_half
    dsimp [g, E]
    rw [hsum]
    linarith
  have hconcentrated := score_concentrated_in_paid_gap hleg.lam_pos l hnonneg
    hg hE hgbig hEsmall hrest
  have hrow : rowScore lam (directionRow o G.window.base c B) = n - 2 :=
    (rowScore_directionRow_reference_eq o e G.window.base he G.window.base_ne_zero
      c hleg.inj B lam).symm.trans hB
  have hpaid : gapScore lam g = n - 2 := by
    change rowScore lam (directionRow o G.window.base c B) = gapScore lam g at hconcentrated
    omega
  have hfloor : n - 1 ≤ ⌊g / lam⌋₊ := by
    unfold gapScore at hpaid
    omega
  have hcast : ((n - 1 : ℕ) : ℝ) ≤ (⌊g / lam⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hglower : ((n - 1 : ℕ) : ℝ) * lam ≤ g :=
    (le_div_iff₀ hleg.lam_pos).mp (hcast.trans (Nat.floor_le
      (div_nonneg (hleg.lam_pos.le.trans (by linarith : lam ≤ g)) hleg.lam_pos.le)))
  rw [Nat.cast_sub (by omega : 1 ≤ n)] at hglower
  norm_num only [Nat.cast_one] at hglower
  intro i j hi hj hdiff
  -- Reuse the actual sorted cut directly with its stronger gap lower bound.
  have hstrong : ActualHullSmallScoreTypes.Clumps G.window G.internalScore
      (((n : ℝ) - 1) * lam) (Real.pi - (n : ℝ) * lam) := {
    leftRay := G.clumps.leftRay, rightRay := G.clumps.rightRay
    left_ne_center := G.clumps.left_ne_center, right_ne_center := G.clumps.right_ne_center
    left_lt_right := G.clumps.left_lt_right, no_middle := G.clumps.no_middle
    actual_gap := G.clumps.actual_gap, gap_score := G.clumps.gap_score
    gap_lower := hglower, remaining_width := G.clumps.remaining_width }
  have hcodes (k : Fin s) : hstrong.code k = G.clumps.code k := rfl
  exact hstrong.different_angle_ge hleg i j hi hj (by simpa only [hcodes] using hdiff)

private noncomputable def weight {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ) (T : Finset (Fin s)) : ℕ :=
  ∑ q ∈ T, 2 ^ rowScore lam (directionRow o e c q)

private theorem weight_mono {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ) {T U : Finset (Fin s)} (hTU : T ⊆ U) :
    weight o e c lam T ≤ weight o e c lam U := by
  unfold weight
  exact Finset.sum_le_sum_of_subset_of_nonneg hTU (fun _ _ _ => Nat.zero_le _)

private theorem weight_insert {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ) (q : Fin s) (T : Finset (Fin s)) (hq : q ∉ T) :
    weight o e c lam (insert q T) = 2 ^ rowScore lam (directionRow o e c q) + weight o e c lam T := by
  unfold weight
  exact Finset.sum_insert hq

private theorem bool_not_ne_self (b : Bool) : (!b) ≠ b := by cases b <;> decide

private theorem clump_weights_sum {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (G : ActualMaximalLowRowClumps.Data n o c lam p) (b : Bool) :
    weight o e c lam (ActualMaximalLowClumpWeight.members G b) +
      weight o e c lam (ActualMaximalLowClumpWeight.members G (!b)) =
        weight o e c lam (Finset.univ.erase p) := by
  classical
  have hdisjoint : Disjoint (ActualMaximalLowClumpWeight.members G b)
      (ActualMaximalLowClumpWeight.members G (!b)) := by
    apply Finset.disjoint_left.mpr
    intro q hqb hqnb
    have hcb := (Finset.mem_filter.mp hqb).2.2
    have hcnb := (Finset.mem_filter.mp hqnb).2.2
    exact bool_not_ne_self b (hcnb.symm.trans hcb)
  have hcover : ActualMaximalLowClumpWeight.members G b ∪
      ActualMaximalLowClumpWeight.members G (!b) = Finset.univ.erase p := by
    ext q
    cases b <;> cases hcode : G.clumps.code q <;>
      simp [ActualMaximalLowClumpWeight.members, hcode]
  unfold weight
  rw [← Finset.sum_union hdisjoint, hcover]

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (B C v : Fin s) (hBC : B ≠ C) :
    ∠ (c C) (c B) (c v) + ∠ (c B) (c C) (c v) + ∠ (c B) (c v) (c C) = Real.pi := by
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c B) (p₂ := c C) (c v) (hleg.inj.ne hBC.symm)
  rw [EuclideanGeometry.angle_comm (c C) (c v) (c B),
    EuclideanGeometry.angle_comm (c v) (c B) (c C)] at h
  linarith

/-- Uniform n>=4: a maximal original obtuse row cannot coexist with a
second maximal original nonacute row. No paid gap or clump is a caller input. -/
theorem actual_maximal_obtuse_other_nonacute_false {s n : ℕ} (hn4 : 4 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((n : ℝ) + 1 / 2)) (Real.pi / (n : ℝ)) (2 ^ n) s c lam)
    (B : Fin s) (hB : rowScore lam (directionRow o e c B) = n - 2)
    (hobtuse : ∃ a b : Fin s, a ≠ B ∧ b ≠ B ∧ a ≠ b ∧
      Real.pi - 2 * lam < ∠ (c a) (c B) (c b))
    (C : Fin s) (hC : rowScore lam (directionRow o e c C) = n - 2) (hCB : C ≠ B)
    (hCwide : ∃ a b : Fin s, a ≠ C ∧ b ≠ C ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c C) (c b)) : False := by
  classical
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hnpos : (0 : ℝ) < n := by linarith
  have hnl : (n : ℝ) * lam ≤ Real.pi := by
    have h := (le_div_iff₀ hnpos).mp H.scale_upper
    nlinarith
  have hfour : 4 * lam ≤ Real.pi := by
    have h := mul_le_mul_of_nonneg_right hnR H.legality.lam_pos.le
    linarith
  have hBwide : ∃ a b : Fin s, a ≠ B ∧ b ≠ B ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c B) (c b) := by
    obtain ⟨a,b,ha,hb,hab,hangle⟩ := hobtuse
    exact ⟨a,b,ha,hb,hab,by linarith⟩
  obtain ⟨GB⟩ := ActualMaximalLowClumpWeight.exists_actual_maximal_low_clump_weight
    hn4 o e he H B hB hBwide
  obtain ⟨GC⟩ := ActualMaximalLowClumpWeight.exists_actual_maximal_low_clump_weight
    hn4 o e he H C hC hCwide
  let b := GB.geometry.clumps.code C
  let T := ActualMaximalLowClumpWeight.members GB.geometry (!b)
  let d := GC.geometry.clumps.code B
  have hPi : Real.pi < ((n : ℝ) + 1 / 2) * lam :=
    (div_lt_iff₀ (by linarith : 0 < (n : ℝ) + 1 / 2)).mp H.scale_lower
  have hTsub : T ⊆ ActualMaximalLowClumpWeight.members GC.geometry d := by
    intro v hv
    have hvd := (Finset.mem_filter.mp hv).2
    have hvB : v ≠ B := hvd.1
    have hcodes : GB.geometry.clumps.code v ≠ GB.geometry.clumps.code C := by
      intro heq
      exact bool_not_ne_self b (hvd.2.symm.trans heq)
    have hvC : v ≠ C := by intro heq; exact hcodes (by rw [heq])
    have hbig := obtuse_clump_different_angle_ge hn4 o e he H.legality B hB hobtuse
      GB.geometry C v hCB hvB hcodes.symm
    have hcode : GC.geometry.clumps.code v = GC.geometry.clumps.code B := by
      by_contra hdiff
      have hlarge := GC.geometry.clumps.different_angle_ge H.legality B v hCB.symm hvC hdiff.symm
      have hsum := actual_triangle_sum H.legality B C v hCB.symm
      have hthird := EuclideanGeometry.angle_nonneg (c B) (c v) (c C)
      nlinarith [H.legality.lam_pos]
    simp [ActualMaximalLowClumpWeight.members, hvC, hcode, d]
  have hBT : B ∉ T := by simp [T, ActualMaximalLowClumpWeight.members]
  have hBd : B ∈ ActualMaximalLowClumpWeight.members GC.geometry d := by
    simp [ActualMaximalLowClumpWeight.members, hCB.symm, d]
  have hsub : insert B T ⊆ ActualMaximalLowClumpWeight.members GC.geometry d := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hqB | hq
    · rw [hqB]; exact hBd
    · exact hTsub hq
  have hTweight : (potential lam (directionRows o e c) - 2 ^ n) + 2 ^ (n - 2) ≤
      weight o e c lam T := GB.weight_lower (!b)
  have hother : (potential lam (directionRows o e c) - 2 ^ n) + 2 ^ (n - 2) ≤
      weight o e c lam (ActualMaximalLowClumpWeight.members GC.geometry (!d)) :=
    GC.weight_lower (!d)
  have hinsert : weight o e c lam (insert B T) =
      2 ^ (n - 2) + weight o e c lam T := by
    rw [weight_insert o e c lam B T hBT, hB]
  have hmono := weight_mono o e c lam hsub
  rw [hinsert] at hmono
  have htotal := clump_weights_sum o e GC.geometry d
  have hmass := Finset.sum_erase_add (Finset.univ : Finset (Fin s))
    (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ C)
  have hfull : (∑ q : Fin s, 2 ^ rowScore lam (directionRow o e c q)) =
      potential lam (directionRows o e c) := rfl
  rw [hC, hfull] at hmass
  have herased : weight o e c lam (Finset.univ.erase C) =
      potential lam (directionRows o e c) - 2 ^ (n - 2) := by unfold weight; omega
  rw [herased] at htotal
  have hQ : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := by congr 1; omega
      _ = 2 ^ (n - 2) * 2 ^ 2 := by rw [pow_add]
      _ = 4 * 2 ^ (n - 2) := by rw [show (2 : ℕ) ^ 2 = 4 by decide, Nat.mul_comm]
  have hover := H.over_cap
  omega

#print axioms actual_maximal_obtuse_other_nonacute_false

end Jsp404.ActualMaximalLowObtuseExclusion
