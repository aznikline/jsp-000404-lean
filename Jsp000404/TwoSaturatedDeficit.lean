import Jsp000404.SaturatedNesting
import Jsp000404.TwoSaturatedFour
import Jsp000404.TriangleRestriction
import Jsp000404.ThreeDirectionCapacity

/-!
# The sharper original-row deficit bound from two saturated anchors

Selected directions are retained with their original multiplicities.
Subpermutation on center indices is transported through the direction map
before sorting, so the transport needs no injectivity of directions.
The actual nesting theorem and the two three-gap identities then give
`rowScore + 3 ≤ n` and `rowDefect ≥ 3` for every non-anchor row when at
least four centers are present. No additional geometric certificate is
assumed; this remains a local restriction rather than a global mass bound.
-/

namespace Jsp404

open scoped EuclideanGeometry

private theorem subperm_map_of_subperm {α β : Type*} (f : α → β)
    {small large : List α} (h : small.Subperm large) :
    (small.map f).Subperm (large.map f) := by
  obtain ⟨middle, hperm, hsub⟩ := h
  exact ⟨middle.map f, hperm.map f, hsub.map f⟩

/-- Any three selected rays give an upper bound on the original row
score. Distinctness is required only for the selected center indices;
the direction map itself need not be injective. -/
theorem rowScore_le_sorted_three_directions {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) {lam : ℝ} (hlam : 0 < lam)
    {v a b d : Fin s} (hva : v ≠ a) (hvb : v ≠ b) (hvd : v ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    rowScore lam (directionRow o e c v) ≤
      rowScore lam ([dirRep o e c v a, dirRep o e c v b,
        dirRep o e c v d].insertionSort (· ≤ ·)) := by
  classical
  have hind : ([a, b, d] : List (Fin s)).Subperm ((List.finRange s).erase v) := by
    apply List.subperm_of_subset (by simp [hab, had, hbd])
    intro x hx
    rw [(List.nodup_finRange s).mem_erase_iff]
    have hxv : x ≠ v := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hva.symm
      · exact hvb.symm
      · exact hvd.symm
    exact ⟨hxv, List.mem_finRange x⟩
  have hraw := subperm_map_of_subperm (dirRep o e c v) hind
  have hsmall := (List.perm_insertionSort (· ≤ ·)
    [dirRep o e c v a, dirRep o e c v b, dirRep o e c v d]).subperm
  have hlarge := (List.perm_insertionSort (· ≤ ·)
    (((List.finRange s).erase v).map (dirRep o e c v))).symm.subperm
  have hsub : ([dirRep o e c v a, dirRep o e c v b,
      dirRep o e c v d].insertionSort (· ≤ ·)).Sublist
      (directionRow o e c v) := by
    apply List.sublist_of_subperm_of_sortedLE
      (hsmall.trans (hraw.trans hlarge))
      List.sortedLE_insertionSort (directionRow_sorted o e c v)
  exact rowScore_le_of_sublist hlam hsub (directionRow_sorted o e c v)
    (fun x hx => directionRow_mem_Ico o e c hx)
    (by
      apply List.ne_nil_of_length_pos
      rw [List.length_insertionSort]
      simp)

/-- At least four indices permit a fourth point beside any three
distinct selected centers. -/
theorem exists_fourth_center {s : ℕ} (hs : 4 ≤ s)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ l : Fin s, i ≠ l ∧ j ≠ l ∧ k ≠ l := by
  classical
  have hcard : ({i, j, k} : Finset (Fin s)).card <
      (Finset.univ : Finset (Fin s)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    have hthree : ({i, j, k} : Finset (Fin s)).card = 3 := by
      simp [hij, hik, hjk]
    omega
  obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  exact ⟨l, Ne.symm hl.1, Ne.symm hl.2.1, Ne.symm hl.2.2⟩

/-- The strip `n=2` cannot contain a legal four-point selection with
two saturated anchors. This uses the actual nested geometry and its
three legal angles; no direction-gap identity is needed. -/
theorem three_le_of_two_saturated_four_centers {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k l : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) : 3 ≤ n := by
  obtain ⟨E, hE, hinner | hinner⟩ :=
    two_saturated_nested o e he hn2 hlam hn hleg hs2
      hij hik hil hjk hjl hkl hi hj
  · have h := inner_supplement_gapScore_add_three_le hlam hn hE hinner
      (hleg.triAngle i k j hik hjk.symm hij)
      (hleg.triAngle i k l hik hkl hil)
      (hleg.triAngle j k l hjk hkl hjl)
    omega
  · have h := inner_supplement_gapScore_add_three_le hlam hn hE hinner
      (hleg.triAngle i l j hil hjl.symm hij)
      (hleg.triAngle i l k hil hkl.symm hik)
      (hleg.triAngle j l k hjl hkl.symm hjk)
    omega

/-- Every non-anchor row loses three cells when a fourth center is
present beside two saturated anchors. All hypotheses refer to the
original configuration and its original rows. -/
theorem rowScore_add_three_le_of_two_saturated_four_centers {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs2 : 2 ≤ s)
    {i j k l : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    rowScore lam (directionRow o e c k) + 3 ≤ n := by
  have hlt a b d (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
      ∠ (c a) (c b) (c d) < Real.pi :=
    lt_of_le_of_lt (hleg.triAngle a b d hab hbd had) (sub_lt_self _ hlam)
  have hrestrict := rowScore_le_sorted_three_directions o e c hlam
    hik.symm hjk.symm hkl hij hil hjl
  obtain ⟨E, hE, hinner | hinner⟩ :=
    two_saturated_nested o e he hn2 hlam hn hleg hs2
      hij hik hil hjk hjl hkl hi hj
  · have hid := rowScore_inner_nested_three_directions o e c he hleg.inj
      hik hjk hkl.symm hE hinner
      (hlt i k j hik hjk.symm hij)
      (hlt i k l hik hkl hil)
      (hlt j k l hjk hkl hjl) lam
    have hbound := inner_supplement_gapScore_add_three_le hlam hn hE hinner
      (hleg.triAngle i k j hik hjk.symm hij)
      (hleg.triAngle i k l hik hkl hil)
      (hleg.triAngle j k l hjk hkl hjl)
    rw [hid] at hrestrict
    omega
  · have hid := rowScore_outer_nested_three_directions o e c he hleg.inj
      hik hjk hkl.symm hE hinner
      (EuclideanGeometry.angle_pos_of_not_collinear
        (legal_triple_not_collinear hleg hik hil hkl))
      (EuclideanGeometry.angle_pos_of_not_collinear
        (legal_triple_not_collinear hleg hkl.symm hjl.symm hjk.symm))
      (hlt i k j hik hjk.symm hij) lam
    have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor
    have hbeta : Real.pi - n * lam < lam := by linarith
    have hA : ∠ (c j) (c i) (c k) < lam := lt_of_le_of_lt
      (angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
        hij hik hjk hi) hbeta
    have hB : ∠ (c i) (c j) (c k) < lam := lt_of_le_of_lt
      (angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he hs2
        hij.symm hjk hik hj) hbeta
    have hbound := outer_nested_gapScore_add_three_le hlam hn hE hinner
      (hleg.inj.ne hik) (hleg.inj.ne hjk) hA hB
      (hleg.triAngle i l j hil hjl.symm hij)
      (hleg.triAngle i l k hil hkl.symm hik)
      (hleg.triAngle j l k hjl hkl.symm hjk)
    have htri := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := c i) (p₂ := c j) (c k) (hleg.inj.ne hij.symm)
    rw [EuclideanGeometry.angle_comm (c j) (c k) (c i),
      EuclideanGeometry.angle_comm (c k) (c i) (c j)] at htri
    have hsupp : Real.pi - ∠ (c i) (c k) (c j) =
        ∠ (c j) (c i) (c k) + ∠ (c i) (c j) (c k) := by linarith
    rw [hid, hsupp] at hrestrict
    omega

/-- The sharper original-row exponent bound for configurations with
at least four centers and two saturated anchors. In particular `n ≥ 3`;
there is no natural-subtraction ambiguity at `n=2`. -/
theorem rowScore_add_three_le_of_two_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs4 : 4 ≤ s)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    rowScore lam (directionRow o e c k) + 3 ≤ n := by
  obtain ⟨l, hil, hjl, hkl⟩ := exists_fourth_center hs4 hij hik hjk
  exact rowScore_add_three_le_of_two_saturated_four_centers o e he hn2 hlam hn
    hleg (by omega) hij hik hil hjk hjl hkl hi hj

/-- In the repository's defect convention, every remaining row has
defect at least 3 (a deficit of at least 2 from the saturated exponent). -/
theorem rowDefect_ge_three_of_two_saturated {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (hs4 : 4 ≤ s)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : rowDefect n lam (directionRow o e c i) = 1)
    (hj : rowDefect n lam (directionRow o e c j) = 1) :
    3 ≤ rowDefect n lam (directionRow o e c k) := by
  have hs := rowScore_add_three_le_of_two_saturated o e he hn2 hlam hn
    hleg hs4 hij hik hjk hi hj
  have hc : rowCells lam (directionRow o e c k) ≤ n := by
    simpa only [hn] using rowCells_directionRow_le o e c hlam k (by omega)
  have heq := rowScore_eq_sub_defect lam hlam n (directionRow o e c k) hc
  have hd := rowDefect_le lam hlam n (directionRow o e c k) hc
  omega

end Jsp404

#print axioms Jsp404.rowScore_le_sorted_three_directions
#print axioms Jsp404.exists_fourth_center
#print axioms Jsp404.three_le_of_two_saturated_four_centers
#print axioms Jsp404.rowScore_add_three_le_of_two_saturated_four_centers
#print axioms Jsp404.rowScore_add_three_le_of_two_saturated
#print axioms Jsp404.rowDefect_ge_three_of_two_saturated
