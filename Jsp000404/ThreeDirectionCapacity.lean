import Jsp000404.AnchoredRows
import Jsp000404.TwoSaturatedFour
import Mathlib.Data.List.Permutation

/-!
# The actual three projective gaps of a nested four-point configuration

For three distinct line directions, each cyclic gap is an angle or its
supplement. Three positive proposed gaps summing to pi determine which
choices occur. This identifies the actual sorted rows without assuming a
gap-identification certificate or choosing an additional reference chart.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

private lemma three_arcs_unique {a b c x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = Real.pi) (ht : a + b + c = Real.pi)
    (ha : a = x ∨ a = Real.pi - x)
    (hb : b = y ∨ b = Real.pi - y)
    (hc : c = z ∨ c = Real.pi - z) :
    a = x ∧ b = y ∧ c = z := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc
  all_goals refine ⟨?_, ?_, ?_⟩ <;> linarith

private lemma ne_of_cyclicDiff_choices {a b x : ℝ} (hx : 0 < x)
    (hxp : x < Real.pi) (h : cyclicDiff a b = x ∨ cyclicDiff a b = Real.pi - x) :
    a ≠ b := by
  intro hab
  subst b
  simp only [cyclicDiff, ↓reduceIte] at h
  rcases h with h | h <;> linarith

private lemma cyclicDiff_choices_rev {a b x : ℝ} (hne : a ≠ b)
    (h : cyclicDiff a b = x ∨ cyclicDiff a b = Real.pi - x) :
    cyclicDiff b a = x ∨ cyclicDiff b a = Real.pi - x := by
  have hs := cyclicDiff_anti hne
  rcases h with h | h
  · right; linarith
  · left; linarith

private lemma rowScore_ordered_three {a b c x y z : ℝ}
    (hsort : ([a,b,c] : List ℝ).SortedLE)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = Real.pi)
    (ha : cyclicDiff a b = x ∨ cyclicDiff a b = Real.pi - x)
    (hb : cyclicDiff b c = y ∨ cyclicDiff b c = Real.pi - y)
    (hc : cyclicDiff c a = z ∨ cyclicDiff c a = Real.pi - z)
    (lam : ℝ) :
    rowScore lam [a, b, c] = gapScore lam x + gapScore lam y + gapScore lam z := by
  have hab : a ≠ b := ne_of_cyclicDiff_choices hx (by linarith) ha
  have hcg : cycGaps [a,b,c] = [cyclicDiff a b, cyclicDiff b c, cyclicDiff c a] := by
    simp [cycGaps, wrapGap, hab.symm]
  have ht : cyclicDiff a b + cyclicDiff b c + cyclicDiff c a = Real.pi := by
    simpa [hcg, add_assoc] using cycGaps_sum_eq_pi hsort (by simp)
  obtain ⟨ha', hb', hc'⟩ := three_arcs_unique hx hy hz hs ht ha hb hc
  simp [rowScore, hcg, ha', hb', hc', Nat.add_assoc]

/-- Positive angle-or-supplement candidates summing to pi identify all
three actual cyclic gaps of the sorted direction triple. -/
theorem rowScore_sort_three_of_pair_arcs {a b c x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = Real.pi)
    (ha : cyclicDiff a b = x ∨ cyclicDiff a b = Real.pi - x)
    (hb : cyclicDiff b c = y ∨ cyclicDiff b c = Real.pi - y)
    (hc : cyclicDiff c a = z ∨ cyclicDiff c a = Real.pi - z)
    (lam : ℝ) :
    rowScore lam ([a, b, c].insertionSort (· ≤ ·)) =
      gapScore lam x + gapScore lam y + gapScore lam z := by
  have hab : a ≠ b := ne_of_cyclicDiff_choices hx (by linarith) ha
  have hbc : b ≠ c := ne_of_cyclicDiff_choices hy (by linarith) hb
  have hca : c ≠ a := ne_of_cyclicDiff_choices hz (by linarith) hc
  have ha' := cyclicDiff_choices_rev hab ha
  have hb' := cyclicDiff_choices_rev hbc hb
  have hc' := cyclicDiff_choices_rev hca hc
  let t := [a,b,c].insertionSort (· ≤ ·)
  have hsort : t.SortedLE := List.sortedLE_insertionSort
  have hcases : t ∈ ([a,b,c] : List ℝ).permutations' :=
    List.mem_permutations'.mpr (List.perm_insertionSort _ _)
  change t ∈ [[a,b,c], [b,a,c], [b,c,a], [a,c,b], [c,a,b], [c,b,a]] at hcases
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcases
  change rowScore lam t = _
  rcases hcases with h | h | h | h | h | h
  · rw [h] at hsort ⊢
    exact rowScore_ordered_three hsort hx hy hz hs ha hb hc lam
  · rw [h] at hsort ⊢
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      rowScore_ordered_three hsort hx hz hy (by linarith) ha' hc' hb' lam
  · rw [h] at hsort ⊢
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      rowScore_ordered_three hsort hy hz hx (by linarith) hb hc ha lam
  · rw [h] at hsort ⊢
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      rowScore_ordered_three hsort hz hy hx (by linarith) hc' hb' ha' lam
  · rw [h] at hsort ⊢
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      rowScore_ordered_three hsort hz hx hy (by linarith) hc ha hb lam
  · rw [h] at hsort ⊢
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      rowScore_ordered_three hsort hy hx hz (by linarith) hb' ha' hc' lam

private lemma dirRep_angle_choices {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (he : e ≠ 0) {v a b : Fin s} (ha : c a ≠ c v) (hb : c b ≠ c v) :
    cyclicDiff (dirRep o e c v a) (dirRep o e c v b) = ∠ (c a) (c v) (c b) ∨
      cyclicDiff (dirRep o e c v a) (dirRep o e c v b) =
        Real.pi - ∠ (c a) (c v) (c b) := by
  rw [cyclicDiff_dirRep o e c he ha hb]
  exact linRep_oangle_eq_angle_or_pi_sub (o := o) ha hb

private lemma choices_complement {d x : ℝ} (h : d = x ∨ d = Real.pi - x) :
    d = Real.pi - x ∨ d = Real.pi - (Real.pi - x) := by
  rcases h with h | h
  · right; linarith
  · exact Or.inl h

/-- At the inner point, the actual three projective gaps are the
supplements of the three surrounding angles. The reference is arbitrary. -/
theorem rowScore_inner_nested_three_directions {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (he : e ≠ 0) (hc : Function.Injective c) {a b k l : Fin s}
    (hak : a ≠ k) (hbk : b ≠ k) (hlk : l ≠ k)
    {E : Plane₂} (hE : Sbtw ℝ (c a) E (c b)) (hC : Sbtw ℝ (c l) (c k) E)
    (hAB : ∠ (c a) (c k) (c b) < Real.pi)
    (hAD : ∠ (c a) (c k) (c l) < Real.pi)
    (hBD : ∠ (c b) (c k) (c l) < Real.pi) (lam : ℝ) :
    rowScore lam ([dirRep o e c k a, dirRep o e c k b, dirRep o e c k l].insertionSort
      (· ≤ ·)) =
      gapScore lam (Real.pi - ∠ (c a) (c k) (c b)) +
      gapScore lam (Real.pi - ∠ (c a) (c k) (c l)) +
      gapScore lam (Real.pi - ∠ (c b) (c k) (c l)) := by
  have hsum := angle_sum_eq_two_pi_of_nested hE hC
  have ha := choices_complement
    (dirRep_angle_choices o e c he (hc.ne hak) (hc.ne hbk))
  have hb := choices_complement
    (dirRep_angle_choices o e c he (hc.ne hbk) (hc.ne hlk))
  have hd := choices_complement
    (dirRep_angle_choices o e c he (hc.ne hlk) (hc.ne hak))
  rw [EuclideanGeometry.angle_comm (c l) (c k) (c a)] at hd
  have h := rowScore_sort_three_of_pair_arcs
    (sub_pos.mpr hAB) (sub_pos.mpr hBD) (sub_pos.mpr hAD)
    (by linarith) ha hb hd lam
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- At the outer point, the ray to the inner point splits the angle to
the two anchors; its two pieces and the exterior angle are the actual gaps. -/
theorem rowScore_outer_nested_three_directions {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (he : e ≠ 0) (hc : Function.Injective c) {a b k l : Fin s}
    (hal : a ≠ l) (hbl : b ≠ l) (hkl : k ≠ l)
    {E : Plane₂} (hE : Sbtw ℝ (c a) E (c b)) (hC : Sbtw ℝ (c l) (c k) E)
    (hACpos : 0 < ∠ (c a) (c l) (c k))
    (hCBpos : 0 < ∠ (c k) (c l) (c b))
    (hABlt : ∠ (c a) (c l) (c b) < Real.pi) (lam : ℝ) :
    rowScore lam ([dirRep o e c l a, dirRep o e c l b, dirRep o e c l k].insertionSort
      (· ≤ ·)) =
      gapScore lam (∠ (c a) (c l) (c k)) +
      gapScore lam (∠ (c k) (c l) (c b)) +
      gapScore lam (Real.pi - ∠ (c a) (c l) (c b)) := by
  have hsplit : ∠ (c a) (c l) (c k) + ∠ (c k) (c l) (c b) =
      ∠ (c a) (c l) (c b) := by
    rw [hC.angle_eq_right (c a), hC.angle_eq_left (c b)]
    exact EuclideanGeometry.angle_add_angle_eq_of_sbtw hE
  have ha := choices_complement
    (dirRep_angle_choices o e c he (hc.ne hal) (hc.ne hbl))
  have hb := dirRep_angle_choices o e c he (hc.ne hbl) (hc.ne hkl)
  have hd := dirRep_angle_choices o e c he (hc.ne hkl) (hc.ne hal)
  rw [EuclideanGeometry.angle_comm (c b) (c l) (c k)] at hb
  rw [EuclideanGeometry.angle_comm (c k) (c l) (c a)] at hd
  have h := rowScore_sort_three_of_pair_arcs
    (sub_pos.mpr hABlt) hCBpos hACpos (by linarith) ha hb hd lam
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- The inner row identity specialized to the complete four-point fan. -/
theorem rowScore_inner_nested_fin4
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin 4 → Plane₂)
    (he : e ≠ 0) (hc : Function.Injective c)
    {E : Plane₂} (hE : Sbtw ℝ (c 0) E (c 1)) (hC : Sbtw ℝ (c 3) (c 2) E)
    (hAB : ∠ (c 0) (c 2) (c 1) < Real.pi)
    (hAD : ∠ (c 0) (c 2) (c 3) < Real.pi)
    (hBD : ∠ (c 1) (c 2) (c 3) < Real.pi) (lam : ℝ) :
    rowScore lam (directionRow o e c 2) =
      gapScore lam (Real.pi - ∠ (c 0) (c 2) (c 1)) +
      gapScore lam (Real.pi - ∠ (c 0) (c 2) (c 3)) +
      gapScore lam (Real.pi - ∠ (c 1) (c 2) (c 3)) := by
  exact rowScore_inner_nested_three_directions o e c he hc
    (by decide) (by decide) (by decide) hE hC hAB hAD hBD lam

/-- The outer row identity specialized to the complete four-point fan. -/
theorem rowScore_outer_nested_fin4
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin 4 → Plane₂)
    (he : e ≠ 0) (hc : Function.Injective c)
    {E : Plane₂} (hE : Sbtw ℝ (c 0) E (c 1)) (hC : Sbtw ℝ (c 3) (c 2) E)
    (hACpos : 0 < ∠ (c 0) (c 3) (c 2))
    (hCBpos : 0 < ∠ (c 2) (c 3) (c 1))
    (hABlt : ∠ (c 0) (c 3) (c 1) < Real.pi) (lam : ℝ) :
    rowScore lam (directionRow o e c 3) =
      gapScore lam (∠ (c 0) (c 3) (c 2)) +
      gapScore lam (∠ (c 2) (c 3) (c 1)) +
      gapScore lam (Real.pi - ∠ (c 0) (c 3) (c 1)) := by
  exact rowScore_outer_nested_three_directions o e c he hc
    (by decide) (by decide) (by decide) hE hC hACpos hCBpos hABlt lam

#print axioms rowScore_sort_three_of_pair_arcs
#print axioms rowScore_inner_nested_three_directions
#print axioms rowScore_outer_nested_three_directions
#print axioms rowScore_inner_nested_fin4
#print axioms rowScore_outer_nested_fin4

end Jsp404
