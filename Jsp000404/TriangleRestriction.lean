import Jsp000404.Induction

/-!
# Restricting row weights to selected triangle directions

Deleting directions from a nonempty sorted row can only increase its score.
Consequently any three weights selected from a larger legal configuration
are bounded by the corresponding three-center potential. This is a local
restriction theorem, not an arbitrary-size capacity theorem.
-/

namespace Jsp404

open scoped EuclideanGeometry BigOperators

private theorem rowScore_le_sublist_with_pre {lam : ℝ} (hlam : 0 < lam)
    {small large : List ℝ} (hsub : small.Sublist large) :
    ∀ pre : List ℝ, (pre ++ large).SortedLE →
      (∀ x ∈ pre ++ large, 0 ≤ x ∧ x < Real.pi) →
      pre ++ small ≠ [] →
      rowScore lam (pre ++ large) ≤ rowScore lam (pre ++ small) := by
  induction hsub with
  | slnil => intro pre _ _ _; exact le_rfl
  | @cons small large x hsub ih =>
      intro pre hsort hmem hne
      have hdel : (pre ++ x :: large).eraseIdx pre.length = pre ++ large := by
        rw [List.eraseIdx_append_of_length_le (by omega)]
        simp
      have hkeep : (pre ++ large).Sublist (pre ++ x :: large) :=
        (List.Sublist.refl pre).append (List.sublist_cons_self x large)
      have hlen : 0 < (pre ++ large).length := by
        have hsmall := List.length_pos_iff.mpr hne
        have hle := ((List.Sublist.refl pre).append hsub).length_le
        omega
      obtain ⟨g, _, hg⟩ := rowScore_eraseIdx hlam hsort hmem
        (k := pre.length) (by simp) (by
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega)
      rw [hdel] at hg
      have hstep : rowScore lam (pre ++ x :: large) ≤
          rowScore lam (pre ++ large) := by omega
      exact hstep.trans (ih pre (hsort.pairwise.sublist hkeep).sortedLE
        (fun x hx => hmem x (hkeep.mem hx)) hne)
  | @cons_cons small large x hsub ih =>
      intro pre hsort hmem hne
      simpa only [List.append_assoc, List.singleton_append] using
        ih (pre ++ [x]) (by simpa using hsort)
          (by simpa using hmem) (by simp)

/-- Removing directions from a sorted row, while retaining a nonempty row,
can only increase its cyclic gap score. Multiplicities are allowed. -/
theorem rowScore_le_of_sublist {lam : ℝ} (hlam : 0 < lam)
    {small large : List ℝ} (hsub : small.Sublist large)
    (hsort : large.SortedLE)
    (hmem : ∀ x ∈ large, 0 ≤ x ∧ x < Real.pi) (hne : small ≠ []) :
    rowScore lam large ≤ rowScore lam small := by
  simpa using rowScore_le_sublist_with_pre hlam hsub [] hsort hmem hne

private theorem rowScore_le_pair_of_lt {lam : ℝ} (hlam : 0 < lam)
    {l : List ℝ} (hsort : l.SortedLE)
    (hmem : ∀ x ∈ l, 0 ≤ x ∧ x < Real.pi)
    {a b : ℝ} (ha : a ∈ l) (hb : b ∈ l) (hab : a < b) :
    rowScore lam l ≤ gapScore lam (b-a) + gapScore lam (Real.pi-(b-a)) := by
  have hsub : [a,b].Sublist l := List.sublist_of_subperm_of_sortedLE
    (List.subperm_of_subset (by simp [ne_of_lt hab]) (by simpa using And.intro ha hb))
    (List.pairwise_pair.mpr hab.le).sortedLE hsort
  have h := rowScore_le_of_sublist hlam hsub hsort hmem (by simp)
  simpa [rowScore, cycGaps_pair hab.le] using h

/-- Keeping any two directions bounds the original row by the two
complementary arcs between them. The directions may be equal. -/
theorem rowScore_le_two_arcs {lam : ℝ} (hlam : 0 < lam)
    {l : List ℝ} (hsort : l.SortedLE)
    (hmem : ∀ x ∈ l, 0 ≤ x ∧ x < Real.pi)
    {a b : ℝ} (ha : a ∈ l) (hb : b ∈ l) :
    rowScore lam l ≤ gapScore lam (cyclicDiff a b) +
      gapScore lam (Real.pi - cyclicDiff a b) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · simpa [cyclicDiff, ne_of_lt hab, hab] using
      rowScore_le_pair_of_lt hlam hsort hmem ha hb hab
  · have hsub : [a].Sublist l := List.singleton_sublist.mpr ha
    have h := rowScore_le_of_sublist hlam hsub hsort hmem (by simp)
    simpa [rowScore, cycGaps, wrapGap, cyclicDiff, gapScore] using h
  · have h := rowScore_le_pair_of_lt hlam hsort hmem hb ha hab
    have hcd : cyclicDiff a b = Real.pi + b - a := by
      simp [cyclicDiff, ne_of_gt hab, not_lt_of_gt hab]
    rw [hcd, show Real.pi + b - a = Real.pi - (a-b) by ring,
      show Real.pi - (Real.pi - (a-b)) = a-b by ring]
    simpa [Nat.add_comm] using h

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- A geometric row is bounded by the two arcs of any selected angle at
its center. Only injectivity and positive lambda are needed here. -/
theorem rowScore_le_triangle_arcs {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hlam : 0 < lam) (hinj : Function.Injective c) (he : e ≠ 0)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) :
    rowScore lam (directionRow o e c i) ≤
      gapScore lam (∠ (c j) (c i) (c k)) +
      gapScore lam (Real.pi - ∠ (c j) (c i) (c k)) := by
  have h := rowScore_le_two_arcs hlam (directionRow_sorted o e c i)
    (fun x hx => directionRow_mem_Ico o e c hx)
    ((mem_directionRow o e c).mpr ⟨j, hij.symm, rfl⟩)
    ((mem_directionRow o e c).mpr ⟨k, hik.symm, rfl⟩)
  have hj : c j ≠ c i := fun h => hij (hinj h).symm
  have hk : c k ≠ c i := fun h => hik (hinj h).symm
  rw [cyclicDiff_dirRep o e c he hj hk] at h
  rcases linRep_oangle_eq_angle_or_pi_sub (o := o) hj hk with hA | hA
  · rwa [hA] at h
  · rw [hA, show Real.pi - (Real.pi - ∠ (c j) (c i) (c k)) =
        ∠ (c j) (c i) (c k) by ring] at h
    simpa [Nat.add_comm] using h

/-- Legality is hereditary under any injective choice of center indices. -/
theorem Section4Legality.restrict_injective {s t : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hlegal : Section4Legality c lam)
    (pick : Fin t → Fin s) (hpick : Function.Injective pick) :
    Section4Legality (c ∘ pick) lam where
  lam_pos := hlegal.lam_pos
  inj := hlegal.inj.comp hpick
  triAngle := by
    intro i j k hij hjk hik
    exact hlegal.triAngle (pick i) (pick j) (pick k)
      (fun h => hij (hpick h)) (fun h => hjk (hpick h))
      (fun h => hik (hpick h))

/-- A selected center's full row is bounded by its row in any selected
three-center subconfiguration. -/
theorem rowScore_le_selected_triple {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hlegal : Section4Legality c lam) (he : e ≠ 0)
    (pick : Fin 3 → Fin s) (hpick : Function.Injective pick) (i : Fin 3) :
    rowScore lam (directionRow o e c (pick i)) ≤
      rowScore lam (directionRow o e (c ∘ pick) i) := by
  rw [rowScore_eq_gapScore_arcs (hlegal.restrict_injective pick hpick) he i]
  exact rowScore_le_triangle_arcs o e hlegal.lam_pos hlegal.inj he
    (fun h => other1_ne i (hpick h).symm)
    (fun h => other2_ne i (hpick h).symm)

/-- The three original weights are bounded by the potential of the
selected triangle, whose row gaps can only be larger. -/
theorem selected_triple_weights_le_potential {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hlegal : Section4Legality c lam) (he : e ≠ 0)
    (pick : Fin 3 → Fin s) (hpick : Function.Injective pick) :
    (∑ i : Fin 3, 2 ^ rowScore lam (directionRow o e c (pick i))) ≤
      potential lam (directionRows o e (c ∘ pick)) := by
  unfold potential exponentAt directionRows
  exact Finset.sum_le_sum fun i _ =>
    Nat.pow_le_pow_right (by decide : 0 < 2)
      (rowScore_le_selected_triple o e hlegal he pick hpick i)

/-- Any three selected weights from an arbitrary-size legal configuration
satisfy the three-center low capacity bound. -/
theorem selected_triple_weights_le_low {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hlegal : Section4Legality c lam) (he : e ≠ 0)
    (hlampi : lam < Real.pi) {n : ℕ}
    (hn : Nat.floor (Real.pi / lam) = n) (hn2 : 2 ≤ n)
    (hdelta : Real.pi / lam - n < 1 / 2)
    (pick : Fin 3 → Fin s) (hpick : Function.Injective pick) :
    (∑ i : Fin 3, 2 ^ rowScore lam (directionRow o e c (pick i))) ≤ 2 ^ n := by
  exact (selected_triple_weights_le_potential o e hlegal he pick hpick).trans
    (base3_potential_le (hlegal.restrict_injective pick hpick) he hlampi hn hn2 hdelta)

/-- Any three selected weights from an arbitrary-size legal configuration
satisfy the uniform three-center high capacity bound. -/
theorem selected_triple_weights_le_high {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hlegal : Section4Legality c lam) (he : e ≠ 0)
    (hlampi : lam < Real.pi) {n : ℕ}
    (hn : Nat.floor (Real.pi / lam) = n) (hn2 : 2 ≤ n)
    (pick : Fin 3 → Fin s) (hpick : Function.Injective pick) :
    (∑ i : Fin 3, 2 ^ rowScore lam (directionRow o e c (pick i))) ≤
      2 ^ n + 2 ^ (n-2) := by
  have h := (selected_triple_weights_le_potential o e hlegal he pick hpick).trans
    (base3_potential_le_big (hlegal.restrict_injective pick hpick) he hlampi hn hn2)
  have heq : 5 * 2 ^ (n-2) = 2 ^ n + 2 ^ (n-2) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m+2 := ⟨n-2, by omega⟩
    simp only [Nat.add_sub_cancel, pow_add]
    ring
  rwa [heq] at h

#print axioms rowScore_le_of_sublist
#print axioms rowScore_le_two_arcs
#print axioms rowScore_le_triangle_arcs
#print axioms rowScore_le_selected_triple
#print axioms selected_triple_weights_le_low
#print axioms selected_triple_weights_le_high

end Jsp404
