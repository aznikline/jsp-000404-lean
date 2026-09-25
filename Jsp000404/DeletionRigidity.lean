import Jsp000404.MixedStarExclusion
import Jsp000404.TwoSaturatedDeficit

/-!
# Deletion rigidity of defect-`2` rows

`deletion_rigidity` (general `s`): in a legal configuration with at least
five points, a saturated row `A` and two defect-`2` rows `i, j`, deleting
any fourth point `q ∉ {A, i, j}` leaves row `i` with *exactly* its old
score (and defect `2`).  Deletion never lowers a score
(`rowScore_eraseIdx'`); if `i` rose to saturation, the reduced
configuration (still `≥ 4` points) would have two saturated rows `A, i`
and `rowScore_add_three_le_of_two_saturated` would force
`k'_j + 3 ≤ n`, against `k'_j ≥ k_j = n − 2`.

Scope: the anchor is not deleted, a second defect-`2` row survives, and
the reduced configuration has `≥ 4` points.  Nothing is claimed about
high-defect rows.

Five-point consumers (`five_point_merge_zero_*`): in the anchored row
`[θ_i, x₁, x₂, x₃]` of a defect-`2` row, deleting the vertex behind `x_k`
(with a second defect-`2` survivor) forces zero merge gain of the two
gaps adjacent to `x_k`; in particular they are not both `≥ λ`
(`not_both_big_of_mergeGain_zero`).  The anchor-direction merge
`(g₃, g₀)` is not covered.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- **Deletion rigidity.** -/
theorem deletion_rigidity {s n : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (he : e ≠ 0) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam) (hs4 : 4 ≤ s)
    {A i j q : Fin (s + 1)} (hAi : A ≠ i) (hAj : A ≠ j) (hij : i ≠ j)
    (hAq : A ≠ q) (hjq : j ≠ q)
    (hA : rowDefect n lam (directionRow o e c A) = 1)
    (hi : rowDefect n lam (directionRow o e c i) = 2)
    (hj : rowDefect n lam (directionRow o e c j) = 2)
    {i' : Fin s} (hi' : q.succAbove i' = i) :
    rowScore lam (directionRow o e (c ∘ q.succAbove) i') =
        rowScore lam (directionRow o e c i) ∧
      rowDefect n lam (directionRow o e (c ∘ q.succAbove) i') = 2 := by
  classical
  obtain ⟨A', hA'⟩ := Fin.exists_succAbove_eq hAq
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hjq
  have hleg' := hleg.erase q
  have hup : ∀ x' : Fin s,
      rowScore lam (directionRow o e c (q.succAbove x')) ≤
        rowScore lam (directionRow o e (c ∘ q.succAbove) x') := by
    intro x'
    rw [eraseIdx_directionRow o e q x']
    have hx : q.succAbove x' ≠ q := Fin.succAbove_ne q x'
    rw [rowScore_eraseIdx' hlam (directionRow_sorted o e c _)
      (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
      (deleteIndex_lt o e c hx) (by rw [directionRow_length]; omega)]
    omega
  have cO : ∀ x, rowCells lam (directionRow o e c x) ≤ n := fun x =>
    rowCells_directionRow_le_of_floor_eq o e c hlam x (by omega) hn
  have cN : ∀ x', rowCells lam (directionRow o e (c ∘ q.succAbove) x') ≤ n :=
    fun x' => rowCells_directionRow_le_of_floor_eq o e _ hlam x' (by omega) hn
  have sO := fun x => rowScore_eq_sub_defect lam hlam n _ (cO x)
  have sN := fun x' => rowScore_eq_sub_defect lam hlam n _ (cN x')
  have dN := fun x' => rowDefect_le lam hlam n _ (cN x')
  have gN := fun x' => one_le_rowDefect lam hlam n _ (by omega) (cN x')
  have dO := fun x => rowDefect_le lam hlam n _ (cO x)
  have uA := hup A'
  have ui := hup i'
  have uj := hup j'
  rw [hA'] at uA
  rw [hi'] at ui
  rw [hj'] at uj
  have sA := sO A
  have si := sO i
  have sj := sO j
  have sA' := sN A'
  have si' := sN i'
  have sj' := sN j'
  have gA' := gN A'
  have gi' := gN i'
  have dA' := dN A'
  have di' := dN i'
  have dj' := dN j'
  have dA := dO A
  have hA1 : rowDefect n lam (directionRow o e (c ∘ q.succAbove) A') = 1 := by
    omega
  have hAi' : A' ≠ i' := fun h => hAi (by rw [← hA', ← hi', h])
  have hAj' : A' ≠ j' := fun h => hAj (by rw [← hA', ← hj', h])
  have hij' : i' ≠ j' := fun h => hij (by rw [← hi', ← hj', h])
  have hi2 : rowDefect n lam (directionRow o e (c ∘ q.succAbove) i') = 2 := by
    by_contra hne
    have hi1 : rowDefect n lam (directionRow o e (c ∘ q.succAbove) i') = 1 := by
      omega
    have h3 := rowScore_add_three_le_of_two_saturated o e he hn2 hlam hn hleg'
      hs4 hAi' hAj' hij' hA1 hi1
    omega
  exact ⟨by omega, hi2⟩

/-- Two gaps with zero merge gain are not both `≥ λ`. -/
theorem not_both_big_of_mergeGain_zero {lam x y : ℝ} (hlam : 0 < lam)
    (h : mergeGain lam x y = 0) : ¬ (lam ≤ x ∧ lam ≤ y) := by
  rintro ⟨hx, hy⟩
  have := mergeGain_pos_of_ge hlam hx hy
  omega

theorem sortedLE_three {a b d : ℝ} (h1 : a ≤ b) (h2 : b ≤ d) :
    [a, b, d].SortedLE := by
  refine List.Pairwise.sortedLE (List.pairwise_cons.mpr ⟨fun x hx => ?_,
    List.pairwise_cons.mpr ⟨fun x hx => ?_, List.pairwise_singleton _ _⟩⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain rfl | rfl := hx <;> linarith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; exact h2

theorem sortedLE_four {a b d f : ℝ} (h1 : a ≤ b) (h2 : b ≤ d) (h3 : d ≤ f) :
    [a, b, d, f].SortedLE := by
  refine List.Pairwise.sortedLE (List.pairwise_cons.mpr ⟨fun x hx => ?_,
    (sortedLE_three h2 h3).pairwise⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain rfl | rfl | rfl := hx <;> linarith

section FivePoint

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- The anchored full row of a non-anchor vertex. -/
theorem anchor_row (i : Fin 4) :
    directionRow o e c (v.succAbove i) =
      theta i :: directionRow o e (c ∘ v.succAbove) i := by
  have hlampi : lam < Real.pi := by
    have := C.hnl; have := C.hn3'; have := C.hlam; nlinarith
  exact directionRow_anchor_cons o e C.he c C.hleg.inj v C.hlam hlampi theta
    (fun k => ⟨Set.Icc_subset_Icc le_rfl C.hβ.le (C.htheta k).1, (C.htheta k).2⟩)
    (fun a b hab => phi_ge_lam C hab) i

/-- Five-point sub-row identification. -/
theorem row4_eq {h a b d : Fin 4} (hha : h ≠ a) (hhb : h ≠ b) (hhd : h ≠ d)
    (h1 : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (h2 : dirRep o e (c ∘ v.succAbove) h b < dirRep o e (c ∘ v.succAbove) h d) :
    directionRow o e (c ∘ v.succAbove) h =
      [dirRep o e (c ∘ v.succAbove) h a, dirRep o e (c ∘ v.succAbove) h b,
        dirRep o e (c ∘ v.succAbove) h d] := by
  have hlen : (directionRow o e (c ∘ v.succAbove) h).length = 3 := by
    rw [directionRow_length]
  obtain ⟨p, q, r, hl⟩ := List.length_eq_three.mp hlen
  have hsort := (directionRow_sorted o e (c ∘ v.succAbove) h).pairwise
  rw [hl] at hsort
  have hpq : p ≤ q := by simp at hsort; exact hsort.1.1
  have hqr : q ≤ r := by simp at hsort; exact hsort.2
  have hmem : ∀ j, j ≠ h → dirRep o e (c ∘ v.succAbove) h j ∈ [p, q, r] := by
    intro j hj; rw [← hl]
    exact (mem_directionRow o e (c ∘ v.succAbove)).mpr ⟨j, hj, rfl⟩
  have hA := hmem a hha.symm
  have hB := hmem b hhb.symm
  have hD := hmem d hhd.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA hB hD
  rw [hl]
  rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
    rcases hD with hD | hD | hD <;>
    first
    | (exfalso; linarith)
    | (rw [hA, hB, hD])

/-- Common deletion step: deleting `v.succAbove k` keeps the score of row
`v.succAbove i`, provided another defect-`2` row `j ∉ {i, k}` survives. -/
theorem five_point_delete_score {i k j : Fin 4} (hik : i ≠ k) (hji : j ≠ i)
    (hjk : j ≠ k)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    rowScore lam ((directionRow o e c (v.succAbove i)).erase
        (dirRep o e (c ∘ v.succAbove) i k)) =
      rowScore lam (directionRow o e c (v.succAbove i)) := by
  have hne : v.succAbove i ≠ v.succAbove k :=
    fun h => hik (Fin.succAbove_right_injective h)
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hne
  have hr := (deletion_rigidity o e C.he (by have := C.hn3; omega) C.hlam C.hn
    C.hleg (le_refl 4) (Fin.ne_succAbove v i) (Fin.ne_succAbove v j)
    (fun h => hji (Fin.succAbove_right_injective h).symm)
    (Fin.ne_succAbove v k)
    (fun h => hjk (Fin.succAbove_right_injective h)) hA hi hj hi').1
  rw [erase_directionRow o e (c' := c) (v.succAbove k) i', hi'] at hr
  exact hr

/-- **Zero merge gain at the middle chord.** -/
theorem five_point_merge_zero_mid {i a b d j : Fin 4}
    (hia : i ≠ a) (hib : i ≠ b) (hid : i ≠ d) (hji : j ≠ i) (hjb : j ≠ b)
    (h1 : dirRep o e (c ∘ v.succAbove) i a < dirRep o e (c ∘ v.succAbove) i b)
    (h2 : dirRep o e (c ∘ v.succAbove) i b < dirRep o e (c ∘ v.succAbove) i d)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    mergeGain lam
      (dirRep o e (c ∘ v.succAbove) i b - dirRep o e (c ∘ v.succAbove) i a)
      (dirRep o e (c ∘ v.succAbove) i d - dirRep o e (c ∘ v.succAbove) i b) = 0 := by
  have hdel := five_point_delete_score C hib hji hjb hA hi hj
  rw [anchor_row C i, row4_eq C hia hib hid h1 h2] at hdel
  set A := dirRep o e (c ∘ v.succAbove) i a
  set B := dirRep o e (c ∘ v.succAbove) i b
  set D := dirRep o e (c ∘ v.succAbove) i d
  have hθA : theta i < A := by
    have := phi_ge_lam C hia; have := C.hβ; linarith [(C.htheta i).1.2]
  have hlist : [theta i, A, B, D].erase B = [theta i, A, D] := by
    simp [show theta i ≠ B by linarith, show A ≠ B by linarith]
  rw [hlist, rowScore_cons_eq_linear (sortedLE_three (by linarith) (by linarith)),
    rowScore_cons_eq_linear (sortedLE_four (by linarith) (by linarith) (by linarith))] at hdel
  simp only [linearGapScore] at hdel
  have hspec := mergeGain_spec C.hlam (by linarith : (0 : ℝ) ≤ B - A)
    (by linarith : (0 : ℝ) ≤ D - B)
  rw [show B - A + (D - B) = D - A by ring] at hspec
  omega

/-- **Zero merge gain at the first chord.** -/
theorem five_point_merge_zero_first {i a b d j : Fin 4}
    (hia : i ≠ a) (hib : i ≠ b) (hid : i ≠ d) (hji : j ≠ i) (hja : j ≠ a)
    (h1 : dirRep o e (c ∘ v.succAbove) i a < dirRep o e (c ∘ v.succAbove) i b)
    (h2 : dirRep o e (c ∘ v.succAbove) i b < dirRep o e (c ∘ v.succAbove) i d)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    mergeGain lam (dirRep o e (c ∘ v.succAbove) i a - theta i)
      (dirRep o e (c ∘ v.succAbove) i b - dirRep o e (c ∘ v.succAbove) i a) = 0 := by
  have hdel := five_point_delete_score C hia hji hja hA hi hj
  rw [anchor_row C i, row4_eq C hia hib hid h1 h2] at hdel
  set A := dirRep o e (c ∘ v.succAbove) i a
  set B := dirRep o e (c ∘ v.succAbove) i b
  set D := dirRep o e (c ∘ v.succAbove) i d
  have hθA : theta i < A := by
    have := phi_ge_lam C hia; have := C.hβ; linarith [(C.htheta i).1.2]
  have hlist : [theta i, A, B, D].erase A = [theta i, B, D] := by
    simp [show theta i ≠ A by linarith]
  rw [hlist, rowScore_cons_eq_linear (sortedLE_three (by linarith) (by linarith)),
    rowScore_cons_eq_linear (sortedLE_four (by linarith) (by linarith) (by linarith))] at hdel
  simp only [linearGapScore] at hdel
  have hspec := mergeGain_spec C.hlam (by linarith : (0 : ℝ) ≤ A - theta i)
    (by linarith : (0 : ℝ) ≤ B - A)
  rw [show A - theta i + (B - A) = B - theta i by ring] at hspec
  omega

/-- **Zero merge gain at the last chord.** -/
theorem five_point_merge_zero_last {i a b d j : Fin 4}
    (hia : i ≠ a) (hib : i ≠ b) (hid : i ≠ d) (hji : j ≠ i) (hjd : j ≠ d)
    (h1 : dirRep o e (c ∘ v.succAbove) i a < dirRep o e (c ∘ v.succAbove) i b)
    (h2 : dirRep o e (c ∘ v.succAbove) i b < dirRep o e (c ∘ v.succAbove) i d)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    mergeGain lam
      (dirRep o e (c ∘ v.succAbove) i d - dirRep o e (c ∘ v.succAbove) i b)
      (theta i + Real.pi - dirRep o e (c ∘ v.succAbove) i d) = 0 := by
  have hdel := five_point_delete_score C hid hji hjd hA hi hj
  rw [anchor_row C i, row4_eq C hia hib hid h1 h2] at hdel
  set A := dirRep o e (c ∘ v.succAbove) i a
  set B := dirRep o e (c ∘ v.succAbove) i b
  set D := dirRep o e (c ∘ v.succAbove) i d
  have hθA : theta i < A := by
    have := phi_ge_lam C hia; have := C.hβ; linarith [(C.htheta i).1.2]
  have hDpi : D < Real.pi := (phi_mem C i d).2
  have hlist : [theta i, A, B, D].erase D = [theta i, A, B] := by
    simp [show theta i ≠ D by linarith, show A ≠ D by linarith,
      show B ≠ D by linarith]
  rw [hlist, rowScore_cons_eq_linear (sortedLE_three (by linarith) (by linarith)),
    rowScore_cons_eq_linear (sortedLE_four (by linarith) (by linarith) (by linarith))] at hdel
  simp only [linearGapScore] at hdel
  have hspec := mergeGain_spec C.hlam (by linarith : (0 : ℝ) ≤ D - B)
    (by linarith [(C.htheta i).1.1] : (0 : ℝ) ≤ theta i + Real.pi - D)
  rw [show D - B + (theta i + Real.pi - D) = theta i + Real.pi - B by ring] at hspec
  omega

end FivePoint

#print axioms deletion_rigidity
#print axioms not_both_big_of_mergeGain_zero
#print axioms row4_eq
#print axioms five_point_delete_score
#print axioms five_point_merge_zero_mid
#print axioms five_point_merge_zero_first
#print axioms five_point_merge_zero_last

end Jsp404
