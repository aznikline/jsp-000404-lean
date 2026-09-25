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

Two-in receivers (`two_in_*_row`): a receiver with short chords from
exactly two non-anchor sources has reduced score `n−2` (same side) or
`n−3` (mixed) after deleting the third source, and reinsertion splits a
single real gap with `c_h = c_h⁻ + μ`, `μ ≤ 2`.  Since all other reduced
gaps are `< 2λ`, a growing defect pins the third direction into the
unique long gap: `two_in_F_above`/`two_in_L_below` (`z` beyond both
received directions, `c_h = 2 + μ ≤ 4`) and `two_in_mixed_between`
(`z` strictly between, `c_h = 3 + μ ≤ 5`); `two_in_mixed_five` extracts
the `μ = 2` floor-carry pattern (`n ≥ 5`, both pieces `≥ λ`).
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

/-! ### Two-in receivers: the one-insertion normal form

If a five-point receiver `h` has short chords from exactly two of the
three other non-anchor vertices, delete the third (`t`): the reduced
two-chord row is a star receiver, so `star_linear_score_*` evaluates it
(`n−2` same side, `n−3` mixed).  Reinserting `t` splits exactly one real
gap `G = X + Y` and `mergeGain_spec` gives `score_full + μ = score_red`,
i.e. `c_h = c_h⁻ + μ`.  Since each reduced gap outside the unique long
one is `< 2λ`, `mergeGain_eq_zero_of_lt` pins `z = φ(h,t)` into that gap
whenever the defect grows. -/

/-- Splitting the first gap: `[θ, x, y]` vs `[θ, z, x, y]`. -/
theorem linScore_split_low {lam θ x y z R : ℝ} (hlam : 0 < lam)
    (hθz : θ ≤ z) (hzx : z ≤ x) :
    linearGapScore lam θ R [x, y] =
      linearGapScore lam θ R [z, x, y] + mergeGain lam (z - θ) (x - z) := by
  have hspec := mergeGain_spec hlam (sub_nonneg.mpr hθz) (sub_nonneg.mpr hzx)
  rw [show z - θ + (x - z) = x - θ by ring] at hspec
  simp only [linearGapScore]
  omega

/-- Splitting the middle gap: `[θ, x, y]` vs `[θ, x, z, y]`. -/
theorem linScore_split_mid {lam θ x y z R : ℝ} (hlam : 0 < lam)
    (hxz : x ≤ z) (hzy : z ≤ y) :
    linearGapScore lam θ R [x, y] =
      linearGapScore lam θ R [x, z, y] + mergeGain lam (z - x) (y - z) := by
  have hspec := mergeGain_spec hlam (sub_nonneg.mpr hxz) (sub_nonneg.mpr hzy)
  rw [show z - x + (y - z) = y - x by ring] at hspec
  simp only [linearGapScore]
  omega

/-- Splitting the last gap: `[θ, x, y]` vs `[θ, x, y, z]`. -/
theorem linScore_split_high {lam θ x y z R : ℝ} (hlam : 0 < lam)
    (hyz : y ≤ z) (hzR : z ≤ R) :
    linearGapScore lam θ R [x, y] =
      linearGapScore lam θ R [x, y, z] + mergeGain lam (z - y) (R - z) := by
  have hspec := mergeGain_spec hlam (sub_nonneg.mpr hyz) (sub_nonneg.mpr hzR)
  rw [show z - y + (R - z) = R - y by ring] at hspec
  simp only [linearGapScore]
  omega

/-- A merge gain of `2` forces both pieces `≥ λ` and a floor carry. -/
theorem mergeGain_eq_two {lam x y : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : mergeGain lam x y = 2) :
    lam ≤ x ∧ lam ≤ y ∧
      ⌊(x + y) / lam⌋₊ = ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 1 := by
  have hspec := mergeGain_spec hlam hx hy
  have hx' : 0 ≤ x / lam := div_nonneg hx hlam.le
  have hy' : 0 ≤ y / lam := div_nonneg hy hlam.le
  have hxy' : 0 ≤ (x + y) / lam := div_nonneg (add_nonneg hx hy) hlam.le
  have hdiv : (x + y) / lam = x / lam + y / lam := add_div x y lam
  have h1 : ⌊x / lam⌋₊ + ⌊y / lam⌋₊ ≤ ⌊(x + y) / lam⌋₊ := by
    rcases Nat.eq_zero_or_pos (⌊x / lam⌋₊ + ⌊y / lam⌋₊) with hh | hh
    · omega
    · rw [Nat.le_floor_iff' (Nat.ne_of_gt hh), hdiv]
      push_cast
      exact add_le_add (Nat.floor_le hx') (Nat.floor_le hy')
  have h2 : ⌊(x + y) / lam⌋₊ ≤ ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 1 := by
    have h3 : ⌊(x + y) / lam⌋₊ < ⌊x / lam⌋₊ + ⌊y / lam⌋₊ + 2 := by
      rw [Nat.floor_lt hxy', hdiv]
      push_cast
      linarith [Nat.lt_floor_add_one (x / lam), Nat.lt_floor_add_one (y / lam)]
    omega
  unfold mergeGain gapScore at h
  have hax : 1 ≤ ⌊x / lam⌋₊ := by omega
  have hay : 1 ≤ ⌊y / lam⌋₊ := by omega
  refine ⟨?_, ?_, by omega⟩
  · have := (Nat.le_floor_iff' one_ne_zero).mp hax
    rw [le_div_iff₀ hlam] at this; simpa using this
  · have := (Nat.le_floor_iff' one_ne_zero).mp hay
    rw [le_div_iff₀ hlam] at this; simpa using this

section TwoIn

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- **Two-in receiver, F side.**  If `h` receives short chords from
`a, b` whose rows sit above (`theta h < theta ·`), both chords land in
the F window.  Either the third direction `z` leaves the defect at `2`,
or `z` lies strictly above both received directions and the defect is
`2 + μ` with `μ ≤ 2` the merge gain of the split last gap. -/
theorem two_in_F_row {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta h < theta b)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) = 2 ∨
      (dirRep o e (c ∘ v.succAbove) h b < dirRep o e (c ∘ v.succAbove) h t ∧
        rowDefect n lam (directionRow o e c (v.succAbove h)) =
          2 + mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
            (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) ∧
        mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
            (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) ≤ 2) := by
  classical
  set xa := dirRep o e (c ∘ v.succAbove) h a with hxa
  set xb := dirRep o e (c ∘ v.succAbove) h b with hxb
  set z := dirRep o e (c ∘ v.succAbove) h t with hz
  have hn3 := C.hn3
  have hθ0 := (C.htheta h).1.1
  have P : StarParams n lam (theta h) :=
    ⟨C.hn3, C.hlam, (C.htheta h).1.1, (C.htheta h).1.2, C.hβ⟩
  have hFa : StarF n lam (theta h) xa := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwa with
      hF | hL
    · exact hF.1
    · exact absurd hL.2 (not_lt.mpr haθ.le)
  have hFb : StarF n lam (theta h) xb := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwb with
      hF | hL
    · exact hF.1
    · exact absurd hL.2 (not_lt.mpr hbθ.le)
  have hsort2 : [xa, xb].Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simpa using hord.le, List.pairwise_singleton _ _⟩
  have hwin2 : ∀ w ∈ [xa, xb],
      StarF n lam (theta h) w ∨ StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hFa
    · exact Or.inl hFb
  have hside2 : ∀ w ∈ [xa, xb], StarF n lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hFa
    · exact hFb
  have hk2 : linearGapScore lam (theta h) (theta h + Real.pi) [xa, xb] = n - 2 :=
    star_linear_score_one_sided P hsort2 (by simp) hwin2 (Or.inl hside2)
  have hsd := score_add_defect C (by decide) h
  have hθz : theta h < z := by
    have h1 := phi_ge_lam C htt
    have h2 := (C.htheta h).1.2
    have h3 := C.hβ
    linarith
  have hzπ : z < Real.pi := (phi_mem C h t).2
  have hgap0 : xa - theta h < 2 * lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.1
    linarith [hFa.2]
  have hgap1 : xb - xa < 2 * lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.1
    linarith [hFa.1, hFb.2]
  rcases lt_trichotomy z xa with hz1 | hz1 | hz1
  · left
    have hrow := row4_eq C htt hta htb hz1 hord
    rw [hrow] at hsd
    simp only [← hxa, ← hxb, ← hz] at hsd
    have hμ : mergeGain lam (z - theta h) (xa - z) = 0 :=
      mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hθz.le) (sub_nonneg.mpr hz1.le) (by linarith)
    have hsp := linScore_split_low (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hθz.le hz1.le
    omega
  · exact absurd hz1 hzta
  · rcases lt_trichotomy z xb with hz2 | hz2 | hz2
    · left
      have hrow := row4_eq C hta htt htb hz1 hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xa) (xb - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz1.le) (sub_nonneg.mpr hz2.le) (by linarith)
      have hsp := linScore_split_mid (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hz1.le hz2.le
      omega
    · exact absurd hz2 hztb
    · right
      have hrow := row4_eq C hta htb htt hord hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ2 := mergeGain_le_two C.hlam (sub_nonneg.mpr hz2.le)
        (by linarith : (0 : ℝ) ≤ theta h + Real.pi - z)
      have hsp := linScore_split_high (θ := theta h) (x := xa) (y := xb) (R := theta h + Real.pi) C.hlam hz2.le
        (by linarith : z ≤ theta h + Real.pi)
      refine ⟨hz2, by omega, ?_⟩
      omega

/-- F-side consumer: defect `≥ 3` forces `z` above both received
directions, positive merge gain, and defect `≤ 4`. -/
theorem two_in_F_above {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta h < theta b)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h))) :
    dirRep o e (c ∘ v.succAbove) h b < dirRep o e (c ∘ v.succAbove) h t ∧
      1 ≤ mergeGain lam
        (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
        (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) ∧
      rowDefect n lam (directionRow o e c (v.succAbove h)) =
        2 + mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
          (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) := by
  rcases two_in_F_row C hta htb htt hwa hwb haθ hbθ hord hzta hztb with
    h | ⟨h1, h2, _⟩
  · omega
  · exact ⟨h1, by omega, h2⟩

/-- **Two-in receiver, L side** (mirror of `two_in_F_row`). -/
theorem two_in_L_row {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta a < theta h) (hbθ : theta b < theta h)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) = 2 ∨
      (dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h a ∧
        rowDefect n lam (directionRow o e c (v.succAbove h)) =
          2 + mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - theta h)
            (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t) ∧
        mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - theta h)
            (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t)
          ≤ 2) := by
  classical
  set xa := dirRep o e (c ∘ v.succAbove) h a with hxa
  set xb := dirRep o e (c ∘ v.succAbove) h b with hxb
  set z := dirRep o e (c ∘ v.succAbove) h t with hz
  have hn3 := C.hn3
  have hθ0 := (C.htheta h).1.1
  have P : StarParams n lam (theta h) :=
    ⟨C.hn3, C.hlam, (C.htheta h).1.1, (C.htheta h).1.2, C.hβ⟩
  have hLa : StarL lam (theta h) xa := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwa with
      hF | hL
    · exact absurd hF.2 (not_lt.mpr haθ.le)
    · exact hL.1
  have hLb : StarL lam (theta h) xb := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwb with
      hF | hL
    · exact absurd hF.2 (not_lt.mpr hbθ.le)
    · exact hL.1
  have hsort2 : [xa, xb].Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simpa using hord.le, List.pairwise_singleton _ _⟩
  have hwin2 : ∀ w ∈ [xa, xb],
      StarF n lam (theta h) w ∨ StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inr hLa
    · exact Or.inr hLb
  have hside2 : ∀ w ∈ [xa, xb], StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hLa
    · exact hLb
  have hk2 : linearGapScore lam (theta h) (theta h + Real.pi) [xa, xb] = n - 2 :=
    star_linear_score_one_sided P hsort2 (by simp) hwin2 (Or.inr hside2)
  have hsd := score_add_defect C (by decide) h
  have hθz : theta h < z := by
    have h1 := phi_ge_lam C htt
    have h2 := (C.htheta h).1.2
    have h3 := C.hβ
    linarith
  have hzπ : z < Real.pi := (phi_mem C h t).2
  have hθlt : theta h < lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.2
    linarith
  have hgap1 : xb - xa < 2 * lam := by
    linarith [hLa.1, hLb.2]
  have hgap2 : theta h + Real.pi - xb < 2 * lam := by
    linarith [hLb.1]
  rcases lt_trichotomy z xa with hz1 | hz1 | hz1
  · right
    have hrow := row4_eq C htt hta htb hz1 hord
    rw [hrow] at hsd
    simp only [← hxa, ← hxb, ← hz] at hsd
    have hμ2 := mergeGain_le_two C.hlam (sub_nonneg.mpr hθz.le)
      (sub_nonneg.mpr hz1.le)
    have hsp := linScore_split_low (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hθz.le hz1.le
    refine ⟨hz1, by omega, ?_⟩
    omega
  · exact absurd hz1 hzta
  · rcases lt_trichotomy z xb with hz2 | hz2 | hz2
    · left
      have hrow := row4_eq C hta htt htb hz1 hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xa) (xb - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz1.le) (sub_nonneg.mpr hz2.le) (by linarith)
      have hsp := linScore_split_mid (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hz1.le hz2.le
      omega
    · exact absurd hz2 hztb
    · left
      have hrow := row4_eq C hta htb htt hord hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xb) (theta h + Real.pi - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz2.le)
          (by linarith : (0 : ℝ) ≤ theta h + Real.pi - z)
          (by linarith)
      have hsp := linScore_split_high (θ := theta h) (x := xa) (y := xb) (R := theta h + Real.pi) C.hlam hz2.le
        (by linarith : z ≤ theta h + Real.pi)
      omega

/-- L-side consumer: defect `≥ 3` forces `z` below both received
directions, positive merge gain, and defect `≤ 4`. -/
theorem two_in_L_below {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta a < theta h) (hbθ : theta b < theta h)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h))) :
    dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h a ∧
      1 ≤ mergeGain lam
        (dirRep o e (c ∘ v.succAbove) h t - theta h)
        (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t) ∧
      rowDefect n lam (directionRow o e c (v.succAbove h)) =
        2 + mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - theta h)
          (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t) := by
  rcases two_in_L_row C hta htb htt hwa hwb haθ hbθ hord hzta hztb with
    h | ⟨h1, h2, _⟩
  · omega
  · exact ⟨h1, by omega, h2⟩

/-- **Two-in receiver, mixed.**  One F chord `a` and one L chord `b`.
Either the defect is exactly `3`, or `z` lies strictly between the two
received directions and the defect is `3 + μ` with `μ ≤ 2` the merge
gain of the split middle gap. -/
theorem two_in_mixed_row {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) = 3 ∨
      (dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h t ∧
        dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h b ∧
        rowDefect n lam (directionRow o e c (v.succAbove h)) =
          3 + mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
            (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) ∧
        mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
            (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t)
          ≤ 2) := by
  classical
  set xa := dirRep o e (c ∘ v.succAbove) h a with hxa
  set xb := dirRep o e (c ∘ v.succAbove) h b with hxb
  set z := dirRep o e (c ∘ v.succAbove) h t with hz
  have hn3 := C.hn3
  have hθ0 := (C.htheta h).1.1
  have P : StarParams n lam (theta h) :=
    ⟨C.hn3, C.hlam, (C.htheta h).1.1, (C.htheta h).1.2, C.hβ⟩
  have hFa : StarF n lam (theta h) xa := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwa with
      hF | hL
    · exact hF.1
    · exact absurd hL.2 (not_lt.mpr haθ.le)
  have hLb : StarL lam (theta h) xb := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwb with
      hF | hL
    · exact absurd hF.2 (not_lt.mpr hbθ.le)
    · exact hL.1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hord : xa < xb := by
    have h1 : 2 * lam ≤ n * lam := by nlinarith [C.hlam]
    linarith [hFa.2, hLb.1]
  have hsort2 : [xa, xb].Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simpa using hord.le, List.pairwise_singleton _ _⟩
  have hwin2 : ∀ w ∈ [xa, xb],
      StarF n lam (theta h) w ∨ StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hFa
    · exact Or.inr hLb
  have hk2 : linearGapScore lam (theta h) (theta h + Real.pi) [xa, xb] = n - 3 :=
    star_linear_score_mixed P hsort2 hwin2
      ⟨xa, by simp, hFa⟩ ⟨xb, by simp, hLb⟩
  have hsd := score_add_defect C (by decide) h
  have hθz : theta h < z := by
    have h1 := phi_ge_lam C htt
    have h2 := (C.htheta h).1.2
    have h3 := C.hβ
    linarith
  have hzπ : z < Real.pi := (phi_mem C h t).2
  have hθlt : theta h < lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.2
    linarith
  have hgap0 : xa - theta h < 2 * lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.1
    linarith [hFa.2]
  have hgap2 : theta h + Real.pi - xb < 2 * lam := by
    linarith [hLb.1]
  rcases lt_trichotomy z xa with hz1 | hz1 | hz1
  · left
    have hrow := row4_eq C htt hta htb hz1 hord
    rw [hrow] at hsd
    simp only [← hxa, ← hxb, ← hz] at hsd
    have hμ : mergeGain lam (z - theta h) (xa - z) = 0 :=
      mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hθz.le) (sub_nonneg.mpr hz1.le) (by linarith)
    have hsp := linScore_split_low (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hθz.le hz1.le
    omega
  · exact absurd hz1 hzta
  · rcases lt_trichotomy z xb with hz2 | hz2 | hz2
    · right
      have hrow := row4_eq C hta htt htb hz1 hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ2 := mergeGain_le_two C.hlam (sub_nonneg.mpr hz1.le)
        (sub_nonneg.mpr hz2.le)
      have hsp := linScore_split_mid (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hz1.le hz2.le
      exact ⟨hz1, hz2, by omega, hμ2⟩
    · exact absurd hz2 hztb
    · left
      have hrow := row4_eq C hta htb htt hord hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xb) (theta h + Real.pi - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz2.le)
          (by linarith : (0 : ℝ) ≤ theta h + Real.pi - z)
          (by linarith)
      have hsp := linScore_split_high (θ := theta h) (x := xa) (y := xb) (R := theta h + Real.pi) C.hlam hz2.le
        (by linarith : z ≤ theta h + Real.pi)
      omega

/-- A mixed two-in receiver always has defect `≥ 3`. -/
theorem two_in_mixed_ge_three {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b)
    (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h)) := by
  rcases two_in_mixed_row C hta htb htt hwa hwb haθ hbθ hzta hztb with
    h | ⟨_, _, h2, _⟩
  · omega
  · omega

/-- Mixed consumer: defect `> 3` forces `z` strictly between the received
directions and defect `= 3 + μ`, `μ ∈ {1, 2}`. -/
theorem two_in_mixed_between {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b)
    (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : 3 < rowDefect n lam (directionRow o e c (v.succAbove h))) :
    dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h t ∧
      dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h b ∧
      rowDefect n lam (directionRow o e c (v.succAbove h)) =
        3 + mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
          (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) ∧
      1 ≤ mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
          (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) := by
  rcases two_in_mixed_row C hta htb htt hwa hwb haθ hbθ hzta hztb with
    h | ⟨h1, h2, h3, _⟩
  · omega
  · exact ⟨h1, h2, h3, by omega⟩

/-- The extremal mixed case `c_h = 5`: the insertion gain is `2`, so both
split pieces are `≥ λ` with a floor carry, and `n ≥ 5`. -/
theorem two_in_mixed_five {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b)
    (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove h)) = 5) :
    lam ≤ dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a ∧
      lam ≤ dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t ∧
      ⌊(dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h a) /
          lam⌋₊ =
        ⌊(dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a) /
            lam⌋₊ +
          ⌊(dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) /
            lam⌋₊ + 1 ∧
      5 ≤ n := by
  obtain ⟨h1, h2, h3, hμ1⟩ := two_in_mixed_between C hta htb htt hwa hwb
    haθ hbθ hzta hztb (by omega)
  have hμ : mergeGain lam
      (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
      (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) = 2 := by
    omega
  obtain ⟨hx, hy, hcar⟩ := mergeGain_eq_two C.hlam
    (sub_nonneg.mpr h1.le) (sub_nonneg.mpr h2.le) hμ
  rw [show (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a) +
      (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) =
      dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h a
      by ring] at hcar
  have hsd := score_add_defect C (by decide) h
  exact ⟨hx, hy, hcar, by omega⟩

end TwoIn

#print axioms deletion_rigidity
#print axioms not_both_big_of_mergeGain_zero
#print axioms row4_eq
#print axioms five_point_delete_score
#print axioms five_point_merge_zero_mid
#print axioms five_point_merge_zero_first
#print axioms five_point_merge_zero_last
#print axioms linScore_split_low
#print axioms linScore_split_mid
#print axioms linScore_split_high
#print axioms mergeGain_eq_two
#print axioms two_in_F_row
#print axioms two_in_F_above
#print axioms two_in_L_row
#print axioms two_in_L_below
#print axioms two_in_mixed_row
#print axioms two_in_mixed_ge_three
#print axioms two_in_mixed_between
#print axioms two_in_mixed_five

end Jsp404
