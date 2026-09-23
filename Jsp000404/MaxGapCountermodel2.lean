import Jsp000404.Induction
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle

/-!
# `s = 4` countermodel for `maxGap_boundary_emission`: the square

`MaxGapCountermodel.lean` already records three distinct obstructions to
the naive statement of `maxGap_boundary_emission`:

* the **unconditional `s = 2` refutation** — singleton rows can never gain;
* the **`lam > π / 2` gain-vanishing lemma** — every cyclic gap lies in
  `[0, π]`, so `⌊g / lam⌋₊ ≤ 1` and every `rowGain` is `0` (this is a
  lemma about gains, not by itself a legal geometric countermodel);
* the **conditional `s = 3` countermodel**.

This file adds the fourth, missing, witness class: **`s = 4`, low regime**.
With `c` the vertices of the square `0, e, e + w, w` (where `w` is `e`
rotated by `π/2`; at the standard orientation `o`, `e = basis 0` this is
`[(0,0), (1,0), (1,1), (0,1)]`) and `lam = 5π/12`:

* `⌊π / lam⌋₊ = 2`, `δ = π/lam - 2 = 2/5 < 1/2` — the LOW regime;
* every direction row is `{0, π/4, π/2}` or `{0, π/2, 3π/4}` with cyclic
  gaps `{π/4, π/4, π/2}`;
* every post-deletion gap is `< 2·lam = 5π/6`, so **every `rowGain` is 0**;
* the max-gap hypotheses instantiate with `t = 0`, `a = 3`, `b = 1`,
  `G = π/2`, so all three conclusion disjuncts of
  `maxGap_boundary_emission` fail.

Two facts that matter for the repair (see `notes/MAXGAP_SPEC_AUDIT.md`):

* the square is **flat**: `potential = 4 = sendovCap 2 false`, so it lies
  *at* the cap and does **not** refute the consumer-domain repair
  (`cap < potential` is the actual `CertExists` hypothesis);
* it **does** refute any repair whose only extra hypothesis is `4 ≤ s`.
-/

open scoped EuclideanGeometry RealInnerProductSpace EuclideanSpace

namespace Jsp404

noncomputable section

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- Quarter-turn of `e`: the square's second edge direction. -/
noncomputable def sqW (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) : Plane₂ :=
  o.rotation (↑(Real.pi / 2)) e

/-- The unit square on the frame `(e, sqW o e)`: vertices `0, e, e+w, w`.
At `o` standard and `e = EuclideanSpace.basisFun (Fin 2) ℝ 0` this is
`[(0,0), (1,0), (1,1), (0,1)]`. -/
noncomputable def sq (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) :
    Fin 4 → Plane₂ :=
  ![0, e, e + sqW o e, sqW o e]

/-- The countermodel scale `λ = 5π/12`: `⌊π/λ⌋₊ = 2`, `δ = 2/5 < 1/2`. -/
noncomputable def sqLam : ℝ := 5 * Real.pi / 12

lemma sqLam_pos : 0 < sqLam := by
  unfold sqLam; positivity

lemma sqLam_lt_pi_div_two : sqLam < Real.pi / 2 := by
  unfold sqLam; linarith [Real.pi_pos]

/-- `2·λ = 5π/6`; every gap we meet is strictly below it. -/
lemma two_mul_sqLam : 2 * sqLam = 5 * Real.pi / 6 := by
  unfold sqLam; ring

private lemma pi_quarter_pos : (0 : ℝ) < Real.pi / 4 := by positivity
private lemma pi_half_pos : (0 : ℝ) < Real.pi / 2 := by positivity
private lemma pi_3quarter_pos : (0 : ℝ) < 3 * Real.pi / 4 := by positivity
private lemma q_lt_h : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
private lemma h_lt_3q : Real.pi / 2 < 3 * Real.pi / 4 := by
  linarith [Real.pi_pos]

/-! ### Vector facts -/

lemma norm_sqW : ‖sqW o e‖ = ‖e‖ :=
  (o.rotation _).norm_map e

lemma sqW_ne_zero (he : e ≠ 0) : sqW o e ≠ 0 := by
  intro h
  have hnorm := norm_sqW (o := o) (e := e)
  rw [h, norm_zero] at hnorm
  exact he (norm_eq_zero.mp hnorm.symm)

lemma inner_e_sqW : ⟪e, sqW o e⟫ = 0 :=
  o.inner_rotation_pi_div_two_right e

lemma inner_sqW_e : ⟪sqW o e, e⟫ = 0 := by
  rw [real_inner_comm]; exact inner_e_sqW

lemma inner_sqW_sqW : ⟪sqW o e, sqW o e⟫ = ⟪e, e⟫ := by
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sqW]

lemma e_ne_sqW (he : e ≠ 0) : e ≠ sqW o e := by
  intro h
  have h1 := congrArg (fun x : Plane₂ => ⟪e, x⟫) h
  rw [inner_e_sqW] at h1
  exact (real_inner_self_pos.mpr he).ne' h1

lemma e_add_sqW_ne (he : e ≠ 0) : e + sqW o e ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : Plane₂ => ⟪e, x⟫) h
  rw [inner_add_right, inner_e_sqW, inner_zero_right, add_zero] at h1
  exact (real_inner_self_pos.mpr he).ne' h1

lemma e_sub_sqW_ne (he : e ≠ 0) : e - sqW o e ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : Plane₂ => ⟪e, x⟫) h
  rw [inner_sub_right, inner_e_sqW, inner_zero_right, sub_zero] at h1
  exact (real_inner_self_pos.mpr he).ne' h1

/-- The square's vertices are pairwise distinct. -/
lemma sq_inj (he : e ≠ 0) : Function.Injective (sq o e) := by
  have d01 : (0 : Plane₂) ≠ e := fun h => he h.symm
  have d10 : e ≠ (0 : Plane₂) := he
  have d02 : (0 : Plane₂) ≠ e + sqW o e := fun h => e_add_sqW_ne he h.symm
  have d20 : e + sqW o e ≠ (0 : Plane₂) := e_add_sqW_ne he
  have d03 : (0 : Plane₂) ≠ sqW o e := fun h => sqW_ne_zero he h.symm
  have d30 : sqW o e ≠ (0 : Plane₂) := sqW_ne_zero he
  have d12 : e ≠ e + sqW o e := fun h => sqW_ne_zero he (add_eq_left.mp h.symm)
  have d21 : e + sqW o e ≠ e := fun h => sqW_ne_zero he (add_eq_left.mp h)
  have d13 : e ≠ sqW o e := e_ne_sqW he
  have d31 : sqW o e ≠ e := (e_ne_sqW he).symm
  have d23 : e + sqW o e ≠ sqW o e := fun h => he (add_eq_right.mp h)
  have d32 : sqW o e ≠ e + sqW o e := fun h => he (add_eq_right.mp h.symm)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sq]

/-! ### Oriented-angle table -/

lemma oangle_e_e : o.oangle e e = 0 := o.oangle_self e

lemma oangle_e_sqW (he : e ≠ 0) :
    o.oangle e (sqW o e) = ↑(Real.pi / 2) :=
  o.oangle_rotation_self_right he _

lemma oangle_e_add_sqW (he : e ≠ 0) :
    o.oangle e (e + sqW o e) = ↑(Real.pi / 4) := by
  have h := o.oangle_add_right_smul_rotation_pi_div_two he (1 : ℝ)
  rw [one_smul, Real.arctan_one] at h
  exact h

lemma oangle_e_sub_sqW (he : e ≠ 0) :
    o.oangle e (e - sqW o e) = ↑(-(Real.pi / 4)) := by
  have h := o.oangle_add_right_smul_rotation_pi_div_two he (-1 : ℝ)
  rw [neg_smul, one_smul, Real.arctan_neg, Real.arctan_one] at h
  rw [sub_eq_add_neg]
  exact h

lemma oangle_e_sqW_sub_e (he : e ≠ 0) :
    o.oangle e (sqW o e - e) = ↑(3 * Real.pi / 4) := by
  rw [show sqW o e - e = -(e - sqW o e) from (neg_sub _ _).symm,
    o.oangle_neg_right he (e_sub_sqW_ne he), oangle_e_sub_sqW he,
    ← Real.Angle.coe_add]
  congr 1
  ring

/-! ### `linRep`/`dirRep` computation -/

/-- `dirRep i j` for a pair whose oriented angle is `d`: any `ρ ∈ [0, π)`
with `↑ρ = d + kπ` is the representative. -/
lemma dirRep_sq_of (i j : Fin 4) {v : Plane₂} {d : Real.Angle} {ρ : ℝ}
    (hsub : sq o e j - sq o e i = v)
    (hoa : o.oangle e v = d)
    (hIco : ρ ∈ Set.Ico 0 Real.pi) (k : ℤ)
    (hper : ((ρ : ℝ) : Real.Angle) =
      d + k • ((Real.pi : ℝ) : Real.Angle)) :
    dirRep o e (sq o e) i j = ρ := by
  unfold dirRep
  rw [hsub, hoa]
  exact (eq_linRep_of_int_pi hIco ⟨k, hper⟩).symm

/-- `dirRep i j` for a reversed pair: the `+π` shift is killed by
`linRep`. -/
lemma dirRep_sq_neg (i j : Fin 4) {v : Plane₂} {d : Real.Angle} {ρ : ℝ}
    (he : e ≠ 0) (hv : v ≠ 0)
    (hsub : sq o e j - sq o e i = -v)
    (hoa : o.oangle e v = d)
    (hIco : ρ ∈ Set.Ico 0 Real.pi) (k : ℤ)
    (hper : ((ρ : ℝ) : Real.Angle) =
      d + k • ((Real.pi : ℝ) : Real.Angle)) :
    dirRep o e (sq o e) i j = ρ := by
  unfold dirRep
  rw [hsub, o.oangle_neg_right he hv, linRep_add_pi, hoa]
  exact (eq_linRep_of_int_pi hIco ⟨k, hper⟩).symm

lemma Ico_zero_pi_quarter : (Real.pi / 4 : ℝ) ∈ Set.Ico 0 Real.pi :=
  ⟨by positivity, by linarith [Real.pi_pos]⟩

lemma Ico_zero_pi_half : (Real.pi / 2 : ℝ) ∈ Set.Ico 0 Real.pi :=
  ⟨by positivity, by linarith [Real.pi_pos]⟩

lemma Ico_zero_pi_3quarter : (3 * Real.pi / 4 : ℝ) ∈ Set.Ico 0 Real.pi :=
  ⟨by positivity, by linarith [Real.pi_pos]⟩

lemma Ico_zero_pi_zero : (0 : ℝ) ∈ Set.Ico 0 Real.pi :=
  ⟨le_refl 0, Real.pi_pos⟩

-- Row 0 (vertex 0): directions to `e`, `e+w`, `w` give `0, π/4, π/2`.
lemma dirRep_sq_01 (_he : e ≠ 0) :
    dirRep o e (sq o e) 0 1 = 0 := by
  refine dirRep_sq_of _ _ (v := e) (by simp [sq]) oangle_e_e
    Ico_zero_pi_zero 0 (by simp)

lemma dirRep_sq_02 (he : e ≠ 0) :
    dirRep o e (sq o e) 0 2 = Real.pi / 4 := by
  refine dirRep_sq_of _ _ (v := e + sqW o e) (by simp [sq])
    (oangle_e_add_sqW he) Ico_zero_pi_quarter 0 (by simp)

lemma dirRep_sq_03 (he : e ≠ 0) :
    dirRep o e (sq o e) 0 3 = Real.pi / 2 := by
  refine dirRep_sq_of _ _ (v := sqW o e) (by simp [sq])
    (oangle_e_sqW he) Ico_zero_pi_half 0 (by simp)

-- Row 1 (vertex `e`): directions to `0`, `e+w`, `w` give `0, π/2, 3π/4`.
lemma dirRep_sq_10 (he : e ≠ 0) :
    dirRep o e (sq o e) 1 0 = 0 := by
  refine dirRep_sq_neg _ _ he he (v := e) (by simp [sq]) oangle_e_e
    Ico_zero_pi_zero 0 (by simp)

lemma dirRep_sq_12 (he : e ≠ 0) :
    dirRep o e (sq o e) 1 2 = Real.pi / 2 := by
  refine dirRep_sq_of _ _ (v := sqW o e) (by simp [sq])
    (oangle_e_sqW he) Ico_zero_pi_half 0 (by simp)

lemma dirRep_sq_13 (he : e ≠ 0) :
    dirRep o e (sq o e) 1 3 = 3 * Real.pi / 4 := by
  refine dirRep_sq_of _ _ (v := sqW o e - e) (by simp [sq])
    (oangle_e_sqW_sub_e he) Ico_zero_pi_3quarter 0 (by simp)

-- Row 2 (vertex `e+w`): directions to `0`, `e`, `w` give `π/4, π/2, 0`.
lemma dirRep_sq_20 (he : e ≠ 0) :
    dirRep o e (sq o e) 2 0 = Real.pi / 4 := by
  refine dirRep_sq_neg _ _ he (e_add_sqW_ne he) (v := e + sqW o e)
    (by simp [sq]) (oangle_e_add_sqW he) Ico_zero_pi_quarter 0 (by simp)

lemma dirRep_sq_21 (he : e ≠ 0) :
    dirRep o e (sq o e) 2 1 = Real.pi / 2 := by
  refine dirRep_sq_neg _ _ he (sqW_ne_zero he) (v := sqW o e)
    (by simp [sq]) (oangle_e_sqW he) Ico_zero_pi_half 0 (by simp)

lemma dirRep_sq_23 (he : e ≠ 0) :
    dirRep o e (sq o e) 2 3 = 0 := by
  refine dirRep_sq_neg _ _ he he (v := e) (by simp [sq]) oangle_e_e
    Ico_zero_pi_zero 0 (by simp)

-- Row 3 (vertex `w`): directions to `0`, `e`, `e+w` give `π/2, 3π/4, 0`.
lemma dirRep_sq_30 (he : e ≠ 0) :
    dirRep o e (sq o e) 3 0 = Real.pi / 2 := by
  refine dirRep_sq_neg _ _ he (sqW_ne_zero he) (v := sqW o e)
    (by simp [sq]) (oangle_e_sqW he) Ico_zero_pi_half 0 (by simp)

lemma dirRep_sq_31 (he : e ≠ 0) :
    dirRep o e (sq o e) 3 1 = 3 * Real.pi / 4 := by
  refine dirRep_sq_of _ _ (v := e - sqW o e) (by simp [sq])
    (oangle_e_sub_sqW he) Ico_zero_pi_3quarter 1 ?_
  rw [one_smul, ← Real.Angle.coe_add]
  congr 1
  ring

lemma dirRep_sq_32 (_he : e ≠ 0) :
    dirRep o e (sq o e) 3 2 = 0 := by
  refine dirRep_sq_of _ _ (v := e) (by simp [sq]) oangle_e_e
    Ico_zero_pi_zero 0 (by simp)

/-! ### The direction rows -/

lemma directionRow_sq_0 (he : e ≠ 0) :
    directionRow o e (sq o e) 0 = [0, Real.pi / 4, Real.pi / 2] := by
  unfold directionRow
  rw [show (List.finRange 4).erase (0 : Fin 4) = [1, 2, 3] from by decide]
  simp only [List.map_cons, List.map_nil]
  rw [dirRep_sq_01 he, dirRep_sq_02 he, dirRep_sq_03 he]
  simp only [List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_nil, List.orderedInsert_cons]
  rw [ite_eq_left q_lt_h.le, List.orderedInsert_cons]
  rw [ite_eq_left pi_quarter_pos.le]

lemma directionRow_sq_1 (he : e ≠ 0) :
    directionRow o e (sq o e) 1 = [0, Real.pi / 2, 3 * Real.pi / 4] := by
  unfold directionRow
  rw [show (List.finRange 4).erase (1 : Fin 4) = [0, 2, 3] from by decide]
  simp only [List.map_cons, List.map_nil]
  rw [dirRep_sq_10 he, dirRep_sq_12 he, dirRep_sq_13 he]
  simp only [List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_nil, List.orderedInsert_cons]
  rw [ite_eq_left h_lt_3q.le, List.orderedInsert_cons]
  rw [ite_eq_left pi_half_pos.le]

lemma directionRow_sq_2 (he : e ≠ 0) :
    directionRow o e (sq o e) 2 = [0, Real.pi / 4, Real.pi / 2] := by
  unfold directionRow
  rw [show (List.finRange 4).erase (2 : Fin 4) = [0, 1, 3] from by decide]
  simp only [List.map_cons, List.map_nil]
  rw [dirRep_sq_20 he, dirRep_sq_21 he, dirRep_sq_23 he]
  simp only [List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_nil, List.orderedInsert_cons]
  rw [ite_eq_right (not_le.mpr pi_half_pos), List.orderedInsert_cons]
  rw [ite_eq_right (not_le.mpr pi_quarter_pos), List.orderedInsert_cons]
  rw [ite_eq_left q_lt_h.le]

lemma directionRow_sq_3 (he : e ≠ 0) :
    directionRow o e (sq o e) 3 = [0, Real.pi / 2, 3 * Real.pi / 4] := by
  unfold directionRow
  rw [show (List.finRange 4).erase (3 : Fin 4) = [0, 1, 2] from by decide]
  simp only [List.map_cons, List.map_nil]
  rw [dirRep_sq_30 he, dirRep_sq_31 he, dirRep_sq_32 he]
  simp only [List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_nil, List.orderedInsert_cons]
  rw [ite_eq_right (not_le.mpr pi_3quarter_pos), List.orderedInsert_cons]
  rw [ite_eq_right (not_le.mpr pi_half_pos), List.orderedInsert_cons]
  rw [ite_eq_left h_lt_3q.le]

/-- Every square row is one of the two sorted lists.  Stated as a
disjunction so consumers never need to `fin_cases` into literal
`Fin 4` indices. -/
lemma sq_row_mem (he : e ≠ 0) (i : Fin 4) :
    directionRow o e (sq o e) i = [0, Real.pi / 4, Real.pi / 2] ∨
    directionRow o e (sq o e) i = [0, Real.pi / 2, 3 * Real.pi / 4] := by
  fin_cases i
  · exact Or.inl (directionRow_sq_0 he)
  · exact Or.inr (directionRow_sq_1 he)
  · exact Or.inl (directionRow_sq_2 he)
  · exact Or.inr (directionRow_sq_3 he)

/-! ### Cyclic gaps, scores, gains -/

lemma cyclicDiff_lt {a b : ℝ} (h : a < b) : cyclicDiff a b = b - a := by
  unfold cyclicDiff
  rw [ite_eq_right (ne_of_lt h), ite_eq_left h]

lemma cyclicDiff_gt {a b : ℝ} (h : b < a) :
    cyclicDiff a b = Real.pi + b - a := by
  unfold cyclicDiff
  rw [ite_eq_right (ne_of_gt h), ite_eq_right (not_lt.mpr h.le)]

/-- `cycGaps` of a strictly sorted triple, computed to values. -/
lemma cycGaps_triple {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    cycGaps [a, b, c] = [b - a, c - b, Real.pi - (c - a)] := by
  have hwrap : wrapGap [a, b, c] (List.cons_ne_nil _ _)
      = Real.pi - (c - a) := by
    unfold wrapGap
    rw [ite_eq_right]
    · rw [show [a, b, c].getLast (List.cons_ne_nil _ _) = c from rfl,
        show [a, b, c].head (List.cons_ne_nil _ _) = a from rfl]
      rw [cyclicDiff_gt (lt_trans hab hbc)]
      ring
    · intro hAll
      exact absurd (hAll b (by simp)).symm (ne_of_lt hab)
  rw [cycGaps_eq_map_append_wrap _ (List.cons_ne_nil _ _)]
  simp only [List.dropLast_cons_cons, List.tail_cons, List.zip_cons_cons,
    List.zip_nil_right, List.map_cons, List.map_nil, hwrap]
  rw [cyclicDiff_lt hab, cyclicDiff_lt hbc]
  rfl

/-- Every gap below `2·λ` contributes `0` to the score. -/
lemma gapScore_eq_zero_of_lt {lam g : ℝ} (hlam : 0 < lam)
    (hg : g < 2 * lam) :
    gapScore lam g = 0 := by
  unfold gapScore
  have h2 : g / lam < (2 : ℝ) := by
    rw [div_lt_iff₀ hlam]
    nlinarith [hg, hlam]
  have hf : ⌊g / lam⌋₊ ≤ 1 := by
    rw [← Nat.lt_succ_iff]
    exact (Nat.floor_lt' two_ne_zero).mpr h2
  omega

lemma gapScore_sqLam_quarter : gapScore sqLam (Real.pi / 4) = 0 :=
  gapScore_eq_zero_of_lt sqLam_pos (by
    rw [two_mul_sqLam]; linarith [Real.pi_pos])

lemma gapScore_sqLam_half : gapScore sqLam (Real.pi / 2) = 0 :=
  gapScore_eq_zero_of_lt sqLam_pos (by
    rw [two_mul_sqLam]; linarith [Real.pi_pos])

lemma gapScore_sqLam_3quarter : gapScore sqLam (3 * Real.pi / 4) = 0 :=
  gapScore_eq_zero_of_lt sqLam_pos (by
    rw [two_mul_sqLam]; linarith [Real.pi_pos])

/-- A row all of whose cyclic gaps have vanishing score has `rowScore = 0`. -/
lemma rowScore_eq_zero_of_forall {lam : ℝ} {l : List ℝ}
    (h : ∀ g ∈ cycGaps l, gapScore lam g = 0) :
    rowScore lam l = 0 := by
  unfold rowScore
  have hz : ∀ x ∈ (cycGaps l).map (gapScore lam), x = 0 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact h g hg
  exact List.sum_eq_zero_iff.mpr hz

/-- Every two-element row `[a,b]` (`a ≤ b`) with both cyclic gaps below
`2·λ` scores `0`. -/
lemma rowScore_sq_pair {a b : ℝ} (hab : a ≤ b)
    (ha : b - a < 2 * sqLam) (hb : Real.pi - (b - a) < 2 * sqLam) :
    rowScore sqLam [a, b] = 0 := by
  apply rowScore_eq_zero_of_forall
  rw [cycGaps_pair hab]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact gapScore_eq_zero_of_lt sqLam_pos ha
  · exact gapScore_eq_zero_of_lt sqLam_pos hb

lemma rowScore_sq_0245 :
    rowScore sqLam ([0, Real.pi / 4, Real.pi / 2] : List ℝ) = 0 := by
  apply rowScore_eq_zero_of_forall
  rw [cycGaps_triple pi_quarter_pos q_lt_h]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [sub_zero]; exact gapScore_sqLam_quarter
  · rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring]
    exact gapScore_sqLam_quarter
  · rw [show Real.pi - (Real.pi / 2 - 0) = Real.pi / 2 by ring]
    exact gapScore_sqLam_half

lemma rowScore_sq_0267 :
    rowScore sqLam ([0, Real.pi / 2, 3 * Real.pi / 4] : List ℝ) = 0 := by
  apply rowScore_eq_zero_of_forall
  rw [cycGaps_triple pi_half_pos h_lt_3q]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [sub_zero]; exact gapScore_sqLam_half
  · rw [show 3 * Real.pi / 4 - Real.pi / 2 = Real.pi / 4 by ring]
    exact gapScore_sqLam_quarter
  · rw [show Real.pi - (3 * Real.pi / 4 - 0) = Real.pi / 4 by ring]
    exact gapScore_sqLam_quarter

/-- After any single deletion, row `[0, π/4, π/2]` still scores `0`,
so its `rowGain` is `0` at every index. -/
lemma rowGain_sq_0245 (k : ℕ) :
    rowGain sqLam ([0, Real.pi / 4, Real.pi / 2] : List ℝ) k = 0 := by
  unfold rowGain
  rcases lt_or_ge k 3 with hk | hk
  · interval_cases k
    · rw [List.eraseIdx_cons_zero,
        rowScore_sq_pair q_lt_h.le
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos])
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos]),
        rowScore_sq_0245]
    · rw [show ([0, Real.pi / 4, Real.pi / 2] : List ℝ).eraseIdx 1 =
        [0, Real.pi / 2] from by simp,
        rowScore_sq_pair pi_half_pos.le
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos])
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos]),
        rowScore_sq_0245]
    · rw [show ([0, Real.pi / 4, Real.pi / 2] : List ℝ).eraseIdx 2 =
        [0, Real.pi / 4] from by simp,
        rowScore_sq_pair pi_quarter_pos.le
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos])
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos]),
        rowScore_sq_0245]
  · rw [List.eraseIdx_of_length_le (by simp; omega)]
    exact Nat.sub_self _

/-- After any single deletion, row `[0, π/2, 3π/4]` still scores `0`,
so its `rowGain` is `0` at every index. -/
lemma rowGain_sq_0267 (k : ℕ) :
    rowGain sqLam ([0, Real.pi / 2, 3 * Real.pi / 4] : List ℝ) k = 0 := by
  unfold rowGain
  rcases lt_or_ge k 3 with hk | hk
  · interval_cases k
    · rw [List.eraseIdx_cons_zero,
        rowScore_sq_pair h_lt_3q.le
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos])
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos]),
        rowScore_sq_0267]
    · rw [show ([0, Real.pi / 2, 3 * Real.pi / 4] : List ℝ).eraseIdx 1 =
        [0, 3 * Real.pi / 4] from by simp,
        rowScore_sq_pair pi_3quarter_pos.le
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos])
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos]),
        rowScore_sq_0267]
    · rw [show ([0, Real.pi / 2, 3 * Real.pi / 4] : List ℝ).eraseIdx 2 =
        [0, Real.pi / 2] from by simp,
        rowScore_sq_pair pi_half_pos.le
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos])
          (by rw [two_mul_sqLam]; linarith [Real.pi_pos]),
        rowScore_sq_0267]
  · rw [List.eraseIdx_of_length_le (by simp; omega)]
    exact Nat.sub_self _

/-- **Every `rowGain` vanishes** on the square at `lam = 5π/12`. -/
lemma rowGain_sq_zero (he : e ≠ 0) (i v : Fin 4) :
    rowGain sqLam (directionRow o e (sq o e) i)
      (deleteIndex o e (sq o e) v i) = 0 := by
  rcases sq_row_mem he i with h | h
  · rw [h]; exact rowGain_sq_0245 _
  · rw [h]; exact rowGain_sq_0267 _

/-! ### Legality -/

/-- Nonnegative inner product forces the (unoriented) angle `≤ π/2`. -/
lemma angle_le_pi_div_two_of_inner_nonneg {u v : Plane₂}
    (h : 0 ≤ ⟪u, v⟫) :
    InnerProductGeometry.angle u v ≤ Real.pi / 2 :=
  le_of_not_gt fun hl =>
    not_lt.mpr h (InnerProductGeometry.inner_neg_iff_pi_div_two_lt_angle.mpr hl)

/-- Every angle of the square is `≤ π/2 ≤ π - 5π/12`. -/
lemma sq_legal (he : e ≠ 0) : Section4Legality (sq o e) sqLam := by
  refine ⟨sqLam_pos, sq_inj he, ?_⟩
  intro i j k hij hjk hik
  have hcap : Real.pi / 2 ≤ Real.pi - sqLam := by
    unfold sqLam; linarith [Real.pi_pos]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [sq, EuclideanGeometry.angle]
  all_goals
    refine le_trans (angle_le_pi_div_two_of_inner_nonneg ?_) hcap
    simp only [inner_sub_left, inner_sub_right, inner_add_left,
      inner_add_right, inner_neg_left, inner_neg_right, inner_zero_left,
      inner_zero_right, inner_e_sqW, inner_sqW_e, inner_sqW_sqW,
      sub_zero, zero_sub, neg_zero, add_zero, zero_add, neg_neg,
      sub_eq_add_neg, neg_add]
    linarith [real_inner_self_nonneg (x := e)]

/-! ### The max-gap hypotheses hold -/

/-- The `hgap` hypothesis: `dirRep 0 3 = π/2`, `dirRep 0 1 = 0`, so the
sweep `3→1` inside row 0 is `π/2`. -/
lemma sq_hgap (he : e ≠ 0) :
    cyclicDiff (dirRep o e (sq o e) 0 3) (dirRep o e (sq o e) 0 1)
      = Real.pi / 2 := by
  rw [dirRep_sq_03 he, dirRep_sq_01 he, cyclicDiff_gt pi_half_pos]
  ring

/-- The `hadj` hypothesis: in row 0, every `z ≠ π/2` is at forward sweep
`≥ π/2` from `dirRep 0 3 = π/2`. -/
lemma sq_hadj (he : e ≠ 0) :
    ∀ z ∈ directionRow o e (sq o e) 0,
      z ≠ dirRep o e (sq o e) 0 3 →
      Real.pi / 2 ≤ cyclicDiff (dirRep o e (sq o e) 0 3) z := by
  intro z hz hne
  rw [directionRow_sq_0 he] at hz
  rw [dirRep_sq_03 he] at hne ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · rw [cyclicDiff_gt pi_half_pos]; linarith [Real.pi_pos]
  · rw [cyclicDiff_gt q_lt_h]; linarith [Real.pi_pos]
  · exact absurd rfl hne

/-- Successor gaps of the `[0, π/4, π/2]` row are `≤ π/2`. -/
lemma sq_succ_0245 {x : ℝ} (hx : x ∈ ([0, Real.pi / 4, Real.pi / 2] : List ℝ)) :
    ∃ z ∈ ([0, Real.pi / 4, Real.pi / 2] : List ℝ),
      z ≠ x ∧ cyclicDiff x z ≤ Real.pi / 2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨Real.pi / 4, by simp, (ne_of_lt pi_quarter_pos).symm,
      by rw [cyclicDiff_lt pi_quarter_pos]; linarith [Real.pi_pos]⟩
  · exact ⟨Real.pi / 2, by simp, (ne_of_lt q_lt_h).symm,
      by rw [cyclicDiff_lt q_lt_h]; linarith [Real.pi_pos]⟩
  · exact ⟨0, by simp, ne_of_lt pi_half_pos,
      by rw [cyclicDiff_gt pi_half_pos]; linarith [Real.pi_pos]⟩

/-- Successor gaps of the `[0, π/2, 3π/4]` row are `≤ π/2`. -/
lemma sq_succ_0267 {x : ℝ}
    (hx : x ∈ ([0, Real.pi / 2, 3 * Real.pi / 4] : List ℝ)) :
    ∃ z ∈ ([0, Real.pi / 2, 3 * Real.pi / 4] : List ℝ),
      z ≠ x ∧ cyclicDiff x z ≤ Real.pi / 2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨Real.pi / 2, by simp, (ne_of_lt pi_half_pos).symm,
      by rw [cyclicDiff_lt pi_half_pos, sub_zero]⟩
  · exact ⟨3 * Real.pi / 4, by simp, (ne_of_lt h_lt_3q).symm,
      by rw [cyclicDiff_lt h_lt_3q]; linarith [Real.pi_pos]⟩
  · exact ⟨0, by simp, ne_of_lt pi_3quarter_pos,
      by rw [cyclicDiff_gt pi_3quarter_pos]; linarith [Real.pi_pos]⟩

/-- The `hglob` hypothesis: in every row, the minimizing forward sweep is
`≤ π/2 = G`. -/
lemma sq_hglob (he : e ≠ 0) :
    ∀ i : Fin 4, ∀ x y : ℝ,
      x ∈ directionRow o e (sq o e) i →
      y ∈ directionRow o e (sq o e) i →
      (∀ z ∈ directionRow o e (sq o e) i, z ≠ x →
        cyclicDiff x y ≤ cyclicDiff x z) →
      cyclicDiff x y ≤ Real.pi / 2 := by
  intro i x y hx hy hmin
  rcases sq_row_mem he i with h | h
  · rw [h] at hx hmin
    obtain ⟨z, hz, hzx, hcz⟩ := sq_succ_0245 hx
    exact le_trans (hmin z hz hzx) hcz
  · rw [h] at hx hmin
    obtain ⟨z, hz, hzx, hcz⟩ := sq_succ_0267 hx
    exact le_trans (hmin z hz hzx) hcz

/-! ### The countermodel -/

/-- The LOW-regime arithmetic: `π/λ = 12/5`, so `⌊π/λ⌋₊ = 2` and
`δ = 2/5 < 1/2`. -/
lemma sqLam_ratio : Real.pi / sqLam = 12 / 5 := by
  unfold sqLam
  field_simp

lemma sq_floor_pi_div : ⌊Real.pi / sqLam⌋₊ = 2 := by
  rw [sqLam_ratio]
  exact Nat.floor_eq_on_Ico 2 _ ⟨by norm_num, by norm_num⟩

lemma sq_delta_lt_half : Real.pi / sqLam - 2 < 1 / 2 := by
  rw [sqLam_ratio]
  norm_num

/-- The conclusion of `maxGap_boundary_emission` fails on the square:
every `rowGain` is `0`, so no `1 ≤ rowGain` disjunct can hold. -/
lemma sq_conclusion_fails (he : e ≠ 0) (t a b : Fin 4) :
    ¬ ((1 ≤ rowGain sqLam (directionRow o e (sq o e) a)
          (deleteIndex o e (sq o e) t a)) ∨
        (1 ≤ rowGain sqLam (directionRow o e (sq o e) b)
          (deleteIndex o e (sq o e) t b)) ∨
        (∃ i v : Fin 4, i ≠ v ∧
          1 ≤ rowGain sqLam (directionRow o e (sq o e) i)
            (deleteIndex o e (sq o e) v i) ∧
          exponentAt sqLam (directionRows o e (sq o e)) v ≤
            exponentAt sqLam (directionRows o e (sq o e)) i)) := by
  rintro (h | h | ⟨i, v, -, hgain, -⟩)
  · rw [rowGain_sq_zero he a t] at h; omega
  · rw [rowGain_sq_zero he b t] at h; omega
  · rw [rowGain_sq_zero he i v] at hgain; omega

/-- **`s = 4` countermodel**: all hypotheses of
`maxGap_boundary_emission` hold on the square with `lam = 5π/12`,
`t = 0`, `a = 3`, `b = 1`, `G = π/2`, but its conclusion fails. -/
theorem maxGap_boundary_emission_countermodel_s4 (he : e ≠ 0) :
    ∃ (lam : ℝ) (_ : Section4Legality (sq o e) lam) (t a b : Fin 4)
      (G : ℝ),
      (0 < lam) ∧ (lam < Real.pi / 2) ∧ (⌊Real.pi / lam⌋₊ = 2) ∧
      (Real.pi / lam - 2 < 1 / 2) ∧
      (t ≠ a) ∧ (t ≠ b) ∧
      (cyclicDiff (dirRep o e (sq o e) t a)
        (dirRep o e (sq o e) t b) = G) ∧
      (∀ z ∈ directionRow o e (sq o e) t, z ≠ dirRep o e (sq o e) t a →
        G ≤ cyclicDiff (dirRep o e (sq o e) t a) z) ∧
      (∀ i : Fin 4, ∀ x y : ℝ,
        x ∈ directionRow o e (sq o e) i →
        y ∈ directionRow o e (sq o e) i →
        (∀ z ∈ directionRow o e (sq o e) i, z ≠ x →
          cyclicDiff x y ≤ cyclicDiff x z) →
        cyclicDiff x y ≤ G) ∧
      ¬ ((1 ≤ rowGain lam (directionRow o e (sq o e) a)
            (deleteIndex o e (sq o e) t a)) ∨
          (1 ≤ rowGain lam (directionRow o e (sq o e) b)
            (deleteIndex o e (sq o e) t b)) ∨
          (∃ i v : Fin 4, i ≠ v ∧
            1 ≤ rowGain lam (directionRow o e (sq o e) i)
              (deleteIndex o e (sq o e) v i) ∧
            exponentAt lam (directionRows o e (sq o e)) v ≤
              exponentAt lam (directionRows o e (sq o e)) i)) := by
  exact ⟨sqLam, sq_legal he, 0, 3, 1, Real.pi / 2,
    sqLam_pos, sqLam_lt_pi_div_two, sq_floor_pi_div, sq_delta_lt_half,
    by decide, by decide, sq_hgap he, sq_hadj he, sq_hglob he,
    sq_conclusion_fails he 0 3 1⟩

/-- The naive "`4 ≤ s`" repair is still false on the square.  (The
*consumer* domain `cap < potential` is not refuted by this witness —
see `sq_not_over_cap`.) -/
theorem maxGap_boundary_emission_false_s4 :
    ¬ (∀ (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (_ : e ≠ 0)
        (c : Fin 4 → Plane₂) (lam : ℝ) (_ : Section4Legality c lam)
        (_ : 0 < lam) (_ : lam < Real.pi / 2)
        (t a b : Fin 4) (G : ℝ),
        (t ≠ a) → (t ≠ b) →
        (cyclicDiff (dirRep o e c t a)
            (dirRep o e c t b) = G) →
        (∀ z ∈ directionRow o e c t, z ≠ dirRep o e c t a →
          G ≤ cyclicDiff (dirRep o e c t a) z) →
        (∀ i : Fin 4, ∀ x y : ℝ,
          x ∈ directionRow o e c i →
          y ∈ directionRow o e c i →
          (∀ z ∈ directionRow o e c i, z ≠ x →
            cyclicDiff x y ≤ cyclicDiff x z) →
          cyclicDiff x y ≤ G) →
        (1 ≤ rowGain lam (directionRow o e c a)
          (deleteIndex o e c t a)) ∨
        (1 ≤ rowGain lam (directionRow o e c b)
          (deleteIndex o e c t b)) ∨
        (∃ i v : Fin 4, i ≠ v ∧
          1 ≤ rowGain lam (directionRow o e c i)
            (deleteIndex o e c v i) ∧
          exponentAt lam (directionRows o e c) v ≤
            exponentAt lam (directionRows o e c) i)) := by
  intro h
  let o₀ : Orientation ℝ Plane₂ (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let e₀ : Plane₂ := EuclideanSpace.basisFun (Fin 2) ℝ (0 : Fin 2)
  have he₀ : e₀ ≠ 0 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero _
  obtain ⟨lam, hleg, t, a, b, G, hlam, hlamlt, _, _, hta, htb, hgap,
    hadj, hglob, hfail⟩ :=
    maxGap_boundary_emission_countermodel_s4 (o := o₀) (e := e₀) he₀
  exact hfail (h o₀ e₀ he₀ (sq o₀ e₀) lam hleg hlam hlamlt t a b G hta
    htb hgap hadj hglob)

/-! ### The square sits *at* the capacity bound -/

/-- Every exponent vanishes: the square is `Flat`. -/
lemma sq_flat (he : e ≠ 0) :
    Flat sqLam (directionRows o e (sq o e)) := by
  intro i
  unfold exponentAt directionRows
  rcases sq_row_mem he i with h | h
  · rw [h]; exact rowScore_sq_0245
  · rw [h]; exact rowScore_sq_0267

/-- The square's potential equals `s = 4` — exactly `sendovCap 2 false`.
Hence `cap < potential` fails: the square is **not** a countermodel to
the consumer-domain (`CertExists`) repair; it only falsifies the bare
`4 ≤ s` repair. -/
lemma sq_potential_eq (he : e ≠ 0) :
    potential sqLam (directionRows o e (sq o e)) = 4 := by
  rw [flat_potential sqLam _ (sq_flat he)]

lemma sq_not_over_cap (he : e ≠ 0) :
    ¬ (sendovCap 2 false <
        potential sqLam (directionRows o e (sq o e))) := by
  rw [sq_potential_eq he]
  decide

end

end Jsp404

#print axioms Jsp404.maxGap_boundary_emission_countermodel_s4
#print axioms Jsp404.maxGap_boundary_emission_false_s4
#print axioms Jsp404.rowGain_sq_zero
#print axioms Jsp404.sq_legal
#print axioms Jsp404.sq_potential_eq
#print axioms Jsp404.sq_not_over_cap
