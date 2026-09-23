import Jsp000404.GeometricDeletion

/-!
# Countermodels to `maxGap_boundary_emission` as stated

`maxGap_boundary_emission` (`GeometricDeletion.lean:612`) is false as
stated: it quantifies over arbitrary `s` and arbitrary `lam > 0`, but

* `s = 2`: every `directionRow` is a singleton, so every `rowGain`
  vanishes (`rowScore [] - rowScore [d] = 0` in `ℕ`), while the
  hypotheses `hgap`/`hadj`/`hglob` are trivially satisfiable with
  `a = b`, `G = 0`.

* `s = 3`, `lam > π/2` (equivalently `⌊π/lam⌋₊ ≤ 1`): every `gapScore`
  vanishes on `[0, π]`, so every `rowScore` and every `rowGain` is `0`.
  The hypotheses are satisfiable on any legal configuration (realize the
  global maximum gap at the vertex minimizing the smaller projective
  separation), e.g. an equilateral triangle at `lam = 2π/3`.

The live hypothesis needed by the intended application (`CertExists`,
`4 ≤ t`) is `4 ≤ s` — which forces `lam ≤ π/2` since any four planar
points contain a triple with angle `≥ π/2`.  The `s = 2` countermodel
below is fully checked.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- In a two-center configuration every direction row is a singleton. -/
lemma directionRow_length_two {c : Fin 2 → Plane₂} (i : Fin 2) :
    ∃ d : ℝ, directionRow o e c i = [d] := by
  have hlen := directionRow_length o e c i
  rw [show (2 : ℕ) - 1 = 1 from rfl] at hlen
  exact List.length_eq_one_iff.mp hlen

/-- A singleton row has `rowGain = 0` at every index: erasing gives the
empty list (score `0`) or the same list — saturated `ℕ` subtraction
collapses both cases. -/
lemma rowGain_singleton (lam d : ℝ) (k : ℕ) : rowGain lam [d] k = 0 := by
  unfold rowGain
  by_cases hk : k = 0
  · subst hk
    rw [show ([d] : List ℝ).eraseIdx 0 = [] from rfl]
    rw [show rowScore lam ([] : List ℝ) = 0 from rfl]
    exact Nat.zero_sub _
  · rw [List.eraseIdx_of_length_le (by simp; omega)]
    exact Nat.sub_self _

/-- Two unequal indices in `Fin 2` share the same complement. -/
lemma Fin2.eq_of_ne {i j k : Fin 2} (hji : j ≠ i) (hki : k ≠ i) :
    j = k := by
  have hji' : j.val ≠ i.val := fun h => hji (Fin.ext h)
  have hki' : k.val ≠ i.val := fun h => hki (Fin.ext h)
  have hi2 := i.isLt; have hj2 := j.isLt; have hk2 := k.isLt
  have hjk : j.val = k.val := by omega
  exact Fin.ext hjk

/-- **`s = 2` countermodel.**  With two distinct centers the hypotheses
of `maxGap_boundary_emission` are satisfiable (`a = b`, `G = 0`), but all
three disjuncts fail since every `rowGain` is `0`. -/
theorem maxGap_boundary_emission_countermodel_s2
    {c : Fin 2 → Plane₂} (hinj : Function.Injective c) (_he : e ≠ 0) :
    ∃ (lam : ℝ) (_ : Section4Legality c lam) (t a b : Fin 2) (G : ℝ),
      (t ≠ a) ∧ (t ≠ b) ∧
      (cyclicDiff (dirRep o e c t a) (dirRep o e c t b) = G) ∧
      (∀ z ∈ directionRow o e c t, z ≠ dirRep o e c t a →
        G ≤ cyclicDiff (dirRep o e c t a) z) ∧
      (∀ i : Fin 2, ∀ x y : ℝ,
        x ∈ directionRow o e c i → y ∈ directionRow o e c i →
        (∀ z ∈ directionRow o e c i, z ≠ x →
          cyclicDiff x y ≤ cyclicDiff x z) →
        cyclicDiff x y ≤ G) ∧
      ¬ ((1 ≤ rowGain lam (directionRow o e c a) (deleteIndex o e c t a)) ∨
        (1 ≤ rowGain lam (directionRow o e c b) (deleteIndex o e c t b)) ∨
        (∃ i v : Fin 2, i ≠ v ∧
          1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) ∧
          exponentAt lam (directionRows o e c) v ≤
            exponentAt lam (directionRows o e c) i)) := by
  classical
  refine ⟨1, ?_, 0, 1, 1, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Section4Legality`: `triAngle` is vacuous on `Fin 2`.
    refine ⟨one_pos, hinj, ?_⟩
    intro i j k hij hjk hik
    exfalso
    apply hik
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have hi2 := i.isLt; have hj2 := j.isLt; have hk2 := k.isLt
    have : i.val = k.val := by omega
    exact Fin.ext this
  · decide
  · decide
  · -- `cyclicDiff x x = 0 = G`.
    simp [cyclicDiff]
  · -- `hadj`: `row t` is the singleton `[dirRep t 1]`, so `z ≠ dirRep t a`
    -- is impossible.
    intro z hz hzne
    obtain ⟨j, hjt, rfl⟩ := (mem_directionRow o e c).mp hz
    exfalso
    apply hzne
    congr 1
    exact Fin2.eq_of_ne hjt (by decide : (1 : Fin 2) ≠ 0)
  · -- `hglob`: any two elements of a singleton row coincide.
    intro i x y hx hy _
    obtain ⟨jx, hjx, rfl⟩ := (mem_directionRow o e c).mp hx
    obtain ⟨jy, hjy, rfl⟩ := (mem_directionRow o e c).mp hy
    rw [Fin2.eq_of_ne hjx hjy]
    simp [cyclicDiff]
  · -- the conclusion fails: every `rowGain` is `0`.
    rintro (h1 | h2 | ⟨i, v, hiv, hg, _⟩)
    · obtain ⟨d, hd⟩ := directionRow_length_two o e (1 : Fin 2)
      rw [hd, rowGain_singleton] at h1
      omega
    · obtain ⟨d, hd⟩ := directionRow_length_two o e (1 : Fin 2)
      rw [hd, rowGain_singleton] at h2
      omega
    · obtain ⟨d, hd⟩ := directionRow_length_two o e i
      rw [hd, rowGain_singleton] at hg
      omega

/-- **Unconditional refutation.** `maxGap_boundary_emission` is false
already at `s = 2`, on the standard orientation, standard axis `e`, and
the two-point configuration `c = ![0, e]`. -/
theorem maxGap_boundary_emission_false_s2 :
    ¬ (∀ (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (_ : e ≠ 0)
        (c : Fin 2 → Plane₂) (lam : ℝ) (_ : Section4Legality c lam)
        (t a b : Fin 2) (G : ℝ),
        t ≠ a → t ≠ b →
        cyclicDiff (dirRep o e c t a) (dirRep o e c t b) = G →
        (∀ z ∈ directionRow o e c t, z ≠ dirRep o e c t a →
          G ≤ cyclicDiff (dirRep o e c t a) z) →
        (∀ i : Fin 2, ∀ x y : ℝ,
          x ∈ directionRow o e c i → y ∈ directionRow o e c i →
          (∀ z ∈ directionRow o e c i, z ≠ x →
            cyclicDiff x y ≤ cyclicDiff x z) →
          cyclicDiff x y ≤ G) →
        (1 ≤ rowGain lam (directionRow o e c a) (deleteIndex o e c t a)) ∨
        (1 ≤ rowGain lam (directionRow o e c b) (deleteIndex o e c t b)) ∨
        (∃ i v : Fin 2, i ≠ v ∧
          1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) ∧
          exponentAt lam (directionRows o e c) v ≤
            exponentAt lam (directionRows o e c) i)) := by
  intro h
  let o₀ : Orientation ℝ Plane₂ (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let e₀ : Plane₂ := EuclideanSpace.basisFun (Fin 2) ℝ (0 : Fin 2)
  have he₀ : e₀ ≠ 0 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero _
  have hinj : Function.Injective (fun i : Fin 2 => (i : ℝ) • e₀) := by
    intro i j hij
    have h2 : ((i : ℝ) - (j : ℝ)) • e₀ = 0 := by
      have h3 : (i : ℝ) • e₀ - (j : ℝ) • e₀ = 0 := sub_eq_zero.mpr hij
      rwa [← sub_smul] at h3
    rcases smul_eq_zero.mp h2 with h0 | h0
    · have hval : i.val = j.val := by
        have : (i : ℝ) = (j : ℝ) := sub_eq_zero.mp h0
        exact_mod_cast this
      exact Fin.ext hval
    · exact absurd h0 he₀
  obtain ⟨lam, hlegal, t, a, b, G, hta, htb, hgap, hadj, hglob, hcon⟩ :=
    maxGap_boundary_emission_countermodel_s2 o₀ e₀
      (c := fun i : Fin 2 => (i : ℝ) • e₀) hinj he₀
  exact hcon (h o₀ e₀ he₀ _ lam hlegal t a b G hta htb hgap hadj hglob)

/-- `cyclicDiff` never exceeds `π` for arguments in `[0, π)`. -/
lemma cyclicDiff_le_pi {a b : ℝ} (ha : 0 ≤ a) (hb : b < Real.pi) :
    cyclicDiff a b ≤ Real.pi := by
  unfold cyclicDiff; split_ifs with h1 h2 <;> linarith [Real.pi_pos]

/-- Under `lam > π/2` every gap `≤ π` scores `0`: `⌊g/lam⌋₊ ≤ 1`. -/
lemma gapScore_eq_zero_of_le_pi {lam g : ℝ} (hlam : Real.pi / 2 < lam)
    (hg : g ≤ Real.pi) : gapScore lam g = 0 := by
  have hlam' : 0 < lam := by linarith [Real.pi_pos]
  have hglt : g / lam < 2 := by
    rw [div_lt_iff₀ hlam']
    linarith
  unfold gapScore
  rw [Nat.sub_eq_zero_iff_le]
  exact Nat.le_of_lt_succ ((Nat.floor_lt' two_ne_zero).mpr hglt)

/-- Every cyclic gap of a list inside `[0, π)` is at most `π`. -/
lemma cycGaps_le_pi {l : List ℝ}
    (hall : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) :
    ∀ g ∈ cycGaps l, g ≤ Real.pi := by
  intro g hg
  unfold cycGaps at hg
  rw [List.mem_append] at hg
  rcases hg with hg | hg
  · rw [List.mem_map] at hg
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hg
    obtain ⟨hx1, hy2⟩ := List.of_mem_zip hxy
    exact cyclicDiff_le_pi
      (hall _ (List.mem_of_mem_dropLast hx1)).1
      (hall _ (List.tail_subset _ hy2)).2
  · split at hg
    · simp at hg
    · simp only [List.mem_singleton] at hg
      subst hg
      unfold wrapGap
      split_ifs with hall_eq
      · exact le_rfl
      · rename_i hne
        exact cyclicDiff_le_pi
          (hall _ (List.getLast_mem hne)).1
          (hall _ (List.head_mem hne)).2

/-- If `lam > π/2` (i.e. `⌊π/lam⌋₊ ≤ 1`), every row score vanishes. -/
lemma rowScore_eq_zero_of_half_pi_lt {lam : ℝ} (hlam : Real.pi / 2 < lam)
    {l : List ℝ} (hall : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) :
    rowScore lam l = 0 := by
  unfold rowScore
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact gapScore_eq_zero_of_le_pi hlam (cycGaps_le_pi hall g hg)

/-- If `lam > π/2`, `rowGain` vanishes at every index of every `[0,π)`
list — so no disjunct of `maxGap_boundary_emission` can hold. -/
lemma rowGain_eq_zero_of_half_pi_lt {lam : ℝ} (hlam : Real.pi / 2 < lam)
    {l : List ℝ} (hall : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) (k : ℕ) :
    rowGain lam l k = 0 := by
  unfold rowGain
  have h0 : rowScore lam l = 0 :=
    rowScore_eq_zero_of_half_pi_lt hlam hall
  have hsub : ∀ x ∈ l.eraseIdx k, x ∈ Set.Ico 0 Real.pi := by
    intro x hx
    rw [eraseIdx_eq_take_drop] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hall x (List.take_subset _ _ hx)
    · exact hall x (List.drop_subset _ _ hx)
  rw [rowScore_eq_zero_of_half_pi_lt hlam hsub, h0]

/-- The two companions of `i` in `Fin 3`, so that `{i, j₁ i, j₂ i}` is a
partition of `Fin 3`. -/
def others3 : Fin 3 → Fin 3 × Fin 3 :=
  ![((1 : Fin 3), (2 : Fin 3)), ((0 : Fin 3), (2 : Fin 3)),
    ((0 : Fin 3), (1 : Fin 3))]

lemma others3_fst_ne (i : Fin 3) : (others3 i).1 ≠ i := by
  fin_cases i <;> decide

lemma others3_snd_ne (i : Fin 3) : (others3 i).2 ≠ i := by
  fin_cases i <;> decide

lemma others3_mem {i j : Fin 3} (h : j ≠ i) :
    j = (others3 i).1 ∨ j = (others3 i).2 := by
  fin_cases i <;> fin_cases j <;> simp_all [others3]

/-- The larger of the two cyclic gaps inside row `i` (`s = 3`). -/
noncomputable def rowMaxGap3 (c : Fin 3 → Plane₂) (i : Fin 3) : ℝ :=
  max (cyclicDiff (dirRep o e c i (others3 i).1)
        (dirRep o e c i (others3 i).2))
    (cyclicDiff (dirRep o e c i (others3 i).2)
      (dirRep o e c i (others3 i).1))

lemma cyclicDiff_le_rowMaxGap3 {c : Fin 3 → Plane₂} {i j : Fin 3}
    (hij : j ≠ i) (x : Fin 3) (hxi : x ≠ i) :
    cyclicDiff (dirRep o e c i x) (dirRep o e c i j) ≤
      rowMaxGap3 o e c i := by
  have hnn : 0 ≤ cyclicDiff (dirRep o e c i (others3 i).1)
      (dirRep o e c i (others3 i).2) :=
    cyclicDiff_nonneg (linRep_mem_Ico _).2 (linRep_mem_Ico _).1
  rcases others3_mem hij with rfl | rfl <;>
    rcases others3_mem hxi with rfl | rfl
  · rw [show cyclicDiff (dirRep o e c i (others3 i).1)
        (dirRep o e c i (others3 i).1) = 0 from by simp [cyclicDiff]]
    exact le_trans hnn (le_max_left _ _)
  · exact le_max_right _ _
  · exact le_max_left _ _
  · rw [show cyclicDiff (dirRep o e c i (others3 i).2)
        (dirRep o e c i (others3 i).2) = 0 from by simp [cyclicDiff]]
    exact le_trans hnn (le_max_left _ _)

/-- **`s = 3` countermodel (conditional on legality).**  For `lam > π/2`
— the regime `⌊π/lam⌋₊ = 1`, realizable legally by an equilateral
triangle at `lam = 2π/3` — the hypotheses of `maxGap_boundary_emission`
are instantiable on *every* legal configuration, yet every `rowGain`
vanishes so the conclusion fails. -/
theorem maxGap_boundary_emission_countermodel_s3
    {c : Fin 3 → Plane₂} {lam : ℝ} (hlam : Real.pi / 2 < lam)
    (_hlegal : Section4Legality c lam) (_he : e ≠ 0) :
    ∃ (t a b : Fin 3) (G : ℝ),
      (t ≠ a) ∧ (t ≠ b) ∧
      (cyclicDiff (dirRep o e c t a) (dirRep o e c t b) = G) ∧
      (∀ z ∈ directionRow o e c t, z ≠ dirRep o e c t a →
        G ≤ cyclicDiff (dirRep o e c t a) z) ∧
      (∀ i : Fin 3, ∀ x y : ℝ,
        x ∈ directionRow o e c i → y ∈ directionRow o e c i →
        (∀ z ∈ directionRow o e c i, z ≠ x →
          cyclicDiff x y ≤ cyclicDiff x z) →
        cyclicDiff x y ≤ G) ∧
      ¬ ((1 ≤ rowGain lam (directionRow o e c a) (deleteIndex o e c t a)) ∨
        (1 ≤ rowGain lam (directionRow o e c b) (deleteIndex o e c t b)) ∨
        (∃ i v : Fin 3, i ≠ v ∧
          1 ≤ rowGain lam (directionRow o e c i) (deleteIndex o e c v i) ∧
          exponentAt lam (directionRows o e c) v ≤
            exponentAt lam (directionRows o e c) i)) := by
  classical
  -- `t` maximizes the largest cyclic gap of its row.
  obtain ⟨t, -, ht⟩ :=
    Finset.exists_max_image Finset.univ (rowMaxGap3 o e c)
      Finset.univ_nonempty
  -- Order `a, b` so that `dirRep t a → dirRep t b` is the larger gap.
  set d1 := dirRep o e c t (others3 t).1 with hd1
  set d2 := dirRep o e c t (others3 t).2 with hd2
  by_cases hle : cyclicDiff d1 d2 ≤ cyclicDiff d2 d1
  · -- swap: `a := j₂`, `b := j₁`, `G = cyclicDiff d2 d1 = rowMaxGap3 t`
    refine ⟨t, (others3 t).2, (others3 t).1,
      cyclicDiff d2 d1, (others3_snd_ne t).symm, (others3_fst_ne t).symm,
      rfl,
      ?_, ?_, ?_⟩
    · intro z hz hzne
      obtain ⟨j, hjt, rfl⟩ := (mem_directionRow o e c).mp hz
      rcases others3_mem hjt with rfl | rfl
      · exact le_rfl
      · exfalso; exact hzne rfl
    · intro i x y hx hy _
      obtain ⟨jx, hjx, rfl⟩ := (mem_directionRow o e c).mp hx
      obtain ⟨jy, hjy, rfl⟩ := (mem_directionRow o e c).mp hy
      calc cyclicDiff (dirRep o e c i jx) (dirRep o e c i jy)
          ≤ rowMaxGap3 o e c i := cyclicDiff_le_rowMaxGap3 o e hjy jx hjx
        _ ≤ rowMaxGap3 o e c t := ht i (Finset.mem_univ i)
        _ = cyclicDiff d2 d1 := by
          unfold rowMaxGap3
          exact max_eq_right hle
    · rintro (h1 | h2 | ⟨i, v, hiv, hg, _⟩) <;>
        · first
          | rw [rowGain_eq_zero_of_half_pi_lt hlam
              (fun x hx => directionRow_mem_Ico o e c hx)] at h1
          | rw [rowGain_eq_zero_of_half_pi_lt hlam
              (fun x hx => directionRow_mem_Ico o e c hx)] at h2
          | rw [rowGain_eq_zero_of_half_pi_lt hlam
              (fun x hx => directionRow_mem_Ico o e c hx)] at hg
          · omega
  · -- keep: `a := j₁`, `b := j₂`, `G = cyclicDiff d1 d2 = rowMaxGap3 t`
    replace hle := not_le.mp hle
    refine ⟨t, (others3 t).1, (others3 t).2,
      cyclicDiff d1 d2, (others3_fst_ne t).symm, (others3_snd_ne t).symm,
      rfl,
      ?_, ?_, ?_⟩
    · intro z hz hzne
      obtain ⟨j, hjt, rfl⟩ := (mem_directionRow o e c).mp hz
      rcases others3_mem hjt with rfl | rfl
      · exfalso; exact hzne rfl
      · exact le_rfl
    · intro i x y hx hy _
      obtain ⟨jx, hjx, rfl⟩ := (mem_directionRow o e c).mp hx
      obtain ⟨jy, hjy, rfl⟩ := (mem_directionRow o e c).mp hy
      calc cyclicDiff (dirRep o e c i jx) (dirRep o e c i jy)
          ≤ rowMaxGap3 o e c i := cyclicDiff_le_rowMaxGap3 o e hjy jx hjx
        _ ≤ rowMaxGap3 o e c t := ht i (Finset.mem_univ i)
        _ = cyclicDiff d1 d2 := by
          unfold rowMaxGap3
          exact max_eq_left (le_of_lt hle)
    · rintro (h1 | h2 | ⟨i, v, hiv, hg, _⟩) <;>
        · first
          | rw [rowGain_eq_zero_of_half_pi_lt hlam
              (fun x hx => directionRow_mem_Ico o e c hx)] at h1
          | rw [rowGain_eq_zero_of_half_pi_lt hlam
              (fun x hx => directionRow_mem_Ico o e c hx)] at h2
          | rw [rowGain_eq_zero_of_half_pi_lt hlam
              (fun x hx => directionRow_mem_Ico o e c hx)] at hg
          · omega

end Jsp404
