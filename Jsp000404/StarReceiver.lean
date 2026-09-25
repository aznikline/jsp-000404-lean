import Jsp000404.ProjectionDescent

/-!
# Full-in star receivers: exact defect classification

Setting: saturated anchored chart, `β = π − nλ`, `n ≥ 3`, anchor rays
`θ_i ∈ [0, β]`.  A row `h` is a *full-in star receiver* if every other
non-anchor vertex `j` has a short chord into `h`
(`ShortWitness j h`: `dirRep j h − θ_j < λ` or `θ_j + π − dirRep j h < λ`).

Each such chord sits, in row `h`, in one of two disjoint windows
(`star_chord_window`):

* F (from a short-first source, `θ_h < θ_j`): `[θ_h + λ, β + λ)`;
* L (from a short-last source, `θ_j < θ_h`): `(π − λ, π − λ + θ_h]`.

On the actual row list (`linearGapScore` over the sorted chords, anchored
at `θ_h`, `θ_h + π`), every gap inside a window has score `0`, and
(`star_linear_score_*`):

* all chords in F: the only positive score is the last gap,
  `⌊·/λ⌋₊ = n − 1`, so score `n − 2`;
* all chords in L: the only positive score is the first gap, score
  `n − 2`;
* both windows used: the gap between the last F chord and the first L
  chord is a genuine primitive gap with floor `n − 2`, first and last
  gaps have floor `1`, all other floors `0`; score `n − 3`.

Hence (`star_receiver_defect_*`) `c_h = 2` for one-sided stars and
`c_h = 3` for mixed stars.  No assumption is made that residual
configurations are stars.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- `gapScore` vanishes below `2λ` (no sign hypothesis). -/
theorem gapScore_zero_of_lt_two {lam x : ℝ} (hlam : 0 < lam)
    (hx : x < 2 * lam) : gapScore lam x = 0 := by
  unfold gapScore
  have h : ⌊x / lam⌋₊ < 2 := by
    rw [Nat.floor_lt' (by norm_num)]
    rw [div_lt_iff₀ hlam]; push_cast; linarith
  omega

/-- `gapScore` on `[(k+1)λ, (k+2)λ)` equals `k`. -/
theorem gapScore_eq_of_mem {lam x : ℝ} (hlam : 0 < lam) (k : ℕ)
    (h1 : ((k : ℝ) + 1) * lam ≤ x) (h2 : x < ((k : ℝ) + 2) * lam) :
    gapScore lam x = k := by
  unfold gapScore
  have hx : 0 ≤ x / lam := div_nonneg
    (le_trans (mul_nonneg (by positivity) hlam.le) h1) hlam.le
  have hf : ⌊x / lam⌋₊ = k + 1 := by
    rw [Nat.floor_eq_iff hx]
    constructor
    · rw [le_div_iff₀ hlam]; push_cast; linarith
    · rw [div_lt_iff₀ hlam]; push_cast; linarith
  omega

section Windows

variable {n : ℕ} {lam θ : ℝ}

/-- F window of a star receiver anchored at `θ`. -/
def StarF (n : ℕ) (lam θ x : ℝ) : Prop :=
  θ + lam ≤ x ∧ x < Real.pi - n * lam + lam

/-- L window of a star receiver anchored at `θ`. -/
def StarL (lam θ x : ℝ) : Prop :=
  Real.pi - lam < x ∧ x ≤ Real.pi - lam + θ

/-- Numeric package: `β = π − nλ ∈ [θ, λ)`, `θ ≥ 0`, `n ≥ 3`. -/
structure StarParams (n : ℕ) (lam θ : ℝ) : Prop where
  hn3 : 3 ≤ n
  hlam : 0 < lam
  hθ0 : 0 ≤ θ
  hθβ : θ ≤ Real.pi - n * lam
  hβ : Real.pi - n * lam < lam

variable (P : StarParams n lam θ)
include P

private lemma cast_sub3 : ((n - 3 : ℕ) : ℝ) = n - 3 := by
  have := P.hn3; push_cast [Nat.cast_sub this]; ring

private lemma cast_sub2 : ((n - 2 : ℕ) : ℝ) = n - 2 := by
  have : 2 ≤ n := by have := P.hn3; omega
  push_cast [Nat.cast_sub this]; ring

private lemma n_ge3 : (3 : ℝ) ≤ n := by exact_mod_cast P.hn3

lemma starF_not_L {x : ℝ} (hF : StarF n lam θ x) : ¬ StarL lam θ x := by
  intro hL
  have := n_ge3 P
  have := P.hlam
  nlinarith [hF.2, hL.1]

/-- Tail inside L: `linearGapScore x (θ+π) xs = 0`. -/
lemma lgs_tail_L : ∀ (xs : List ℝ) (x : ℝ), StarL lam θ x →
    (∀ y ∈ xs, StarL lam θ y) →
    linearGapScore lam x (θ + Real.pi) xs = 0 := by
  intro xs
  induction xs with
  | nil =>
      intro x hx _
      simp only [linearGapScore]
      exact gapScore_zero_of_lt_two P.hlam (by
        have := P.hθβ; have := P.hβ; linarith [hx.1])
  | cons y ys ih =>
      intro x hx hall
      have hy := hall y (by simp)
      simp only [linearGapScore]
      rw [gapScore_zero_of_lt_two P.hlam (by
        have := P.hθβ; have := P.hβ; have := P.hlam; linarith [hy.2, hx.1]),
        ih y hy (fun z hz => hall z (by simp [hz]))]

/-- Tail inside F: `linearGapScore x (θ+π) xs = n − 2`. -/
lemma lgs_tail_F : ∀ (xs : List ℝ) (x : ℝ), StarF n lam θ x →
    (∀ y ∈ xs, StarF n lam θ y) →
    linearGapScore lam x (θ + Real.pi) xs = n - 2 := by
  intro xs
  induction xs with
  | nil =>
      intro x hx _
      simp only [linearGapScore]
      apply gapScore_eq_of_mem P.hlam
      · rw [cast_sub2 P]; have := P.hθ0; nlinarith [hx.2]
      · rw [cast_sub2 P]; have := P.hβ; nlinarith [hx.1]
  | cons y ys ih =>
      intro x hx hall
      have hy := hall y (by simp)
      simp only [linearGapScore]
      rw [gapScore_zero_of_lt_two P.hlam (by
        have := P.hθ0; have := P.hβ; have := P.hlam; linarith [hy.2, hx.1]),
        ih y hy (fun z hz => hall z (by simp [hz]))]
      simp

/-- Mixed tail: starting in F, sorted, some later chord in L:
`linearGapScore x (θ+π) xs = n − 3`. -/
lemma lgs_tail_mixed : ∀ (xs : List ℝ) (x : ℝ), StarF n lam θ x →
    (x :: xs).Pairwise (· ≤ ·) →
    (∀ y ∈ xs, StarF n lam θ y ∨ StarL lam θ y) →
    (∃ y ∈ xs, StarL lam θ y) →
    linearGapScore lam x (θ + Real.pi) xs = n - 3 := by
  intro xs
  induction xs with
  | nil => intro x _ _ _ hex; simp at hex
  | cons y ys ih =>
      intro x hx hpw hall hex
      simp only [linearGapScore]
      have hpw' := List.pairwise_cons.mp hpw
      rcases hall y (by simp) with hyF | hyL
      · rw [gapScore_zero_of_lt_two P.hlam (by
          have := P.hθ0; have := P.hβ; have := P.hlam; linarith [hyF.2, hx.1]),
          ih y hyF hpw'.2 (fun z hz => hall z (by simp [hz])) (by
            obtain ⟨z, hz, hzL⟩ := hex
            rcases List.mem_cons.mp hz with rfl | hz'
            · exact absurd hzL (starF_not_L P hyF)
            · exact ⟨z, hz', hzL⟩)]
        simp
      · -- first L chord: the F→L gap has floor `n − 2`.
        have hrest : ∀ z ∈ ys, StarL lam θ z := by
          intro z hz
          rcases hall z (by simp [hz]) with hzF | hzL
          · exfalso
            have hyz : y ≤ z :=
              (List.pairwise_cons.mp hpw'.2).1 z hz
            have := n_ge3 P; have := P.hlam
            nlinarith [hzF.2, hyL.1]
          · exact hzL
        rw [lgs_tail_L P ys y hyL hrest, add_zero]
        apply gapScore_eq_of_mem P.hlam
        · rw [cast_sub3 P]; have := P.hθβ; nlinarith [hyL.1, hx.2]
        · rw [cast_sub3 P]; have := P.hβ; nlinarith [hyL.2, hx.1]

/-- **One-sided star score.** -/
theorem star_linear_score_one_sided {sub : List ℝ}
    (hsort : sub.Pairwise (· ≤ ·)) (hne : sub ≠ [])
    (hwin : ∀ x ∈ sub, StarF n lam θ x ∨ StarL lam θ x)
    (hside : (∀ x ∈ sub, StarF n lam θ x) ∨ (∀ x ∈ sub, StarL lam θ x)) :
    linearGapScore lam θ (θ + Real.pi) sub = n - 2 := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [linearGapScore]
  rcases hside with hF | hL
  · have hy := hF y (by simp)
    rw [gapScore_zero_of_lt_two P.hlam (by
      have := P.hθ0; have := P.hβ; linarith [hy.2]),
      lgs_tail_F P ys y hy (fun z hz => hF z (by simp [hz]))]
    simp
  · have hy := hL y (by simp)
    rw [lgs_tail_L P ys y hy (fun z hz => hL z (by simp [hz])), add_zero]
    apply gapScore_eq_of_mem P.hlam
    · rw [cast_sub2 P]; have := P.hθβ; nlinarith [hy.1]
    · rw [cast_sub2 P]; have := P.hβ; nlinarith [hy.2]

/-- **Mixed star score.** -/
theorem star_linear_score_mixed {sub : List ℝ}
    (hsort : sub.Pairwise (· ≤ ·))
    (hwin : ∀ x ∈ sub, StarF n lam θ x ∨ StarL lam θ x)
    (hexF : ∃ x ∈ sub, StarF n lam θ x) (hexL : ∃ x ∈ sub, StarL lam θ x) :
    linearGapScore lam θ (θ + Real.pi) sub = n - 3 := by
  cases sub with
  | nil => simp at hexF
  | cons y ys =>
      simp only [linearGapScore]
      rcases hwin y (by simp) with hyF | hyL
      · rw [gapScore_zero_of_lt_two P.hlam (by
          have := P.hθ0; have := P.hβ; linarith [hyF.2]),
          lgs_tail_mixed P ys y hyF hsort
            (fun z hz => hwin z (by simp [hz])) (by
              obtain ⟨z, hz, hzL⟩ := hexL
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact absurd hzL (starF_not_L P hyF)
              · exact ⟨z, hz', hzL⟩)]
        simp
      · -- sorted and `y ∈ L` first: every chord is in L, no F chord.
        exfalso
        obtain ⟨z, hz, hzF⟩ := hexF
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact starF_not_L P hzF hyL
        · have hyz : y ≤ z := (List.pairwise_cons.mp hsort).1 z hz'
          have := n_ge3 P; have := P.hlam
          nlinarith [hzF.2, hyL.1]

end Windows

section Anchored

variable {s n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (s + 1) → Plane₂} {v : Fin (s + 1)}
  {theta : Fin s → ℝ}

/-- **Window of an incoming short chord.**  If `j` has a short chord into
`h`, then `dirRep h j` lies in the F window (short-first source) or the L
window (short-last source) of row `h`. -/
theorem star_chord_window (he : e ≠ 0) (hn3 : 3 ≤ n)
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hleg : Section4Legality c lam)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    {h j : Fin s} (hw : ShortWitness (lam := lam) (c := c) o e v theta j h) :
    (StarF n lam (theta h) (dirRep o e (c ∘ v.succAbove) h j) ∧
        theta h < theta j) ∨
      (StarL lam (theta h) (dirRep o e (c ∘ v.succAbove) h j) ∧
        theta j < theta h) := by
  obtain ⟨hjh, hsh⟩ := hw
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hcomm : dirRep o e (c ∘ v.succAbove) h j =
      dirRep o e (c ∘ v.succAbove) j h :=
    dirRep_comm o e _ he (fun hc => hjh (hp'inj hc).symm)
  rw [hcomm]
  rcases hsh with hf | hl
  · left
    have hlt : theta h < theta j :=
      saturated_row_bot_sliver_forces_low o e he hn2 hlam hn hleg v htheta
        j h hjh le_rfl (by linarith)
    refine ⟨⟨?_, by linarith [(htheta j).1.2]⟩, hlt⟩
    by_contra hcon
    push_neg at hcon
    have := saturated_row_bot_sliver_forces_low o e he hn2 hlam hn hleg v
      htheta h j hjh.symm le_rfl (by rw [hcomm]; linarith)
    linarith
  · right
    have hlt : theta j < theta h :=
      saturated_row_top_sliver_forces_high o e he hn2 hlam hn hleg v htheta
        j h hjh le_rfl (by linarith)
    refine ⟨⟨by linarith [(htheta j).1.1], ?_⟩, hlt⟩
    by_contra hcon
    push_neg at hcon
    have := saturated_row_top_sliver_forces_high o e he hn2 hlam hn hleg v
      htheta h j hjh.symm le_rfl (by rw [hcomm]; linarith)
    linarith

/-- Shared setup: score of row `h` equals the linear score and
`rowDefect = n − score`. -/
private lemma star_defect_eq (he : e ≠ 0) (hn3 : 3 ≤ n)
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hleg : Section4Legality c lam)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) (h : Fin s) {k : ℕ}
    (hk : linearGapScore lam (theta h) (theta h + Real.pi)
      (directionRow o e (c ∘ v.succAbove) h) = k) (hkn : k ≤ n) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) = n - k := by
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b := by
    intro a b hab
    have hab' : v.succAbove a ≠ v.succAbove b :=
      fun h => hab (Fin.succAbove_right_injective h)
    exact (chord_in_corridor o he
      (fun h => Fin.succAbove_ne v a (hleg.inj h))
      (fun h => Fin.succAbove_ne v b (hleg.inj h))
      (fun h => hab' (hleg.inj h))
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))).1
  have hscore := anchored_rowScore_eq_linear o e he c hleg.inj v hlam
    hlampi theta htheta' hdirge h
  have hcells : rowCells lam (directionRow o e c (v.succAbove h)) ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove h)
      (by omega) hn
  have hsd := rowScore_eq_sub_defect lam hlam n _ hcells
  have hdle := rowDefect_le lam hlam n _ hcells
  omega

/-- **Full-in star receiver defect.**  If every other non-anchor vertex
has a short chord into `h`, then `c_h = 3` when both windows are used and
`c_h = 2` otherwise. -/
theorem star_receiver_defect (he : e ≠ 0) (hn3 : 3 ≤ n)
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hleg : Section4Legality c lam)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) (h : Fin s)
    (hstar : ∀ j, j ≠ h → ShortWitness (lam := lam) (c := c) o e v theta j h) :
    ((∃ j, j ≠ h ∧ theta h < theta j) ∧ (∃ j, j ≠ h ∧ theta j < theta h) →
      rowDefect n lam (directionRow o e c (v.succAbove h)) = 3) ∧
    (¬ ((∃ j, j ≠ h ∧ theta h < theta j) ∧
        (∃ j, j ≠ h ∧ theta j < theta h)) →
      rowDefect n lam (directionRow o e c (v.succAbove h)) = 2) := by
  classical
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
  have P : StarParams n lam (theta h) :=
    ⟨hn3, hlam, (htheta h).1.1, (htheta h).1.2, hdelta⟩
  set sub := directionRow o e (c ∘ v.succAbove) h with hsub
  have hsort : sub.Pairwise (· ≤ ·) :=
    (directionRow_sorted o e (c ∘ v.succAbove) h).pairwise
  have hmem : ∀ x ∈ sub, ∃ j, j ≠ h ∧ x = dirRep o e (c ∘ v.succAbove) h j :=
    fun x hx => (mem_directionRow o e (c ∘ v.succAbove)).mp hx
  have hwin : ∀ x ∈ sub, StarF n lam (theta h) x ∨ StarL lam (theta h) x := by
    intro x hx
    obtain ⟨j, hjh, rfl⟩ := hmem x hx
    rcases star_chord_window he hn3 hlam hn hleg htheta (hstar j hjh) with
      hF | hL
    · exact Or.inl hF.1
    · exact Or.inr hL.1
  have hin : ∀ j, j ≠ h → dirRep o e (c ∘ v.succAbove) h j ∈ sub :=
    fun j hjh => (mem_directionRow o e (c ∘ v.succAbove)).mpr ⟨j, hjh, rfl⟩
  have hne : sub ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hsub, directionRow_length]; omega
  constructor
  · rintro ⟨⟨j₁, hj₁, hlt₁⟩, ⟨j₂, hj₂, hlt₂⟩⟩
    have hF : StarF n lam (theta h) (dirRep o e (c ∘ v.succAbove) h j₁) := by
      rcases star_chord_window he hn3 hlam hn hleg htheta (hstar j₁ hj₁) with
        hF | hL
      · exact hF.1
      · exact absurd hL.2 (not_lt.mpr hlt₁.le)
    have hL : StarL lam (theta h) (dirRep o e (c ∘ v.succAbove) h j₂) := by
      rcases star_chord_window he hn3 hlam hn hleg htheta (hstar j₂ hj₂) with
        hF | hL
      · exact absurd hF.2 (not_lt.mpr hlt₂.le)
      · exact hL.1
    have hk := star_linear_score_mixed P hsort hwin
      ⟨_, hin j₁ hj₁, hF⟩ ⟨_, hin j₂ hj₂, hL⟩
    rw [star_defect_eq he hn3 hlam hn hleg htheta hs h hk (by omega)]
    omega
  · intro hnot
    have hside : (∀ x ∈ sub, StarF n lam (theta h) x) ∨
        (∀ x ∈ sub, StarL lam (theta h) x) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨⟨x₁, hx₁, hx₁F⟩, ⟨x₂, hx₂, hx₂L⟩⟩ := hcon
      obtain ⟨j₁, hj₁, rfl⟩ := hmem x₁ hx₁
      obtain ⟨j₂, hj₂, rfl⟩ := hmem x₂ hx₂
      apply hnot
      constructor
      · refine ⟨j₂, hj₂, ?_⟩
        rcases star_chord_window he hn3 hlam hn hleg htheta (hstar j₂ hj₂)
          with hF | hL
        · exact hF.2
        · exact absurd hL.1 hx₂L
      · refine ⟨j₁, hj₁, ?_⟩
        rcases star_chord_window he hn3 hlam hn hleg htheta (hstar j₁ hj₁)
          with hF | hL
        · exact absurd hF.1 hx₁F
        · exact hL.2
    have hk := star_linear_score_one_sided P hsort hne hwin hside
    rw [star_defect_eq he hn3 hlam hn hleg htheta hs h hk (by omega)]
    omega

/-- **Consumer.**  A full-in star receiver of defect `≥ 3` is mixed and
has defect exactly `3`. -/
theorem star_receiver_high_is_mixed (he : e ≠ 0) (hn3 : 3 ≤ n)
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hleg : Section4Legality c lam)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) (h : Fin s)
    (hstar : ∀ j, j ≠ h → ShortWitness (lam := lam) (c := c) o e v theta j h)
    (hhigh : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h))) :
    (∃ j, j ≠ h ∧ theta h < theta j) ∧ (∃ j, j ≠ h ∧ theta j < theta h) ∧
      rowDefect n lam (directionRow o e c (v.succAbove h)) = 3 := by
  obtain ⟨hmix, hone⟩ := star_receiver_defect he hn3 hlam hn hleg htheta
    hs h hstar
  by_cases hm : (∃ j, j ≠ h ∧ theta h < theta j) ∧
      (∃ j, j ≠ h ∧ theta j < theta h)
  · exact ⟨hm.1, hm.2, hmix hm⟩
  · have := hone hm; omega

end Anchored

#print axioms gapScore_zero_of_lt_two
#print axioms gapScore_eq_of_mem
#print axioms star_linear_score_one_sided
#print axioms star_linear_score_mixed
#print axioms star_chord_window
#print axioms star_receiver_defect
#print axioms star_receiver_high_is_mixed

end Jsp404
