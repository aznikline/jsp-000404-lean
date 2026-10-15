import Jsp000404.ConeCorridor

/-!
# Projection descent along short-end witnesses

In a saturated anchored chart (anchor `A = c v`, anchor rays
`θ_i ∈ [0, β]`, `β = π − nλ`), put `Ψ i = ⟪e, P_i − A⟫`.

* `short_first_inner_neg` / `short_last_inner_neg` (pure geometry): if
  the projective chord direction `φ = linRep (oangle e (Y − X))` lies in
  the short first window `φ − t_X < λ` (resp. short last window
  `t_X + π − φ < λ`), the *actual* directed edge `Y − X` satisfies
  `⟪e, Y − X⟫ < 0`.  The lift branch is decided by the endpoint caps
  (`directed_chord_in_corridor'`): for a short first chord the direct
  branch would force `φ ≥ t_X + λ`, for a short last chord the reversed
  branch would force `φ ≤ π − λ + t_X`.  The sign then comes from
  `β + λ < π/2`.
* `acute_margin_of_floor`: `n = ⌊π/λ⌋₊ ≥ 3` gives `β + λ < π/2`.
* `shortWitness_projection_lt`: every short chord (first or last window,
  any row, any defect) strictly lowers `Ψ`.
* `shortWitness_no_cycle`: the short-chord relation has no cycle of
  any length (`TransGen` irreflexive).
* `psi_min_row_ends_big`: the `Ψ`-minimal non-anchor row has both end
  gaps `≥ λ`.

No cycle does *not* give `R ≤ 2` on its own: a chain may end at a
defect-`2` row whose two end gaps are both big.
-/

open scoped EuclideanGeometry EuclideanSpace RealInnerProductSpace

namespace Jsp404

/-- Local copy of the (private) directed corridor lemma of
`ConeCorridor.lean`. -/
theorem directed_chord_in_corridor'
    (o : Orientation ℝ Plane₂ (Fin 2)) {e A X Y : Plane₂}
    (he : e ≠ 0) (hx : X ≠ A) (hy : Y ≠ A) (hxy : X ≠ Y)
    {lam beta tx ty phi : ℝ} (hbeta : beta < lam) (hbetapi : beta < Real.pi)
    (htx : tx ∈ Set.Icc 0 beta) (hty : ty ∈ Set.Icc 0 beta)
    (hp : phi ∈ Set.Ico 0 Real.pi)
    (hxdir : o.oangle e (X - A) = (tx : Real.Angle))
    (hydir : o.oangle e (Y - A) = (ty : Real.Angle))
    (hchord : o.oangle e (Y - X) = (phi : Real.Angle))
    (hcapx : ∠ A X Y ≤ Real.pi - lam)
    (hcapy : ∠ A Y X ≤ Real.pi - lam) :
    phi ∈ Set.Icc (tx + lam) (Real.pi - lam + ty) := by
  have hxangle := angle_eq_abs_of_half_plane_chart o he (sub_ne_zero.mpr hx)
    (sub_ne_zero.mpr hxy.symm) ⟨htx.1, htx.2.trans_lt hbetapi⟩ hp hxdir hchord
  have hyangle := angle_eq_abs_of_half_plane_chart o he (sub_ne_zero.mpr hy)
    (sub_ne_zero.mpr hxy.symm) ⟨hty.1, hty.2.trans_lt hbetapi⟩ hp hydir hchord
  change InnerProductGeometry.angle (A - X) (Y - X) ≤ Real.pi - lam at hcapx
  rw [show A - X = -(X - A) by abel,
    InnerProductGeometry.angle_neg_left, hxangle] at hcapx
  change InnerProductGeometry.angle (A - Y) (X - Y) ≤ Real.pi - lam at hcapy
  rw [show A - Y = -(Y - A) by abel,
    show X - Y = -(Y - X) by abel,
    InnerProductGeometry.angle_neg_neg, hyangle] at hcapy
  constructor
  · rcases abs_choice (phi - tx) with h | h
    · linarith
    · exfalso
      linarith [hp.1, htx.2, hbeta]
  · linarith [le_trans (le_abs_self (phi - ty)) hcapy]

/-- `n = ⌊π/λ⌋₊ ≥ 3` gives the acute margin `β + λ < π/2`,
`β = π − nλ`. -/
theorem acute_margin_of_floor {n : ℕ} (hn3 : 3 ≤ n) {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n) :
    Real.pi - n * lam + lam < Real.pi / 2 := by
  have h := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at h
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  nlinarith

/-- The inner product with `e` of a vector whose oriented angle from `e`
is `ψ`. -/
private lemma inner_eq_cos (o : Orientation ℝ Plane₂ (Fin 2)) (e w : Plane₂)
    {ψ : ℝ} (h : o.oangle e w = (ψ : Real.Angle)) :
    ⟪e, w⟫ = ‖e‖ * ‖w‖ * Real.cos ψ := by
  rw [o.inner_eq_norm_mul_norm_mul_cos_oangle, h, Real.Angle.cos_coe]

/-- **Short first chord points toward `−e`.** -/
theorem short_first_inner_neg
    (o : Orientation ℝ Plane₂ (Fin 2)) {e A X Y : Plane₂}
    (he : e ≠ 0) (hx : X ≠ A) (hy : Y ≠ A) (hxy : X ≠ Y)
    {lam beta tx ty : ℝ} (hbeta : beta < lam) (hbetapi : beta < Real.pi)
    (hacute : beta + lam < Real.pi / 2)
    (htx : tx ∈ Set.Icc 0 beta) (hty : ty ∈ Set.Icc 0 beta)
    (hxdir : o.oangle e (X - A) = (tx : Real.Angle))
    (hydir : o.oangle e (Y - A) = (ty : Real.Angle))
    (hcapx : ∠ A X Y ≤ Real.pi - lam)
    (hcapy : ∠ A Y X ≤ Real.pi - lam)
    (hshort : linRep (o.oangle e (Y - X)) - tx < lam) :
    ⟪e, Y - X⟫ < 0 := by
  set φ := linRep (o.oangle e (Y - X)) with hφ
  have hp : φ ∈ Set.Ico 0 Real.pi := linRep_mem_Ico _
  rcases linRep_class (o.oangle e (Y - X)) with hdir | hdir
  · exfalso
    have h := directed_chord_in_corridor' o he hx hy hxy hbeta hbetapi
      htx hty hp hxdir hydir hdir.symm hcapx hcapy
    linarith [h.1]
  · -- Reversed branch: `oangle e (Y − X) = φ − π`.
    have hd : o.oangle e (Y - X) = ((φ - Real.pi : ℝ) : Real.Angle) := by
      rw [Real.Angle.coe_sub, hφ, hdir]; abel
    rw [inner_eq_cos o e _ hd, Real.cos_sub_pi]
    have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.1, Real.pi_pos], by linarith [htx.2]⟩
    have hne : 0 < ‖e‖ * ‖Y - X‖ :=
      mul_pos (norm_pos_iff.mpr he) (norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm))
    nlinarith

/-- **Short last chord points toward `−e`.** -/
theorem short_last_inner_neg
    (o : Orientation ℝ Plane₂ (Fin 2)) {e A X Y : Plane₂}
    (he : e ≠ 0) (hx : X ≠ A) (hy : Y ≠ A) (hxy : X ≠ Y)
    {lam beta tx ty : ℝ} (hbeta : beta < lam) (hbetapi : beta < Real.pi)
    (hacute : beta + lam < Real.pi / 2)
    (htx : tx ∈ Set.Icc 0 beta) (hty : ty ∈ Set.Icc 0 beta)
    (hxdir : o.oangle e (X - A) = (tx : Real.Angle))
    (hydir : o.oangle e (Y - A) = (ty : Real.Angle))
    (hcapx : ∠ A X Y ≤ Real.pi - lam)
    (hcapy : ∠ A Y X ≤ Real.pi - lam)
    (hshort : tx + Real.pi - linRep (o.oangle e (Y - X)) < lam) :
    ⟪e, Y - X⟫ < 0 := by
  set φ := linRep (o.oangle e (Y - X)) with hφ
  have hp : φ ∈ Set.Ico 0 Real.pi := linRep_mem_Ico _
  rcases linRep_class (o.oangle e (Y - X)) with hdir | hdir
  · -- Direct branch: `oangle e (Y − X) = φ`, with `φ ∈ (π/2, π)`.
    rw [inner_eq_cos o e _ hdir.symm]
    have hcos : Real.cos φ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt
      (by linarith [htx.1, htx.2]) (by linarith [hp.2, Real.pi_pos])
    have hne : 0 < ‖e‖ * ‖Y - X‖ :=
      mul_pos (norm_pos_iff.mpr he) (norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm))
    nlinarith
  · -- Reversed branch is excluded: `X − Y` would be a direct chord at `Y`
    -- forcing `φ ≤ π − λ + t_X`.
    exfalso
    have hrev : o.oangle e (X - Y) = (φ : Real.Angle) := by
      rw [show X - Y = -(Y - X) by abel,
        o.oangle_neg_right he (sub_ne_zero.mpr hxy.symm)]
      exact hdir.symm
    have h := directed_chord_in_corridor' o he hy hx hxy.symm hbeta hbetapi
      hty htx hp hydir hxdir hrev hcapy hcapx
    linarith [h.2]

section Anchored

variable {s n : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
  {lam : ℝ} {c : Fin (s + 1) → Plane₂} (v : Fin (s + 1))
  (theta : Fin s → ℝ)

/-- The projection potential `Ψ i = ⟪e, P_i − A⟫`. -/
noncomputable def psi (i : Fin s) : ℝ := ⟪e, c (v.succAbove i) - c v⟫

/-- A short chord `i → j`: the chord direction lies in the short first
or short last window of row `i`.  Row-end witnesses
(`short_first_gap_gives_lower` / `short_last_gap_gives_higher`) are
instances; no defect hypothesis is involved. -/
def ShortWitness (i j : Fin s) : Prop :=
  i ≠ j ∧ (dirRep o e (c ∘ v.succAbove) i j - theta i < lam ∨
    theta i + Real.pi - dirRep o e (c ∘ v.succAbove) i j < lam)

variable {o e v theta}

/-- **Projection descent.**  Every short chord strictly lowers `Ψ`. -/
theorem shortWitness_projection_lt (he : e ≠ 0) (hn3 : 3 ≤ n)
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hleg : Section4Legality c lam)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    {i j : Fin s} (h : ShortWitness (lam := lam) (c := c) o e v theta i j) :
    psi (c := c) e v j < psi (c := c) e v i := by
  obtain ⟨hij, hsh⟩ := h
  have hab' : v.succAbove i ≠ v.succAbove j :=
    fun h => hij (Fin.succAbove_right_injective h)
  have hacute := acute_margin_of_floor hn3 hlam hn
  have hbeta : Real.pi - n * lam < lam := by
    have h := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at h
    linarith
  have hbetapi : Real.pi - n * lam < Real.pi := by
    nlinarith [show (0 : ℝ) < n by exact_mod_cast (by omega : 0 < n)]
  have hx : c (v.succAbove i) ≠ c v := fun h => Fin.succAbove_ne v i (hleg.inj h)
  have hy : c (v.succAbove j) ≠ c v := fun h => Fin.succAbove_ne v j (hleg.inj h)
  have hxy : c (v.succAbove i) ≠ c (v.succAbove j) := fun h => hab' (hleg.inj h)
  have hcapx := hleg.triAngle v _ _ (Fin.ne_succAbove v i) hab'
    (Fin.ne_succAbove v j)
  have hcapy := hleg.triAngle v _ _ (Fin.ne_succAbove v j) hab'.symm
    (Fin.ne_succAbove v i)
  have key : ⟪e, c (v.succAbove j) - c (v.succAbove i)⟫ < 0 := by
    rcases hsh with hf | hl
    · exact short_first_inner_neg o he hx hy hxy hbeta hbetapi hacute
        (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2 hcapx hcapy hf
    · exact short_last_inner_neg o he hx hy hxy hbeta hbetapi hacute
        (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2 hcapx hcapy hl
  unfold psi
  have hsplit : c (v.succAbove j) - c (v.succAbove i) =
      (c (v.succAbove j) - c v) - (c (v.succAbove i) - c v) := by abel
  rw [hsplit, inner_sub_right] at key
  linarith

/-- **No short-witness cycle of any length.** -/
theorem shortWitness_no_cycle (he : e ≠ 0) (hn3 : 3 ≤ n)
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hleg : Section4Legality c lam)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (i : Fin s) :
    ¬ Relation.TransGen
      (ShortWitness (lam := lam) (c := c) o e v theta) i i := by
  have hdesc : ∀ a b, Relation.TransGen
      (ShortWitness (lam := lam) (c := c) o e v theta) a b →
      psi (c := c) e v b < psi (c := c) e v a := by
    intro a b hab
    induction hab with
    | single h => exact shortWitness_projection_lt he hn3 hlam hn hleg htheta h
    | tail _ hbc ih =>
        exact lt_trans (shortWitness_projection_lt he hn3 hlam hn hleg
          htheta hbc) ih
  intro hcyc
  exact lt_irrefl _ (hdesc i i hcyc)

end Anchored

end Jsp404
