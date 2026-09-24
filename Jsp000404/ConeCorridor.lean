import Jsp000404.Induction

/-!
# A narrow anchor cone confines every other chord direction

This uses the two endpoint angle caps, not an assumed condition on the
chord directions. It is the geometric interval for the low-regime cover.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

lemma angle_eq_abs_of_half_plane_chart
    (o : Orientation ℝ Plane₂ (Fin 2)) {e u v : Plane₂}
    (he : e ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) {a b : ℝ}
    (ha : a ∈ Set.Ico 0 Real.pi) (hb : b ∈ Set.Ico 0 Real.pi)
    (hua : o.oangle e u = (a : Real.Angle))
    (hvb : o.oangle e v = (b : Real.Angle)) :
    InnerProductGeometry.angle u v = |b - a| := by
  rw [o.angle_eq_abs_oangle_toReal hu hv,
    ← o.oangle_sub_left he hu hv, hua, hvb, ← Real.Angle.coe_sub]
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [ha.1, hb.1, ha.2, hb.2],
    by linarith [ha.1, hb.1, ha.2, hb.2]⟩]

private theorem directed_chord_in_corridor
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
  · -- |phi - tx| ≥ lam and phi - tx > -lam (phi ≥ 0, tx < lam), so phi ≥ tx + lam.
    rcases abs_choice (phi - tx) with h | h
    · linarith
    · exfalso
      linarith [hp.1, htx.2, hbeta]
  · -- |phi - ty| ≤ π - lam gives phi ≤ ty + π - lam.
    linarith [le_trans (le_abs_self (phi - ty)) hcapy]

/-- If the anchor rays lie in [0,beta] with beta < lambda, all other
unoriented lines lie in [lambda, pi-lambda+beta]. -/
theorem chord_in_corridor
    (o : Orientation ℝ Plane₂ (Fin 2)) {e A X Y : Plane₂}
    (he : e ≠ 0) (hx : X ≠ A) (hy : Y ≠ A) (hxy : X ≠ Y)
    {lam beta tx ty : ℝ} (hbeta : beta < lam) (hbetapi : beta < Real.pi)
    (htx : tx ∈ Set.Icc 0 beta) (hty : ty ∈ Set.Icc 0 beta)
    (hxdir : o.oangle e (X - A) = (tx : Real.Angle))
    (hydir : o.oangle e (Y - A) = (ty : Real.Angle))
    (hcapx : ∠ A X Y ≤ Real.pi - lam)
    (hcapy : ∠ A Y X ≤ Real.pi - lam) :
    linRep (o.oangle e (Y - X)) ∈ Set.Icc lam (Real.pi - lam + beta) := by
  have hp := linRep_mem_Ico (o.oangle e (Y - X))
  rcases linRep_class (o.oangle e (Y - X)) with hdir | hdir
  · exact Set.Icc_subset_Icc (by linarith [htx.1]) (by linarith [hty.2])
      (directed_chord_in_corridor o he hx hy hxy hbeta hbetapi
        htx hty hp hxdir hydir hdir.symm hcapx hcapy)
  · have hreverse : o.oangle e (X - Y) =
        (linRep (o.oangle e (Y - X)) : Real.Angle) := by
      rw [show X - Y = -(Y - X) by abel,
        o.oangle_neg_right he (sub_ne_zero.mpr hxy.symm)]
      exact hdir.symm
    exact Set.Icc_subset_Icc (by linarith [hty.1]) (by linarith [htx.2])
      (directed_chord_in_corridor o he hy hx hxy.symm hbeta hbetapi
        hty htx hp hydir hxdir hreverse hcapy hcapx)

/-- **Endpoint-refined chord window.**  The same two endpoint angle caps
give a sharper, orientation-dependent bound: the chord representative lies
either in `[tx + lam, π − lam + ty]` or in `[ty + lam, π − lam + tx]`.  In
particular it always lies in `[lam + min tx ty, π − lam + max tx ty]`, and a
chord reaching the top sliver `> π − lam + t` must have an endpoint ray
above `t` — the source of the extreme-sliver exclusivity in the residual
R-HIGH1 analysis. -/
theorem chord_in_endpoint_window
    (o : Orientation ℝ Plane₂ (Fin 2)) {e A X Y : Plane₂}
    (he : e ≠ 0) (hx : X ≠ A) (hy : Y ≠ A) (hxy : X ≠ Y)
    {lam beta tx ty : ℝ} (hbeta : beta < lam) (hbetapi : beta < Real.pi)
    (htx : tx ∈ Set.Icc 0 beta) (hty : ty ∈ Set.Icc 0 beta)
    (hxdir : o.oangle e (X - A) = (tx : Real.Angle))
    (hydir : o.oangle e (Y - A) = (ty : Real.Angle))
    (hcapx : ∠ A X Y ≤ Real.pi - lam)
    (hcapy : ∠ A Y X ≤ Real.pi - lam) :
    linRep (o.oangle e (Y - X)) ∈ Set.Icc (tx + lam) (Real.pi - lam + ty) ∨
      linRep (o.oangle e (Y - X)) ∈
        Set.Icc (ty + lam) (Real.pi - lam + tx) := by
  have hp := linRep_mem_Ico (o.oangle e (Y - X))
  rcases linRep_class (o.oangle e (Y - X)) with hdir | hdir
  · exact Or.inl (directed_chord_in_corridor o he hx hy hxy hbeta hbetapi
      htx hty hp hxdir hydir hdir.symm hcapx hcapy)
  · have hreverse : o.oangle e (X - Y) =
        (linRep (o.oangle e (Y - X)) : Real.Angle) := by
      rw [show X - Y = -(Y - X) by abel,
        o.oangle_neg_right he (sub_ne_zero.mpr hxy.symm)]
      exact hdir.symm
    exact Or.inr (directed_chord_in_corridor o he hy hx hxy.symm hbeta
      hbetapi hty htx hp hydir hxdir hreverse hcapy hcapx)

/-- In the low regime, this corridor fits in n-1 bins strictly narrower
than lambda. The actual bin construction also requires a positive span. -/
theorem corridor_length_lt {n : ℕ} (hn : 1 ≤ n) {lam beta : ℝ}
    (hwidth : beta ≤ Real.pi - n * lam)
    (hlow : Real.pi < ((n : ℝ) + 1/2) * lam) :
    Real.pi - 2 * lam + beta < (n - 1 : ℕ) * lam := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa using (Nat.cast_sub (R := ℝ) hn)
  rw [hcast]
  nlinarith

/-- A finite family of nonzero planar rays with pairwise angles at most
beta < pi/2 admits a common oriented window [0,beta]. -/
theorem exists_ray_window {ι : Type*} [Fintype ι] [Nonempty ι]
    (o : Orientation ℝ Plane₂ (Fin 2)) (u : ι → Plane₂)
    (hu : ∀ i, u i ≠ 0) {beta : ℝ} (hbeta : 2 * beta < Real.pi)
    (hang : ∀ i j, InnerProductGeometry.angle (u i) (u j) ≤ beta) :
    ∃ e : Plane₂, e ≠ 0 ∧ ∃ theta : ι → ℝ,
      ∀ i, theta i ∈ Set.Icc 0 beta ∧ o.oangle e (u i) = (theta i : Real.Angle) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let a : ι → ℝ := fun i => (o.oangle (u i₀) (u i)).toReal
  have ha (i : ι) : -beta ≤ a i ∧ a i ≤ beta := by
    have h := hang i₀ i
    rw [o.angle_eq_abs_oangle_toReal (hu i₀) (hu i)] at h
    exact abs_le.mp h
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  refine ⟨u j, hu j, fun i => a i - a j, ?_⟩
  intro i
  have hji : a j ≤ a i := hj i (Finset.mem_univ _)
  have hdir : o.oangle (u j) (u i) = ((a i - a j : ℝ) : Real.Angle) := by
    rw [← o.oangle_sub_left (hu i₀) (hu j) (hu i), Real.Angle.coe_sub]
    simp only [a, Real.Angle.coe_toReal]
  have hrep : (((a i - a j : ℝ) : Real.Angle)).toReal = a i - a j :=
    Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [Real.pi_pos], by linarith [(ha i).2, (ha j).1]⟩
  have hi := hang j i
  rw [o.angle_eq_abs_oangle_toReal (hu j) (hu i), hdir, hrep,
    abs_of_nonneg (sub_nonneg.mpr hji)] at hi
  exact ⟨⟨sub_nonneg.mpr hji, hi⟩, hdir⟩

/-- A saturated center supplies the common ray window from actual geometry. -/
theorem saturated_ray_window {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 1 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (hsat : rowDefect n lam (directionRow o e c v) = 1) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin s → ℝ,
      ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
        o.oangle e' (c (v.succAbove i) - c v) = (theta i : Real.Angle) := by
  letI : NeZero s := ⟨by omega⟩
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hbeta0 : 0 ≤ Real.pi - n * lam := by linarith
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  apply exists_ray_window o (fun i : Fin s => c (v.succAbove i) - c v)
    (fun i => sub_ne_zero.mpr (fun h => Fin.succAbove_ne v i (hleg.inj h)))
    (by nlinarith)
  intro i j
  by_cases hij : i = j
  · subst j
    rw [InnerProductGeometry.angle_self
      (sub_ne_zero.mpr (fun h => Fin.succAbove_ne v i (hleg.inj h)))]
    exact hbeta0
  · exact angle_le_pi_sub_of_saturation o e hn2 hlam hn hleg he (by omega)
      (Fin.ne_succAbove v i) (Fin.ne_succAbove v j)
      (fun h => hij (Fin.succAbove_right_injective h)) hsat

/-- All non-anchor chord lines fit in the corridor supplied by saturation.
The reference vector is constructed, rather than assumed. -/
theorem saturated_chord_corridor {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 1 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (hsat : rowDefect n lam (directionRow o e c v) = 1) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin s → ℝ,
      (∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
        o.oangle e' (c (v.succAbove i) - c v) = (theta i : Real.Angle)) ∧
      ∀ i j : Fin s, i ≠ j →
        linRep (o.oangle e' (c (v.succAbove j) - c (v.succAbove i))) ∈
          Set.Icc lam (2 * Real.pi - (n + 1) * lam) := by
  obtain ⟨e', he', theta, htheta⟩ :=
    saturated_ray_window o e he hs hn2 hlam hn hleg v hsat
  refine ⟨e', he', theta, htheta, ?_⟩
  intro i j hij
  have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcij : v.succAbove i ≠ v.succAbove j :=
    fun h => hij (Fin.succAbove_right_injective h)
  have hcorr := chord_in_corridor o he'
    (fun h => Fin.succAbove_ne v i (hleg.inj h))
    (fun h => Fin.succAbove_ne v j (hleg.inj h))
    (fun h => hcij (hleg.inj h))
    (by nlinarith : Real.pi - n * lam < lam)
    (by nlinarith : Real.pi - n * lam < Real.pi)
    (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
    (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij (Fin.ne_succAbove v j))
    (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm (Fin.ne_succAbove v i))
  convert hcorr using 1 <;> ring

/-- Endpoint-refined window for the saturated-anchor data: each chord
`i → j` between non-anchor centers lands in one of the two intervals
`[θᵢ + λ, π − λ + θⱼ]` / `[θⱼ + λ, π − λ + θᵢ]`.  Both bounds follow from
the two triangle-angle caps at `i` and `j`; which disjunct holds is
determined by the chord's orientation class.  This is the formal source of
the extreme-sliver exclusivity used in the residual R-HIGH1 analysis. -/
theorem saturated_chord_endpoint_window {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (i j : Fin s) (hij : i ≠ j) :
    linRep (o.oangle e (c (v.succAbove j) - c (v.succAbove i))) ∈
      Set.Icc (theta i + lam) (Real.pi - lam + theta j) ∨
    linRep (o.oangle e (c (v.succAbove j) - c (v.succAbove i))) ∈
      Set.Icc (theta j + lam) (Real.pi - lam + theta i) := by
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcij : v.succAbove i ≠ v.succAbove j :=
    fun h => hij (Fin.succAbove_right_injective h)
  exact chord_in_endpoint_window o he
    (fun h => Fin.succAbove_ne v i (hleg.inj h))
    (fun h => Fin.succAbove_ne v j (hleg.inj h))
    (fun h => hcij (hleg.inj h))
    (by nlinarith : Real.pi - n * lam < lam)
    (by nlinarith : Real.pi - n * lam < Real.pi)
    (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
    (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij (Fin.ne_succAbove v j))
    (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm (Fin.ne_succAbove v i))

/-- The non-disjunctive consequence: every chord representative lies between
`lam + min θᵢ θⱼ` and `π − lam + max θᵢ θⱼ`. -/
theorem saturated_chord_minmax_window {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (i j : Fin s) (hij : i ≠ j) :
    linRep (o.oangle e (c (v.succAbove j) - c (v.succAbove i))) ∈
      Set.Icc (lam + min (theta i) (theta j))
        (Real.pi - lam + max (theta i) (theta j)) := by
  rcases saturated_chord_endpoint_window o e he hn2 hlam hn hleg v htheta
    i j hij with h | h
  · exact ⟨by linarith [h.1, min_le_left (theta i) (theta j)],
      by linarith [h.2, le_max_right (theta i) (theta j)]⟩
  · exact ⟨by linarith [h.1, min_le_right (theta i) (theta j)],
      by linarith [h.2, le_max_left (theta i) (theta j)]⟩

/-- Top-sliver exclusivity: a chord whose representative exceeds
`π − lam + t` must have an endpoint ray above `t`.  With `theta` sorted,
a chord in `(π−λ+θ_{s−2}, π−λ+θ_{s−1}]` is therefore incident to the
extreme-θ center. -/
theorem saturated_chord_top_sliver {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (i j : Fin s) (hij : i ≠ j) {t : ℝ}
    (hdir : Real.pi - lam + t <
      linRep (o.oangle e (c (v.succAbove j) - c (v.succAbove i)))) :
    t < theta i ∨ t < theta j := by
  have h := saturated_chord_minmax_window o e he hn2 hlam hn hleg v htheta
    i j hij
  have hlt : t < max (theta i) (theta j) := by linarith [h.2]
  exact lt_max_iff.mp hlt

/-- Bottom-sliver exclusivity: a chord whose representative is below
`lam + t` must have an endpoint ray below `t`. -/
theorem saturated_chord_bot_sliver {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (i j : Fin s) (hij : i ≠ j) {t : ℝ}
    (hdir : linRep (o.oangle e (c (v.succAbove j) - c (v.succAbove i))) <
      lam + t) :
    theta i < t ∨ theta j < t := by
  have h := saturated_chord_minmax_window o e he hn2 hlam hn hleg v htheta
    i j hij
  have hlt : min (theta i) (theta j) < t := by linarith [h.1]
  exact min_lt_iff.mp hlt

/-- Chord-to-row bridge, bottom sliver: in a row `w` whose own anchor
ray is not low (`t ≤ θ_w`), every bottom-sliver direction `w → j`
(`dir < λ + t`) is forced to land on a low endpoint (`θ_j < t`).
This is the per-row direction-level fact underlying sliver occupancy;
the low row itself (`θ_w < t`) is excluded on purpose — it may contain
arbitrarily many sliver chords and must be charged separately. -/
theorem saturated_row_bot_sliver_forces_low {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (w j : Fin s) (hwj : w ≠ j) {t : ℝ}
    (htw : t ≤ theta w)
    (hdir : dirRep o e (c ∘ v.succAbove) w j < lam + t) :
    theta j < t := by
  rcases saturated_chord_bot_sliver o e he hn2 hlam hn hleg v htheta w j
      hwj hdir with h | h
  · exact absurd h (not_lt.mpr htw)
  · exact h

/-- Per-row bottom-sliver occupancy: if `p` is the only index with
`θ < t`, then a row `w` with `t ≤ θ_w` contributes at most one
direction below `λ + t` — the chord `w → p` if present.  This is the
index-level counting bridge that a bin argument can consume; it does
NOT bound the low row `p` itself, which can occupy the sliver with
many chords. -/
theorem saturated_row_bot_sliver_card_le_one {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (w p : Fin s) {t : ℝ}
    (htw : t ≤ theta w)
    (huniq : ∀ j : Fin s, theta j < t → j = p) :
    (Finset.univ.filter fun j : Fin s =>
        w ≠ j ∧ dirRep o e (c ∘ v.succAbove) w j < lam + t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j hj k hk
  rw [Finset.mem_filter] at hj hk
  exact (huniq j (saturated_row_bot_sliver_forces_low o e he hn2 hlam hn
    hleg v htheta w j hj.2.1 htw hj.2.2)).trans
    (huniq k (saturated_row_bot_sliver_forces_low o e he hn2 hlam hn hleg
      v htheta w k hk.2.1 htw hk.2.2)).symm

/-- Chord-to-row bridge, top sliver: in a row `w` whose own anchor ray
is not high (`θ_w ≤ u`), every top-sliver direction `w → j`
(`dir > π − λ + u`) is forced to land on a high endpoint (`θ_j > u`). -/
theorem saturated_row_top_sliver_forces_high {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (w j : Fin s) (hwj : w ≠ j) {u : ℝ}
    (huw : theta w ≤ u)
    (hdir : Real.pi - lam + u < dirRep o e (c ∘ v.succAbove) w j) :
    u < theta j := by
  rcases saturated_chord_top_sliver o e he hn2 hlam hn hleg v htheta w j
      hwj hdir with h | h
  · exact absurd h (not_lt.mpr huw)
  · exact h

/-- Per-row top-sliver occupancy: if `q` is the only index with
`u < θ`, then a row `w` with `θ_w ≤ u` contributes at most one
direction above `π − λ + u` — the chord `w → q` if present. -/
theorem saturated_row_top_sliver_card_le_one {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (w q : Fin s) {u : ℝ}
    (huw : theta w ≤ u)
    (huniq : ∀ j : Fin s, u < theta j → j = q) :
    (Finset.univ.filter fun j : Fin s =>
        w ≠ j ∧ Real.pi - lam + u <
          dirRep o e (c ∘ v.succAbove) w j).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j hj k hk
  rw [Finset.mem_filter] at hj hk
  exact (huniq j (saturated_row_top_sliver_forces_high o e he hn2 hlam hn
    hleg v htheta w j hj.2.1 huw hj.2.2)).trans
    (huniq k (saturated_row_top_sliver_forces_high o e he hn2 hlam hn
      hleg v htheta w k hk.2.1 huw hk.2.2)).symm

/-- In the low regime the constructed anchor window may be enlarged to
[0,lambda/2], giving the fixed chord corridor [lambda,pi-lambda/2]. -/
theorem saturated_low_corridor {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 1 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : Real.pi / lam - n < 1/2) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin s → ℝ,
      (∀ i, theta i ∈ Set.Icc 0 (lam / 2) ∧
        o.oangle e' (c (v.succAbove i) - c v) = (theta i : Real.Angle)) ∧
      ∀ i j : Fin s, i ≠ j →
        linRep (o.oangle e' (c (v.succAbove j) - c (v.succAbove i))) ∈
          Set.Icc lam (Real.pi - lam / 2) := by
  obtain ⟨e', he', theta, ht, hc⟩ :=
    saturated_chord_corridor o e he hs hn2 hlam hn hleg v hsat
  have hpi : Real.pi < ((n : ℝ) + 1/2) * lam :=
    (div_lt_iff₀ hlam).mp (by linarith)
  refine ⟨e', he', theta, ?_, ?_⟩
  · intro i
    exact ⟨⟨(ht i).1.1, by nlinarith [(ht i).1.2]⟩, (ht i).2⟩
  · intro i j hij
    exact ⟨(hc i j hij).1, by nlinarith [(hc i j hij).2]⟩

/-- The fixed corridor has positive width and splits into n-1 bins of
width strictly between zero and lambda. -/
theorem low_corridor_grid_width {n : ℕ} (hn2 : 2 ≤ n) {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hδ : Real.pi / lam - n < 1/2) :
    0 < (Real.pi - 3 * lam / 2) / (n - 1 : ℕ) ∧
      (Real.pi - 3 * lam / 2) / (n - 1 : ℕ) < lam := by
  have hf := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hf
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hm : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hpi : Real.pi < ((n : ℝ) + 1/2) * lam :=
    (div_lt_iff₀ hlam).mp (by linarith)
  refine ⟨div_pos (by nlinarith) hm, ?_⟩
  rw [div_lt_iff₀ hm]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ n by omega))
  rw [hcast]
  nlinarith

#print axioms chord_in_corridor
#print axioms chord_in_endpoint_window
#print axioms corridor_length_lt
#print axioms saturated_ray_window
#print axioms saturated_chord_corridor
#print axioms saturated_chord_endpoint_window
#print axioms saturated_chord_minmax_window
#print axioms saturated_chord_top_sliver
#print axioms saturated_chord_bot_sliver
#print axioms saturated_row_bot_sliver_forces_low
#print axioms saturated_row_bot_sliver_card_le_one
#print axioms saturated_row_top_sliver_forces_high
#print axioms saturated_row_top_sliver_card_le_one
#print axioms saturated_low_corridor
#print axioms low_corridor_grid_width

end Jsp404
