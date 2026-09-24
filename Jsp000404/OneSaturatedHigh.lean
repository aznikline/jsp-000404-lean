import Jsp000404.OneSaturatedLow

/-!
# The high-regime capacity bound with a saturated center: narrow-window case

With one saturated center `v`, all anchor rays `c w − c v` lie in a
window of width `π − nλ = δλ < λ` (`saturated_ray_window`).  If the
actual pairwise spread of the anchor rays is strictly below
`α = (n+1)λ − π = (1−δ)λ`, the chord corridor
`[λ, π − λ + β]` has width strictly below `(n−1)λ`, so the low-regime
`n−1` bin argument applies verbatim: the remaining centers carry weight
`≤ 2^{n−1}` and the total potential is `≤ 2^n ≤ 2^n + 2^{n−2}`.

This is a *conditional* theorem closing the narrow-window subdomain of
R-HIGH1.  The residual obligation is the complementary case: legal
configurations whose anchor-ray spread reaches `α` or more.  The exact
four-point counterexample in `notes/ONE_SATURATED_HIGH_GEOMETRY.md`
(spread ≈ 29° ≫ α ≈ 4.3°) shows that the residual case is nonempty and
that the capacity bound cannot come from the corridor alone there.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

private lemma directionRow_score_le_floor' {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (hs : 2 ≤ s) {lam : ℝ} (hlam : 0 < lam) (i : Fin s) :
    rowScore lam (directionRow o e c i) ≤ Nat.floor (Real.pi / lam) - 1 := by
  classical
  let l := directionRow o e c i
  have hsort : l.SortedLE := directionRow_sorted o e c i
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [directionRow_length]
    omega
  have hsortD : l.dedup.SortedLE :=
    (hsort.pairwise.sublist (List.dedup_sublist l)).sortedLE
  have hneD : l.dedup ≠ [] := fun h => hne ((List.dedup_eq_nil l).mp h)
  have hmemD : ∀ x ∈ l.dedup, x ∈ Set.Ico 0 Real.pi := by
    intro x hx
    exact directionRow_mem_Ico o e c (List.mem_dedup.mp hx)
  have h := exponent_le_floor hsortD (List.nodup_dedup l) hmemD hneD hlam
  rw [exponents_entry_eq_rowScore hsortD, rowScore_dedup lam hsort] at h
  exact h

/-- **Narrow-window capacity, chart form.**  In the `δ ≥ 1/2` regime,
if the rays from a center `v` to all other centers pairwise fit in an
angle `< α = (n+1)λ − π`, the potential stays below `2^n`.  The
saturation hypothesis is kept in the signature because the intended
consumer is the unique-saturated R-HIGH1 case (the narrow window is
then supplied by `saturated_ray_window`), but the bound itself only
needs the spread hypothesis. -/
theorem one_saturated_capacity_of_narrow_window {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (_he : e ≠ 0)
    (hs : 1 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (_hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    {beta : ℝ} (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin s,
      InnerProductGeometry.angle (c (v.succAbove i) - c v)
        (c (v.succAbove j) - c v) ≤ beta) :
    ∃ e' : Plane₂, e' ≠ 0 ∧
      potential lam (directionRows o e' c) ≤ 2 ^ n := by
  classical
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlampi : lam < Real.pi := by nlinarith
  have : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  have hb0 : 0 ≤ beta := by
    have h := hspread ⟨0, by omega⟩ ⟨0, by omega⟩
    rwa [InnerProductGeometry.angle_self
      (sub_ne_zero.mpr (fun h =>
        Fin.succAbove_ne v ⟨0, by omega⟩ (hleg.inj h)))] at h
  have hα : (0 : ℝ) < ((n : ℝ) + 1) * lam - Real.pi := by linarith
  -- `α ≤ λ/2` is exactly `δ ≥ 1/2`; hence `β < λ/2` and `2β < π`.
  have hβhalf : beta < lam / 2 := by
    have h1 : ((n : ℝ) + 1) * lam - Real.pi ≤ lam / 2 := by
      have h2 : ((n : ℝ) + 1 / 2) * lam ≤ Real.pi := by
        have h := hδ
        rw [le_sub_iff_add_le] at h
        have := (le_div_iff₀ hlam).mp (by linarith :
            ((n : ℝ) + 1 / 2) ≤ Real.pi / lam)
        linarith
      linarith
    linarith
  have hβpi : 2 * beta < Real.pi := by linarith
  -- Anchor rays in a window of width `β`, then the chord corridor.
  obtain ⟨e', he', theta, htheta⟩ := exists_ray_window o
    (fun i : Fin s => c (v.succAbove i) - c v)
    (fun i => sub_ne_zero.mpr
      (fun h => Fin.succAbove_ne v i (hleg.inj h)))
    hβpi hspread
  have hcorr : ∀ i j : Fin s, i ≠ j →
      linRep (o.oangle e' (c (v.succAbove j) - c (v.succAbove i)))
        ∈ Set.Icc lam (Real.pi - lam + beta) := by
    intro i j hij
    have hcij : v.succAbove i ≠ v.succAbove j :=
      fun h => hij (Fin.succAbove_right_injective h)
    exact chord_in_corridor o he'
      (fun h => Fin.succAbove_ne v i (hleg.inj h))
      (fun h => Fin.succAbove_ne v j (hleg.inj h))
      (fun h => hcij (hleg.inj h))
      (by linarith : beta < lam) (by linarith : beta < Real.pi)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij
        (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  -- `n−1` bins of width `< λ` covering `[λ, π−λ+β]`.
  let m := n - 1
  let width : ℝ := (Real.pi - 2 * lam + beta) / m
  have hm : 0 < m := by dsimp [m]; omega
  have hmreal : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hw : 0 < width := by
    dsimp [width]
    apply div_pos _ hmreal
    nlinarith [hb0, hfloor, hnreal]
  have hwidth : width < lam := by
    dsimp [width]
    rw [div_lt_iff₀ hmreal]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ n by omega))
    rw [hcast]
    nlinarith [hbeta]
  have hend : lam + (m : ℝ) * width = Real.pi - lam + beta := by
    dsimp [width]
    field_simp
    ring
  let p := c ∘ v.succAbove
  have hp : Function.Injective p :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hpos : ∀ i j : Fin s, i ≠ j →
      dirRep o e' p i j ∈ Set.Icc lam (lam + m * width) := by
    intro i j hij
    rw [hend]
    exact hcorr i j hij
  have hangle : ∀ i j k : Fin s, i ≠ j → i ≠ k → j ≠ k →
      ∠ (p i) (p j) (p k) ≤ Real.pi - lam := by
    intro i j k hij hik hjk
    exact hleg.triAngle _ _ _
      (fun h => hij (Fin.succAbove_right_injective h))
      (fun h => hjk (Fin.succAbove_right_injective h))
      (fun h => hik (Fin.succAbove_right_injective h))
  have hbins := directionBinGraph_row_weighted_bound o e' p he' hp hm
    hw hwidth hlam.le (by rw [hend]; linarith) hangle hpos
  have htheta2 : ∀ i, theta i ∈ Set.Icc 0 (lam / 2) ∧
      o.oangle e' (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨⟨(htheta i).1.1,
      (htheta i).1.2.trans hβhalf.le⟩, (htheta i).2⟩
  have hlocal (i : Fin s) :
      rowScore lam (directionRow o e' c (v.succAbove i)) ≤
        m - ((directionRow o e' p i).map
          (uniformBin lam width m)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e' he' c hleg.inj v hlam hlampi
      theta (fun i => ⟨(Set.Icc_subset_Icc le_rfl (half_le_self hlam.le))
        (htheta2 i).1, (htheta2 i).2⟩)
      (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval hm hw hwidth
      (by linarith [(htheta i).1.1])
      (by rw [hend]; linarith [(htheta i).1.2])
      _ (directionRow_sorted o e' p i)
    intro x hx
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e' p).mp hx
    exact hpos i j hji.symm
  have hrest : (∑ i : Fin s, 2 ^ rowScore lam
      (directionRow o e' c (v.succAbove i))) ≤ 2 ^ m := by
    exact (Finset.sum_le_sum (fun i _ =>
      Nat.pow_le_pow_right (by omega) (hlocal i))).trans hbins
  have hv : rowScore lam (directionRow o e' c v) ≤ m := by
    have h := directionRow_score_le_floor' o e' c (by omega) hlam v
    rwa [hn] at h
  refine ⟨e', he', ?_⟩
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  calc 2 ^ rowScore lam (directionRow o e' c v) +
        ∑ i : Fin s, 2 ^ rowScore lam (directionRow o e' c
          (v.succAbove i))
      ≤ 2 ^ m + 2 ^ m := Nat.add_le_add
          (Nat.pow_le_pow_right (by omega) hv) hrest
    _ = 2 ^ n := by
        rw [← two_mul, ← pow_succ']
        congr 1
        dsimp [m]
        omega

/-- The same bound returned to the original reference chart. -/
theorem potential_le_two_pow_of_saturated_narrow {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin s) (_hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    {beta : ℝ} (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin s, i ≠ v → j ≠ v →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ beta) :
    potential lam (directionRows o e c) ≤ 2 ^ n := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  obtain ⟨e', he', hbound⟩ :=
    one_saturated_capacity_of_narrow_window o e he (by omega) hn3
      hlam hn hleg v _hsat hδ hbeta
      (fun i j => hspread _ _ (Fin.succAbove_ne v i)
        (Fin.succAbove_ne v j))
  rw [potential_directionRows_reference_eq o e e' he he' c hleg.inj lam]
  exact hbound

/-- **Small-size closure.**  With a unique saturated center and at most
three remaining centers, each remaining row has defect `≥ 2`, hence
exponent `≤ n−2`; the HIGH cap follows immediately.  No corridor or
window hypothesis is needed. -/
theorem potential_le_high_of_saturated_small {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (hs : 2 ≤ s) (hs4 : s ≤ 4) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (_hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (huniq : ∀ w : Fin s, w ≠ v →
      2 ≤ rowDefect n lam (directionRow o e c w)) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hcells : ∀ i, rowCells lam (directionRow o e c i) ≤ n :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i hs hn
  have key : ∀ i, rowScore lam (directionRow o e c i) =
      n - rowDefect n lam (directionRow o e c i) :=
    fun i => rowScore_eq_sub_defect lam hlam n _ (hcells i)
  unfold potential exponentAt directionRows
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  have hbound : ∀ w ∈ Finset.univ.erase v,
      2 ^ rowScore lam (directionRow o e c w) ≤ 2 ^ (n - 2) := by
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    rw [key w]
    exact Nat.pow_le_pow_right (by omega)
      (by have := huniq w hwv; omega)
  have hcard : (Finset.univ.erase v).card = s - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
      Fintype.card_fin]
  calc 2 ^ rowScore lam (directionRow o e c v) +
        ∑ w ∈ Finset.univ.erase v, 2 ^ rowScore lam (directionRow o e c w)
      ≤ 2 ^ (n - 1) + 3 * 2 ^ (n - 2) := by
        apply Nat.add_le_add
        · rw [key v, hsat]
        · calc ∑ w ∈ Finset.univ.erase v,
                2 ^ rowScore lam (directionRow o e c w)
              ≤ ∑ _w ∈ Finset.univ.erase v, 2 ^ (n - 2) :=
                Finset.sum_le_sum hbound
            _ = (s - 1) * 2 ^ (n - 2) := by
                rw [Finset.sum_const, hcard, smul_eq_mul]
            _ ≤ 3 * 2 ^ (n - 2) :=
                Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ n + 2 ^ (n - 2) := by
        have h1 : (2 : ℕ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
          conv_lhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
          ring
        have h2 : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
          conv_lhs => rw [show n = n - 2 + 2 by omega, pow_add]
          ring
        rw [h1, h2]
        ring

/-- **Bottom-clump capacity.**  With a unique saturated center `v`, in a
chart where the anchor rays lie in `[0, δλ]` (supplied upstream by
`saturated_chord_corridor`), all non-anchor chord directions lie in the
corridor `[λ, π − λ + δλ]` of width `(n + 2δ − 2)λ < nλ`, so a uniform
`n`-bin cover of width `< λ` exists.  If some non-anchor row `i*` has all
its chord directions inside `[λ, λ + w₀)` with `w₀·n < π − λ`, a cover of
width `> w₀` puts all of `i*`'s chords into bin `0`.  Its encoding cube
then has volume `2^{n−1}` while its defect `≥ 2` bounds the actual weight
by `2^{n−2}`: the resulting `2^{n−2}` slack is exactly the quarter-cube
saving needed, so `potential ≤ 2^n + 2^{n−2} = sendovCap n true`.

This covers the tight equality family of `notes/AVERAGED_BIN_PACKING.md`:
its slack row `Q` has both chord directions at `9λ/8` and `5λ/4`, lying in
`[λ, λ + λ/3)`, and `λn/3 < π − λ` holds for `n ≥ 3`.  The hypothesis is
chart-relative: `dirRep` values are taken in the same chart in which
`theta` realizes the anchor rays, and the interval's left endpoint is
fixed at `λ` — middle-seated narrow rows are NOT covered. -/
theorem potential_le_high_of_saturated_clump {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 1 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (_hsat : rowDefect n lam (directionRow o e c v) = 1)
    (huniq : ∀ i : Fin s,
      2 ≤ rowDefect n lam (directionRow o e c (v.succAbove i)))
    {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    {w0 : ℝ} (hw0 : w0 * (n : ℝ) < Real.pi - lam)
    (istar : Fin s)
    (hclump : ∀ j : Fin s, j ≠ istar →
      dirRep o e (c ∘ v.succAbove) istar j ∈ Set.Ico lam (lam + w0)) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnge : (0 : ℝ) < n := by linarith
  have hnne : (n : ℝ) ≠ 0 := hnge.ne'
  have hlampi : lam < Real.pi := by nlinarith
  have hdel : Real.pi - n * lam < lam := by nlinarith
  -- Chord corridor with `beta = δλ`.
  have hcorr : ∀ i j : Fin s, i ≠ j →
      dirRep o e (c ∘ v.succAbove) i j
        ∈ Set.Icc lam (Real.pi - lam + (Real.pi - n * lam)) := by
    intro i j hij
    have hcij : v.succAbove i ≠ v.succAbove j :=
      fun h => hij (Fin.succAbove_right_injective h)
    exact chord_in_corridor o he
      (fun h => Fin.succAbove_ne v i (hleg.inj h))
      (fun h => Fin.succAbove_ne v j (hleg.inj h))
      (fun h => hcij (hleg.inj h))
      hdel (by linarith)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  -- `n` uniform bins of width `< λ` covering the corridor `[λ, π−λ+δλ]`;
  -- the width is chosen `> w0` so the clumped row lands in a single bin.
  set W : ℝ := Real.pi - 2 * lam + (Real.pi - n * lam) with hW
  set B : ℝ := (Real.pi - lam) / n with hB
  set width : ℝ := max (W / n) ((w0 + B) / 2) with hwidth_def
  have hWpos : 0 < W := by dsimp [W]; nlinarith
  have hWlt : W < (n : ℝ) * lam := by
    dsimp [W]; nlinarith
  have hWB : W / n < B := by
    rw [hB, div_lt_div_iff_of_pos_right hnge]
    dsimp [W]; nlinarith
  have hw0B : w0 < B := by
    rwa [hB, lt_div_iff₀ hnge]
  have hmid : (w0 + B) / 2 < B := by linarith
  have hwidth : width < lam := by
    rw [hwidth_def]
    apply max_lt
    · exact hWB.trans (by rw [hB, div_lt_iff₀ hnge]; nlinarith)
    · exact hmid.trans (by rw [hB, div_lt_iff₀ hnge]; nlinarith)
  have hw : 0 < width := by
    rw [hwidth_def]
    exact lt_max_of_lt_left (div_pos hWpos hnge)
  have hgtw0 : w0 < width := by
    rw [hwidth_def]
    exact lt_of_lt_of_le (by linarith : w0 < (w0 + B) / 2)
      (le_max_right _ _)
  have hnwW : W ≤ (n : ℝ) * width := by
    rw [hwidth_def]
    calc W = (n : ℝ) * (W / n) := by
          rw [mul_comm]; exact (div_mul_cancel₀ W hnne).symm
      _ ≤ (n : ℝ) * width :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hnge.le
  have hnB : (n : ℝ) * B = Real.pi - lam := by
    rw [hB]; field_simp
  have hnwlt : (n : ℝ) * width < Real.pi - lam := by
    have h2 : (n : ℝ) * ((w0 + B) / 2) < Real.pi - lam := by
      nlinarith [hw0, hnB]
    rw [hwidth_def]
    by_cases hmax : (w0 + B) / 2 ≤ W / n
    · rw [max_eq_left hmax]
      have hWn : (n : ℝ) * (W / n) = W := by
        rw [mul_comm]; exact div_mul_cancel₀ W hnne
      rw [hWn]; rw [hW]; nlinarith
    · rw [max_eq_right (le_of_lt (not_le.mp hmax))]; exact h2
  let p := c ∘ v.succAbove
  have hp : Function.Injective p :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hpos : ∀ i j : Fin s, i ≠ j →
      dirRep o e p i j ∈ Set.Icc lam (lam + (n : ℝ) * width) := by
    intro i j hij
    refine ⟨(hcorr i j hij).1, ?_⟩
    have h2 := (hcorr i j hij).2
    have hW' := hnwW
    rw [hW] at hW'
    linarith
  have hangle : ∀ i j k : Fin s, i ≠ j → i ≠ k → j ≠ k →
      ∠ (p i) (p j) (p k) ≤ Real.pi - lam := by
    intro i j k hij hik hjk
    exact hleg.triAngle _ _ _
      (fun h => hij (Fin.succAbove_right_injective h))
      (fun h => hjk (Fin.succAbove_right_injective h))
      (fun h => hik (Fin.succAbove_right_injective h))
  have hbins := directionBinGraph_row_weighted_bound o e p he hp
    (m := n) (by omega) hw hwidth hlam.le (by linarith) hangle hpos
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdel.le (htheta i).1, (htheta i).2⟩
  have hlocal (i : Fin s) :
      rowScore lam (directionRow o e c (v.succAbove i)) ≤
        n - ((directionRow o e p i).map
          (uniformBin lam width n)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlampi
      theta htheta' (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval (m := n) (by omega) hw hwidth
    · linarith [(htheta i).1.1]
    · linarith [(htheta i).1.2, hnwW, hW]
    · exact directionRow_sorted o e p i
    · intro x hx
      obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e p).mp hx
      exact hpos i j hji.symm
  -- The clumped row occupies a single bin: all its chord directions lie
  -- in `[λ, λ + w₀)` and `w₀ < width`, so `uniformBin` maps them all to 0.
  have hbin0 : ∀ x ∈ directionRow o e p istar,
      uniformBin lam width n x = 0 := by
    intro x hx
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e p).mp hx
    have hmem := hclump j hji
    have hlt : (dirRep o e p istar j - lam) / width < 1 := by
      rw [div_lt_one hw]
      linarith [hmem.1, hmem.2, hgtw0]
    unfold uniformBin
    rw [Nat.floor_eq_zero.mpr hlt]
    exact Nat.min_eq_left (Nat.zero_le _)
  have hstar_card : ((directionRow o e p istar).map
      (uniformBin lam width n)).toFinset.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro a b ha hb
    rw [List.mem_toFinset, List.mem_map] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [hbin0 x hx, hbin0 y hy]
  -- Its defect `≥ 2` bounds the weight by `2^{n−2}` while the cube bound
  -- gives `2^{n−1}`: the difference is the needed `2^{n−2}` slack.
  have hkstar : rowScore lam (directionRow o e c (v.succAbove istar))
      ≤ n - 2 := by
    have hcells : rowCells lam (directionRow o e c (v.succAbove istar))
        ≤ n :=
      rowCells_directionRow_le_of_floor_eq o e c hlam _ (by omega) hn
    rw [rowScore_eq_sub_defect lam hlam n _ hcells]
    have := huniq istar
    omega
  have hstar : 2 ^ rowScore lam (directionRow o e c (v.succAbove istar))
      + 2 ^ (n - 2) ≤
      2 ^ (n - ((directionRow o e p istar).map
        (uniformBin lam width n)).toFinset.card) := by
    have hstep : (2 : ℕ) ^ (n - 2) + 2 ^ (n - 2) = 2 ^ (n - 1) := by
      have h1 : (2 : ℕ) ^ (n - 1) = 2 ^ (n - 2) * 2 := by
        conv_lhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
      omega
    calc 2 ^ rowScore lam (directionRow o e c (v.succAbove istar))
          + 2 ^ (n - 2)
        ≤ 2 ^ (n - 2) + 2 ^ (n - 2) :=
          Nat.add_le_add
            (Nat.pow_le_pow_right (by omega) hkstar) le_rfl
      _ = 2 ^ (n - 1) := hstep
      _ ≤ 2 ^ (n - ((directionRow o e p istar).map
            (uniformBin lam width n)).toFinset.card) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  have hrest : (∑ i : Fin s,
      2 ^ rowScore lam (directionRow o e c (v.succAbove i)))
      + 2 ^ (n - 2) ≤ 2 ^ n := by
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun i : Fin s =>
        2 ^ rowScore lam (directionRow o e c (v.succAbove i)))
      (Finset.mem_univ istar)]
    calc (2 ^ rowScore lam (directionRow o e c (v.succAbove istar))
            + ∑ i ∈ Finset.univ.erase istar,
                2 ^ rowScore lam (directionRow o e c (v.succAbove i)))
          + 2 ^ (n - 2)
        = (2 ^ rowScore lam (directionRow o e c (v.succAbove istar))
            + 2 ^ (n - 2))
          + ∑ i ∈ Finset.univ.erase istar,
              2 ^ rowScore lam (directionRow o e c (v.succAbove i)) :=
          add_right_comm _ _ _
      _ ≤ 2 ^ (n - ((directionRow o e p istar).map
              (uniformBin lam width n)).toFinset.card)
          + ∑ i ∈ Finset.univ.erase istar,
              2 ^ (n - ((directionRow o e p i).map
                (uniformBin lam width n)).toFinset.card) :=
          Nat.add_le_add hstar (Finset.sum_le_sum (fun i _ =>
            Nat.pow_le_pow_right (by omega) (hlocal i)))
      _ = ∑ i : Fin s, 2 ^ (n - ((directionRow o e p i).map
            (uniformBin lam width n)).toFinset.card) :=
          Finset.add_sum_erase (s := Finset.univ)
            (f := fun i : Fin s => 2 ^ (n - ((directionRow o e p i).map
              (uniformBin lam width n)).toFinset.card))
            (Finset.mem_univ istar)
      _ ≤ 2 ^ n := hbins
  have hv : rowScore lam (directionRow o e c v) ≤ n - 1 := by
    have h := directionRow_score_le_floor' o e c (by omega) hlam v
    rwa [hn] at h
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  calc 2 ^ rowScore lam (directionRow o e c v) +
        ∑ i : Fin s, 2 ^ rowScore lam (directionRow o e c
          (v.succAbove i))
      ≤ 2 ^ (n - 1) + (2 ^ n - 2 ^ (n - 2)) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by omega) hv)
          (Nat.le_sub_of_add_le hrest)
    _ = 2 ^ n + 2 ^ (n - 2) := by
        have h1 : (2 : ℕ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
          conv_lhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
          ring
        have h2 : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
          conv_lhs => rw [show n = n - 2 + 2 by omega, pow_add]
          ring
        rw [h1, h2]
        omega

/-- **Slack-certificate family.**  Under the worst-case `n`-bin corridor
cover of width `width < λ`, if a family `T` of non-anchor rows each
occupies at most `r` bins (`card ≤ r`) and has defect `≥ r+1`, then
each contributes slack `≥ 2^{n−r−1}`; with `|T| ≥ 2^{r−1}` the total
slack is `≥ 2^{n−2}` — the whole quarter-cube.  This is the
`1 ≤ r < n` certificate family of
`notes/ONE_SATURATED_HIGH_RESEARCH.md`: `r = 1`, `|T| = 1` is the
clump theorem (occupancy `≤ 1`, defect `≥ 2`); `r = 2`, `|T| = 2` is
the two small-row certificate.  The premises are geometric/bin-level,
not a renamed aggregate bound. -/
theorem potential_le_high_of_saturated_slack_family {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 1 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    {width : ℝ} (hw : 0 < width) (hwidth : width < lam)
    (hcover : Real.pi - 2 * lam + (Real.pi - n * lam) ≤
      (n : ℝ) * width)
    (hcoverlt : (n : ℝ) * width < Real.pi - lam)
    (T : Finset (Fin s)) {r : ℕ} (hr1 : 1 ≤ r) (hrn : r + 1 ≤ n)
    (hocc : ∀ i ∈ T, ((directionRow o e (c ∘ v.succAbove) i).map
      (uniformBin lam width n)).toFinset.card ≤ r)
    (hdef : ∀ i ∈ T, r + 1 ≤
      rowDefect n lam (directionRow o e c (v.succAbove i)))
    (hcard : 2 ^ (r - 1) ≤ T.card) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnge : (0 : ℝ) < n := by linarith
  have hlampi : lam < Real.pi := by nlinarith
  have hdel : Real.pi - n * lam < lam := by nlinarith
  have hcorr : ∀ i j : Fin s, i ≠ j →
      dirRep o e (c ∘ v.succAbove) i j
        ∈ Set.Icc lam (Real.pi - lam + (Real.pi - n * lam)) := by
    intro i j hij
    have hcij : v.succAbove i ≠ v.succAbove j :=
      fun h => hij (Fin.succAbove_right_injective h)
    exact chord_in_corridor o he
      (fun h => Fin.succAbove_ne v i (hleg.inj h))
      (fun h => Fin.succAbove_ne v j (hleg.inj h))
      (fun h => hcij (hleg.inj h))
      hdel (by linarith)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  set W : ℝ := Real.pi - 2 * lam + (Real.pi - n * lam) with hW
  have hWpos : 0 < W := by dsimp [W]; nlinarith
  have hp : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hpos : ∀ i j : Fin s, i ≠ j →
      dirRep o e (c ∘ v.succAbove) i j ∈
        Set.Icc lam (lam + (n : ℝ) * width) := by
    intro i j hij
    refine ⟨(hcorr i j hij).1, ?_⟩
    have h2 := (hcorr i j hij).2
    have hW' := hcover
    rw [hW] at hW'
    linarith
  have hangle : ∀ i j k : Fin s, i ≠ j → i ≠ k → j ≠ k →
      ∠ ((c ∘ v.succAbove) i) ((c ∘ v.succAbove) j)
        ((c ∘ v.succAbove) k) ≤ Real.pi - lam := by
    intro i j k hij hik hjk
    exact hleg.triAngle _ _ _
      (fun h => hij (Fin.succAbove_right_injective h))
      (fun h => hjk (Fin.succAbove_right_injective h))
      (fun h => hik (Fin.succAbove_right_injective h))
  have hbins := directionBinGraph_row_weighted_bound o e
    (c ∘ v.succAbove) he hp (m := n) (by omega) hw hwidth hlam.le
    (by linarith) hangle hpos
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdel.le (htheta i).1, (htheta i).2⟩
  have hlocal (i : Fin s) :
      rowScore lam (directionRow o e c (v.succAbove i)) ≤
        n - ((directionRow o e (c ∘ v.succAbove) i).map
          (uniformBin lam width n)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlampi
      theta htheta' (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval (m := n) (by omega) hw hwidth
    · linarith [(htheta i).1.1]
    · have h1 := (htheta i).1.2
      have h2 := hcover
      rw [hW] at h2
      linarith
    · exact directionRow_sorted o e (c ∘ v.succAbove) i
    · intro x hx
      obtain ⟨j, hji, rfl⟩ :=
        (mem_directionRow o e (c ∘ v.succAbove)).mp hx
      exact hpos i j hji.symm
  -- Each certified row: defect ≥ r+1 bounds its weight by `2^{n−r−1}`
  -- while occupancy ≤ r bounds its cube below by `2^{n−r}`.
  have hslack : ∀ i ∈ T,
      2 ^ rowScore lam (directionRow o e c (v.succAbove i)) +
        2 ^ (n - (r + 1)) ≤
      2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) := by
    intro i hi
    have hki : rowScore lam (directionRow o e c (v.succAbove i)) ≤
        n - (r + 1) := by
      have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam
        (v.succAbove i) (by omega) hn
      rw [rowScore_eq_sub_defect lam hlam n _ hcells]
      have := hdef i hi
      omega
    have hstep : (2 : ℕ) ^ (n - (r + 1)) + 2 ^ (n - (r + 1)) =
        2 ^ (n - r) := by
      conv_rhs => rw [show n - r = n - (r + 1) + 1 by omega, pow_succ]
      ring
    calc 2 ^ rowScore lam (directionRow o e c (v.succAbove i)) +
          2 ^ (n - (r + 1))
        ≤ 2 ^ (n - (r + 1)) + 2 ^ (n - (r + 1)) :=
          Nat.add_le_add (Nat.pow_le_pow_right (by omega) hki) le_rfl
      _ = 2 ^ (n - r) := hstep
      _ ≤ 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
            (uniformBin lam width n)).toFinset.card) :=
          Nat.pow_le_pow_right (by omega) (by
            have := hocc i hi; omega)
  have hT : (∑ i ∈ T, 2 ^ rowScore lam (directionRow o e c
        (v.succAbove i))) + 2 ^ (n - 2) ≤
      ∑ i ∈ T, 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) := by
    have h2 := Finset.sum_le_sum hslack
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (2 : ℕ) ^ (n - 2) ≤ T.card * 2 ^ (n - (r + 1)) := by
      have h4 : (2 : ℕ) ^ (n - 2) =
          2 ^ (r - 1) * 2 ^ (n - (r + 1)) := by
        conv_lhs => rw [show n - 2 = (r - 1) + (n - (r + 1)) by omega,
          pow_add]
      rw [h4]
      exact Nat.mul_le_mul_right _ hcard
    exact (Nat.add_le_add_left h3 _).trans h2
  have hrest : (∑ i : Fin s,
      2 ^ rowScore lam (directionRow o e c (v.succAbove i)))
      + 2 ^ (n - 2) ≤ 2 ^ n := by
    rw [← Finset.sum_sdiff (Finset.subset_univ T)]
    calc (∑ i ∈ Finset.univ \ T, 2 ^ rowScore lam (directionRow o e c
              (v.succAbove i))
            + ∑ i ∈ T, 2 ^ rowScore lam (directionRow o e c
              (v.succAbove i))) + 2 ^ (n - 2)
        = (∑ i ∈ T, 2 ^ rowScore lam (directionRow o e c
              (v.succAbove i)) + 2 ^ (n - 2))
          + ∑ i ∈ Finset.univ \ T, 2 ^ rowScore lam (directionRow o e c
              (v.succAbove i)) := by omega
      _ ≤ (∑ i ∈ T, 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
              (uniformBin lam width n)).toFinset.card))
          + ∑ i ∈ Finset.univ \ T,
              2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
                (uniformBin lam width n)).toFinset.card) :=
          Nat.add_le_add hT (Finset.sum_le_sum (fun i _ =>
            Nat.pow_le_pow_right (by omega) (hlocal i)))
      _ = ∑ i : Fin s, 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
            (uniformBin lam width n)).toFinset.card) := by
          rw [add_comm, Finset.sum_sdiff (Finset.subset_univ T)]
      _ ≤ 2 ^ n := hbins
  have hv : rowScore lam (directionRow o e c v) ≤ n - 1 := by
    have h := directionRow_score_le_floor' o e c (by omega) hlam v
    rwa [hn] at h
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  calc 2 ^ rowScore lam (directionRow o e c v) +
        ∑ i : Fin s, 2 ^ rowScore lam (directionRow o e c
          (v.succAbove i))
      ≤ 2 ^ (n - 1) + (2 ^ n - 2 ^ (n - 2)) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by omega) hv)
          (Nat.le_sub_of_add_le hrest)
    _ = 2 ^ n + 2 ^ (n - 2) := by
        have h1 : (2 : ℕ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
          conv_lhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
          ring
        have h2 : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
          conv_lhs => rw [show n = n - 2 + 2 by omega, pow_add]
          ring
        rw [h1, h2]
        omega

/-- **Single-outlier deletion closure.**  If deleting one non-anchor
center `q` leaves every pair of surviving anchor rays within
`β < α = (n+1)λ − π`, then `potential ≤ 2^n + 2^{n−2}`: the deleted
row's weight `≤ 2^{n−2}` (defect `≥ 2`) is paid explicitly, and the
narrow-window bound `≤ 2^n` applies to the sub-configuration
`c ∘ q.succAbove`.  The anchor stays saturated after deletion because
erasing a direction never lowers a row score (`rowScore_eraseIdx'`)
while no row score exceeds `n−1` (`one_le_rowDefect`).  No removability
of `q` is required, and other rows are allowed to become saturated in
the sub-configuration. -/
theorem potential_le_high_of_saturated_delete_narrow {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v q : Fin (s + 1)) (hvq : v ≠ q)
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hq : 2 ≤ rowDefect n lam (directionRow o e c q))
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    {beta : ℝ} (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin (s + 1), i ≠ v → j ≠ v → i ≠ q → j ≠ q →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ beta) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq hvq
  have hleg' : Section4Legality (c ∘ q.succAbove) lam := hleg.erase q
  have hrowv : directionRow o e (c ∘ q.succAbove) v' =
      (directionRow o e c v).eraseIdx (deleteIndex o e c q v) := by
    have h := eraseIdx_directionRow o e (c' := c) q v'
    rwa [hv'] at h
  have hscv : rowScore lam (directionRow o e c v) = n - 1 := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam v
      (by omega) hn
    rw [rowScore_eq_sub_defect lam hlam n _ hcells, hsat]
  have hsat' : rowDefect n lam (directionRow o e (c ∘ q.succAbove) v')
      = 1 := by
    have hcells' := rowCells_directionRow_le_of_floor_eq o e
      (c ∘ q.succAbove) hlam v' hs hn
    have hge : n - 1 ≤
        rowScore lam (directionRow o e (c ∘ q.succAbove) v') := by
      rw [hrowv, rowScore_eraseIdx' hlam (directionRow_sorted o e c v)
          (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
          (deleteIndex_lt o e c hvq)
          (by rw [directionRow_length o e c v]; omega), hscv]
      exact Nat.le_add_right _ _
    have hle : rowScore lam (directionRow o e (c ∘ q.succAbove) v') ≤
        n - 1 := by
      rw [rowScore_eq_sub_defect lam hlam n _ hcells']
      have h1 := one_le_rowDefect lam hlam n _ (by omega) hcells'
      omega
    have hsc : rowScore lam (directionRow o e (c ∘ q.succAbove) v') =
        n - 1 := le_antisymm hle hge
    have := rowScore_eq_sub_defect lam hlam n _ hcells'
    omega
  have hspread' : ∀ i j : Fin s, i ≠ v' → j ≠ v' →
      InnerProductGeometry.angle
        ((c ∘ q.succAbove) i - (c ∘ q.succAbove) v')
        ((c ∘ q.succAbove) j - (c ∘ q.succAbove) v') ≤ beta := by
    intro i' j' hi' hj'
    have hvi : q.succAbove i' ≠ v := by
      rw [← hv']; exact fun h => hi' (Fin.succAbove_right_injective h)
    have hvj : q.succAbove j' ≠ v := by
      rw [← hv']; exact fun h => hj' (Fin.succAbove_right_injective h)
    simpa [Function.comp_apply, hv'] using
      hspread (q.succAbove i') (q.succAbove j') hvi hvj
        (Fin.succAbove_ne q i') (Fin.succAbove_ne q j')
  have hcap : potential lam (directionRows o e (c ∘ q.succAbove)) ≤
      2 ^ n :=
    potential_le_two_pow_of_saturated_narrow o e he hs hn3 hlam hn
      hleg' v' hsat' hδ hbeta hspread'
  have hmain : potential lam (directionRows o e c) ≤
      2 ^ (n - 2) +
        potential lam (directionRows o e (c ∘ q.succAbove)) := by
    have hrow : ∀ i' : Fin s,
        rowScore lam (directionRow o e c (q.succAbove i')) ≤
          rowScore lam (directionRow o e (c ∘ q.succAbove) i') := by
      intro i'
      rw [eraseIdx_directionRow o e (c' := c) q i',
        rowScore_eraseIdx' hlam (directionRow_sorted o e c _)
          (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
          (deleteIndex_lt o e c (Fin.succAbove_ne q i'))
          (by rw [directionRow_length o e c _]; omega)]
      exact Nat.le_add_right _ _
    have hqexp : rowScore lam (directionRow o e c q) ≤ n - 2 := by
      have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam q
        (by omega) hn
      rw [rowScore_eq_sub_defect lam hlam n _ hcells]
      omega
    unfold potential exponentAt directionRows
    rw [Fin.sum_univ_succAbove _ q]
    have hstep :
        2 ^ rowScore lam (directionRow o e c q) +
            ∑ t : Fin s, 2 ^ rowScore lam (directionRow o e c
              (q.succAbove t))
          ≤ 2 ^ (n - 2) +
            ∑ t : Fin s, 2 ^ rowScore lam
              (directionRow o e (c ∘ q.succAbove) t) :=
      Nat.add_le_add (Nat.pow_le_pow_right (by omega) hqexp)
        (Finset.sum_le_sum fun t _ =>
          Nat.pow_le_pow_right (by omega) (hrow t))
    exact hstep
  omega

/-- **One high outlier.**  In the saturated-corridor chart, if all anchor
rays except possibly the one toward `q` lie strictly below
`α = (n+1)λ − π`, the cap follows: the surviving rays are pairwise within
`max θ < α`, and the outlier's row weight is paid as `2^{n−2}`.  This is
the direct corollary of `potential_le_high_of_saturated_delete_narrow`
covering "a single ray reaches `α` or beyond". -/
theorem potential_le_high_of_saturated_one_outlier {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (iqr : Fin s)
    (hqdef : 2 ≤ rowDefect n lam (directionRow o e c (v.succAbove iqr)))
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    (hlow : ∀ i : Fin s, i ≠ iqr →
      theta i < ((n : ℝ) + 1) * lam - Real.pi) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_ne
    (by rw [Finset.card_univ, Fintype.card_fin]; exact hs) iqr
  have hSne : (Finset.univ.erase iqr).Nonempty :=
    ⟨j₀, Finset.mem_erase.mpr ⟨hj₀, Finset.mem_univ _⟩⟩
  set M := (Finset.univ.erase iqr).sup' hSne theta with hM
  obtain ⟨t, htm, hteq⟩ := Finset.exists_mem_eq_sup' hSne theta
  have hMlt : M < ((n : ℝ) + 1) * lam - Real.pi := by
    rw [hM, hteq]
    exact hlow t (Finset.mem_erase.mp htm).1
  have htle (i : Fin s) (hi : i ≠ iqr) : theta i ≤ M := by
    rw [hM]
    exact Finset.le_sup' theta
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  apply potential_le_high_of_saturated_delete_narrow o e he hs hn3 hlam
    hn hleg v (v.succAbove iqr) (Fin.ne_succAbove v iqr) hsat hqdef hδ hMlt
  intro i j hiv hjv hiq hjq
  obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hiv
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjv
  have hii : i' ≠ iqr := fun h => hiq (h ▸ rfl)
  have hjj : j' ≠ iqr := fun h => hjq (h ▸ rfl)
  have hico : ∀ t : Fin s, theta t ∈ Set.Ico 0 Real.pi := fun t =>
    ⟨(htheta t).1.1,
      by nlinarith [(htheta t).1.2, hfloor', hnreal, hlam]⟩
  rw [angle_eq_abs_of_half_plane_chart o he
    (sub_ne_zero.mpr (fun h => (Fin.ne_succAbove v i').symm (hleg.inj h)))
    (sub_ne_zero.mpr (fun h => (Fin.ne_succAbove v j').symm (hleg.inj h)))
    (hico i') (hico j') (htheta i').2 (htheta j').2]
  exact abs_le.mpr
    ⟨by linarith [(htheta j').1.1, htle i' hii],
      by linarith [htle j' hjj, (htheta i').1.1]⟩

#print axioms one_saturated_capacity_of_narrow_window
#print axioms potential_le_two_pow_of_saturated_narrow
#print axioms potential_le_high_of_saturated_small
#print axioms potential_le_high_of_saturated_clump
#print axioms potential_le_high_of_saturated_slack_family
#print axioms potential_le_high_of_saturated_delete_narrow
#print axioms potential_le_high_of_saturated_one_outlier

end Jsp404
