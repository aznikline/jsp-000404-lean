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

/-- **Volume obstruction.**  Five or more non-anchor rows cannot contain
four defect-`2` rows: each has score `n−2`, hence occupies at most two
bins and contributes cube volume `≥ 2^{n−2}`; four of them already
exhaust the `2^n` bin-graph budget, leaving no room for a fifth row.
Consequently any residual configuration with `s ≥ 5` non-anchor rows has
at least `s − 4 ≥ 1` rows of defect `≥ 3`. -/
theorem defect_two_rows_le_three {s n : ℕ}
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
    (hs5 : 5 ≤ s)
    (T : Finset (Fin s))
    (hdef : ∀ i ∈ T, rowDefect n lam
      (directionRow o e c (v.succAbove i)) = 2) :
    T.card ≤ 3 := by
  classical
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    nlinarith
  have hdel : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    nlinarith
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
      hdel (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij
        (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  set W : ℝ := Real.pi - 2 * lam + (Real.pi - n * lam) with hW
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
    (by linarith [hcoverlt]) hangle hpos
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdel.le (htheta i).1,
      (htheta i).2⟩
  have hlocal (i : Fin s) :
      rowScore lam (directionRow o e c (v.succAbove i)) ≤
        n - ((directionRow o e (c ∘ v.succAbove) i).map
          (uniformBin lam width n)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlampi
      theta htheta' (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval (m := n) (by omega) hw
      hwidth
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
  -- defect `2` gives score `n−2`, hence at most two occupied bins.
  have hcube : ∀ i ∈ T, 2 ^ (n - 2) ≤
      2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) := by
    intro i hi
    have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam
      (v.succAbove i) (by omega) hn
    have hscore : rowScore lam (directionRow o e c (v.succAbove i)) =
        n - 2 := by
      rw [rowScore_eq_sub_defect lam hlam n _ hcells, hdef i hi]
    have h2 := hlocal i
    rw [hscore] at h2
    exact Nat.pow_le_pow_right (by omega) (by omega)
  by_contra hT
  push_neg at hT
  obtain ⟨T4, hT4sub, hT4card⟩ :=
    T.exists_subset_card_eq (n := 4) (by omega)
  have hsum4 : 4 * 2 ^ (n - 2) ≤
      ∑ i ∈ T4, 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) := by
    have h := Finset.sum_le_sum (fun i hi => hcube i (hT4sub hi))
    rwa [Finset.sum_const, hT4card, nsmul_eq_mul, Nat.cast_ofNat] at h
  -- A fifth row exists and contributes a positive cube.
  obtain ⟨j, -, hjT4⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := T4) (t := Finset.univ) (by
      rw [hT4card, Finset.card_univ, Fintype.card_fin]; omega)
  have hcompl : 1 ≤
      ∑ i ∈ Finset.univ \ T4, 2 ^ (n - ((directionRow o e
        (c ∘ v.succAbove) i).map
          (uniformBin lam width n)).toFinset.card) :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le _)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjT4⟩)).trans'
      (Nat.one_le_pow _ _ (by omega))
  have h2n : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  have hsplit : ∑ i : Fin s,
      2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card)
      = ∑ i ∈ Finset.univ \ T4, 2 ^ (n - ((directionRow o e
            (c ∘ v.succAbove) i).map
              (uniformBin lam width n)).toFinset.card)
        + ∑ i ∈ T4, 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
              (uniformBin lam width n)).toFinset.card) :=
    (Finset.sum_sdiff (Finset.subset_univ T4)).symm
  have hadd := Nat.add_le_add hcompl hsum4
  omega

/-- **Perfect tiling (boundary case).**  With exactly four non-anchor rows
all of defect `2`, the cube volumes sum to exactly `2^n`: every row
occupies precisely two bins and the bin-graph budget is saturated — the
rigid configuration a geometric sliver argument must rule out. -/
theorem four_defect_two_tiling {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (_hs : 1 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
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
    (hs4 : s = 4)
    (hdef : ∀ i : Fin s, rowDefect n lam
      (directionRow o e c (v.succAbove i)) = 2) :
    (∀ i : Fin s, ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card = 2) ∧
    ∑ i : Fin s, 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) = 2 ^ n := by
  classical
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    nlinarith
  have hdel : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    nlinarith
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
      hdel (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij
        (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  set W : ℝ := Real.pi - 2 * lam + (Real.pi - n * lam) with hW
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
    (by linarith [hcoverlt]) hangle hpos
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdel.le (htheta i).1,
      (htheta i).2⟩
  have hlocal (i : Fin s) :
      rowScore lam (directionRow o e c (v.succAbove i)) ≤
        n - ((directionRow o e (c ∘ v.succAbove) i).map
          (uniformBin lam width n)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlampi
      theta htheta' (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval (m := n) (by omega) hw
      hwidth
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
  have hocc : ∀ i : Fin s, ((directionRow o e (c ∘ v.succAbove) i).map
      (uniformBin lam width n)).toFinset.card ≤ 2 := by
    intro i
    have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam
      (v.succAbove i) (by omega) hn
    have hscore : rowScore lam (directionRow o e c (v.succAbove i)) =
        n - 2 := by
      rw [rowScore_eq_sub_defect lam hlam n _ hcells, hdef i]
    have h2 := hlocal i
    rw [hscore] at h2
    omega
  have hcube : ∀ i ∈ Finset.univ, (2 : ℕ) ^ (n - 2) ≤
      2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) :=
    fun i _ => Nat.pow_le_pow_right (by omega) (by
      have := hocc i; omega)
  have hcard4 : (Finset.univ : Finset (Fin s)).card = 4 := by
    rw [Finset.card_univ, Fintype.card_fin, hs4]
  have h2n : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  have hsum : ∑ i : Fin s, 2 ^ (n - ((directionRow o e
        (c ∘ v.succAbove) i).map
          (uniformBin lam width n)).toFinset.card) = 2 ^ n := by
    apply le_antisymm hbins
    have h := Finset.sum_le_sum hcube
    rw [Finset.sum_const, hcard4, nsmul_eq_mul] at h
    rwa [h2n]
  refine ⟨fun i => ?_, hsum⟩
  have heq := (Finset.sum_eq_sum_iff_of_le hcube).mp (by
    rw [Finset.sum_const, hcard4, nsmul_eq_mul, Nat.cast_ofNat, ← h2n,
      hsum]) i (Finset.mem_univ i)
  have ha2 := Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    (show (2 : ℕ) ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) = 2 ^ (n - 2)
      from heq.symm)
  have := hocc i
  omega

/-- **Three-row tightness.**  With `s ≥ 4` non-anchor rows, a family `T`
of three defect-`2` rows cannot include a row occupying only one bin:
its cube would be `≥ 2^{n−1}` and, together with the other two rows'
`≥ 2^{n−2}` each and a fourth row's positive cube, the volume bound
`∑ ≤ 2^n` would be violated.  Hence every defect-`2` row in a
three-element family occupies **exactly two** bins — the rigid
zero-slack pattern (`S_i = 0`) whose geometric exclusion is the
five-point residual obligation. -/
theorem three_defect_two_rows_tight {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
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
    (hs4 : 4 ≤ s)
    (T : Finset (Fin s)) (hTcard : T.card = 3)
    (hdef : ∀ i ∈ T, rowDefect n lam
      (directionRow o e c (v.succAbove i)) = 2)
    (i : Fin s) (hi : i ∈ T) :
    ((directionRow o e (c ∘ v.succAbove) i).map
      (uniformBin lam width n)).toFinset.card = 2 := by
  classical
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    nlinarith
  have hdel : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    nlinarith
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
      hdel (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij
        (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  set W : ℝ := Real.pi - 2 * lam + (Real.pi - n * lam) with hW
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
    (by linarith [hcoverlt]) hangle hpos
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdel.le (htheta i).1,
      (htheta i).2⟩
  have hlocal (i : Fin s) :
      rowScore lam (directionRow o e c (v.succAbove i)) ≤
        n - ((directionRow o e (c ∘ v.succAbove) i).map
          (uniformBin lam width n)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlampi
      theta htheta' (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval (m := n) (by omega) hw
      hwidth
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
  have hocc : ∀ i ∈ T, ((directionRow o e (c ∘ v.succAbove) i).map
      (uniformBin lam width n)).toFinset.card ≤ 2 := by
    intro i hi
    have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam
      (v.succAbove i) (by omega) hn
    have hscore : rowScore lam (directionRow o e c (v.succAbove i)) =
        n - 2 := by
      rw [rowScore_eq_sub_defect lam hlam n _ hcells, hdef i hi]
    have h2 := hlocal i
    rw [hscore] at h2
    omega
  have h2n : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    omega
  have h2n1 : (2 : ℕ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
    ring
  -- Suppose `i` occupies only one bin: its cube is `≥ 2^{n−1}`.
  by_contra hne
  have hoci1 : ((directionRow o e (c ∘ v.succAbove) i).map
      (uniformBin lam width n)).toFinset.card ≤ 1 := by
    have h := hocc i hi
    omega
  have hbig : 2 ^ (n - 1) ≤
      2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  -- Two further defect-`2` rows.
  have hT'card : (T.erase i).card = 2 := by
    rw [Finset.card_erase_of_mem hi, hTcard]
  obtain ⟨j1, j2, h12, hT'⟩ := Finset.card_eq_two.mp hT'card
  have hj1T : j1 ∈ T := Finset.mem_of_mem_erase
    (hT' ▸ Finset.mem_insert_self j1 {j2})
  have hj2T : j2 ∈ T := Finset.mem_of_mem_erase
    (hT' ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j2))
  have hj1i : j1 ≠ i := fun h =>
    (Finset.mem_erase.mp (hT' ▸ Finset.mem_insert_self j1 {j2})).1 h
  have hj2i : j2 ≠ i := fun h =>
    (Finset.mem_erase.mp (hT' ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self j2))).1 h
  have hcj1 : 2 ^ (n - 2) ≤
      2 ^ (n - ((directionRow o e (c ∘ v.succAbove) j1).map
        (uniformBin lam width n)).toFinset.card) := by
    have h := hocc j1 hj1T
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hcj2 : 2 ^ (n - 2) ≤
      2 ^ (n - ((directionRow o e (c ∘ v.succAbove) j2).map
        (uniformBin lam width n)).toFinset.card) := by
    have h := hocc j2 hj2T
    exact Nat.pow_le_pow_right (by omega) (by omega)
  -- A fourth row contributes a positive cube.
  obtain ⟨k, -, hkT⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := T) (t := Finset.univ) (by
      rw [hTcard, Finset.card_univ, Fintype.card_fin]; omega)
  have hk1 : 1 ≤ 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) k).map
      (uniformBin lam width n)).toFinset.card) :=
    Nat.one_le_pow _ _ (by omega)
  have hki : k ≠ i := fun h => hkT (h ▸ hi)
  have hkj1 : k ≠ j1 := fun h => hkT (h ▸ hj1T)
  have hkj2 : k ≠ j2 := fun h => hkT (h ▸ hj2T)
  -- Four distinct rows already exceed the `2^n` budget.
  have hiN : i ∉ ({j1, j2, k} : Finset (Fin s)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hj1i.symm, hj2i.symm, hki.symm⟩
  have hj1N : j1 ∉ ({j2, k} : Finset (Fin s)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, hkj1.symm⟩
  have hj2N : j2 ∉ ({k} : Finset (Fin s)) := by
    simp [hkj2.symm]
  have hS : ∑ x ∈ ({i, j1, j2, k} : Finset (Fin s)),
        2 ^ (n - ((directionRow o e (c ∘ v.succAbove) x).map
          (uniformBin lam width n)).toFinset.card)
      = 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) i).map
          (uniformBin lam width n)).toFinset.card)
        + 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) j1).map
          (uniformBin lam width n)).toFinset.card)
        + 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) j2).map
          (uniformBin lam width n)).toFinset.card)
        + 2 ^ (n - ((directionRow o e (c ∘ v.succAbove) k).map
          (uniformBin lam width n)).toFinset.card) := by
    rw [Finset.sum_insert hiN, Finset.sum_insert hj1N,
      Finset.sum_insert hj2N, Finset.sum_singleton]
    omega
  have hsub : ∑ x ∈ ({i, j1, j2, k} : Finset (Fin s)),
        2 ^ (n - ((directionRow o e (c ∘ v.succAbove) x).map
          (uniformBin lam width n)).toFinset.card)
      ≤ ∑ x : Fin s,
        2 ^ (n - ((directionRow o e (c ∘ v.succAbove) x).map
          (uniformBin lam width n)).toFinset.card) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

/-- Every member of a sorted list is at least its head. -/
private lemma SortedLE_head_le {l : List ℝ} (hs : l.SortedLE)
    (hne : l ≠ []) {x : ℝ} (hx : x ∈ l) : l.head hne ≤ x := by
  obtain ⟨y, ys, rfl⟩ := List.ne_nil_iff_exists_cons.mp hne
  rw [List.head_cons]
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_rfl
  · exact (List.sortedLE_cons.mp hs).1 x hx

/-- Every member of a sorted list is at most its last element. -/
private lemma SortedLE_le_getLast {l : List ℝ} (hs : l.SortedLE)
    (hne : l ≠ []) {x : ℝ} (hx : x ∈ l) : x ≤ l.getLast hne := by
  induction l generalizing x with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    cases ys with
    | nil =>
      rw [List.getLast_singleton]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_rfl
      · exact absurd hx (by simp)
    | cons z zs =>
      have hne' : z :: zs ≠ [] := by simp
      rw [List.getLast_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans ((List.sortedLE_cons.mp hs).1 z (by simp))
          (ih (List.sortedLE_cons.mp hs).2 hne' (by simp))
      · exact ih (List.sortedLE_cons.mp hs).2 hne' hx

/-- **End-gap span rigidity.**  A defect-`2` non-anchor row whose two
end gaps (at `θ_i` and `θ_i + π`) both reach `λ` has chord-direction
span at most `δλ = π − nλ`: its two big gaps are the end gaps and
their floors sum to `n`. -/
theorem row_span_le_delta_of_defect_two_ends {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 1 ≤ s) (i : Fin s)
    (hd : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hne : directionRow o e (c ∘ v.succAbove) i ≠ [])
    (hfirst : lam ≤ (directionRow o e (c ∘ v.succAbove) i).head hne -
      theta i)
    (hlast : lam ≤ theta i + Real.pi -
      (directionRow o e (c ∘ v.succAbove) i).getLast hne) :
    (directionRow o e (c ∘ v.succAbove) i).getLast hne -
      (directionRow o e (c ∘ v.succAbove) i).head hne ≤
        Real.pi - n * lam := by
  classical
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have h3l : 3 * lam ≤ (n : ℝ) * lam :=
    mul_le_mul_of_nonneg_right hn3r hlam.le
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    linarith
  have hdel : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    linarith
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
      hdel (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij
        (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdel.le (htheta i).1,
      (htheta i).2⟩
  have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam
    (v.succAbove i) (by omega) hn
  have hscore : rowScore lam (directionRow o e c (v.succAbove i)) =
      n - 2 := by
    rw [rowScore_eq_sub_defect lam hlam n _ hcells, hd]
  rw [anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlampi
    theta htheta' (fun a b hab => (hcorr a b hab).1)] at hscore
  have h1 : theta i + Real.pi - theta i = Real.pi := by ring
  have hspan := linearGapScore_span_le_of_big_ends lam (theta i)
    (theta i + Real.pi) hlam hne
    ((directionRow_sorted o e (c ∘ v.succAbove) i).pairwise)
    (fun x hx => by
      obtain ⟨j, hji, rfl⟩ :=
        (mem_directionRow o e (c ∘ v.succAbove)).mp hx
      have hxl := (hcorr i j hji.symm).1
      have hxu := directionRow_mem_Ico o e (c ∘ v.succAbove) hx
      have hti := (htheta i).1
      exact ⟨by linarith [hti.2, hdel, hxl],
        by linarith [hti.1, hxu.2]⟩)
    hfirst hlast (n := n) (by rw [h1]; exact hn) (by omega)
  rw [h1] at hspan
  exact hspan

/-- **Shared-chord exclusion.**  Three distinct non-anchor defect-`2`
rows cannot *all* have both end gaps `≥ λ`: their direction spans
would each be `≤ δλ`, so the three shared chords `d_ij`, `d_ik`,
`d_jk` would pairwise differ by `≤ δλ` and lie in a common interval
`[U−δλ, U]` of width `< λ`.  The single-bin weighted bound applied to
the three-point sub-configuration then forces `∑ 2^{1−occ} ≤ 2`,
while every term is `≥ 1` — contradiction. -/
theorem three_defect_two_rows_big_ends_impossible {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hdelta : 0 < Real.pi - n * lam)
    (hs : 2 ≤ s) {i j k : Fin s}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hdj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hdk : rowDefect n lam (directionRow o e c (v.succAbove k)) = 2)
    (hne : ∀ r ∈ ({i, j, k} : Finset (Fin s)),
      directionRow o e (c ∘ v.succAbove) r ≠ [])
    (hends : ∀ r ∈ ({i, j, k} : Finset (Fin s)),
      ∀ h : directionRow o e (c ∘ v.succAbove) r ≠ [],
        lam ≤ (directionRow o e (c ∘ v.succAbove) r).head h - theta r ∧
          lam ≤ theta r + Real.pi -
            (directionRow o e (c ∘ v.succAbove) r).getLast h) :
    False := by
  classical
  have hsi : i ∈ ({i, j, k} : Finset (Fin s)) := by simp
  have hsj : j ∈ ({i, j, k} : Finset (Fin s)) := by simp
  have hsk : k ∈ ({i, j, k} : Finset (Fin s)) := by simp
  have hnei := hne i hsi
  have hnej := hne j hsj
  have hnek := hne k hsk
  obtain ⟨hfi, hli⟩ := hends i hsi hnei
  obtain ⟨hfj, hlj⟩ := hends j hsj hnej
  obtain ⟨hfk, hlk⟩ := hends k hsk hnek
  have hspan_i := row_span_le_delta_of_defect_two_ends o e he hn3 hlam
    hn hleg v htheta (by omega) i hdi hnei hfi hli
  have hspan_j := row_span_le_delta_of_defect_two_ends o e he hn3 hlam
    hn hleg v htheta (by omega) j hdj hnej hfj hlj
  have hspan_k := row_span_le_delta_of_defect_two_ends o e he hn3 hlam
    hn hleg v htheta (by omega) k hdk hnek hfk hlk
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have h3l : 3 * lam ≤ (n : ℝ) * lam :=
    mul_le_mul_of_nonneg_right hn3r hlam.le
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    linarith
  have hdel : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    linarith
  have hcorr : ∀ a b : Fin s, a ≠ b →
      dirRep o e (c ∘ v.succAbove) a b
        ∈ Set.Icc lam (Real.pi - lam + (Real.pi - n * lam)) := by
    intro a b hab
    have hab' : v.succAbove a ≠ v.succAbove b :=
      fun h => hab (Fin.succAbove_right_injective h)
    exact chord_in_corridor o he
      (fun h => Fin.succAbove_ne v a (hleg.inj h))
      (fun h => Fin.succAbove_ne v b (hleg.inj h))
      (fun h => hab' (hleg.inj h))
      hdel (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  -- The three shared chords.
  set a := dirRep o e (c ∘ v.succAbove) i j with ha
  set b := dirRep o e (c ∘ v.succAbove) i k with hb
  set cc := dirRep o e (c ∘ v.succAbove) j k with hcc
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hcji : dirRep o e (c ∘ v.succAbove) j i = a :=
    dirRep_comm o e _ he (fun h => hij (hp'inj h).symm)
  have hcki : dirRep o e (c ∘ v.succAbove) k i = b :=
    dirRep_comm o e _ he (fun h => hik (hp'inj h).symm)
  have hckj : dirRep o e (c ∘ v.succAbove) k j = cc :=
    dirRep_comm o e _ he (fun h => hjk (hp'inj h).symm)
  -- Row memberships.
  have hai : a ∈ directionRow o e (c ∘ v.succAbove) i :=
    (mem_directionRow o e _).mpr ⟨j, hij.symm, ha⟩
  have hbi : b ∈ directionRow o e (c ∘ v.succAbove) i :=
    (mem_directionRow o e _).mpr ⟨k, hik.symm, hb⟩
  have haj : a ∈ directionRow o e (c ∘ v.succAbove) j :=
    (mem_directionRow o e _).mpr ⟨i, hij, hcji.symm⟩
  have hccj : cc ∈ directionRow o e (c ∘ v.succAbove) j :=
    (mem_directionRow o e _).mpr ⟨k, hjk.symm, hcc⟩
  have hbk : b ∈ directionRow o e (c ∘ v.succAbove) k :=
    (mem_directionRow o e _).mpr ⟨i, hik, hcki.symm⟩
  have hcck : cc ∈ directionRow o e (c ∘ v.succAbove) k :=
    (mem_directionRow o e _).mpr ⟨j, hjk, hckj.symm⟩
  -- Pairwise distance ≤ δλ.
  have hdist : ∀ (r : Fin s) (hsr : directionRow o e (c ∘ v.succAbove) r ≠ [])
      (hsp : (directionRow o e (c ∘ v.succAbove) r).getLast hsr -
        (directionRow o e (c ∘ v.succAbove) r).head hsr ≤
          Real.pi - n * lam)
      {x y : ℝ} (hx : x ∈ directionRow o e (c ∘ v.succAbove) r)
      (hy : y ∈ directionRow o e (c ∘ v.succAbove) r),
      |x - y| ≤ Real.pi - n * lam := by
    intro r hsr hsp x y hx hy
    have hs := directionRow_sorted o e (c ∘ v.succAbove) r
    have h1 := SortedLE_head_le hs hsr hx
    have h2 := SortedLE_le_getLast hs hsr hx
    have h3 := SortedLE_head_le hs hsr hy
    have h4 := SortedLE_le_getLast hs hsr hy
    rw [abs_le]
    constructor <;> linarith
  have hab : |a - b| ≤ Real.pi - n * lam := hdist i hnei hspan_i hai hbi
  have hac : |a - cc| ≤ Real.pi - n * lam := hdist j hnej hspan_j haj hccj
  have hbc : |b - cc| ≤ Real.pi - n * lam := hdist k hnek hspan_k hbk hcck
  -- All three chords in [U − δλ, U].
  set U := max (max a b) cc with hU
  have hdpos : 0 < Real.pi - n * lam := hdelta
  have haU : a ∈ Set.Icc (U - (Real.pi - n * lam)) U := by
    have hb_le : b ≤ a + (Real.pi - n * lam) := by
      linarith [(abs_le.mp hab).1]
    have hcc_le : cc ≤ a + (Real.pi - n * lam) := by
      linarith [(abs_le.mp hac).1]
    exact ⟨by
      have h1 : max (max a b) cc ≤ a + (Real.pi - n * lam) :=
        max_le (max_le (by linarith) hb_le) hcc_le
      linarith, le_max_of_le_left (le_max_left _ _)⟩
  have hbU : b ∈ Set.Icc (U - (Real.pi - n * lam)) U := by
    have ha_le : a ≤ b + (Real.pi - n * lam) := by
      linarith [(abs_le.mp hab).2]
    have hcc_le : cc ≤ b + (Real.pi - n * lam) := by
      linarith [(abs_le.mp hbc).1]
    exact ⟨by
      have h1 : max (max a b) cc ≤ b + (Real.pi - n * lam) :=
        max_le (max_le ha_le (by linarith)) hcc_le
      linarith, le_max_of_le_left (le_max_right _ _)⟩
  have hccU : cc ∈ Set.Icc (U - (Real.pi - n * lam)) U := by
    have ha_le : a ≤ cc + (Real.pi - n * lam) := by
      linarith [(abs_le.mp hac).2]
    have hb_le : b ≤ cc + (Real.pi - n * lam) := by
      linarith [(abs_le.mp hbc).2]
    exact ⟨by
      have h1 : max (max a b) cc ≤ cc + (Real.pi - n * lam) :=
        max_le (max_le ha_le hb_le) (by linarith)
      linarith, le_max_right _ _⟩
  -- The three-point sub-configuration.
  set ix : Fin 3 → Fin s := ![i, j, k] with hixdef
  have hix : Function.Injective ix := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> first
      | rfl
      | (exfalso; rw [hixdef] at hxy
         simp only [Fin.isValue, Matrix.cons_val_zero,
           Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
           Matrix.tail_cons] at hxy
         first
         | exact absurd hxy hij | exact absurd hxy hik
         | exact absurd hxy hjk
         | exact absurd hxy.symm hij | exact absurd hxy.symm hik
         | exact absurd hxy.symm hjk)
  set p' : Fin 3 → Plane₂ := fun t => (c ∘ v.succAbove) (ix t) with hp'def
  have hp' : Function.Injective p' := hp'inj.comp hix
  have ha_low : lam ≤ a := (hcorr i j hij).1
  have ha_le_U : a ≤ U := le_trans (le_max_left _ _) (le_max_left _ _)
  have hU_lt : U < Real.pi := by
    have h1 := (hcorr i j hij).2
    have h2 := (hcorr i k hik).2
    have h3 := (hcorr j k hjk).2
    simp only [hU]
    rw [max_lt_iff, max_lt_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith
  have hbound := directionBinGraph_row_weighted_bound o e p' he hp'
    (lam := lam) (start := U - (Real.pi - n * lam))
    (width := Real.pi - n * lam) (m := 1) (by norm_num) hdpos hdel
    (by linarith [ha_low, ha_le_U, hdel]) (by
      simp only [Nat.cast_one, one_mul, sub_add_cancel]
      exact hU_lt)
    (by
      intro a' b' d' h1 h2 h3
      exact hleg.triAngle _ _ _
        (fun h => h1 (hix (Fin.succAbove_right_injective h)))
        (fun h => h3 (hix (Fin.succAbove_right_injective h)))
        (fun h => h2 (hix (Fin.succAbove_right_injective h))))
    (by
      intro t u htu
      have htv : ∀ w : Fin 3, ix w = i ∨ ix w = j ∨ ix w = k := by
        intro w; fin_cases w <;>
          (rw [hixdef]; simp only [Fin.isValue, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
            Matrix.tail_cons]) <;>
          first
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
      have hdir : dirRep o e p' t u =
          dirRep o e (c ∘ v.succAbove) (ix t) (ix u) := rfl
      rw [hdir]
      rcases htv t with ht | ht | ht <;>
        rcases htv u with hu | hu | hu <;>
        rw [ht, hu] <;>
        simp only [Nat.cast_one, one_mul, sub_add_cancel] <;>
        first
        | (exfalso; exact htu (hix (ht.trans hu.symm)))
        | exact haU
        | exact hbU
        | exact hccU
        | (rw [hcji]; exact haU)
        | (rw [hcki]; exact hbU)
        | (rw [hckj]; exact hccU))
  -- Every term is ≥ 1, so the sum over the three vertices is ≥ 3 > 2.
  have hge : (3 : ℕ) ≤ ∑ t : Fin 3, 2 ^ (1 - ((directionRow o e p' t).map (uniformBin (U - (Real.pi - n * lam)) (Real.pi - n * lam) 1)).toFinset.card) := by
    calc (3 : ℕ) = Finset.univ.sum (fun _ : Fin 3 => 1) := by simp
      _ ≤ _ := Finset.sum_le_sum fun t _ => Nat.one_le_two_pow
  omega

/-- **Short-end witness.**  Three distinct non-anchor defect-`2` rows
cannot all have both end gaps `≥ λ`, so at least one of them has a
short first or last gap.  The witness row and its orientation (first
`=` lower-`θ` chord, last `=` upper-`θ` chord) are then available for
the shared-chord continuation argument. -/
theorem exists_short_end_of_three_defect_two {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hdelta : 0 < Real.pi - n * lam)
    (hs : 2 ≤ s) {i j k : Fin s}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hdj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hdk : rowDefect n lam (directionRow o e c (v.succAbove k)) = 2) :
    ∃ r ∈ ({i, j, k} : Finset (Fin s)),
      ∃ h : directionRow o e (c ∘ v.succAbove) r ≠ [],
        (directionRow o e (c ∘ v.succAbove) r).head h - theta r < lam ∨
          theta r + Real.pi -
            (directionRow o e (c ∘ v.succAbove) r).getLast h < lam := by
  classical
  by_contra hcon
  push_neg at hcon
  exact three_defect_two_rows_big_ends_impossible o e he hn3 hlam hn
    hleg v htheta hdelta hs hij hik hjk hdi hdj hdk
    (fun r _ => by
      apply List.ne_nil_of_length_pos
      rw [directionRow_length]; omega)
    hcon

/-- **Short first-gap witness.**  If row `r` has a short first gap
(`head < θ_r + λ`), its head element is a chord `r → j` with
`θ_j < θ_r` — a strictly lower-`θ` non-anchor vertex.  This is the
endpoint-window consumption of `exists_short_end_of_three_defect_two`'s
first disjunct. -/
theorem short_first_gap_gives_lower {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (r : Fin s) (hne : directionRow o e (c ∘ v.succAbove) r ≠ [])
    (hshort : (directionRow o e (c ∘ v.succAbove) r).head hne -
      theta r < lam) :
    ∃ j : Fin s, r ≠ j ∧ theta j < theta r ∧
      dirRep o e (c ∘ v.succAbove) r j =
        (directionRow o e (c ∘ v.succAbove) r).head hne := by
  classical
  obtain ⟨j, hrj, hdir⟩ := (mem_directionRow o e (c ∘ v.succAbove)).mp
    (List.head_mem hne)
  refine ⟨j, hrj.symm, ?_, hdir.symm⟩
  exact saturated_row_bot_sliver_forces_low o e he (by omega) hlam hn
    hleg v htheta r j hrj.symm (t := theta r) le_rfl (by
      rw [← hdir]; linarith)

/-- **Short last-gap witness.**  If row `r` has a short last gap
(`getLast > θ_r + π − λ`), its last element is a chord `r → j` with
`θ_j > θ_r` — a strictly higher-`θ` non-anchor vertex. -/
theorem short_last_gap_gives_higher {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (r : Fin s) (hne : directionRow o e (c ∘ v.succAbove) r ≠ [])
    (hshort : theta r + Real.pi -
      (directionRow o e (c ∘ v.succAbove) r).getLast hne < lam) :
    ∃ j : Fin s, r ≠ j ∧ theta r < theta j ∧
      dirRep o e (c ∘ v.succAbove) r j =
        (directionRow o e (c ∘ v.succAbove) r).getLast hne := by
  classical
  obtain ⟨j, hrj, hdir⟩ := (mem_directionRow o e (c ∘ v.succAbove)).mp
    (List.getLast_mem hne)
  refine ⟨j, hrj.symm, ?_, hdir.symm⟩
  exact saturated_row_top_sliver_forces_high o e he (by omega) hlam hn
    hleg v htheta r j hrj.symm (u := theta r) le_rfl (by
      rw [← hdir]; linarith)

/-- **Full witness chain.**  Three defect-`2` rows produce an actual
crossing chord: some row `r ∈ {i,j,k}` has a chord endpoint at a
strictly lower or strictly higher `θ` vertex.  This is the honest
conclusion stage — the crossing vertex may lie outside `{i,j,k}`; the
residual analysis must use *which* side the short gap is on, not just
its existence. -/
theorem exists_crossing_witness_of_three_defect_two {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hdelta : 0 < Real.pi - n * lam)
    (hs : 2 ≤ s) {i j k : Fin s}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hdj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hdk : rowDefect n lam (directionRow o e c (v.succAbove k)) = 2) :
    ∃ r ∈ ({i, j, k} : Finset (Fin s)), ∃ u : Fin s, r ≠ u ∧
      (theta u < theta r ∨ theta r < theta u) := by
  classical
  obtain ⟨r, hr, hne, hshort⟩ :=
    exists_short_end_of_three_defect_two o e he hn3 hlam hn hleg v
      htheta hdelta hs hij hik hjk hdi hdj hdk
  refine ⟨r, hr, ?_⟩
  rcases hshort with hfirst | hlast
  · obtain ⟨u, hru, hu, _⟩ := short_first_gap_gives_lower o e he hn3
      hlam hn hleg v htheta r hne hfirst
    exact ⟨u, hru, Or.inl hu⟩
  · obtain ⟨u, hru, hu, _⟩ := short_last_gap_gives_higher o e he hn3
      hlam hn hleg v htheta r hne hlast
    exact ⟨u, hru, Or.inr hu⟩

/-- The `θ`-minimum non-anchor row has no lower vertex to point to, so
its first gap cannot be short.  Contrapositive of
`short_first_gap_gives_lower`. -/
theorem first_gap_ge_of_theta_min {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (r : Fin s) (hne : directionRow o e (c ∘ v.succAbove) r ≠ [])
    (hmin : ∀ u : Fin s, theta r ≤ theta u) :
    lam ≤ (directionRow o e (c ∘ v.succAbove) r).head hne - theta r := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨u, -, hu, -⟩ := short_first_gap_gives_lower o e he hn3 hlam
    hn hleg v htheta r hne hlt
  exact absurd (hmin u) (not_le.mpr hu)

/-- Symmetrically, the `θ`-maximum non-anchor row has a non-short last
gap. -/
theorem last_gap_ge_of_theta_max {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (r : Fin s) (hne : directionRow o e (c ∘ v.succAbove) r ≠ [])
    (hmax : ∀ u : Fin s, theta u ≤ theta r) :
    lam ≤ theta r + Real.pi -
      (directionRow o e (c ∘ v.succAbove) r).getLast hne := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨u, -, hu, -⟩ := short_last_gap_gives_higher o e he hn3 hlam
    hn hleg v htheta r hne hlt
  exact absurd (hmax u) (not_le.mpr hu)

/-- **Two short rows when all four are defect-`2`.**  In the `s = 4`
five-point case with `R = 4` (every non-anchor row defect `2`), at least
two rows have a short end gap: otherwise the three rows without one
would form an all-big-ends defect-`2` triple, contradicting
`three_defect_two_rows_big_ends_impossible`. -/
theorem exists_two_short_end_rows_of_four {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin 5 → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin 5) {theta : Fin 4 → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hdelta : 0 < Real.pi - n * lam)
    (hdef2 : ∀ r : Fin 4, rowDefect n lam
      (directionRow o e c (v.succAbove r)) = 2) :
    ∃ a b : Fin 4, a ≠ b ∧
      (∃ h : directionRow o e (c ∘ v.succAbove) a ≠ [],
        (directionRow o e (c ∘ v.succAbove) a).head h - theta a < lam ∨
          theta a + Real.pi -
            (directionRow o e (c ∘ v.succAbove) a).getLast h < lam) ∧
      (∃ h : directionRow o e (c ∘ v.succAbove) b ≠ [],
        (directionRow o e (c ∘ v.succAbove) b).head h - theta b < lam ∨
          theta b + Real.pi -
            (directionRow o e (c ∘ v.succAbove) b).getLast h < lam) := by
  classical
  by_contra hcon
  push_neg at hcon
  set row : Fin 4 → List ℝ := fun r =>
    directionRow o e (c ∘ v.succAbove) r with hrow
  set S := Finset.univ.filter (fun r : Fin 4 =>
    ∃ h : row r ≠ [], (row r).head h - theta r < lam ∨
      theta r + Real.pi - (row r).getLast h < lam) with hS
  have hScard : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rw [Finset.mem_filter] at ha hb
    obtain ⟨hnb, hbs⟩ := hb.2
    have h := hcon a b hab ha.2 hnb
    rcases hbs with h' | h'
    · exact absurd h' (not_lt.mpr h.1)
    · exact absurd h' (not_lt.mpr h.2)
  have hT : 3 ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hT
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hTcard
  have hnot : ∀ r ∈ ({x, y, z} : Finset (Fin 4)),
      ∀ h : row r ≠ [],
        lam ≤ (row r).head h - theta r ∧
          lam ≤ theta r + Real.pi - (row r).getLast h := by
    intro r hr h
    have hrS : r ∉ S := (Finset.mem_sdiff.mp (hTsub hr)).2
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hrS
    push_neg at hrS
    exact hrS h
  exact three_defect_two_rows_big_ends_impossible o e he hn3 hlam hn
    hleg v htheta hdelta (by norm_num) hxy hxz hyz
    (hdef2 x) (hdef2 y) (hdef2 z)
    (fun r _ => by
      apply List.ne_nil_of_length_pos
      rw [directionRow_length]; omega)
    hnot

#print axioms row_span_le_delta_of_defect_two_ends
#print axioms three_defect_two_rows_big_ends_impossible
#print axioms exists_short_end_of_three_defect_two
#print axioms short_first_gap_gives_lower
#print axioms short_last_gap_gives_higher
#print axioms exists_crossing_witness_of_three_defect_two
#print axioms first_gap_ge_of_theta_min
#print axioms last_gap_ge_of_theta_max
#print axioms exists_two_short_end_rows_of_four

/-- **Higher-defect rows exist in the residual.**  In the `S = 1` regime
every non-anchor row has defect `≥ 2`; combined with the volume
obstruction (`defect_two_rows_le_three`) at most three of them have
defect exactly `2`, so with `s ≥ 5` non-anchor rows at least `s − 3 ≥ 2`
rows have defect `≥ 3`.  These are the candidate slack rows for the
`r = 2`, `|T| = 2` instance of `potential_le_high_of_saturated_slack_family`
— the remaining obligation is to show two of them occupy `≤ 2` bins
(a defect-`3` row with occupancy `≤ 2` already yields slack `2^{n−3}`). -/
theorem exists_two_rows_defect_ge_three {s n : ℕ}
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
    (hs5 : 5 ≤ s)
    (hdef2 : ∀ i : Fin s, 2 ≤ rowDefect n lam
      (directionRow o e c (v.succAbove i))) :
    ∃ T : Finset (Fin s), s - 3 ≤ T.card ∧
      ∀ i ∈ T, 3 ≤ rowDefect n lam
        (directionRow o e c (v.succAbove i)) := by
  classical
  set T2 := Finset.univ.filter (fun i : Fin s =>
    rowDefect n lam (directionRow o e c (v.succAbove i)) = 2) with hT2
  have hT2le : T2.card ≤ 3 := defect_two_rows_le_three o e he hs hn3
    hlam hn hleg v htheta hw hwidth hcover hcoverlt hs5 T2
    (fun i hi => (Finset.mem_filter.mp hi).2)
  refine ⟨Finset.univ.filter (fun i : Fin s =>
    3 ≤ rowDefect n lam (directionRow o e c (v.succAbove i))), ?_, ?_⟩
  · have hcompl : Finset.univ.filter (fun i : Fin s =>
        3 ≤ rowDefect n lam (directionRow o e c (v.succAbove i))) =
        Finset.univ \ T2 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff,
        true_and, hT2]
      have := hdef2 i
      omega
    rw [hcompl, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
    omega
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

/-- **Five-point counting (m = 4).**  With `s = 4` non-anchor rows all
of defect `≥ 2` and at most two of them of defect exactly `2`
(`R ≤ 2`), the HIGH cap follows by weight counting alone: the defect-`2`
rows contribute `≤ 2·2^{n−2}` and the remaining `4−R` rows `≤ Q/2` each,
bounding the non-anchor weight by `3Q`.  The complementary geometric
obligation is exactly `R ≤ 2`: three defect-`2` rows would already
contribute `3Q` and any fourth positive weight breaks the cap. -/
theorem potential_le_high_of_saturated_four_eq {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (hs : s = 4) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (_hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (huniq : ∀ i : Fin s,
      2 ≤ rowDefect n lam (directionRow o e c (v.succAbove i)))
    (hR : (Finset.univ.filter (fun i : Fin s =>
        rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)).card
        ≤ 2) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hcells : ∀ w : Fin (s + 1), rowCells lam (directionRow o e c w)
      ≤ n := fun w =>
    rowCells_directionRow_le_of_floor_eq o e c hlam w (by omega) hn
  have key : ∀ w : Fin (s + 1), rowScore lam (directionRow o e c w) =
      n - rowDefect n lam (directionRow o e c w) :=
    fun w => rowScore_eq_sub_defect lam hlam n _ (hcells w)
  set T2 := Finset.univ.filter (fun i : Fin s =>
      rowDefect n lam (directionRow o e c (v.succAbove i)) = 2) with hT2
  have hT2sum : ∑ i ∈ T2,
        2 ^ rowScore lam (directionRow o e c (v.succAbove i))
      ≤ T2.card * 2 ^ (n - 2) := by
    apply le_of_eq
    calc ∑ i ∈ T2, 2 ^ rowScore lam (directionRow o e c (v.succAbove i))
        = ∑ _i ∈ T2, 2 ^ (n - 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [key, (Finset.mem_filter.mp hi).2]
      _ = T2.card * 2 ^ (n - 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hrest : ∑ i ∈ Finset.univ \ T2,
        2 ^ rowScore lam (directionRow o e c (v.succAbove i))
      ≤ (Finset.univ \ T2).card * 2 ^ (n - 3) := by
    have h2 : ∀ i ∈ Finset.univ \ T2,
        2 ^ rowScore lam (directionRow o e c (v.succAbove i))
          ≤ 2 ^ (n - 3) := by
      intro i hi
      have hne2 : rowDefect n lam (directionRow o e c (v.succAbove i))
          ≠ 2 := fun h => (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      have hge := huniq i
      rw [key]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    calc ∑ i ∈ Finset.univ \ T2,
          2 ^ rowScore lam (directionRow o e c (v.succAbove i))
        ≤ ∑ _i ∈ Finset.univ \ T2, 2 ^ (n - 3) :=
          Finset.sum_le_sum h2
      _ = (Finset.univ \ T2).card * 2 ^ (n - 3) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hrestcard : (Finset.univ \ T2).card = 4 - T2.card := by
    have hcard : (Finset.univ \ T2).card = s - T2.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin]
    omega
  have hT2card : T2.card ≤ 2 := hR
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v, key v, hsat,
    ← Finset.sum_sdiff (Finset.subset_univ T2)]
  have h2n3 : (2 : ℕ) ^ (n - 2) = 2 * 2 ^ (n - 3) := by
    conv_lhs => rw [show n - 2 = n - 3 + 1 by omega, pow_succ]
    ring
  have h2n1 : (2 : ℕ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
    ring
  have h2n : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n = n - 2 + 2 by omega, pow_add]
    ring
  rw [hrestcard] at hrest
  interval_cases T2.card <;> omega

/-- **Strict first-margin ⇒ occupancy deficit (row level).**  If the
first chord direction of non-anchor row `i` has a strict margin over its
bin (`gapScore (x − θ_i) + 1 ≤ bin x` — note the origin is the row's own
anchor ray `θ_i`, NOT the cover start `λ`), then the row's defect
strictly exceeds its occupied-bin count: `occ + 1 ≤ c_i`.  Equivalently
`S_i = C_i − w_i ≥ 2^{n−a_i−1}` — the concrete slack unit the residual
accounting needs.  Geometric supply of `hfirst` remains open in general;
`gapScore_add_one_le_of_cover` reduces it to `θ_i > (b+1)·w − b·λ`
where `b = bin(first)`. -/
theorem rowDefect_add_one_le_of_strict_prefix {s n : ℕ}
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
    (i : Fin s) (x : ℝ) (xs : List ℝ)
    (hrow : directionRow o e (c ∘ v.succAbove) i = x :: xs)
    (hfirst : gapScore lam (x - theta i) + 1 ≤
      uniformBin lam width n x) :
    ((directionRow o e (c ∘ v.succAbove) i).map
        (uniformBin lam width n)).toFinset.card + 1 ≤
      rowDefect n lam (directionRow o e c (v.succAbove i)) := by
  classical
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith
  have hdel : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    nlinarith
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
      hdel (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij
        (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm
        (Fin.ne_succAbove v i))
  have hpos : ∀ a ∈ x :: xs,
      a ∈ Set.Icc lam (lam + (n : ℝ) * width) := by
    intro a ha
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e (c ∘ v.succAbove)).mp
      (hrow ▸ ha)
    have h2 := hcorr i j hji.symm
    refine ⟨h2.1, ?_⟩
    have h3 := h2.2
    have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [hcover, hcoverlt, hw, hwidth]
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdel.le (htheta i).1,
      (htheta i).2⟩
  have hlow : ∀ i j : Fin s, i ≠ j →
      lam ≤ dirRep o e (c ∘ v.succAbove) i j :=
    fun i j hij => (hcorr i j hij).1
  have hscore : rowScore lam (directionRow o e c (v.succAbove i)) =
      linearGapScore lam (theta i) (theta i + Real.pi)
        (directionRow o e (c ∘ v.succAbove) i) :=
    anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlampi
      theta htheta' hlow i
  have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam
    (v.succAbove i) (by omega) hn
  have hsort : (x :: xs).SortedLE := hrow ▸ directionRow_sorted o e
    (c ∘ v.succAbove) i
  have hstrict : linearGapScore lam (theta i) (theta i + Real.pi)
        (x :: xs) +
      ((x :: xs).map (uniformBin lam width n)).toFinset.card + 1 ≤ n := by
    apply linearGapScore_add_one_le_empty_uniform_bins
      (lam := lam) (width := width) (start := lam)
      (m := n) (by omega) hw hwidth
    · -- right margin: θ_i + π ≤ λ + n·w + λ since n·w ≥ W ≥ π−2λ+θ_i
      have hti := (htheta i).1.2
      have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      nlinarith [hcover]
    · exact hsort.pairwise.imp (fun h => uniformBin_monotone hw h)
    · exact fun a _ => uniformBin_lt (by omega) a
    · intro a ha
      exact uniformBin_position (by omega) hw (hpos a ha)
    · exact hfirst
  have hd := rowScore_eq_sub_defect lam hlam n _ hcells
  rw [hscore, hrow] at hd
  rw [hrow]
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

/-- **Double-end residual reduction (one-sided form).**  Deleting any
single non-anchor center `q` whose row has defect `≥ 2` closes the cap
whenever the *surviving* anchor rays have span strictly below
`α = (n+1)λ − π`.  Applied to `q` = argmax of `theta`, the contrapositive
forces `θ_{m−1} − θ_1 ≥ α` in any cap-violating configuration; applied to
`q` = argmin it forces `θ_m − θ_2 ≥ α`.  No sortedness framework is
needed: `Finset.sup'`/`Finset.inf'` over `univ.erase iqr` give the
endpoint selection directly. -/
theorem potential_le_high_of_saturated_delete_span {s n : ℕ}
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
    (hSne : (Finset.univ.erase iqr).Nonempty)
    (hspan : (Finset.univ.erase iqr).sup' hSne theta
        - (Finset.univ.erase iqr).inf' hSne theta
        < ((n : ℝ) + 1) * lam - Real.pi) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle (i : Fin s) (hi : i ≠ iqr) :
      theta i ≤ (Finset.univ.erase iqr).sup' hSne theta :=
    Finset.le_sup' theta
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  have hge (i : Fin s) (hi : i ≠ iqr) :
      (Finset.univ.erase iqr).inf' hSne theta ≤ theta i :=
    Finset.inf'_le theta
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩)
  apply potential_le_high_of_saturated_delete_narrow o e he hs hn3 hlam
    hn hleg v (v.succAbove iqr) (Fin.ne_succAbove v iqr) hsat hqdef hδ
    hspan
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
    ⟨by linarith [hge j' hjj, hle i' hii],
      by linarith [hle j' hjj, hge i' hii]⟩

#print axioms one_saturated_capacity_of_narrow_window
#print axioms potential_le_two_pow_of_saturated_narrow
#print axioms potential_le_high_of_saturated_small
#print axioms potential_le_high_of_saturated_clump
#print axioms potential_le_high_of_saturated_slack_family
#print axioms defect_two_rows_le_three
#print axioms four_defect_two_tiling
#print axioms three_defect_two_rows_tight
#print axioms exists_two_rows_defect_ge_three
#print axioms potential_le_high_of_saturated_four_eq
#print axioms rowDefect_add_one_le_of_strict_prefix
#print axioms potential_le_high_of_saturated_delete_span
#print axioms potential_le_high_of_saturated_delete_narrow
#print axioms potential_le_high_of_saturated_one_outlier

end Jsp404
