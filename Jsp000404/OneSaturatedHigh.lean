import Jsp000404.OneSaturatedLow
import Jsp000404.K3bGeometry

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

/-- **The `0 → 1` arc relation, short-first version.**  A short first
gap in row `r` witnesses a lower-`θ` vertex `j`; the shared chord `φ`
carries `floor((φ−θ_r)/λ) = 0` on the source side while the receiving
prefix arc `φ−θ_j` on the target side satisfies `λ ≤ φ−θ_j < 2λ`, hence
`floor = 1`.  The remainder budget is exact:
`(λ−g) + (A−λ) = θ_r − θ_j`.  The target arc is an aggregate arc — it
need not be a single primitive gap. -/
theorem short_first_arc_floor {s n : ℕ}
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
        (directionRow o e (c ∘ v.succAbove) r).head hne ∧
      ⌊(dirRep o e (c ∘ v.succAbove) r j - theta r) / lam⌋₊ = 0 ∧
      lam + theta j ≤ dirRep o e (c ∘ v.succAbove) j r ∧
      dirRep o e (c ∘ v.succAbove) j r - theta j < 2 * lam ∧
      ⌊(dirRep o e (c ∘ v.succAbove) j r - theta j) / lam⌋₊ = 1 ∧
      (lam - (dirRep o e (c ∘ v.succAbove) r j - theta r)) +
        (dirRep o e (c ∘ v.succAbove) j r - theta j - lam) =
          theta r - theta j := by
  classical
  obtain ⟨j, hrj, hjt, hdir⟩ := short_first_gap_gives_lower o e he hn3
    hlam hn hleg v htheta r hne hshort
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ : dirRep o e (c ∘ v.succAbove) j r =
      dirRep o e (c ∘ v.succAbove) r j :=
    dirRep_comm o e _ he (fun h => hrj (hp'inj h).symm)
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    linarith
  -- Bot-sliver contrapositive: `θ_j ≤ θ_r` forces `dirRep j r ≥ λ+θ_j`.
  have hAlow : lam + theta j ≤ dirRep o e (c ∘ v.succAbove) j r := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_bot_sliver_forces_low o e he (by omega)
      hlam hn hleg v htheta j r hrj.symm (t := theta j) le_rfl hlt
    linarith
  refine ⟨j, hrj, hjt, hdir, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdir]
    exact Nat.floor_eq_zero.mpr ((div_lt_one hlam).mpr hshort)
  · exact hAlow
  · rw [hφ, hdir]
    have h2 : theta r ≤ Real.pi - n * lam := (htheta r).1.2
    have h3 : 0 ≤ theta j := (htheta j).1.1
    linarith
  · have hA0 : 0 ≤ dirRep o e (c ∘ v.succAbove) j r - theta j := by
      linarith
    have hge : 1 ≤ ⌊(dirRep o e (c ∘ v.succAbove) j r - theta j) /
        lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have hlt : ⌊(dirRep o e (c ∘ v.succAbove) j r - theta j) /
        lam⌋₊ < 2 := by
      have h1 : (⌊(dirRep o e (c ∘ v.succAbove) j r - theta j) /
          lam⌋₊ : ℝ) ≤
          (dirRep o e (c ∘ v.succAbove) j r - theta j) / lam :=
        Nat.floor_le (div_nonneg hA0 hlam.le)
      rw [hφ, hdir] at h1 ⊢
      have h2 : ((directionRow o e (c ∘ v.succAbove) r).head hne -
          theta j) / lam < 2 := by
        rw [div_lt_iff₀ hlam]
        have h2' : theta r ≤ Real.pi - n * lam := (htheta r).1.2
        have h3 : 0 ≤ theta j := (htheta j).1.1
        linarith
      have h3 : (⌊((directionRow o e (c ∘ v.succAbove) r).head hne -
          theta j) / lam⌋₊ : ℝ) < 2 := lt_of_le_of_lt h1 h2
      exact_mod_cast h3
    omega
  · rw [hφ]; ring

/-- **The `0 → 1` arc relation, short-last version.**  Symmetrically, a
short last gap in row `r` witnesses a higher-`θ` vertex `j`; the source
gap `θ_r + π − φ` has `floor = 0` while the receiving suffix arc
`θ_j + π − φ` satisfies `λ ≤ · < 2λ`, hence `floor = 1`, with
`(λ−g) + (A−λ) = θ_j − θ_r`. -/
theorem short_last_arc_floor {s n : ℕ}
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
        (directionRow o e (c ∘ v.succAbove) r).getLast hne ∧
      ⌊(theta r + Real.pi - dirRep o e (c ∘ v.succAbove) r j) /
        lam⌋₊ = 0 ∧
      dirRep o e (c ∘ v.succAbove) j r ≤ Real.pi - lam + theta j ∧
      theta j + Real.pi - dirRep o e (c ∘ v.succAbove) j r <
        2 * lam ∧
      ⌊(theta j + Real.pi - dirRep o e (c ∘ v.succAbove) j r) /
        lam⌋₊ = 1 ∧
      (lam - (theta r + Real.pi - dirRep o e (c ∘ v.succAbove) r j)) +
        (theta j + Real.pi - dirRep o e (c ∘ v.succAbove) j r - lam) =
          theta j - theta r := by
  classical
  obtain ⟨j, hrj, hjt, hdir⟩ := short_last_gap_gives_higher o e he hn3
    hlam hn hleg v htheta r hne hshort
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ : dirRep o e (c ∘ v.succAbove) j r =
      dirRep o e (c ∘ v.succAbove) r j :=
    dirRep_comm o e _ he (fun h => hrj (hp'inj h).symm)
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'
    linarith
  -- Top-sliver contrapositive: `θ_r ≤ θ_j` forces `dirRep j r ≤ π−λ+θ_j`.
  have hAhigh : dirRep o e (c ∘ v.succAbove) j r ≤
      Real.pi - lam + theta j := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_top_sliver_forces_high o e he (by omega)
      hlam hn hleg v htheta j r hrj.symm (u := theta j) le_rfl hlt
    linarith
  refine ⟨j, hrj, hjt, hdir, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdir]
    exact Nat.floor_eq_zero.mpr ((div_lt_one hlam).mpr hshort)
  · exact hAhigh
  · -- `θ_j + π − φ < 2λ` since `φ = getLast > θ_r + π − λ`.
    rw [hφ, hdir]
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    have h3 : 0 ≤ theta r := (htheta r).1.1
    linarith
  · have hA0 : 0 ≤ theta j + Real.pi -
        dirRep o e (c ∘ v.succAbove) j r := by linarith
    have hge : 1 ≤ ⌊(theta j + Real.pi -
        dirRep o e (c ∘ v.succAbove) j r) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have hlt : ⌊(theta j + Real.pi -
        dirRep o e (c ∘ v.succAbove) j r) / lam⌋₊ < 2 := by
      have h1 : (⌊(theta j + Real.pi -
          dirRep o e (c ∘ v.succAbove) j r) / lam⌋₊ : ℝ) ≤
          (theta j + Real.pi - dirRep o e (c ∘ v.succAbove) j r) /
            lam :=
        Nat.floor_le (div_nonneg hA0 hlam.le)
      have h2 : (theta j + Real.pi -
          dirRep o e (c ∘ v.succAbove) j r) / lam < 2 := by
        rw [div_lt_iff₀ hlam, hφ, hdir]
        have h2' : theta j ≤ Real.pi - n * lam := (htheta j).1.2
        have h3 : 0 ≤ theta r := (htheta r).1.1
        linarith
      have h3 : (⌊(theta j + Real.pi -
          dirRep o e (c ∘ v.succAbove) j r) / lam⌋₊ : ℝ) < 2 :=
        lt_of_le_of_lt h1 h2
      exact_mod_cast h3
    omega
  · rw [hφ]; ring

/-- **Double-end receiving exclusion.**  A defect-`2` row `j` cannot
simultaneously receive a short-first witness from a higher-`θ` source
(`θ_j < θ_{i₁}`, `dirRep i₁ j − θ_{i₁} < λ`) and a short-last witness
from a lower-`θ` source (`θ_{i₂} < θ_j`, `θ_{i₂} + π − dirRep i₂ j < λ`).

Each receiving arc — prefix `θ_j → φ₁` (cells `≤ 1`, length `≥ λ`) and
suffix `φ₂ → θ_j + π` — forces the unique `floor ≥ n−1` primitive gap
into its complement (`defect_two_big_gap_avoids_arc`); uniqueness pins
the same index `s*`, which must lie in `Ico b₁ b₂`, forcing `b₁ < b₂`.
Then the three disjoint arcs total
`≥ λ + (n−1)λ + λ = (n+1)λ > π`.  Arc endpoints are actual list
elements (first occurrences via `getElem_of_mem`); intersecting or
touching arcs are impossible since `Ico b₁ b₂` would be empty. -/
theorem defect_two_row_not_receive_both {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₁ i₂ : Fin s}
    (hi₁j : i₁ ≠ j) (hi₂j : i₂ ≠ j)
    (hlt₁ : theta j < theta i₁)
    (hgap₁ : dirRep o e (c ∘ v.succAbove) i₁ j - theta i₁ < lam)
    (hlt₂ : theta i₂ < theta j)
    (hgap₂ : theta i₂ + Real.pi -
      dirRep o e (c ∘ v.succAbove) i₂ j < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    False := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₁eq : dirRep o e (c ∘ v.succAbove) j i₁ =
      dirRep o e (c ∘ v.succAbove) i₁ j :=
    dirRep_comm o e _ he (fun h => hi₁j (hp'inj h).symm)
  have hφ₂eq : dirRep o e (c ∘ v.succAbove) j i₂ =
      dirRep o e (c ∘ v.succAbove) i₂ j :=
    dirRep_comm o e _ he (fun h => hi₂j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  -- φ bounds from the endpoint windows.
  set φ₁ := dirRep o e (c ∘ v.succAbove) j i₁ with hφ₁def
  set φ₂ := dirRep o e (c ∘ v.succAbove) j i₂ with hφ₂def
  have hφ₁low : lam + theta j ≤ φ₁ := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_bot_sliver_forces_low o e he hn2 hlam hn
      hleg v htheta j i₁ hi₁j.symm (t := theta j) le_rfl hlt
    linarith
  have hφ₂high : φ₂ ≤ Real.pi - lam + theta j := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_top_sliver_forces_high o e he hn2 hlam hn
      hleg v htheta j i₂ hi₂j.symm (u := theta j) le_rfl hlt
    linarith
  have hφ₁gt : theta j < φ₁ := by linarith
  have hφ₂gt : theta j < φ₂ := by
    have h1 : lam ≤ φ₂ := (hcorr j i₂ hi₂j.symm).1
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    linarith
  have hφ₂le : theta j ≤ φ₂ := hφ₂gt.le
  have hφ₁' : φ₁ = dirRep o e (c ∘ v.succAbove) i₁ j :=
    hφ₁def.trans hφ₁eq
  have hφ₂' : φ₂ = dirRep o e (c ∘ v.succAbove) i₂ j :=
    hφ₂def.trans hφ₂eq
  have hA₁up : φ₁ - theta j < 2 * lam := by
    rw [hφ₁']
    have h2 : theta i₁ ≤ Real.pi - n * lam := (htheta i₁).1.2
    have h3 : 0 ≤ theta j := (htheta j).1.1
    linarith
  have hA₂up : theta j + Real.pi - φ₂ < 2 * lam := by
    rw [hφ₂']
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    have h3 : 0 ≤ theta i₂ := (htheta i₂).1.1
    linarith
  -- Row facts and index positions.
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hsort hmem hne t
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: directionRow o e (c ∘ v.succAbove) j := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    apply le_antisymm
    · -- index `0` is the sorted minimum; `theta j ∈ l`.
      have hθmem : theta j ∈ l := by
        rw [hcons]; exact List.mem_cons_self
      obtain ⟨b, hb⟩ := List.get_of_mem hθmem
      rw [← hb]
      exact List.sortedLE_iff_monotone_get.mp hsort
        (show (⟨0, h⟩ : Fin l.length) ≤ b from Nat.zero_le _)
    · -- every row element is `≥ theta j` (sublist entries are `≥ lam`).
      have hmin : ∀ x ∈ l, theta j ≤ x := by
        intro x hx
        rw [hcons] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact le_rfl
        · obtain ⟨k, hkj, rfl⟩ := (mem_directionRow o e _).mp hx'
          have h1 := hdirge j k hkj.symm
          have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
          linarith
      exact hmin _ (List.get_mem _ _)
  have hφ₁mem : φ₁ ∈ l := by
    rw [hcons]
    exact List.mem_cons_of_mem _
      ((mem_directionRow o e _).mpr ⟨i₁, hi₁j, hφ₁def⟩)
  have hφ₂mem : φ₂ ∈ l := by
    rw [hcons]
    exact List.mem_cons_of_mem _
      ((mem_directionRow o e _).mpr ⟨i₂, hi₂j, hφ₂def⟩)
  obtain ⟨b₁, hgb₁⟩ := List.get_of_mem hφ₁mem
  obtain ⟨b₂, hgb₂⟩ := List.get_of_mem hφ₂mem
  -- Arc cell bounds via `arc_cells_le_arc` / `arc_cells_le_arc_wrap`.
  have hcells : rowCells lam l ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove j)
      (by omega) hn
  have hT₁cells : ∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
      ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc hlam hsort hmem
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
    rw [hget0, hgb₁, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    have h2 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h hA₁up
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
        ⌊gapAfter l t / lam⌋₊) < 2 := by exact_mod_cast h3
    omega
  have hbwrap : l.get ⟨0, Nat.zero_lt_of_lt b₂.2⟩ ≠ l.get b₂ := by
    rw [hget0, hgb₂]
    exact ne_of_lt hφ₂gt
  have hcd₂ : cyclicDiff φ₂ (theta j) = Real.pi + theta j - φ₂ := by
    have h1 := cyclicDiff_add_rev (ne_of_gt hφ₂gt)
    rw [cyclicDiff_eq_sub_of_le hφ₂le] at h1
    linarith
  have hT₂cells : ∑ t ∈ Finset.Ici b₂, ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc_wrap hlam hsort hmem b₂ hbwrap
    rw [hgb₂, hget0, hcd₂] at h
    have h2 : (∑ t ∈ Finset.Ici b₂,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h (by linarith : Real.pi + theta j - φ₂ < 2 * lam)
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ici b₂, ⌊gapAfter l t / lam⌋₊) < 2 := by
      exact_mod_cast h3
    omega
  -- Arc length bounds.
  have hT₁len : lam ≤ ∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
      gapAfter l t := by
    have h := cyclicDiff_eq_Ico_sum_gapAfter hsort
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
    rw [hget0, hgb₁, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    linarith
  have hT₂len : lam ≤ ∑ t ∈ Finset.Ici b₂, gapAfter l t := by
    have h := gapAfter_sum_Ici hsort b₂ hbwrap
    rw [hgb₂, hget0, hcd₂] at h
    linarith
  -- The unique `floor ≥ n−1` index avoids both arcs.
  obtain ⟨s₁, hs₁, hf₁⟩ := defect_two_big_gap_avoids_arc hlam hn hn3
    hsort hmem hcells hdef (Finset.Ico ⟨0, hlen⟩ b₁) hT₁cells hT₁len
  obtain ⟨s₂, hs₂, hf₂⟩ := defect_two_big_gap_avoids_arc hlam hn hn3
    hsort hmem hcells hdef (Finset.Ici b₂) hT₂cells hT₂len
  have hseq : s₁ = s₂ :=
    floor_gap_index_eq_of_cells hn3 hsort hcells hf₁ hf₂
  -- `s₁` lies strictly between `b₁` and `b₂`.
  have hs₁ge : b₁ ≤ s₁ := by
    have h := (Finset.mem_sdiff.mp hs₁).2
    rw [Finset.mem_Ico] at h
    push_neg at h
    exact h (Nat.zero_le _)
  have hs₁lt : s₁ < b₂ := by
    have h := (Finset.mem_sdiff.mp hs₂).2
    rw [Finset.mem_Ici] at h
    have h' := lt_of_not_ge h
    rwa [← hseq] at h'
  have hb₁₂ : b₁ < b₂ := lt_of_le_of_lt hs₁ge hs₁lt
  have hs₁mem : s₁ ∈ Finset.Ico b₁ b₂ := Finset.mem_Ico.mpr ⟨hs₁ge, hs₁lt⟩
  -- The three disjoint arcs cover the circle.
  have hpart : Real.pi = (∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
      gapAfter l t) + (∑ t ∈ Finset.Ico b₁ b₂, gapAfter l t) +
      (∑ t ∈ Finset.Ici b₂, gapAfter l t) := by
    have htot := gapAfter_sum (ds := l) hne
    have hunion : (Finset.univ : Finset (Fin l.length)) =
        Finset.Ico ⟨0, hlen⟩ b₂ ∪ Finset.Ici b₂ := by
      ext t
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ico,
        Finset.mem_Ici]
      constructor
      · intro _
        rcases Nat.lt_or_ge t.1 b₂.1 with h | h
        · exact Or.inl ⟨Nat.zero_le _, h⟩
        · exact Or.inr h
      · intro _; trivial
    have hdisj : Disjoint (Finset.Ico ⟨0, hlen⟩ b₂)
        (Finset.Ici b₂) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      rw [Finset.mem_Ico] at h1
      rw [Finset.mem_Ici] at h2
      exact absurd h1.2 (not_lt_of_ge h2)
    have hIcoU : Finset.Ico ⟨0, hlen⟩ b₁ ∪ Finset.Ico b₁ b₂ =
        Finset.Ico ⟨0, hlen⟩ b₂ :=
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hb₁₂.le
    have hdisj' : Disjoint (Finset.Ico ⟨0, hlen⟩ b₁)
        (Finset.Ico b₁ b₂) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      rw [Finset.mem_Ico] at h1 h2
      exact absurd h1.2 (not_lt_of_ge h2.1)
    rw [hunion, Finset.sum_union hdisj, ← hIcoU,
      Finset.sum_union hdisj'] at htot
    linarith
  have hbig : (n : ℝ) * lam - lam ≤ gapAfter l s₁ := by
    have hf : ((n - 1 : ℕ) : ℝ) ≤ (⌊gapAfter l s₁ / lam⌋₊ : ℝ) := by
      exact_mod_cast hf₁
    have hfm : ((n - 1 : ℕ) : ℝ) * lam ≤
        (⌊gapAfter l s₁ / lam⌋₊ : ℝ) * lam :=
      mul_le_mul_of_nonneg_right hf hlam.le
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n), Nat.cast_one] at hfm
    have h2 := floor_mul_le_gap hlam (hnn s₁)
    linarith
  have hmid : (n : ℝ) * lam - lam ≤
      ∑ t ∈ Finset.Ico b₁ b₂, gapAfter l t :=
    le_trans hbig (Finset.single_le_sum (fun t _ => hnn t) hs₁mem)
  have hpi : Real.pi < (n : ℝ) * lam + lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam, add_mul, one_mul] at hfloor'
    exact hfloor'
  linarith

/-- **Type I propagation.**  A Type I defect-`2` row `j`
(`rowBig = 1`) receiving a short-first witness from a higher-`θ` source
must itself have a short first gap: the unique `floor = n−1` big gap
cannot lie in the receiving prefix arc (its length `≥ 2λ` exceeds the
arc `< 2λ`), so the first primitive gap — which sits inside the arc —
is not big, hence `< λ`.  This is the mechanism that propagates
first-shortness down the `θ`-order among Type I receivers. -/
theorem type_I_first_receiver_is_first_short {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₁ : Fin s}
    (hi₁j : i₁ ≠ j) (hlt₁ : theta j < theta i₁)
    (hgap₁ : dirRep o e (c ∘ v.succAbove) i₁ j - theta i₁ < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hTI : rowBig lam (directionRow o e c (v.succAbove j)) = 1) :
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j <
        lam := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₁eq : dirRep o e (c ∘ v.succAbove) j i₁ =
      dirRep o e (c ∘ v.succAbove) i₁ j :=
    dirRep_comm o e _ he (fun h => hi₁j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₁ := dirRep o e (c ∘ v.succAbove) j i₁ with hφ₁def
  have hφ₁low : lam + theta j ≤ φ₁ := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_bot_sliver_forces_low o e he hn2 hlam hn
      hleg v htheta j i₁ hi₁j.symm (t := theta j) le_rfl hlt
    linarith
  have hφ₁gt : theta j < φ₁ := by linarith
  have hφ₁' : φ₁ = dirRep o e (c ∘ v.succAbove) i₁ j :=
    hφ₁def.trans hφ₁eq
  have hA₁up : φ₁ - theta j < 2 * lam := by
    rw [hφ₁']
    have h2 : theta i₁ ≤ Real.pi - n * lam := (htheta i₁).1.2
    have h3 : 0 ≤ theta j := (htheta j).1.1
    linarith
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hsort hmem hne t
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: directionRow o e (c ∘ v.succAbove) j := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    rw [List.get_of_eq hcons, List.get_mk_zero, List.head_cons]
  have hφ₁mem : φ₁ ∈ l := by
    rw [hcons]
    exact List.mem_cons_of_mem _
      ((mem_directionRow o e _).mpr ⟨i₁, hi₁j, hφ₁def⟩)
  obtain ⟨b₁, hgb₁⟩ := List.get_of_mem hφ₁mem
  have hcells : rowCells lam l ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove j)
      (by omega) hn
  have hT₁cells : ∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
      ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc hlam hsort hmem
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
    rw [hget0, hgb₁, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    have h2 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h hA₁up
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
        ⌊gapAfter l t / lam⌋₊) < 2 := by exact_mod_cast h3
    omega
  have hT₁len : lam ≤ ∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
      gapAfter l t := by
    have h := cyclicDiff_eq_Ico_sum_gapAfter hsort
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
    rw [hget0, hgb₁, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    linarith
  obtain ⟨s₁, hs₁, hf₁⟩ := defect_two_big_gap_avoids_arc hlam hn hn3
    hsort hmem hcells hdef (Finset.Ico ⟨0, hlen⟩ b₁) hT₁cells hT₁len
  have hb₁pos : (⟨0, hlen⟩ : Fin l.length) < b₁ :=
    lt_of_le_of_ne
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
      fun h0eq => by
        have hge : l.get b₁ = l.get ⟨0, hlen⟩ :=
          congrArg (l.get ·) h0eq.symm
        rw [hgb₁, hget0] at hge
        linarith
  have h0mem : (⟨0, hlen⟩ : Fin l.length) ∈ Finset.Ico ⟨0, hlen⟩ b₁ :=
    Finset.mem_Ico.mpr ⟨le_rfl, hb₁pos⟩
  have h01 : (⟨0, hlen⟩ : Fin l.length) ≠ s₁ := fun heq =>
    (Finset.mem_sdiff.mp hs₁).2 (heq ▸ h0mem)
  -- Type I (`rowBig = 1`): index `0`'s gap is not big, hence `< lam`.
  have hg0 : gapAfter l ⟨0, hlen⟩ < lam := by
    by_contra hnot
    push_neg at hnot
    have hgs₁ : lam ≤ gapAfter l s₁ := by
      have h2 := floor_mul_le_gap hlam (hnn s₁)
      have hf : ((n - 1 : ℕ) : ℝ) ≤ (⌊gapAfter l s₁ / lam⌋₊ : ℝ) := by
        exact_mod_cast hf₁
      have hfm : ((n - 1 : ℕ) : ℝ) * lam ≤
          (⌊gapAfter l s₁ / lam⌋₊ : ℝ) * lam :=
        mul_le_mul_of_nonneg_right hf hlam.le
      rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n), Nat.cast_one] at hfm
      have hnn1 : (1 : ℝ) ≤ ↑n - 1 := by
        have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
        linarith
      have hmul : 1 * lam ≤ (↑n - 1) * lam :=
        mul_le_mul_of_nonneg_right hnn1 hlam.le
      rw [one_mul] at hmul
      linarith
    have hsum : (2 : ℕ) ≤ rowBig lam l := by
      rw [rowBig_eq_sum_indicator hsort]
      have hsub : ({⟨0, hlen⟩, s₁} : Finset (Fin l.length)) ⊆
          Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset hsub
        (f := fun t => if lam ≤ gapAfter l t then (1 : ℕ) else 0)
      rw [Finset.sum_pair h01, if_pos hnot, if_pos hgs₁] at hle
      exact hle
    rw [hTI] at hsum
    omega
  -- Transport `gapAfter l ⟨0⟩` to the sub-list head.
  have hsub_ne : directionRow o e (c ∘ v.succAbove) j ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [directionRow_length]; omega
  have h1lt : 1 < l.length := by
    rw [hldef, directionRow_length]; omega
  have hgap0 : gapAfter l ⟨0, hlen⟩ =
      (directionRow o e (c ∘ v.succAbove) j).head hsub_ne - theta j := by
    unfold gapAfter
    rw [dif_pos (show (0 : ℕ) + 1 < l.length by omega)]
    rw [List.get_of_eq hcons, List.get_cons_succ, List.get_mk_zero,
      hget0]
  refine ⟨hsub_ne, ?_⟩
  rw [← hgap0]; exact hg0

/-- **Type I propagation, last end.**  A Type I defect-`2` row `j`
receiving a short-last witness from a lower-`θ` source must itself have
a short last gap: the unique `floor = n−1` big gap cannot lie in the
receiving wrapped suffix arc, so the last (wrapped) primitive gap —
which sits inside the arc — is not big, hence `< λ`. -/
theorem type_I_last_receiver_is_last_short {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₂ : Fin s}
    (hi₂j : i₂ ≠ j) (hlt₂ : theta i₂ < theta j)
    (hgap₂ : theta i₂ + Real.pi -
      dirRep o e (c ∘ v.succAbove) i₂ j < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hTI : rowBig lam (directionRow o e c (v.succAbove j)) = 1) :
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  set sub := directionRow o e (c ∘ v.succAbove) j with hsubdef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₂eq : dirRep o e (c ∘ v.succAbove) j i₂ =
      dirRep o e (c ∘ v.succAbove) i₂ j :=
    dirRep_comm o e _ he (fun h => hi₂j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₂ := dirRep o e (c ∘ v.succAbove) j i₂ with hφ₂def
  have hφ₂high : φ₂ ≤ Real.pi - lam + theta j := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_top_sliver_forces_high o e he hn2 hlam hn
      hleg v htheta j i₂ hi₂j.symm (u := theta j) le_rfl hlt
    linarith
  have hφ₂gt : theta j < φ₂ := by
    have h1 : lam ≤ φ₂ := (hcorr j i₂ hi₂j.symm).1
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    linarith
  have hφ₂le : theta j ≤ φ₂ := hφ₂gt.le
  have hφ₂' : φ₂ = dirRep o e (c ∘ v.succAbove) i₂ j :=
    hφ₂def.trans hφ₂eq
  have hA₂up : theta j + Real.pi - φ₂ < 2 * lam := by
    rw [hφ₂']
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    have h3 : 0 ≤ theta i₂ := (htheta i₂).1.1
    linarith
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hsort hmem hne t
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: sub := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    rw [List.get_of_eq hcons, List.get_mk_zero, List.head_cons]
  have hφ₂mem : φ₂ ∈ l := by
    rw [hcons]
    exact List.mem_cons_of_mem _
      ((mem_directionRow o e _).mpr ⟨i₂, hi₂j, hφ₂def⟩)
  obtain ⟨b₂, hgb₂⟩ := List.get_of_mem hφ₂mem
  have hcells : rowCells lam l ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove j)
      (by omega) hn
  have hbwrap : l.get ⟨0, Nat.zero_lt_of_lt b₂.2⟩ ≠ l.get b₂ := by
    rw [hget0, hgb₂]
    exact ne_of_lt hφ₂gt
  have hcd₂ : cyclicDiff φ₂ (theta j) = Real.pi + theta j - φ₂ := by
    have h1 := cyclicDiff_add_rev (ne_of_gt hφ₂gt)
    rw [cyclicDiff_eq_sub_of_le hφ₂le] at h1
    linarith
  have hT₂cells : ∑ t ∈ Finset.Ici b₂, ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc_wrap hlam hsort hmem b₂ hbwrap
    rw [hgb₂, hget0, hcd₂] at h
    have h2 : (∑ t ∈ Finset.Ici b₂,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h (by linarith : Real.pi + theta j - φ₂ < 2 * lam)
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ici b₂, ⌊gapAfter l t / lam⌋₊) < 2 := by
      exact_mod_cast h3
    omega
  have hT₂len : lam ≤ ∑ t ∈ Finset.Ici b₂, gapAfter l t := by
    have h := gapAfter_sum_Ici hsort b₂ hbwrap
    rw [hgb₂, hget0, hcd₂] at h
    linarith
  obtain ⟨s₁, hs₁, hf₁⟩ := defect_two_big_gap_avoids_arc hlam hn hn3
    hsort hmem hcells hdef (Finset.Ici b₂) hT₂cells hT₂len
  -- The last index lies inside the wrapped arc `Ici b₂`.
  set lastIdx : Fin l.length := ⟨l.length - 1, by omega⟩
  have blast : lastIdx ∈ Finset.Ici b₂ :=
    Finset.mem_Ici.mpr
      (show b₂ ≤ lastIdx from Nat.le_pred_of_lt b₂.2)
  have hlast1 : lastIdx ≠ s₁ := fun heq =>
    (Finset.mem_sdiff.mp hs₁).2 (heq ▸ blast)
  -- Type I (`rowBig = 1`): the last gap is not big, hence `< lam`.
  have hglast0 : gapAfter l lastIdx < lam := by
    by_contra hnot
    push_neg at hnot
    have hgs₁ : lam ≤ gapAfter l s₁ := by
      have h2 := floor_mul_le_gap hlam (hnn s₁)
      have hf : ((n - 1 : ℕ) : ℝ) ≤ (⌊gapAfter l s₁ / lam⌋₊ : ℝ) := by
        exact_mod_cast hf₁
      have hfm : ((n - 1 : ℕ) : ℝ) * lam ≤
          (⌊gapAfter l s₁ / lam⌋₊ : ℝ) * lam :=
        mul_le_mul_of_nonneg_right hf hlam.le
      rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n), Nat.cast_one] at hfm
      have hnn1 : (1 : ℝ) ≤ ↑n - 1 := by
        have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
        linarith
      have hmul : 1 * lam ≤ (↑n - 1) * lam :=
        mul_le_mul_of_nonneg_right hnn1 hlam.le
      rw [one_mul] at hmul
      linarith
    have hsum : (2 : ℕ) ≤ rowBig lam l := by
      rw [rowBig_eq_sum_indicator hsort]
      have hsub : ({lastIdx, s₁} : Finset (Fin l.length)) ⊆
          Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset hsub
        (f := fun t => if lam ≤ gapAfter l t then (1 : ℕ) else 0)
      rw [Finset.sum_pair hlast1, if_pos hnot, if_pos hgs₁] at hle
      exact hle
    rw [hTI] at hsum
    omega
  -- Transport `gapAfter l ⟨len−1⟩` to the sub-list getLast.
  have hsub_ne : sub ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hsubdef, directionRow_length]; omega
  have hgl : l.getLast? = sub.getLast? := by
    rw [hcons]
    exact List.getLast?_cons_of_ne_nil hsub_ne
  have hgl' : l.getLast hne = sub.getLast hsub_ne := by
    have e1 := List.getLast?_eq_getLast hne
    have e2 := List.getLast?_eq_getLast hsub_ne
    rw [hgl, e2] at e1
    exact (Option.some.inj e1).symm
  have hglast : gapAfter l lastIdx =
      theta j + Real.pi - sub.getLast hsub_ne := by
    unfold gapAfter
    rw [dif_neg (show ¬ (l.length - 1 + 1 : ℕ) < l.length by omega)]
    rw [hget0]
    congr 1
    exact ((List.getLast_eq_getElem hne).symm.trans hgl')
  refine ⟨hsub_ne, ?_⟩
  rw [← hglast]; exact hglast0

/-- **Type I first-chain termination.**  Among Type I defect-`2` rows
with a short first gap, the `θ`-minimal one cannot have its first-gap
witness land on another Type I defect-`2` row: propagation would give
the target a short first gap too, contradicting minimality.  Hence
some Type I defect-`2` row's short-first witness always exits the
Type-I-defect-`2` set — either to a Type II defect-`2` row or to a
higher-defect row. -/
theorem type_I_first_witness_leaves_type_I {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s)
    (hT : ∃ j : Fin s,
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      rowBig lam (directionRow o e c (v.succAbove j)) = 1 ∧
      ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
        (directionRow o e (c ∘ v.succAbove) j).head hne - theta j <
          lam) :
    ∃ j : Fin s, ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      rowBig lam (directionRow o e c (v.succAbove j)) = 1 ∧
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j <
        lam ∧
      ∀ w : Fin s, w ≠ j → theta w < theta j →
        dirRep o e (c ∘ v.succAbove) j w =
          (directionRow o e (c ∘ v.succAbove) j).head hne →
        ¬ (rowDefect n lam (directionRow o e c (v.succAbove w)) = 2 ∧
           rowBig lam (directionRow o e c (v.succAbove w)) = 1) := by
  classical
  set T : Finset (Fin s) := Finset.univ.filter fun j =>
    rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
    rowBig lam (directionRow o e c (v.succAbove j)) = 1 ∧
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j < lam
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hT
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨j, hjT, hmin⟩ := Finset.exists_min_image T theta hTne
  obtain ⟨-, hdef, hbig, hne, hshort⟩ := Finset.mem_filter.mp hjT
  refine ⟨j, hne, hdef, hbig, hshort, ?_⟩
  intro w hwj hwt hdir
  rintro ⟨hdefw, hbigw⟩
  have hshort' := type_I_first_receiver_is_first_short o e he hn3 hlam
    hn hleg v htheta hs (j := w) (i₁ := j) hwj.symm hwt
    (by rw [hdir]; exact hshort) hdefw hbigw
  obtain ⟨hnew, hshortw⟩ := hshort'
  have hwT : w ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_univ w, hdefw, hbigw, hnew, hshortw⟩
  have hle := hmin w hwT
  linarith

/-- **Type I last-chain termination** (symmetric): the `θ`-maximal
Type I defect-`2` row with a short last gap cannot have its last-gap
witness land on another Type I defect-`2` row. -/
theorem type_I_last_witness_leaves_type_I {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s)
    (hT : ∃ j : Fin s,
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      rowBig lam (directionRow o e c (v.succAbove j)) = 1 ∧
      ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
        theta j + Real.pi -
          (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam) :
    ∃ j : Fin s, ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      rowBig lam (directionRow o e c (v.succAbove j)) = 1 ∧
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam ∧
      ∀ w : Fin s, w ≠ j → theta j < theta w →
        dirRep o e (c ∘ v.succAbove) j w =
          (directionRow o e (c ∘ v.succAbove) j).getLast hne →
        ¬ (rowDefect n lam (directionRow o e c (v.succAbove w)) = 2 ∧
           rowBig lam (directionRow o e c (v.succAbove w)) = 1) := by
  classical
  set T : Finset (Fin s) := Finset.univ.filter fun j =>
    rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
    rowBig lam (directionRow o e c (v.succAbove j)) = 1 ∧
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hT
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨j, hjT, hmax⟩ := Finset.exists_max_image T theta hTne
  obtain ⟨-, hdef, hbig, hne, hshort⟩ := Finset.mem_filter.mp hjT
  refine ⟨j, hne, hdef, hbig, hshort, ?_⟩
  intro w hwj hwt hdir
  rintro ⟨hdefw, hbigw⟩
  have hshort' := type_I_last_receiver_is_last_short o e he hn3 hlam
    hn hleg v htheta hs (j := w) (i₂ := j) hwj.symm hwt
    (by rw [hdir]; exact hshort) hdefw hbigw
  obtain ⟨hnew, hshortw⟩ := hshort'
  have hwT : w ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_univ w, hdefw, hbigw, hnew, hshortw⟩
  have hle := hmax w hwT
  linarith

/-- **Type II propagation, first end.**  A Type II defect-`2` row `j`
receiving a short-first witness from a higher-`θ` source satisfies a
trichotomy: it is itself short-first, or it is short-last, or both end
gaps are big — the in-arc `floor = 1` gap sits at index `0` and the
out-arc `floor = n−1` gap sits at the last index. -/
theorem type_II_first_receiver_trichotomy {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₁ : Fin s}
    (hi₁j : i₁ ≠ j) (hlt₁ : theta j < theta i₁)
    (hgap₁ : dirRep o e (c ∘ v.succAbove) i₁ j - theta i₁ < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hTII : rowBig lam (directionRow o e c (v.succAbove j)) = 2) :
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j <
        lam ∨
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam ∨
      (⌊((directionRow o e (c ∘ v.succAbove) j).head hne - theta j) /
          lam⌋₊ = 1 ∧
        ⌊(theta j + Real.pi -
          (directionRow o e (c ∘ v.succAbove) j).getLast hne) / lam⌋₊ =
          n - 1) := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₁eq : dirRep o e (c ∘ v.succAbove) j i₁ =
      dirRep o e (c ∘ v.succAbove) i₁ j :=
    dirRep_comm o e _ he (fun h => hi₁j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₁ := dirRep o e (c ∘ v.succAbove) j i₁ with hφ₁def
  have hφ₁low : lam + theta j ≤ φ₁ := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_bot_sliver_forces_low o e he hn2 hlam hn
      hleg v htheta j i₁ hi₁j.symm (t := theta j) le_rfl hlt
    linarith
  have hφ₁gt : theta j < φ₁ := by linarith
  have hφ₁' : φ₁ = dirRep o e (c ∘ v.succAbove) i₁ j :=
    hφ₁def.trans hφ₁eq
  have hA₁up : φ₁ - theta j < 2 * lam := by
    rw [hφ₁']
    have h2 : theta i₁ ≤ Real.pi - n * lam := (htheta i₁).1.2
    have h3 : 0 ≤ theta j := (htheta j).1.1
    linarith
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: directionRow o e (c ∘ v.succAbove) j := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    rw [List.get_of_eq hcons, List.get_mk_zero, List.head_cons]
  have hφ₁mem : φ₁ ∈ l := by
    rw [hcons]
    exact List.mem_cons_of_mem _
      ((mem_directionRow o e _).mpr ⟨i₁, hi₁j, hφ₁def⟩)
  obtain ⟨b₁, hgb₁⟩ := List.get_of_mem hφ₁mem
  have hcells : rowCells lam l ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove j)
      (by omega) hn
  have hT₁cells : ∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
      ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc hlam hsort hmem
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
    rw [hget0, hgb₁, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    have h2 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h hA₁up
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
        ⌊gapAfter l t / lam⌋₊) < 2 := by exact_mod_cast h3
    omega
  have hT₁len : lam ≤ ∑ t ∈ Finset.Ico ⟨0, hlen⟩ b₁,
      gapAfter l t := by
    have h := cyclicDiff_eq_Ico_sum_gapAfter hsort
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
    rw [hget0, hgb₁, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    linarith
  obtain ⟨s_out, hs_out, s_in, hs_in, hf_out, hf_in, hout_small,
    hin_small⟩ := defect_two_type_II_arc_structure hlam hn hn3 hsort
    hmem hcells hdef hTII (Finset.Ico ⟨0, hlen⟩ b₁) hT₁cells hT₁len
  have hb₁pos : (⟨0, hlen⟩ : Fin l.length) < b₁ :=
    lt_of_le_of_ne
      (show (⟨0, hlen⟩ : Fin l.length) ≤ b₁ from Nat.zero_le _)
      fun h0eq => by
        have hge : l.get b₁ = l.get ⟨0, hlen⟩ :=
          congrArg (l.get ·) h0eq.symm
        rw [hgb₁, hget0] at hge
        linarith
  have h0mem : (⟨0, hlen⟩ : Fin l.length) ∈ Finset.Ico ⟨0, hlen⟩ b₁ :=
    Finset.mem_Ico.mpr ⟨le_rfl, hb₁pos⟩
  set lastIdx : Fin l.length := ⟨l.length - 1, by omega⟩
  have blast_out : lastIdx ∉ Finset.Ico ⟨0, hlen⟩ b₁ := by
    rw [Finset.mem_Ico, not_and]
    intro _ hlt
    exact absurd hlt (not_lt.mpr (Nat.le_pred_of_lt b₁.2))
  -- Transports to the sub-list head / getLast.
  have hsub_ne : directionRow o e (c ∘ v.succAbove) j ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [directionRow_length]; omega
  have h1lt : 1 < l.length := by
    rw [hldef, directionRow_length]; omega
  have hgap0 : gapAfter l ⟨0, hlen⟩ =
      (directionRow o e (c ∘ v.succAbove) j).head hsub_ne - theta j := by
    unfold gapAfter
    rw [dif_pos (show (0 : ℕ) + 1 < l.length by omega)]
    rw [List.get_of_eq hcons, List.get_cons_succ, List.get_mk_zero,
      hget0]
  have hgl : l.getLast? =
      (directionRow o e (c ∘ v.succAbove) j).getLast? := by
    rw [hcons]
    exact List.getLast?_cons_of_ne_nil hsub_ne
  have hgl' : l.getLast hne =
      (directionRow o e (c ∘ v.succAbove) j).getLast hsub_ne := by
    have e1 := List.getLast?_eq_getLast hne
    have e2 := List.getLast?_eq_getLast hsub_ne
    rw [hgl, e2] at e1
    exact (Option.some.inj e1).symm
  have hglast : gapAfter l lastIdx = theta j + Real.pi -
      (directionRow o e (c ∘ v.succAbove) j).getLast hsub_ne := by
    unfold gapAfter
    rw [dif_neg (show ¬ (l.length - 1 + 1 : ℕ) < l.length by omega)]
    rw [hget0]
    congr 1
    exact ((List.getLast_eq_getElem hne).symm.trans hgl')
  refine ⟨hsub_ne, ?_⟩
  by_cases h0 : (⟨0, hlen⟩ : Fin l.length) = s_in
  · by_cases hl : lastIdx = s_out
    · exact Or.inr (Or.inr ⟨by
          rw [← hgap0]; exact h0.symm ▸ hf_in, by
          rw [← hglast]; exact hl.symm ▸ hf_out⟩)
    · refine Or.inr (Or.inl ?_)
      rw [← hglast]
      exact hout_small lastIdx blast_out hl
  · refine Or.inl ?_
    rw [← hgap0]
    exact hin_small ⟨0, hlen⟩ h0mem h0

/-- **Type II propagation, last end.**  A Type II defect-`2` row `j`
receiving a short-last witness from a lower-`θ` source satisfies the
mirror trichotomy: short-last, short-first, or both ends big with the
`floor = n−1` gap at index `0` and the `floor = 1` gap at the last
index. -/
theorem type_II_last_receiver_trichotomy {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₂ : Fin s}
    (hi₂j : i₂ ≠ j) (hlt₂ : theta i₂ < theta j)
    (hgap₂ : theta i₂ + Real.pi -
      dirRep o e (c ∘ v.succAbove) i₂ j < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hTII : rowBig lam (directionRow o e c (v.succAbove j)) = 2) :
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j <
        lam ∨
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam ∨
      (⌊((directionRow o e (c ∘ v.succAbove) j).head hne - theta j) /
          lam⌋₊ = n - 1 ∧
        ⌊(theta j + Real.pi -
          (directionRow o e (c ∘ v.succAbove) j).getLast hne) / lam⌋₊ =
          1) := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  set sub := directionRow o e (c ∘ v.succAbove) j with hsubdef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₂eq : dirRep o e (c ∘ v.succAbove) j i₂ =
      dirRep o e (c ∘ v.succAbove) i₂ j :=
    dirRep_comm o e _ he (fun h => hi₂j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₂ := dirRep o e (c ∘ v.succAbove) j i₂ with hφ₂def
  have hφ₂high : φ₂ ≤ Real.pi - lam + theta j := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_top_sliver_forces_high o e he hn2 hlam hn
      hleg v htheta j i₂ hi₂j.symm (u := theta j) le_rfl hlt
    linarith
  have hφ₂gt : theta j < φ₂ := by
    have h1 : lam ≤ φ₂ := (hcorr j i₂ hi₂j.symm).1
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    linarith
  have hφ₂le : theta j ≤ φ₂ := hφ₂gt.le
  have hφ₂' : φ₂ = dirRep o e (c ∘ v.succAbove) i₂ j :=
    hφ₂def.trans hφ₂eq
  have hA₂up : theta j + Real.pi - φ₂ < 2 * lam := by
    rw [hφ₂']
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    have h3 : 0 ≤ theta i₂ := (htheta i₂).1.1
    linarith
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hsort hmem hne t
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: sub := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    rw [List.get_of_eq hcons, List.get_mk_zero, List.head_cons]
  have hφ₂mem : φ₂ ∈ l := by
    rw [hcons]
    exact List.mem_cons_of_mem _
      ((mem_directionRow o e _).mpr ⟨i₂, hi₂j, hφ₂def⟩)
  obtain ⟨b₂, hgb₂⟩ := List.get_of_mem hφ₂mem
  have hcells : rowCells lam l ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove j)
      (by omega) hn
  have hbwrap : l.get ⟨0, Nat.zero_lt_of_lt b₂.2⟩ ≠ l.get b₂ := by
    rw [hget0, hgb₂]
    exact ne_of_lt hφ₂gt
  have hcd₂ : cyclicDiff φ₂ (theta j) = Real.pi + theta j - φ₂ := by
    have h1 := cyclicDiff_add_rev (ne_of_gt hφ₂gt)
    rw [cyclicDiff_eq_sub_of_le hφ₂le] at h1
    linarith
  have hT₂cells : ∑ t ∈ Finset.Ici b₂, ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc_wrap hlam hsort hmem b₂ hbwrap
    rw [hgb₂, hget0, hcd₂] at h
    have h2 : (∑ t ∈ Finset.Ici b₂,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h (by linarith : Real.pi + theta j - φ₂ < 2 * lam)
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ici b₂, ⌊gapAfter l t / lam⌋₊) < 2 := by
      exact_mod_cast h3
    omega
  have hT₂len : lam ≤ ∑ t ∈ Finset.Ici b₂, gapAfter l t := by
    have h := gapAfter_sum_Ici hsort b₂ hbwrap
    rw [hgb₂, hget0, hcd₂] at h
    linarith
  obtain ⟨s_out, hs_out, s_in, hs_in, hf_out, hf_in, hout_small,
    hin_small⟩ := defect_two_type_II_arc_structure hlam hn hn3 hsort
    hmem hcells hdef hTII (Finset.Ici b₂) hT₂cells hT₂len
  set lastIdx : Fin l.length := ⟨l.length - 1, by omega⟩
  have blast : lastIdx ∈ Finset.Ici b₂ :=
    Finset.mem_Ici.mpr (Nat.le_pred_of_lt b₂.2)
  have hb₂pos : (⟨0, hlen⟩ : Fin l.length) < b₂ := by
    by_contra hcon
    push_neg at hcon
    have hz : b₂.val = 0 := Nat.le_zero.mp hcon
    have hfin : b₂ = ⟨0, Nat.zero_lt_of_lt b₂.2⟩ := Fin.ext hz
    have hge : l.get b₂ = theta j := by rw [hfin, hget0]
    rw [hgb₂] at hge
    linarith
  have h0out : (⟨0, hlen⟩ : Fin l.length) ∉ Finset.Ici b₂ := by
    rw [Finset.mem_Ici, not_le]
    exact hb₂pos
  -- Transports to the sub-list head / getLast.
  have hsub_ne : sub ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hsubdef, directionRow_length]; omega
  have h1lt : 1 < l.length := by
    rw [hldef, directionRow_length]; omega
  have hgap0 : gapAfter l ⟨0, hlen⟩ =
      sub.head hsub_ne - theta j := by
    unfold gapAfter
    rw [dif_pos (show (0 : ℕ) + 1 < l.length by omega)]
    rw [List.get_of_eq hcons, List.get_cons_succ, List.get_mk_zero,
      hget0]
  have hgl : l.getLast? = sub.getLast? := by
    rw [hcons]
    exact List.getLast?_cons_of_ne_nil hsub_ne
  have hgl' : l.getLast hne = sub.getLast hsub_ne := by
    have e1 := List.getLast?_eq_getLast hne
    have e2 := List.getLast?_eq_getLast hsub_ne
    rw [hgl, e2] at e1
    exact (Option.some.inj e1).symm
  have hglast : gapAfter l lastIdx =
      theta j + Real.pi - sub.getLast hsub_ne := by
    unfold gapAfter
    rw [dif_neg (show ¬ (l.length - 1 + 1 : ℕ) < l.length by omega)]
    rw [hget0]
    congr 1
    exact ((List.getLast_eq_getElem hne).symm.trans hgl')
  refine ⟨hsub_ne, ?_⟩
  by_cases hl : lastIdx = s_in
  · by_cases h0 : (⟨0, hlen⟩ : Fin l.length) = s_out
    · exact Or.inr (Or.inr ⟨by
          rw [← hgap0]; exact h0.symm ▸ hf_out, by
          rw [← hglast]; exact hl.symm ▸ hf_in⟩)
    · refine Or.inl ?_
      rw [← hgap0]
      exact hout_small ⟨0, hlen⟩ h0out h0
  · refine Or.inr (Or.inl ?_)
    rw [← hglast]
    exact hin_small lastIdx blast hl

/-- **Defect-`2` first-chain classification.**  Among all defect-`2`
rows with a short first gap (either type), the `θ`-minimal one's
first-gap witness cannot return to a defect-`2` short-first row:
- a Type I target would itself be short-first (propagation), and
- a Type II target in the short-first branch would be too;
both contradict minimality.  So a defect-`2` target of that witness
must be Type II and is either short-last or both-ends-big. -/
theorem defect_two_first_witness_classification {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s)
    (hT : ∃ j : Fin s,
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
        (directionRow o e (c ∘ v.succAbove) j).head hne - theta j <
          lam) :
    ∃ j : Fin s, ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j <
        lam ∧
      ∀ w : Fin s, w ≠ j → theta w < theta j →
        dirRep o e (c ∘ v.succAbove) j w =
          (directionRow o e (c ∘ v.succAbove) j).head hne →
        rowDefect n lam (directionRow o e c (v.succAbove w)) = 2 →
        ∃ hnew : directionRow o e (c ∘ v.succAbove) w ≠ [],
          rowBig lam (directionRow o e c (v.succAbove w)) = 2 ∧
          (theta w + Real.pi -
            (directionRow o e (c ∘ v.succAbove) w).getLast hnew <
              lam ∨
            (⌊((directionRow o e (c ∘ v.succAbove) w).head hnew -
                  theta w) / lam⌋₊ = 1 ∧
              ⌊(theta w + Real.pi -
                (directionRow o e (c ∘ v.succAbove) w).getLast hnew) /
                lam⌋₊ = n - 1)) := by
  classical
  set T : Finset (Fin s) := Finset.univ.filter fun j =>
    rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j < lam
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hT
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨j, hjT, hmin⟩ := Finset.exists_min_image T theta hTne
  obtain ⟨-, hdef, hne, hshort⟩ := Finset.mem_filter.mp hjT
  refine ⟨j, hne, hdef, hshort, ?_⟩
  intro w hwj hwt hdir hdefw
  have hcellsw : rowCells lam (directionRow o e c (v.succAbove w)) ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove w)
      (by omega) hn
  rcases rowDefect_eq_two_type hlam hn3 hcellsw hdefw with
    ⟨hB1, _⟩ | ⟨hB2, _⟩
  · -- Type I target: propagation makes it short-first — impossible.
    obtain ⟨hnew, hshortw⟩ :=
      type_I_first_receiver_is_first_short o e he hn3 hlam
        hn hleg v htheta hs (j := w) (i₁ := j) hwj.symm hwt
        (by rw [hdir]; exact hshort) hdefw hB1
    exfalso
    have hwT : w ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_univ w, hdefw, hnew, hshortw⟩
    have hle := hmin w hwT
    linarith
  · -- Type II target: only the short-last / both-big branches survive.
    obtain ⟨hnew, htr⟩ :=
      type_II_first_receiver_trichotomy o e he hn3 hlam
        hn hleg v htheta hs (j := w) (i₁ := j) hwj.symm hwt
        (by rw [hdir]; exact hshort) hdefw hB2
    refine ⟨hnew, hB2, ?_⟩
    rcases htr with hf | hl | hb
    · exfalso
      have hwT : w ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_univ w, hdefw, hnew, hf⟩
      have hle := hmin w hwT
      linarith
    · exact Or.inl hl
    · exact Or.inr hb

/-- **Defect-`2` last-chain classification** (symmetric): the
`θ`-maximal defect-`2` row with a short last gap cannot witness back to
a defect-`2` short-last row; a defect-`2` target must be Type II and is
either short-first or both-ends-big (`floor = n−1` at index `0`,
`floor = 1` at the last index). -/
theorem defect_two_last_witness_classification {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s)
    (hT : ∃ j : Fin s,
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
        theta j + Real.pi -
          (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam) :
    ∃ j : Fin s, ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam ∧
      ∀ w : Fin s, w ≠ j → theta j < theta w →
        dirRep o e (c ∘ v.succAbove) j w =
          (directionRow o e (c ∘ v.succAbove) j).getLast hne →
        rowDefect n lam (directionRow o e c (v.succAbove w)) = 2 →
        ∃ hnew : directionRow o e (c ∘ v.succAbove) w ≠ [],
          rowBig lam (directionRow o e c (v.succAbove w)) = 2 ∧
          ((directionRow o e (c ∘ v.succAbove) w).head hnew - theta w <
              lam ∨
            (⌊((directionRow o e (c ∘ v.succAbove) w).head hnew -
                  theta w) / lam⌋₊ = n - 1 ∧
              ⌊(theta w + Real.pi -
                (directionRow o e (c ∘ v.succAbove) w).getLast hnew) /
                lam⌋₊ = 1)) := by
  classical
  set T : Finset (Fin s) := Finset.univ.filter fun j =>
    rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 ∧
    ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hT
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨j, hjT, hmax⟩ := Finset.exists_max_image T theta hTne
  obtain ⟨-, hdef, hne, hshort⟩ := Finset.mem_filter.mp hjT
  refine ⟨j, hne, hdef, hshort, ?_⟩
  intro w hwj hwt hdir hdefw
  have hcellsw : rowCells lam (directionRow o e c (v.succAbove w)) ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove w)
      (by omega) hn
  rcases rowDefect_eq_two_type hlam hn3 hcellsw hdefw with
    ⟨hB1, _⟩ | ⟨hB2, _⟩
  · -- Type I target: propagation makes it short-last — impossible.
    obtain ⟨hnew, hshortw⟩ :=
      type_I_last_receiver_is_last_short o e he hn3 hlam
        hn hleg v htheta hs (j := w) (i₂ := j) hwj.symm hwt
        (by rw [hdir]; exact hshort) hdefw hB1
    exfalso
    have hwT : w ∈ T := Finset.mem_filter.mpr
      ⟨Finset.mem_univ w, hdefw, hnew, hshortw⟩
    have hle := hmax w hwT
    linarith
  · -- Type II target: only the short-first / both-big branches survive.
    obtain ⟨hnew, htr⟩ :=
      type_II_last_receiver_trichotomy o e he hn3 hlam
        hn hleg v htheta hs (j := w) (i₂ := j) hwj.symm hwt
        (by rw [hdir]; exact hshort) hdefw hB2
    refine ⟨hnew, hB2, ?_⟩
    rcases htr with hf | hl | hb
    · exact Or.inl hf
    · exfalso
      have hwT : w ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_univ w, hdefw, hnew, hl⟩
      have hle := hmax w hwT
      linarith
    · exact Or.inr hb

/-- **No immediate return.**  If a defect-`2` row `j` receives
a short-first witness from a higher-`θ` source `i₁` and is itself
short-last, then its last row element cannot be the source chord
`dirRep j i₁`: otherwise the receiving arc extends to `Ico 0 lastIdx`,
whose complement is `{lastIdx}` — forcing the unique outside floor-`n−1`
gap `s_out = lastIdx`, i.e. the last gap would have length `≥ (n−1)λ`,
against the short-last hypothesis `< λ`.  Hence a defect-`2` short-last
receiver's own last-gap witness always points to a *different* vertex
than the source — the witness relation has no two-cycle inside
defect-`2`.  Holds for both Type I and Type II receivers. -/
theorem defect_two_short_last_witness_ne_source {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₁ : Fin s}
    (hi₁j : i₁ ≠ j) (hlt₁ : theta j < theta i₁)
    (hgap₁ : dirRep o e (c ∘ v.succAbove) i₁ j - theta i₁ < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hlast : ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam) :
    ∀ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).getLast hne ≠
        dirRep o e (c ∘ v.succAbove) j i₁ := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₁eq : dirRep o e (c ∘ v.succAbove) j i₁ =
      dirRep o e (c ∘ v.succAbove) i₁ j :=
    dirRep_comm o e _ he (fun h => hi₁j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₁ := dirRep o e (c ∘ v.succAbove) j i₁ with hφ₁def
  have hφ₁low : lam + theta j ≤ φ₁ := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_bot_sliver_forces_low o e he hn2 hlam hn
      hleg v htheta j i₁ hi₁j.symm (t := theta j) le_rfl hlt
    linarith
  have hφ₁gt : theta j < φ₁ := by linarith
  have hφ₁' : φ₁ = dirRep o e (c ∘ v.succAbove) i₁ j :=
    hφ₁def.trans hφ₁eq
  have hA₁up : φ₁ - theta j < 2 * lam := by
    rw [hφ₁']
    have h2 : theta i₁ ≤ Real.pi - n * lam := (htheta i₁).1.2
    have h3 : 0 ≤ theta j := (htheta j).1.1
    linarith
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: directionRow o e (c ∘ v.succAbove) j := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    rw [List.get_of_eq hcons, List.get_mk_zero, List.head_cons]
  obtain ⟨hsub_ne, hlast_short⟩ := hlast
  have hcells : rowCells lam l ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove j)
      (by omega) hn
  set lastIdx : Fin l.length := ⟨l.length - 1, by omega⟩
  -- The last row element `l.get lastIdx` transports to `sub.getLast`.
  have hgl : l.getLast? =
      (directionRow o e (c ∘ v.succAbove) j).getLast? := by
    rw [hcons]
    exact List.getLast?_cons_of_ne_nil hsub_ne
  have hgl' : l.getLast hne =
      (directionRow o e (c ∘ v.succAbove) j).getLast hsub_ne := by
    have e1 := List.getLast?_eq_getLast hne
    have e2 := List.getLast?_eq_getLast hsub_ne
    rw [hgl, e2] at e1
    exact (Option.some.inj e1).symm
  have hglast : gapAfter l lastIdx = theta j + Real.pi -
      (directionRow o e (c ∘ v.succAbove) j).getLast hsub_ne := by
    unfold gapAfter
    rw [dif_neg (show ¬ (l.length - 1 + 1 : ℕ) < l.length by omega)]
    rw [hget0]
    congr 1
    exact ((List.getLast_eq_getElem hne).symm.trans hgl')
  have hgap_last : gapAfter l lastIdx < lam := by
    rw [hglast]; exact hlast_short
  -- Suppose the last element is the source chord `φ₁`.
  intro hne' heq
  -- `heq : sub.getLast hne' = φ₁`; transport to `l.get lastIdx = φ₁`.
  have hlast_eq : l.get lastIdx = φ₁ := by
    have hpi : (directionRow o e (c ∘ v.succAbove) j).getLast hsub_ne =
        (directionRow o e (c ∘ v.succAbove) j).getLast hne' := rfl
    have h3 : l.get lastIdx = l.getLast hne :=
      (List.getLast_eq_getElem hne).symm
    calc l.get lastIdx = l.getLast hne := h3
      _ = (directionRow o e (c ∘ v.succAbove) j).getLast hsub_ne := hgl'
      _ = (directionRow o e (c ∘ v.succAbove) j).getLast hne' := hpi
      _ = φ₁ := heq
  -- The arc `Ico ⟨0⟩ lastIdx` has the same endpoint `φ₁`.
  have hTcells : ∑ t ∈ Finset.Ico ⟨0, hlen⟩ lastIdx,
      ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc hlam hsort hmem
      (show (⟨0, hlen⟩ : Fin l.length) ≤ lastIdx from Nat.zero_le _)
    rw [hget0, hlast_eq, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    have h2 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ lastIdx,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h hA₁up
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ico ⟨0, hlen⟩ lastIdx,
        ⌊gapAfter l t / lam⌋₊) < 2 := by exact_mod_cast h3
    omega
  have hTlen : lam ≤ ∑ t ∈ Finset.Ico ⟨0, hlen⟩ lastIdx,
      gapAfter l t := by
    have h := cyclicDiff_eq_Ico_sum_gapAfter hsort
      (show (⟨0, hlen⟩ : Fin l.length) ≤ lastIdx from Nat.zero_le _)
    rw [hget0, hlast_eq, cyclicDiff_eq_sub_of_le hφ₁gt.le] at h
    linarith
  obtain ⟨s_out, hs_out, hf_out⟩ := defect_two_big_gap_avoids_arc hlam
    hn hn3 hsort hmem hcells hdef (Finset.Ico ⟨0, hlen⟩ lastIdx)
    hTcells hTlen
  -- The complement of `Ico 0 lastIdx` is `{lastIdx}`.
  have hs_out_eq : s_out = lastIdx := by
    have hmem' := Finset.mem_sdiff.mp hs_out
    by_contra hne''
    exact hmem'.2 (Finset.mem_Ico.mpr ⟨Nat.zero_le _,
      lt_of_le_of_ne (Nat.le_pred_of_lt s_out.2)
        (fun h => hne'' h)⟩)
  have hgs : 2 * lam ≤ gapAfter l lastIdx := by
    have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
      fun t => gapAfter_nonneg hsort hmem hne t
    have h2 := floor_mul_le_gap hlam (hnn lastIdx)
    have hf : ((n - 1 : ℕ) : ℝ) ≤
        (⌊gapAfter l lastIdx / lam⌋₊ : ℝ) := by
      rw [hs_out_eq] at hf_out
      exact_mod_cast hf_out
    have hfm : ((n - 1 : ℕ) : ℝ) * lam ≤
        (⌊gapAfter l lastIdx / lam⌋₊ : ℝ) * lam :=
      mul_le_mul_of_nonneg_right hf hlam.le
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n), Nat.cast_one] at hfm
    have hnn1 : (2 : ℝ) ≤ ↑n - 1 := by
      have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      linarith
    have hmul : 2 * lam ≤ (↑n - 1) * lam :=
      mul_le_mul_of_nonneg_right hnn1 hlam.le
    linarith
  linarith

/-- **No immediate return, first end** (mirror): a defect-`2`
row `j` receiving a short-last witness from a lower-`θ` source `i₂` and
itself short-first cannot have `dirRep j i₂` as its first row element:
otherwise the wrapped arc `Ici ⟨1⟩` has complement `{⟨0⟩}`, forcing
`s_out = ⟨0⟩`, i.e. the first gap would have floor `n−1` and length
`≥ (n−1)λ`, against the short-first hypothesis.  Holds for both Type I
and Type II receivers. -/
theorem defect_two_short_first_witness_ne_source {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₂ : Fin s}
    (hi₂j : i₂ ≠ j) (hlt₂ : theta i₂ < theta j)
    (hgap₂ : theta i₂ + Real.pi -
      dirRep o e (c ∘ v.succAbove) i₂ j < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hfirst : ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).head hne - theta j < lam) :
    ∀ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      (directionRow o e (c ∘ v.succAbove) j).head hne ≠
        dirRep o e (c ∘ v.succAbove) j i₂ := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  set sub := directionRow o e (c ∘ v.succAbove) j with hsubdef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₂eq : dirRep o e (c ∘ v.succAbove) j i₂ =
      dirRep o e (c ∘ v.succAbove) i₂ j :=
    dirRep_comm o e _ he (fun h => hi₂j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₂ := dirRep o e (c ∘ v.succAbove) j i₂ with hφ₂def
  have hφ₂high : φ₂ ≤ Real.pi - lam + theta j := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_top_sliver_forces_high o e he hn2 hlam hn
      hleg v htheta j i₂ hi₂j.symm (u := theta j) le_rfl hlt
    linarith
  have hφ₂gt : theta j < φ₂ := by
    have h1 : lam ≤ φ₂ := (hcorr j i₂ hi₂j.symm).1
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    linarith
  have hφ₂le : theta j ≤ φ₂ := hφ₂gt.le
  have hφ₂' : φ₂ = dirRep o e (c ∘ v.succAbove) i₂ j :=
    hφ₂def.trans hφ₂eq
  have hA₂up : theta j + Real.pi - φ₂ < 2 * lam := by
    rw [hφ₂']
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    have h3 : 0 ≤ theta i₂ := (htheta i₂).1.1
    linarith
  have hne : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi :=
    fun x hx => directionRow_mem_Ico o e c hx
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: sub := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    rw [List.get_of_eq hcons, List.get_mk_zero, List.head_cons]
  obtain ⟨hsub_ne, hfirst_short⟩ := hfirst
  have hcells : rowCells lam l ≤ n :=
    rowCells_directionRow_le_of_floor_eq o e c hlam (v.succAbove j)
      (by omega) hn
  have h1lt : 1 < l.length := by
    rw [hldef, directionRow_length]; omega
  have hhead : l.get ⟨1, h1lt⟩ = sub.head hsub_ne := by
    rw [List.get_of_eq hcons, List.get_cons_succ, List.get_mk_zero]
  have hgap0 : gapAfter l ⟨0, hlen⟩ = sub.head hsub_ne - theta j := by
    unfold gapAfter
    rw [dif_pos (show (0 : ℕ) + 1 < l.length by omega)]
    rw [List.get_of_eq hcons, List.get_cons_succ, List.get_mk_zero,
      hget0]
  have hgap_first : gapAfter l ⟨0, hlen⟩ < lam := by
    rw [hgap0]; exact hfirst_short
  intro hne' heq
  have hfirst_eq : l.get ⟨1, h1lt⟩ = φ₂ := by
    have hpi : sub.head hsub_ne = sub.head hne' := rfl
    calc l.get ⟨1, h1lt⟩ = sub.head hsub_ne := hhead
      _ = sub.head hne' := hpi
      _ = φ₂ := heq
  -- The wrapped arc `Ici ⟨1⟩` ends at `φ₂`.
  set oneIdx : Fin l.length := ⟨1, h1lt⟩
  have hbwrap : l.get ⟨0, Nat.zero_lt_of_lt oneIdx.2⟩ ≠ l.get oneIdx := by
    rw [hget0]
    show theta j ≠ l.get ⟨1, h1lt⟩
    rw [hfirst_eq]
    exact ne_of_lt hφ₂gt
  have hcd : cyclicDiff φ₂ (theta j) = Real.pi + theta j - φ₂ := by
    have h1 := cyclicDiff_add_rev (ne_of_gt hφ₂gt)
    rw [cyclicDiff_eq_sub_of_le hφ₂le] at h1
    linarith
  have hTcells : ∑ t ∈ Finset.Ici oneIdx, ⌊gapAfter l t / lam⌋₊ ≤ 1 := by
    have h := arc_cells_le_arc_wrap hlam hsort hmem oneIdx hbwrap
    rw [show l.get oneIdx = φ₂ from hfirst_eq, hget0, hcd] at h
    have h2 : (∑ t ∈ Finset.Ici oneIdx,
        (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam < 2 * lam :=
      lt_of_le_of_lt h (by linarith : Real.pi + theta j - φ₂ < 2 * lam)
    have h3 := lt_of_mul_lt_mul_right h2 hlam.le
    rw [← Nat.cast_sum] at h3
    have h4 : (∑ t ∈ Finset.Ici oneIdx, ⌊gapAfter l t / lam⌋₊) < 2 := by
      exact_mod_cast h3
    omega
  have hTlen : lam ≤ ∑ t ∈ Finset.Ici oneIdx, gapAfter l t := by
    have h := gapAfter_sum_Ici hsort oneIdx hbwrap
    rw [show l.get oneIdx = φ₂ from hfirst_eq, hget0, hcd] at h
    linarith
  obtain ⟨s_out, hs_out, hf_out⟩ := defect_two_big_gap_avoids_arc hlam
    hn hn3 hsort hmem hcells hdef (Finset.Ici oneIdx) hTcells hTlen
  -- The complement of `Ici ⟨1⟩` is `{⟨0⟩}`.
  have hs_out_eq : s_out = (⟨0, hlen⟩ : Fin l.length) := by
    have hmem' := Finset.mem_sdiff.mp hs_out
    by_contra hne''
    have hpos : 1 ≤ s_out.val := Nat.one_le_iff_ne_zero.mpr
      fun h => hne'' (Fin.ext h)
    exact hmem'.2 (Finset.mem_Ici.mpr hpos)
  have hgs : 2 * lam ≤ gapAfter l ⟨0, hlen⟩ := by
    have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
      fun t => gapAfter_nonneg hsort hmem hne t
    have h2 := floor_mul_le_gap hlam (hnn ⟨0, hlen⟩)
    have hf : ((n - 1 : ℕ) : ℝ) ≤
        (⌊gapAfter l ⟨0, hlen⟩ / lam⌋₊ : ℝ) := by
      rw [hs_out_eq] at hf_out
      exact_mod_cast hf_out
    have hfm : ((n - 1 : ℕ) : ℝ) * lam ≤
        (⌊gapAfter l ⟨0, hlen⟩ / lam⌋₊ : ℝ) * lam :=
      mul_le_mul_of_nonneg_right hf hlam.le
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ n), Nat.cast_one] at hfm
    have hnn1 : (2 : ℝ) ≤ ↑n - 1 := by
      have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      linarith
    have hmul : 2 * lam ≤ (↑n - 1) * lam :=
      mul_le_mul_of_nonneg_right hnn1 hlam.le
    linarith
  linarith

/-- **No witness two-cycles inside defect-`2`.**  Rows `a < b` (in `θ`)
cannot be mutual short-end witnesses: if `a`'s last row element is the
shared chord `dirRep a b` with a short last gap (`a`'s last-witness is
`b`) and `b`'s first row element is `dirRep b a` with a short first gap
(`b`'s first-witness is `a`), contradiction.  The shared chord `φ` would
have to sit simultaneously at `a`'s last end and inside `a`'s receiving
arc complement as the unique floor-`n−1` gap. -/
theorem defect_two_witness_no_two_cycle {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {a b : Fin s} (htab : theta a < theta b)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2)
    (ha : ∃ hne : directionRow o e (c ∘ v.succAbove) a ≠ [],
      (directionRow o e (c ∘ v.succAbove) a).getLast hne =
        dirRep o e (c ∘ v.succAbove) a b ∧
      theta a + Real.pi -
        (directionRow o e (c ∘ v.succAbove) a).getLast hne < lam)
    (hb : ∃ hne : directionRow o e (c ∘ v.succAbove) b ≠ [],
      (directionRow o e (c ∘ v.succAbove) b).head hne =
        dirRep o e (c ∘ v.succAbove) b a ∧
      (directionRow o e (c ∘ v.succAbove) b).head hne - theta b < lam) :
    False := by
  classical
  obtain ⟨hne_a, hlast_a, hshort_a⟩ := ha
  obtain ⟨hne_b, hhead_b, hshort_b⟩ := hb
  have hba : b ≠ a := fun h =>
    (ne_of_lt htab) (congrArg theta h).symm
  have hgap₁ : dirRep o e (c ∘ v.succAbove) b a - theta b < lam :=
    hhead_b ▸ hshort_b
  exact defect_two_short_last_witness_ne_source o e he hn3 hlam hn
    hleg v htheta hs hba htab hgap₁ hda ⟨hne_a, hshort_a⟩
    hne_a hlast_a

/-- **Extremal exit, first end.**  If `j` is a short-first defect-`2`
row whose `θ` is minimal *among all defect-`2` rows*, then its
first-witness exits the defect-`2` set: the witness `w` has
`θ_w < θ_j`, so `w` cannot be defect-`2`; with the global
defect-`≥ 2` hypothesis its defect is `≥ 3`. -/
theorem first_witness_of_min_defect_two_high {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hge2 : ∀ r : Fin s,
      2 ≤ rowDefect n lam (directionRow o e c (v.succAbove r)))
    {j : Fin s}
    (hmin : ∀ r : Fin s,
      rowDefect n lam (directionRow o e c (v.succAbove r)) = 2 →
        theta j ≤ theta r)
    (hne : directionRow o e (c ∘ v.succAbove) j ≠ [])
    (hshort : (directionRow o e (c ∘ v.succAbove) j).head hne -
      theta j < lam) :
    ∃ w : Fin s, w ≠ j ∧ theta w < theta j ∧
      dirRep o e (c ∘ v.succAbove) j w =
        (directionRow o e (c ∘ v.succAbove) j).head hne ∧
      3 ≤ rowDefect n lam (directionRow o e c (v.succAbove w)) := by
  classical
  obtain ⟨w, hwj, hwt, hdir⟩ := short_first_gap_gives_lower o e he hn3
    hlam hn hleg v htheta j hne hshort
  refine ⟨w, hwj.symm, hwt, hdir, ?_⟩
  have h2 := hge2 w
  rcases Nat.lt_or_ge (rowDefect n lam
    (directionRow o e c (v.succAbove w))) 3 with hlt | hge
  · exfalso
    have hd2 : rowDefect n lam
        (directionRow o e c (v.succAbove w)) = 2 := by omega
    exact absurd (hmin w hd2) (not_le_of_gt hwt)
  · exact hge

/-- **Extremal exit, last end** (symmetric): the last-gap witness of a
`θ`-maximal short-last defect-`2` row has defect `≥ 3`. -/
theorem last_witness_of_max_defect_two_high {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hge2 : ∀ r : Fin s,
      2 ≤ rowDefect n lam (directionRow o e c (v.succAbove r)))
    {j : Fin s}
    (hmax : ∀ r : Fin s,
      rowDefect n lam (directionRow o e c (v.succAbove r)) = 2 →
        theta r ≤ theta j)
    (hne : directionRow o e (c ∘ v.succAbove) j ≠ [])
    (hshort : theta j + Real.pi -
      (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam) :
    ∃ w : Fin s, w ≠ j ∧ theta j < theta w ∧
      dirRep o e (c ∘ v.succAbove) j w =
        (directionRow o e (c ∘ v.succAbove) j).getLast hne ∧
      3 ≤ rowDefect n lam (directionRow o e c (v.succAbove w)) := by
  classical
  obtain ⟨w, hwj, hwt, hdir⟩ := short_last_gap_gives_higher o e he hn3
    hlam hn hleg v htheta j hne hshort
  refine ⟨w, hwj.symm, hwt, hdir, ?_⟩
  have h2 := hge2 w
  rcases Nat.lt_or_ge (rowDefect n lam
    (directionRow o e c (v.succAbove w))) 3 with hlt | hge
  · exfalso
    have hd2 : rowDefect n lam
        (directionRow o e c (v.succAbove w)) = 2 := by omega
    exact absurd (hmax w hd2) (not_le_of_gt hwt)
  · exact hge

/-- **Zigzag ordering, last-receive → first-send.**  A defect-`2` row
`j` receiving a short-last witness from a lower-`θ` source `i₂` and
itself short-first has its head strictly below the incoming chord:
`head < dirRep j i₂`.  Reason: `φ₂ = dirRep j i₂` sits at some index
`b₂ ≥ 1` of `l` (index `0` is `θ_j`); if `b₂ = 1` the head would equal
`φ₂`, which `defect_two_short_first_witness_ne_source` excludes; hence
`1 < b₂` is impossible... rather `b₂ ≥ 1` and sortedness give
`head = l[1] ≤ l[b₂] = φ₂`, with strictness by the same no-return
exclusion. -/
theorem defect_two_last_recv_head_lt {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₂ : Fin s}
    (hi₂j : i₂ ≠ j) (hlt₂ : theta i₂ < theta j)
    (hgap₂ : theta i₂ + Real.pi -
      dirRep o e (c ∘ v.succAbove) i₂ j < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hne : directionRow o e (c ∘ v.succAbove) j ≠ [])
    (hshort : (directionRow o e (c ∘ v.succAbove) j).head hne -
      theta j < lam) :
    (directionRow o e (c ∘ v.succAbove) j).head hne <
      dirRep o e (c ∘ v.succAbove) j i₂ := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  set sub := directionRow o e (c ∘ v.succAbove) j with hsubdef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₂eq : dirRep o e (c ∘ v.succAbove) j i₂ =
      dirRep o e (c ∘ v.succAbove) i₂ j :=
    dirRep_comm o e _ he (fun h => hi₂j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₂ := dirRep o e (c ∘ v.succAbove) j i₂ with hφ₂def
  have hφ₂high : φ₂ ≤ Real.pi - lam + theta j := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_top_sliver_forces_high o e he hn2 hlam hn
      hleg v htheta j i₂ hi₂j.symm (u := theta j) le_rfl hlt
    linarith
  have hφ₂gt : theta j < φ₂ := by
    have h1 : lam ≤ φ₂ := (hcorr j i₂ hi₂j.symm).1
    have h2 : theta j ≤ Real.pi - n * lam := (htheta j).1.2
    linarith
  have hne' : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne'
  have hsort : l.SortedLE := directionRow_sorted o e c _
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: sub := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hget0 : ∀ h : 0 < l.length, l.get ⟨0, h⟩ = theta j := by
    intro h
    rw [List.get_of_eq hcons, List.get_mk_zero, List.head_cons]
  have h1lt : 1 < l.length := by
    rw [hldef, directionRow_length]; omega
  have hhead : l.get ⟨1, h1lt⟩ = sub.head hne := by
    rw [List.get_of_eq hcons, List.get_cons_succ, List.get_mk_zero]
  -- Locate `φ₂` inside `l`.
  have hφ₂mem : φ₂ ∈ l := by
    rw [hldef]
    exact (mem_directionRow o e c).mpr ⟨v.succAbove i₂,
      fun h => hi₂j (Fin.succAbove_right_injective h), rfl⟩
  obtain ⟨b₂, hgb₂⟩ := List.get_of_mem hφ₂mem
  -- `b₂ ≠ 0` since `l.get ⟨0⟩ = θ_j < φ₂`.
  have hb₂0 : b₂.val ≠ 0 := by
    intro hb0
    have hb : b₂ = ⟨0, hlen⟩ := Fin.ext hb0
    rw [hb] at hgb₂
    rw [hget0] at hgb₂
    linarith
  have hb₂ge : (⟨1, h1lt⟩ : Fin l.length) ≤ b₂ :=
    Nat.pos_of_ne_zero hb₂0
  have hle : l.get ⟨1, h1lt⟩ ≤ l.get b₂ :=
    (List.sortedLE_iff_monotone_get.mp hsort) hb₂ge
  -- Strictness: `head ≠ φ₂` by the no-return exclusion.
  have hne_head : sub.head hne ≠ φ₂ :=
    defect_two_short_first_witness_ne_source o e he hn3 hlam hn
      hleg v htheta hs hi₂j hlt₂ hgap₂ hdef ⟨hne, hshort⟩ hne
  have hle' : sub.head hne ≤ φ₂ := by
    calc sub.head hne = l.get ⟨1, h1lt⟩ := hhead.symm
      _ ≤ l.get b₂ := hle
      _ = φ₂ := hgb₂
  exact lt_of_le_of_ne hle' hne_head

/-- **Zigzag ordering, first-receive → last-send** (mirror): a defect-`2`
row `j` receiving a short-first witness from a higher-`θ` source `i₁`
and itself short-last has `dirRep j i₁ < getLast` — the outgoing
last-witness chord sits strictly above the incoming shared chord. -/
theorem defect_two_first_recv_getLast_gt {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hs : 2 ≤ s) {j i₁ : Fin s}
    (hi₁j : i₁ ≠ j) (hlt₁ : theta j < theta i₁)
    (hgap₁ : dirRep o e (c ∘ v.succAbove) i₁ j - theta i₁ < lam)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2)
    (hlast : ∃ hne : directionRow o e (c ∘ v.succAbove) j ≠ [],
      theta j + Real.pi -
        (directionRow o e (c ∘ v.succAbove) j).getLast hne < lam)
    (hne : directionRow o e (c ∘ v.succAbove) j ≠ []) :
    dirRep o e (c ∘ v.succAbove) j i₁ <
      (directionRow o e (c ∘ v.succAbove) j).getLast hne := by
  classical
  set l := directionRow o e c (v.succAbove j) with hldef
  set sub := directionRow o e (c ∘ v.succAbove) j with hsubdef
  have hn2 : 2 ≤ n := by omega
  have hp'inj : Function.Injective (c ∘ v.succAbove) :=
    hleg.inj.comp Fin.succAbove_right_injective
  have hφ₁eq : dirRep o e (c ∘ v.succAbove) j i₁ =
      dirRep o e (c ∘ v.succAbove) i₁ j :=
    dirRep_comm o e _ he (fun h => hi₁j (hp'inj h).symm)
  have hlampi : lam < Real.pi := by
    have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
    rw [hn, le_div_iff₀ hlam] at hfl
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    nlinarith [Real.pi_pos]
  have hdelta : Real.pi - n * lam < lam := by
    have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn, div_lt_iff₀ hlam] at hfloor'; linarith
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
      hdelta (by
        have := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
        rw [hn, le_div_iff₀ hlam] at this; linarith)
      (htheta a).1 (htheta b).1 (htheta a).2 (htheta b).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v a) hab'
        (Fin.ne_succAbove v b))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v b) hab'.symm
        (Fin.ne_succAbove v a))
  set φ₁ := dirRep o e (c ∘ v.succAbove) j i₁ with hφ₁def
  have hφ₁low : lam + theta j ≤ φ₁ := by
    by_contra hlt
    push_neg at hlt
    have h := saturated_row_bot_sliver_forces_low o e he hn2 hlam hn
      hleg v htheta j i₁ hi₁j.symm (t := theta j) le_rfl hlt
    linarith
  have hφ₁gt : theta j < φ₁ := by linarith
  have hne' : l ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hldef, directionRow_length]; omega
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne'
  have hsort : l.SortedLE := directionRow_sorted o e c _
  obtain ⟨hsub_ne, hshort'⟩ := hlast
  -- Locate `φ₁` inside `l`.
  have hφ₁mem : φ₁ ∈ l := by
    rw [hldef]
    exact (mem_directionRow o e c).mpr ⟨v.succAbove i₁,
      fun h => hi₁j (Fin.succAbove_right_injective h), rfl⟩
  obtain ⟨b₁, hgb₁⟩ := List.get_of_mem hφ₁mem
  -- `getLast = l.get lastIdx`; `b₁ ≤ lastIdx` gives `φ₁ ≤ getLast`.
  set lastIdx : Fin l.length := ⟨l.length - 1, by omega⟩
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨Set.Icc_subset_Icc le_rfl hdelta.le (htheta i).1,
      (htheta i).2⟩
  have hdirge : ∀ a b : Fin s, a ≠ b →
      lam ≤ dirRep o e (c ∘ v.succAbove) a b :=
    fun a b hab => (hcorr a b hab).1
  have hcons : l = theta j :: sub := by
    rw [hldef]
    exact directionRow_anchor_cons o e he c hleg.inj v hlam hlampi
      theta htheta' hdirge j
  have hgl : l.getLast? = sub.getLast? := by
    rw [hcons]
    exact List.getLast?_cons_of_ne_nil hsub_ne
  have hgl' : l.getLast hne' = sub.getLast hsub_ne := by
    have e1 := List.getLast?_eq_getLast hne'
    have e2 := List.getLast?_eq_getLast hsub_ne
    rw [hgl, e2] at e1
    exact (Option.some.inj e1).symm
  have hlast_eq : l.get lastIdx = l.getLast hne' :=
    (List.getLast_eq_getElem hne').symm
  have hle : l.get b₁ ≤ l.get lastIdx :=
    (List.sortedLE_iff_monotone_get.mp hsort)
      (show b₁ ≤ lastIdx from Nat.le_pred_of_lt b₁.2)
  have hle' : φ₁ ≤ sub.getLast hsub_ne := by
    calc φ₁ = l.get b₁ := hgb₁.symm
      _ ≤ l.get lastIdx := hle
      _ = l.getLast hne' := hlast_eq
      _ = sub.getLast hsub_ne := hgl'
  -- Strictness: `getLast ≠ φ₁` by the no-return exclusion.
  have hne_last : sub.getLast hsub_ne ≠ φ₁ :=
    defect_two_short_last_witness_ne_source o e he hn3 hlam hn
      hleg v htheta hs hi₁j hlt₁ hgap₁ hdef ⟨hsub_ne, hshort'⟩ hsub_ne
  exact lt_of_le_of_ne hle' hne_last.symm

#print axioms defect_two_last_recv_head_lt
#print axioms defect_two_first_recv_getLast_gt
#print axioms first_witness_of_min_defect_two_high
#print axioms last_witness_of_max_defect_two_high
#print axioms defect_two_witness_no_two_cycle
#print axioms defect_two_short_first_witness_ne_source
#print axioms defect_two_short_last_witness_ne_source
#print axioms defect_two_first_witness_classification
#print axioms defect_two_last_witness_classification
#print axioms type_II_first_receiver_trichotomy
#print axioms type_II_last_receiver_trichotomy

#print axioms row_span_le_delta_of_defect_two_ends
#print axioms three_defect_two_rows_big_ends_impossible
#print axioms exists_short_end_of_three_defect_two
#print axioms short_first_gap_gives_lower
#print axioms short_last_gap_gives_higher
#print axioms exists_crossing_witness_of_three_defect_two
#print axioms first_gap_ge_of_theta_min
#print axioms last_gap_ge_of_theta_max
#print axioms exists_two_short_end_rows_of_four
#print axioms short_first_arc_floor
#print axioms short_last_arc_floor
#print axioms defect_two_row_not_receive_both
#print axioms type_I_first_receiver_is_first_short
#print axioms type_I_last_receiver_is_last_short
#print axioms type_I_first_witness_leaves_type_I
#print axioms type_I_last_witness_leaves_type_I

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

/-- **Two-row deletion closure (deletion budget).**  Deleting two
distinct non-anchor centers `q₁, q₂` leaves a legal sub-configuration
`c ∘ q₁.succAbove ∘ q₂'.succAbove` on `s − 1` centers in which the
anchor stays saturated (erasing directions never lowers a row score,
`rowScore_eraseIdx'`, and no row exceeds `n − 1`).  If the surviving
anchor rays stay pairwise within `β < α = (n+1)λ − π`, the
narrow-window bound `≤ 2^n` applies to the sub-configuration and the
two deleted rows are paid at their own weights — the hypothesis
`hqcost` is the deletion budget `2^{k₁} + 2^{k₂} ≤ 2^{n−2}`.  The
prime intended instance is a pair of defect-`≥ 3` rows, each charged
`2^{n−3}`, exactly spending the quarter-cube budget.  No removability
of `q₁, q₂` is required, and other rows may become saturated in the
sub-configuration. -/
theorem potential_le_high_of_saturated_delete_pair {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {q1 q2 : Fin (s + 1)}
    (hvq1 : v ≠ q1) (hvq2 : v ≠ q2) (hq12 : q1 ≠ q2)
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hqcost : 2 ^ rowScore lam (directionRow o e c q1) +
        2 ^ rowScore lam (directionRow o e c q2) ≤ 2 ^ (n - 2))
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    {beta : ℝ} (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin (s + 1), i ≠ v → j ≠ v → i ≠ q1 → j ≠ q1 →
      i ≠ q2 → j ≠ q2 →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ beta) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  obtain ⟨q2', hq2'⟩ := Fin.exists_succAbove_eq hq12.symm
  obtain ⟨v1, hv1⟩ := Fin.exists_succAbove_eq hvq1
  have hq2v1 : q2' ≠ v1 := fun h =>
    hvq2 (by rw [← hv1, ← hq2', h])
  obtain ⟨v2, hv2⟩ :=
    Fin.exists_succAbove_eq (x := v1) (y := q2') hq2v1.symm
  have hleg1 : Section4Legality (c ∘ q1.succAbove) lam := hleg.erase q1
  have hleg2 : Section4Legality ((c ∘ q1.succAbove) ∘ q2'.succAbove) lam :=
    hleg1.erase q2'
  have hscv : rowScore lam (directionRow o e c v) = n - 1 := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e c hlam v
      (by omega) hn
    rw [rowScore_eq_sub_defect lam hlam n _ hcells, hsat]
  have hsat1 : rowDefect n lam
      (directionRow o e (c ∘ q1.succAbove) v1) = 1 := by
    have hrowv1 : directionRow o e (c ∘ q1.succAbove) v1 =
        (directionRow o e c v).eraseIdx (deleteIndex o e c q1 v) := by
      have h := eraseIdx_directionRow o e (c' := c) q1 v1
      rwa [hv1] at h
    have hcells1 := rowCells_directionRow_le_of_floor_eq o e
      (c ∘ q1.succAbove) hlam v1 (by omega) hn
    have hge : n - 1 ≤
        rowScore lam (directionRow o e (c ∘ q1.succAbove) v1) := by
      rw [hrowv1, rowScore_eraseIdx' hlam (directionRow_sorted o e c v)
          (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
          (deleteIndex_lt o e c hvq1)
          (by rw [directionRow_length o e c v]; omega), hscv]
      exact Nat.le_add_right _ _
    have hle : rowScore lam (directionRow o e (c ∘ q1.succAbove) v1) ≤
        n - 1 := by
      rw [rowScore_eq_sub_defect lam hlam n _ hcells1]
      have h1 := one_le_rowDefect lam hlam n _ (by omega) hcells1
      omega
    have hsc : rowScore lam (directionRow o e (c ∘ q1.succAbove) v1) =
        n - 1 := le_antisymm hle hge
    have := rowScore_eq_sub_defect lam hlam n _ hcells1
    omega
  have hsat2 : rowDefect n lam
      (directionRow o e ((c ∘ q1.succAbove) ∘ q2'.succAbove) v2) = 1 := by
    have hrowv2 : directionRow o e ((c ∘ q1.succAbove) ∘ q2'.succAbove)
        v2 = (directionRow o e (c ∘ q1.succAbove) v1).eraseIdx
          (deleteIndex o e (c ∘ q1.succAbove) q2' v1) := by
      have h := eraseIdx_directionRow o e (c' := c ∘ q1.succAbove) q2' v2
      rwa [hv2] at h
    have hscv1 : rowScore lam (directionRow o e (c ∘ q1.succAbove) v1) =
        n - 1 := by
      have hcells1 := rowCells_directionRow_le_of_floor_eq o e
        (c ∘ q1.succAbove) hlam v1 (by omega) hn
      rw [rowScore_eq_sub_defect lam hlam n _ hcells1, hsat1]
    have hcells2 := rowCells_directionRow_le_of_floor_eq o e
      ((c ∘ q1.succAbove) ∘ q2'.succAbove) hlam v2 (by omega) hn
    have hge : n - 1 ≤ rowScore lam
        (directionRow o e ((c ∘ q1.succAbove) ∘ q2'.succAbove) v2) := by
      rw [hrowv2, rowScore_eraseIdx' hlam
          (directionRow_sorted o e (c ∘ q1.succAbove) v1)
          (fun b hb => Set.mem_Ico.mp
            (directionRow_mem_Ico o e (c ∘ q1.succAbove) hb))
          (deleteIndex_lt o e (c ∘ q1.succAbove) hq2v1.symm)
          (by rw [directionRow_length o e (c ∘ q1.succAbove) v1]; omega),
        hscv1]
      exact Nat.le_add_right _ _
    have hle : rowScore lam
        (directionRow o e ((c ∘ q1.succAbove) ∘ q2'.succAbove) v2) ≤
        n - 1 := by
      rw [rowScore_eq_sub_defect lam hlam n _ hcells2]
      have h1 := one_le_rowDefect lam hlam n _ (by omega) hcells2
      omega
    have hsc : rowScore lam
        (directionRow o e ((c ∘ q1.succAbove) ∘ q2'.succAbove) v2) =
        n - 1 := le_antisymm hle hge
    have := rowScore_eq_sub_defect lam hlam n _ hcells2
    omega
  have hspread' : ∀ i j : Fin t, i ≠ v2 → j ≠ v2 →
      InnerProductGeometry.angle
        (((c ∘ q1.succAbove) ∘ q2'.succAbove) i -
          ((c ∘ q1.succAbove) ∘ q2'.succAbove) v2)
        (((c ∘ q1.succAbove) ∘ q2'.succAbove) j -
          ((c ∘ q1.succAbove) ∘ q2'.succAbove) v2) ≤ beta := by
    intro i' j' hi' hj'
    have hveq : q1.succAbove (q2'.succAbove v2) = v := by rw [hv2, hv1]
    have hi1 : q1.succAbove (q2'.succAbove i') ≠ q1 :=
      Fin.succAbove_ne _ _
    have hi2 : q1.succAbove (q2'.succAbove i') ≠ q2 := fun h =>
      Fin.succAbove_ne q2' i'
        (Fin.succAbove_right_injective (h.trans hq2'.symm))
    have hiv : q1.succAbove (q2'.succAbove i') ≠ v := fun h =>
      hi' (Fin.succAbove_right_injective (Fin.succAbove_right_injective
        (h.trans hveq.symm)))
    have hj1 : q1.succAbove (q2'.succAbove j') ≠ q1 :=
      Fin.succAbove_ne _ _
    have hj2 : q1.succAbove (q2'.succAbove j') ≠ q2 := fun h =>
      Fin.succAbove_ne q2' j'
        (Fin.succAbove_right_injective (h.trans hq2'.symm))
    have hjv : q1.succAbove (q2'.succAbove j') ≠ v := fun h =>
      hj' (Fin.succAbove_right_injective (Fin.succAbove_right_injective
        (h.trans hveq.symm)))
    have h := hspread _ _ hiv hjv hi1 hj1 hi2 hj2
    simp only [Function.comp_apply, hveq]
    exact h
  have hcap : potential lam (directionRows o e
      ((c ∘ q1.succAbove) ∘ q2'.succAbove)) ≤ 2 ^ n :=
    potential_le_two_pow_of_saturated_narrow o e he (by omega) hn3 hlam
      hn hleg2 v2 hsat2 hδ hbeta hspread'
  have hrow : ∀ j : Fin t,
      rowScore lam (directionRow o e c (q1.succAbove (q2'.succAbove j)))
        ≤ rowScore lam (directionRow o e
          ((c ∘ q1.succAbove) ∘ q2'.succAbove) j) := by
    intro j
    rw [eraseIdx_directionRow o e (c' := c ∘ q1.succAbove) q2' j]
    rw [rowScore_eraseIdx' hlam
        (directionRow_sorted o e (c ∘ q1.succAbove) (q2'.succAbove j))
        (fun b hb => Set.mem_Ico.mp
          (directionRow_mem_Ico o e (c ∘ q1.succAbove) hb))
        (deleteIndex_lt o e (c ∘ q1.succAbove) (Fin.succAbove_ne q2' j))
        (by rw [directionRow_length o e (c ∘ q1.succAbove)]; omega)]
    rw [eraseIdx_directionRow o e (c' := c) q1 (q2'.succAbove j)]
    rw [rowScore_eraseIdx' hlam
        (directionRow_sorted o e c (q1.succAbove (q2'.succAbove j)))
        (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
        (deleteIndex_lt o e c (Fin.succAbove_ne q1 (q2'.succAbove j)))
        (by rw [directionRow_length o e c]; omega)]
    omega
  have hsum : ∑ i : Fin (t + 1 + 1), 2 ^ rowScore lam (directionRow o e c i) =
      2 ^ rowScore lam (directionRow o e c q1) +
        (2 ^ rowScore lam (directionRow o e c q2) +
          ∑ j : Fin t, 2 ^ rowScore lam (directionRow o e c
            (q1.succAbove (q2'.succAbove j)))) := by
    rw [Fin.sum_univ_succAbove _ q1]
    congr 1
    rw [Fin.sum_univ_succAbove _ q2', hq2']
  have hpow : ∑ j : Fin t, 2 ^ rowScore lam (directionRow o e c
        (q1.succAbove (q2'.succAbove j))) ≤
      potential lam (directionRows o e
        ((c ∘ q1.succAbove) ∘ q2'.succAbove)) := by
    unfold potential exponentAt directionRows
    exact Finset.sum_le_sum fun j _ =>
      Nat.pow_le_pow_right (by omega) (hrow j)
  unfold potential exponentAt directionRows
  rw [hsum]
  calc 2 ^ rowScore lam (directionRow o e c q1) +
        (2 ^ rowScore lam (directionRow o e c q2) +
          ∑ j : Fin t, 2 ^ rowScore lam (directionRow o e c
            (q1.succAbove (q2'.succAbove j))))
      = (2 ^ rowScore lam (directionRow o e c q1) +
          2 ^ rowScore lam (directionRow o e c q2)) +
          ∑ j : Fin t, 2 ^ rowScore lam (directionRow o e c
            (q1.succAbove (q2'.succAbove j))) := (add_assoc _ _ _).symm
    _ ≤ 2 ^ (n - 2) + potential lam (directionRows o e
        ((c ∘ q1.succAbove) ∘ q2'.succAbove)) :=
        Nat.add_le_add hqcost hpow
    _ ≤ 2 ^ (n - 2) + 2 ^ n := Nat.add_le_add_left hcap _
    _ = 2 ^ n + 2 ^ (n - 2) := Nat.add_comm _ _

#print axioms potential_le_high_of_saturated_delete_pair

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
