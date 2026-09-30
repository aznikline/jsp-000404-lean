import Jsp000404.R3WitnessDag
import Jsp000404.OneSaturatedHigh
import Jsp000404.TwoSaturatedHigh

/-!
# Five-point capacity: wiring the SatChart closure to the original potential

The `R3WitnessDag` pair-kill theorems live on a `SatChart`: an anchored
chart whose reference vector `e'` places every anchor ray in the narrow
window `[0, π − nλ]`.  `saturated_ray_window` shows a saturated anchor
supplies exactly such a chart, so no extra geometric hypothesis is
needed.  Both `rowDefect` and `potential` are reference-invariant
(`rowScore_directionRow_reference_eq`,
`potential_directionRows_reference_eq`), so the bound computed on the
chart returns to the original reference.

The consumer `potential_le_high_of_saturated_five`: on five centers with
a uniquely saturated anchor (all other rows of defect `≥ 2`), the
pair-kill closure forces `R = #{defect-2 non-anchor rows} ≤ 2`, and the
weight count `potential_le_high_of_saturated_four_eq` gives
`potential ≤ 2^n + 2^{n−2} = sendovCap n true`.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- `rowDefect` is reference-invariant: with `⌊π/λ⌋ = n` both charts have
`cells ≤ n`, so `defect = n − score` on either side while `rowScore` is
reference-invariant by `rowScore_directionRow_reference_eq`. -/
theorem rowDefect_directionRow_reference_eq {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e f : Plane₂)
    (_he : e ≠ 0) (_hf : f ≠ 0) (c : Fin s → Plane₂)
    (hc : Function.Injective c) (i : Fin s) {lam : ℝ} (hlam : 0 < lam)
    (hs2 : 2 ≤ s) (hn : Nat.floor (Real.pi / lam) = n) :
    rowDefect n lam (directionRow o e c i) =
      rowDefect n lam (directionRow o f c i) := by
  have h1 := rowCells_directionRow_le_of_floor_eq o e c hlam i hs2 hn
  have h2 := rowCells_directionRow_le_of_floor_eq o f c hlam i hs2 hn
  have k1 := rowScore_eq_sub_defect lam hlam n _ h1
  have k2 := rowScore_eq_sub_defect lam hlam n _ h2
  have d1 := rowDefect_le lam hlam n _ h1
  have d2 := rowDefect_le lam hlam n _ h2
  rw [rowScore_directionRow_reference_eq o e f _he _hf c hc i lam] at k1
  omega

/-- **Original five-point capacity (unique saturation).**  A legal
five-center configuration with a saturated anchor `v` and all other rows
of defect `≥ 2` stays under the HIGH cap.  The saturated anchor supplies
a `SatChart` directly; the defect profile there cannot contain three
defect-`2` rows (`five_point_R_ge_three_impossible`), so `R ≤ 2` and the
weight count applies. -/
theorem potential_le_high_of_saturated_five
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {n : ℕ} (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (4 + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (4 + 1))
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (huniq : ∀ w : Fin (4 + 1), w ≠ v →
      2 ≤ rowDefect n lam (directionRow o e c w)) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  -- The saturated anchor supplies the narrow-window chart directly.
  obtain ⟨e', he', theta, htheta⟩ :=
    saturated_ray_window o e he (s := 4) (by omega) (by omega) hlam hn
      hleg v hsat
  have C : SatChart o e' n lam c v theta := ⟨he', hn3, hlam, hn, hleg, htheta⟩
  have hdref : ∀ w : Fin (4 + 1), rowDefect n lam (directionRow o e' c w) =
      rowDefect n lam (directionRow o e c w) :=
    fun w => rowDefect_directionRow_reference_eq o e' e he' he c hleg.inj w
      hlam (by omega) hn
  have hsat' : rowDefect n lam (directionRow o e' c v) = 1 := by
    rw [hdref]; exact hsat
  have huniq' : ∀ i : Fin 4,
      2 ≤ rowDefect n lam (directionRow o e' c (v.succAbove i)) :=
    fun i => by rw [hdref]; exact huniq _ (Fin.succAbove_ne v i)
  -- `R ≤ 2`: three defect-2 rows are impossible on the chart.
  set T := Finset.univ.filter (fun i : Fin 4 =>
    rowDefect n lam (directionRow o e' c (v.succAbove i)) = 2) with hTdef
  have hcard : T.card ≤ 2 := by
    by_contra hle
    have hT3 : 3 ≤ T.card := by omega
    exact five_point_R_ge_three_impossible C T
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i hi => by
        have hge := huniq' i
        have hne : rowDefect n lam
            (directionRow o e' c (v.succAbove i)) ≠ 2 :=
          fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        omega)
      hT3
  rw [potential_directionRows_reference_eq o e e' he he' c hleg.inj lam]
  exact potential_le_high_of_saturated_four_eq o e' rfl hn3 hlam hn hleg v
    hsat' huniq' hcard

/-- **Merged small-size capacity (unconditional).**  For `3 ≤ s ≤ 5`
centers and `n ≥ 3`, `potential ≤ 2^n + 2^{n−2}` in every regime: two
saturated centers close the bound at any size
(`potential_le_high_of_two_saturated`), a unique saturated center closes
`s ≤ 5` by `potential_le_high_of_saturated_{small,five}`, and with no
saturated center all `s` rows have defect `≥ 2`, contributing at most
`s·2^{n−2} ≤ 5·2^{n−2}`. -/
theorem potential_le_high_cap_of_le_five {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs3 : 3 ≤ s) (hs5 : s ≤ 5) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hn2 : 2 ≤ n := by omega
  by_cases h2sat : ∃ i j : Fin s, i ≠ j ∧
      rowDefect n lam (directionRow o e c i) = 1 ∧
      rowDefect n lam (directionRow o e c j) = 1
  · obtain ⟨i, j, hij, hi, hj⟩ := h2sat
    exact potential_le_high_of_two_saturated o e he hs3 hn2 hlam hn hleg
      hij hi hj
  · have hcells : ∀ i : Fin s,
        rowCells lam (directionRow o e c i) ≤ n :=
      fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i
        (by omega) hn
    have hdef1 : ∀ i : Fin s,
        1 ≤ rowDefect n lam (directionRow o e c i) :=
      fun i => one_le_rowDefect lam hlam n _ (by omega) (hcells i)
    by_cases hsat : ∃ v : Fin s,
        rowDefect n lam (directionRow o e c v) = 1
    · obtain ⟨v, hv⟩ := hsat
      have huniq : ∀ w : Fin s, w ≠ v →
          2 ≤ rowDefect n lam (directionRow o e c w) := by
        intro w hwv
        have h1 := hdef1 w
        have hne : rowDefect n lam (directionRow o e c w) ≠ 1 := by
          intro h1w
          exact h2sat ⟨w, v, hwv, h1w, hv⟩
        omega
      by_cases hs5' : s = 5
      · subst hs5'
        exact potential_le_high_of_saturated_five o e he hn3 hlam hn hleg
          v hv huniq
      · exact potential_le_high_of_saturated_small o e (by omega)
          (by omega) hn2 hlam hn hleg v hv huniq
    · have hge2 : ∀ i : Fin s,
          2 ≤ rowDefect n lam (directionRow o e c i) := by
        intro i
        have h1 := hdef1 i
        have hne : rowDefect n lam (directionRow o e c i) ≠ 1 :=
          fun h => hsat ⟨i, h⟩
        omega
      have hscore : ∀ i : Fin s,
          rowScore lam (directionRow o e c i) ≤ n - 2 := by
        intro i
        have h := rowScore_eq_sub_defect lam hlam n _ (hcells i)
        have := hge2 i
        omega
      have hbound : potential lam (directionRows o e c) ≤
          s * 2 ^ (n - 2) := by
        calc potential lam (directionRows o e c)
            ≤ ∑ _i : Fin s, 2 ^ (n - 2) := by
              unfold potential exponentAt directionRows
              exact Finset.sum_le_sum fun i _ =>
                Nat.pow_le_pow_right (by omega) (hscore i)
          _ = s * 2 ^ (n - 2) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                smul_eq_mul]
      have h2n : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
        conv_lhs => rw [show n = n - 2 + 2 by omega, pow_add]
        ring
      calc potential lam (directionRows o e c) ≤ s * 2 ^ (n - 2) := hbound
        _ ≤ 5 * 2 ^ (n - 2) := Nat.mul_le_mul_right _ hs5
        _ = 2 ^ n + 2 ^ (n - 2) := by omega

/-- **Merged small-size LOW capacity.**  For `3 ≤ s ≤ 4` centers in the
low regime, `potential ≤ 2^n`: two saturated centers cannot exist
(`not_two_saturated_of_delta_lt_half`), a saturated center closes the
bound directly, and without one all defects are `≥ 2`, contributing at
most `s·2^{n−2} ≤ 4·2^{n−2} = 2^n`. -/
theorem potential_le_two_pow_of_le_four_low {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs3 : 3 ≤ s) (hs4 : s ≤ 4) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hδ : Real.pi / lam - n < 1 / 2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) :
    potential lam (directionRows o e c) ≤ 2 ^ n := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hdelta : Real.pi < ((n : ℝ) + 1 / 2) * lam := by
    have h1 : Real.pi / lam < (n : ℝ) + 1 / 2 := by linarith
    rwa [div_lt_iff₀ hlam] at h1
  by_cases h2sat : ∃ i j : Fin s, i ≠ j ∧
      rowDefect n lam (directionRow o e c i) = 1 ∧
      rowDefect n lam (directionRow o e c j) = 1
  · obtain ⟨i, j, hij, hi, hj⟩ := h2sat
    exact (not_two_saturated_of_delta_lt_half o e hn2 hlam hn hleg he hs3 hij
      hi hj hdelta).elim
  · have hcells : ∀ i : Fin s,
        rowCells lam (directionRow o e c i) ≤ n :=
      fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i
        (by omega) hn
    have hdef1 : ∀ i : Fin s,
        1 ≤ rowDefect n lam (directionRow o e c i) :=
      fun i => one_le_rowDefect lam hlam n _ (by omega) (hcells i)
    by_cases hsat : ∃ v : Fin s,
        rowDefect n lam (directionRow o e c v) = 1
    · obtain ⟨v, hv⟩ := hsat
      exact potential_le_two_pow_of_saturated o e he (by omega) hn2 hlam hn
        hleg v hv hδ
    · have hge2 : ∀ i : Fin s,
          2 ≤ rowDefect n lam (directionRow o e c i) := by
        intro i
        have h1 := hdef1 i
        have hne : rowDefect n lam (directionRow o e c i) ≠ 1 :=
          fun h => hsat ⟨i, h⟩
        omega
      have hscore : ∀ i : Fin s,
          rowScore lam (directionRow o e c i) ≤ n - 2 := by
        intro i
        have h := rowScore_eq_sub_defect lam hlam n _ (hcells i)
        have := hge2 i
        omega
      calc potential lam (directionRows o e c)
          ≤ ∑ _i : Fin s, 2 ^ (n - 2) := by
            unfold potential exponentAt directionRows
            exact Finset.sum_le_sum fun i _ =>
              Nat.pow_le_pow_right (by omega) (hscore i)
        _ = s * 2 ^ (n - 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul]
        _ ≤ 4 * 2 ^ (n - 2) := Nat.mul_le_mul_right _ hs4
        _ = 2 ^ n := by
            have h2n : (2 : ℕ) ^ n = 4 * 2 ^ (n - 2) := by
              conv_lhs => rw [show n = n - 2 + 2 by omega, pow_add]
              ring
            omega

/-- **Certificate shrinking.**  If every legal configuration of size
`4 ≤ t < t0` stays under the cap, the `CertExists` obligation reduces to
the tail `t0 ≤ t`.  No modification of `CertExists`. -/
theorem certExists_of_bounded_below (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) {n : ℕ} (big : Bool) {lam : ℝ} {t0 : ℕ}
    (hsmall : ∀ {t : ℕ} {c : Fin t → Plane₂}, 4 ≤ t → t < t0 →
      Section4Legality c lam →
      potential lam (directionRows o e c) ≤ sendovCap n big)
    (htail : ∀ {t : ℕ} {c : Fin t → Plane₂}, t0 ≤ t →
      Section4Legality c lam →
      sendovCap n big < potential lam (directionRows o e c) →
      EmissionDichotomy lam
        (fun v i => deleteIndex o e c v i) (directionRows o e c)) :
    CertExists o e n big lam := by
  intro t c ht hleg hover
  by_cases h : t0 ≤ t
  · exact htail h hleg hover
  · exact absurd hover (not_lt_of_ge (hsmall ht (by omega) hleg))

/-- The HIGH certificate obligation reduces to `t ≥ 6`: sizes `4, 5`
never exceed `sendovCap n true`. -/
theorem certExists_true_of_six_le {n : ℕ} (hn3 : 3 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (_he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    (htail : ∀ {t : ℕ} {c : Fin t → Plane₂}, 6 ≤ t →
      Section4Legality c lam →
      sendovCap n true < potential lam (directionRows o e c) →
      EmissionDichotomy lam
        (fun v i => deleteIndex o e c v i) (directionRows o e c)) :
    CertExists o e n true lam :=
  certExists_of_bounded_below o e true
    (fun ht ht0 hleg => by
      have h := potential_le_high_cap_of_le_five o e _he (by omega)
        (by omega) hn3 hlam hn hleg
      simpa [sendovCap] using h)
    htail

/-- The LOW certificate obligation reduces to `t ≥ 5`: size `4` never
exceeds `sendovCap n false`.  (Five unsaturated rows of defect `≥ 2` can
still exceed `2^n` by the counting bound, so `t = 5` is not closed
here.) -/
theorem certExists_false_of_five_le {n : ℕ} (hn3 : 3 ≤ n)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (_he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hδ : Real.pi / lam - n < 1 / 2)
    (htail : ∀ {t : ℕ} {c : Fin t → Plane₂}, 5 ≤ t →
      Section4Legality c lam →
      sendovCap n false < potential lam (directionRows o e c) →
      EmissionDichotomy lam
        (fun v i => deleteIndex o e c v i) (directionRows o e c)) :
    CertExists o e n false lam :=
  certExists_of_bounded_below o e false
    (fun ht ht0 hleg => by
      have h := potential_le_two_pow_of_le_four_low o e _he (by omega)
        (by omega) hn3 hlam hn hδ hleg
      simpa [sendovCap] using h)
    htail

#print axioms rowDefect_directionRow_reference_eq
#print axioms potential_le_high_of_saturated_five
#print axioms potential_le_high_cap_of_le_five
#print axioms potential_le_two_pow_of_le_four_low
#print axioms certExists_of_bounded_below
#print axioms certExists_true_of_six_le
#print axioms certExists_false_of_five_le

end Jsp404
