import Jsp000404.R3WitnessDag
import Jsp000404.OneSaturatedHigh
import Jsp000404.TwoSaturatedHigh
import Jsp000404.DeletionRigidity
import Jsp000404.Reindex

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

/-- Deleting a center never lowers a surviving row's score: the erased
direction merges two gaps (`rowScore_eraseIdx'`). -/
theorem rowScore_le_of_delete {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin (s + 1) → Plane₂) (hs2 : 2 ≤ s) (q : Fin (s + 1)) (i : Fin s) :
    rowScore lam (directionRow o e c (q.succAbove i)) ≤
      rowScore lam (directionRow o e (c ∘ q.succAbove) i) := by
  rw [eraseIdx_directionRow o e q i,
    rowScore_eraseIdx' hlam (directionRow_sorted o e c _)
      (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
      (deleteIndex_lt o e c (Fin.succAbove_ne q i))
      (by rw [directionRow_length]; omega)]
  omega

/-- Deleting a center never raises a surviving row's defect. -/
theorem rowDefect_le_of_delete {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hs2 : 2 ≤ s) (q : Fin (s + 1)) (i : Fin s) :
    rowDefect n lam (directionRow o e (c ∘ q.succAbove) i) ≤
      rowDefect n lam (directionRow o e c (q.succAbove i)) := by
  have hup : rowScore lam (directionRow o e c (q.succAbove i)) ≤
      rowScore lam (directionRow o e (c ∘ q.succAbove) i) :=
    rowScore_le_of_delete hlam o e c hs2 q i
  have cO := rowCells_directionRow_le_of_floor_eq o e c hlam
    (q.succAbove i) (by omega) hn
  have cN := rowCells_directionRow_le_of_floor_eq o e (c ∘ q.succAbove)
    hlam i hs2 hn
  have sO := rowScore_eq_sub_defect lam hlam n _ cO
  have sN := rowScore_eq_sub_defect lam hlam n _ cN
  have dO := rowDefect_le lam hlam n _ cO
  have dN := rowDefect_le lam hlam n _ cN
  omega

/-- **Arbitrary-size lift.**  A legal configuration of `s ≥ 5` centers
with a saturated anchor cannot contain three other defect-`2` rows:
delete every center outside `{v, a, b, d, w}` one at a time.  Each
deletion keeps the anchor saturated (scores can only rise) and keeps
every defect-`2` survivor at defect `2` (`deletion_rigidity` consumes
one other defect-`2` survivor).  At size `5` the chart pair-kill
closure applies directly: a defect-`1` non-anchor row makes two
saturated centers (every further row then has defect `≥ 3` by
`rowDefect_ge_three_of_two_saturated`), and otherwise `T = #{defect 2}`
has `3 ≤ #T` by the surviving rows. -/
theorem saturated_anchor_three_defect_two_impossible {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n) :
    ∀ {s : ℕ}, 5 ≤ s → ∀ {c : Fin s → Plane₂},
      Section4Legality c lam →
      ∀ {v a b d w : Fin s},
      v ≠ a → v ≠ b → v ≠ d → v ≠ w →
      a ≠ b → a ≠ d → a ≠ w → b ≠ d → b ≠ w → d ≠ w →
      rowDefect n lam (directionRow o e c v) = 1 →
      rowDefect n lam (directionRow o e c a) = 2 →
      rowDefect n lam (directionRow o e c b) = 2 →
      rowDefect n lam (directionRow o e c d) = 2 →
      False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro hs5 c hleg v a b d w hva hvb hvd hvw hab had haw hbd hbw hdw
      hsat hda hdb hdd
    by_cases h5 : s = 5
    · -- Base case: `s = 5`.  The anchor supplies the narrow-window chart.
      subst h5
      obtain ⟨e', he', theta, htheta⟩ :=
        saturated_ray_window o e he (s := 4) (by omega) (by omega) hlam hn
          hleg v hsat
      have C : SatChart o e' n lam c v theta :=
        ⟨he', hn3, hlam, hn, hleg, htheta⟩
      have hdref : ∀ x : Fin (4 + 1),
          rowDefect n lam (directionRow o e' c x) =
            rowDefect n lam (directionRow o e c x) :=
        fun x => rowDefect_directionRow_reference_eq o e' e he' he c
          hleg.inj x hlam (by omega) hn
      -- Chart indices of the four named non-anchor centers.
      obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (show a ≠ v from hva.symm)
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq (show b ≠ v from hvb.symm)
      obtain ⟨d', hd'⟩ := Fin.exists_succAbove_eq (show d ≠ v from hvd.symm)
      obtain ⟨w', hw'⟩ := Fin.exists_succAbove_eq (show w ≠ v from hvw.symm)
      have ha'b' : a' ≠ b' := fun h =>
        hab (by rw [← ha', ← hb', h])
      have ha'd' : a' ≠ d' := fun h =>
        had (by rw [← ha', ← hd', h])
      have hb'd' : b' ≠ d' := fun h =>
        hbd (by rw [← hb', ← hd', h])
      set T := Finset.univ.filter (fun i : Fin 4 =>
        rowDefect n lam (directionRow o e' c (v.succAbove i)) = 2)
      have hTmem (i : Fin 4) (x : Fin (4 + 1)) (hx : v.succAbove i = x)
          (hdx : rowDefect n lam (directionRow o e c x) = 2) : i ∈ T :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
          rw [hdref (v.succAbove i), hx]; exact hdx⟩
      have haT : a' ∈ T := hTmem a' a ha' hda
      have hbT : b' ∈ T := hTmem b' b hb' hdb
      have hdT : d' ∈ T := hTmem d' d hd' hdd
      have hT3 : 3 ≤ T.card := by
        have h := Finset.two_lt_card_iff.mpr
          ⟨a', b', d', haT, hbT, hdT, ha'b', ha'd', hb'd'⟩
        omega
      have hrest : ∀ i : Fin 4, i ∉ T →
          3 ≤ rowDefect n lam (directionRow o e' c (v.succAbove i)) := by
        intro i hi
        have hge : 1 ≤ rowDefect n lam
            (directionRow o e' c (v.succAbove i)) :=
          one_le_rowDefect lam hlam n _ (by omega)
            (rowCells_directionRow_le_of_floor_eq o e' c hlam _
              (by omega) hn)
        by_contra hlt
        push Not at hlt
        have hne2 : rowDefect n lam
            (directionRow o e' c (v.succAbove i)) ≠ 2 :=
          fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        have h1 : rowDefect n lam
            (directionRow o e' c (v.succAbove i)) = 1 := by omega
        -- A second saturated row forces every third row to defect `≥ 3`;
        -- `a'` is defect `2`, contradiction.
        have hsatv : rowDefect n lam (directionRow o e' c v) = 1 := by
          rw [hdref]; exact hsat
        have hia' : v.succAbove i ≠ v.succAbove a' := fun hcon =>
          hi (Fin.succAbove_right_injective hcon ▸ haT)
        have hrow := rowDefect_ge_three_of_two_saturated o e' he'
          (by omega) hlam hn hleg (by omega)
          (i := v) (j := v.succAbove i) (k := v.succAbove a')
          (Fin.succAbove_ne v i).symm (Fin.succAbove_ne v a').symm hia'
          hsatv h1
        rw [hdref (v.succAbove a'), ha'] at hrow
        omega
      exact five_point_R_ge_three_impossible C T
        (fun i hi => (Finset.mem_filter.mp hi).2) hrest hT3
    · -- `s ≥ 6`: delete a center outside `{v, a, b, d, w}`.
      have hs6 : 6 ≤ s := by omega
      classical
      have hvw' : v ∉ ({a, b, d, w} : Finset (Fin s)) := by
        simp [Finset.mem_insert, Finset.mem_singleton, hva, hvb, hvd, hvw]
      have haw' : a ∉ ({b, d, w} : Finset (Fin s)) := by
        simp [Finset.mem_insert, Finset.mem_singleton, hab, had, haw]
      have hbw' : b ∉ ({d, w} : Finset (Fin s)) := by
        simp [Finset.mem_insert, Finset.mem_singleton, hbd, hbw]
      have hdw' : d ∉ ({w} : Finset (Fin s)) := by
        simp [Finset.mem_singleton, hdw]
      have hcard5 : ({v, a, b, d, w} : Finset (Fin s)).card = 5 := by
        rw [Finset.card_insert_of_notMem hvw',
          Finset.card_insert_of_notMem haw',
          Finset.card_insert_of_notMem hbw',
          Finset.card_insert_of_notMem hdw', Finset.card_singleton]
      obtain ⟨q, hq⟩ : ∃ q : Fin s, q ∉ ({v, a, b, d, w} : Finset (Fin s)) := by
        by_contra hcon
        push Not at hcon
        have hsub : (Finset.univ : Finset (Fin s)) ⊆ {v, a, b, d, w} :=
          fun x _ => hcon x
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_univ, Fintype.card_fin, hcard5] at hcard
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      obtain ⟨hqv, hqa, hqb, hqd, hqw⟩ := hq
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq (Ne.symm hqv)
      obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (Ne.symm hqa)
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq (Ne.symm hqb)
      obtain ⟨d', hd'⟩ := Fin.exists_succAbove_eq (Ne.symm hqd)
      obtain ⟨w', hw'⟩ := Fin.exists_succAbove_eq (Ne.symm hqw)
      have lift_ne {x y : Fin (t + 1)} {x' y' : Fin t}
          (hx : q.succAbove x' = x) (hy : q.succAbove y' = y)
          (hxy : x ≠ y) : x' ≠ y' :=
        fun h => hxy (by rw [← hx, ← hy, h])
      have hv'a' := lift_ne hv' ha' hva
      have hv'b' := lift_ne hv' hb' hvb
      have hv'd' := lift_ne hv' hd' hvd
      have hv'w' := lift_ne hv' hw' hvw
      have ha'b' := lift_ne ha' hb' hab
      have ha'd' := lift_ne ha' hd' had
      have ha'w' := lift_ne ha' hw' haw
      have hb'd' := lift_ne hb' hd' hbd
      have hb'w' := lift_ne hb' hw' hbw
      have hd'w' := lift_ne hd' hw' hdw
      have hleg' := hleg.erase q
      have hn2 : 2 ≤ n := by omega
      -- The anchor stays saturated after deleting `q`.
      have h0' : rowDefect n lam
          (directionRow o e (c ∘ q.succAbove) v') = 1 := by
        have hle : rowDefect n lam
            (directionRow o e (c ∘ q.succAbove) v') ≤
            rowDefect n lam (directionRow o e c (q.succAbove v')) :=
          rowDefect_le_of_delete o e hlam hn (by omega) q v'
        rw [hv'] at hle
        have hge : 1 ≤ rowDefect n lam
            (directionRow o e (c ∘ q.succAbove) v') :=
          one_le_rowDefect lam hlam n _ (by omega)
            (rowCells_directionRow_le_of_floor_eq o e (c ∘ q.succAbove)
              hlam v' (by omega) hn)
        omega
      -- Each defect-`2` survivor stays defect `2` (`deletion_rigidity`
      -- consumes the anchor and one other defect-`2` survivor).
      have hrig (i j : Fin (t + 1)) (i' : Fin t) (hi' : q.succAbove i' = i)
          (hAi : v ≠ i) (hAj : v ≠ j) (hij : i ≠ j)
          (hjq : j ≠ q)
          (hdi : rowDefect n lam (directionRow o e c i) = 2)
          (hdj : rowDefect n lam (directionRow o e c j) = 2) :
          rowDefect n lam (directionRow o e (c ∘ q.succAbove) i') = 2 :=
        (deletion_rigidity o e he hn2 hlam hn hleg (by omega)
          hAi hAj hij (Ne.symm hqv) hjq hsat hdi hdj hi').2
      exact IH t (by omega) (by omega) hleg' hv'a' hv'b' hv'd' hv'w'
        ha'b' ha'd' ha'w' hb'd' hb'w' hd'w' h0'
        (hrig a b a' ha' hva hvb hab (Ne.symm hqb) hda hdb)
        (hrig b a b' hb' hvb hva hab.symm (Ne.symm hqa) hdb hda)
        (hrig d a d' hd' hvd hva had.symm (Ne.symm hqa) hdd hda)

/-- **Uniform bound on defect-`2` rows under a saturated anchor.**  At
any size `s ≥ 5`, at most two non-anchor rows can have defect `2`:
three such rows (plus any fifth center) are impossible by the
five-point closure lifted through deletion. -/
theorem defect_two_rows_le_two {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs5 : 5 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect n lam (directionRow o e c v) = 1) :
    (Finset.univ.filter (fun i : Fin s =>
      rowDefect n lam (directionRow o e c i) = 2)).card ≤ 2 := by
  classical
  by_contra hle
  push Not at hle
  set T := Finset.univ.filter (fun i : Fin s =>
    rowDefect n lam (directionRow o e c i) = 2)
  obtain ⟨a, b, d, haT, hbT, hdT, hab, had, hbd⟩ :=
    Finset.two_lt_card_iff.mp hle
  have hmem := fun {i : Fin s} (hi : i ∈ T) =>
    (Finset.mem_filter.mp hi).2
  have h2a := hmem haT; have h2b := hmem hbT; have h2d := hmem hdT
  have hne_v (i : Fin s) (hi : rowDefect n lam (directionRow o e c i) = 2) :
      i ≠ v := fun hiv => by rw [hiv, hsat] at hi; omega
  have hav := hne_v a h2a; have hbv := hne_v b h2b; have hdv := hne_v d h2d
  obtain ⟨w, hw⟩ : ∃ w : Fin s, w ∉ ({v, a, b, d} : Finset (Fin s)) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin s)) ⊆ {v, a, b, d} :=
      fun x _ => hcon x
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have hc4 : ({v, a, b, d} : Finset (Fin s)).card ≤ 4 := by
      have g1 := Finset.card_insert_le v ({a, b, d} : Finset (Fin s))
      have g2 := Finset.card_insert_le a ({b, d} : Finset (Fin s))
      have g3 := Finset.card_insert_le b ({d} : Finset (Fin s))
      rw [Finset.card_singleton] at g3
      omega
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨hwv, hwa, hwb, hwd⟩ := hw
  exact saturated_anchor_three_defect_two_impossible o e he hn3 hlam hn
    hs5 hleg hav.symm hbv.symm hdv.symm (Ne.symm hwv) hab had
    (Ne.symm hwa) hbd (Ne.symm hwb) (Ne.symm hwd) hsat h2a h2b h2d

/-- **Two-low-row position lift.**  In a saturated-anchor `SatChart` of
any size `≥ 5`, two defect-`2` rows `a,b` with `theta a < theta b` admit
no pair of further rows in the three cross-region positions:

* `theta x < theta a` and `theta b < theta y` (outer),
* `theta a < theta x < theta b` and `theta b < theta y` (mid-top),
* `theta x < theta a` and `theta a < theta y < theta b` (mid-bottom).

The induction deletes one center at a time.  The sub-chart reuses the
*same* reference vector `e`: erasing a row keeps the remaining `theta`
values inside `[0, π − nλ]`, so no fresh ray-window argument is needed.
Each defect-`2` row survives at defect `2` by `deletion_rigidity` with
the other one as witness; at size five the corresponding `pairkill`
discharges the pattern. -/
theorem two_defect_two_theta_clusters {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n) :
    ∀ {s : ℕ}, 4 ≤ s → ∀ {c : Fin (s + 1) → Plane₂},
      Section4Legality c lam →
      ∀ {v : Fin (s + 1)} {theta : Fin s → ℝ},
      SatChart o e n lam c v theta →
      rowDefect n lam (directionRow o e c v) = 1 →
      ∀ {a b : Fin s}, a ≠ b →
      rowDefect n lam (directionRow o e c (v.succAbove a)) = 2 →
      rowDefect n lam (directionRow o e c (v.succAbove b)) = 2 →
      theta a < theta b →
      ∀ {x y : Fin s}, x ≠ a → x ≠ b → y ≠ a → y ≠ b → x ≠ y →
      ¬ (theta x < theta a ∧ theta b < theta y) ∧
      ¬ (theta a < theta x ∧ theta x < theta b ∧ theta b < theta y) ∧
      ¬ (theta x < theta a ∧ theta a < theta y ∧ theta y < theta b) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro hs4 c hleg v theta C hsat a b hab hda hdb habθ x y
      hxa hxb hya hyb hxy
    by_cases h4 : s = 4
    · subst h4
      exact ⟨fun h => pairkill_outer C hxa hxb hxy hab (Ne.symm hya)
          (Ne.symm hyb) h.1 habθ h.2 hda hdb,
        fun h => pairkill_midtop C (Ne.symm hxa) hab (Ne.symm hya) hxb hxy
          (Ne.symm hyb) h.1 h.2.1 h.2.2 hda hdb,
        fun h => pairkill_midbot C hxa hxy hxb (Ne.symm hya) hab
          hyb h.1 h.2.1 h.2.2 hda hdb⟩
    · -- `s ≥ 5`: delete a center `q` outside `{v, va, vb, vx, vy}`.
      have hs5 : 5 ≤ s := by omega
      classical
      have hva' : v ≠ v.succAbove a := (Fin.succAbove_ne v a).symm
      have hvb' : v ≠ v.succAbove b := (Fin.succAbove_ne v b).symm
      have hvx' : v ≠ v.succAbove x := (Fin.succAbove_ne v x).symm
      have hvy' : v ≠ v.succAbove y := (Fin.succAbove_ne v y).symm
      have hab' : v.succAbove a ≠ v.succAbove b :=
        fun h => hab (Fin.succAbove_right_injective h)
      have hax' : v.succAbove a ≠ v.succAbove x :=
        fun h => (Ne.symm hxa) (Fin.succAbove_right_injective h)
      have hay' : v.succAbove a ≠ v.succAbove y :=
        fun h => (Ne.symm hya) (Fin.succAbove_right_injective h)
      have hbx' : v.succAbove b ≠ v.succAbove x :=
        fun h => (Ne.symm hxb) (Fin.succAbove_right_injective h)
      have hby' : v.succAbove b ≠ v.succAbove y :=
        fun h => (Ne.symm hyb) (Fin.succAbove_right_injective h)
      have hxy' : v.succAbove x ≠ v.succAbove y :=
        fun h => hxy (Fin.succAbove_right_injective h)
      obtain ⟨q, hq⟩ : ∃ q : Fin (s + 1),
          q ∉ ({v, v.succAbove a, v.succAbove b, v.succAbove x,
            v.succAbove y} : Finset (Fin (s + 1))) := by
        by_contra hcon
        push Not at hcon
        have hsub : (Finset.univ : Finset (Fin (s + 1))) ⊆ _ :=
          fun z _ => hcon z
        have hcard := Finset.card_le_card hsub
        have hcard5 : ({v, v.succAbove a, v.succAbove b, v.succAbove x,
            v.succAbove y} : Finset (Fin (s + 1))).card = 5 := by
          have g1 : v ∉ ({v.succAbove a, v.succAbove b, v.succAbove x,
              v.succAbove y} : Finset (Fin (s + 1))) := by
            simp [Finset.mem_insert, Finset.mem_singleton, hva', hvb',
              hvx', hvy']
          have g2 : v.succAbove a ∉ ({v.succAbove b, v.succAbove x,
              v.succAbove y} : Finset (Fin (s + 1))) := by
            simp [Finset.mem_insert, Finset.mem_singleton, hab', hax',
              hay']
          have g3 : v.succAbove b ∉ ({v.succAbove x, v.succAbove y} :
              Finset (Fin (s + 1))) := by
            simp [Finset.mem_insert, Finset.mem_singleton, hbx', hby']
          have g4 : v.succAbove x ∉ ({v.succAbove y} :
              Finset (Fin (s + 1))) := by
            simp [Finset.mem_singleton, hxy']
          rw [Finset.card_insert_of_notMem g1, Finset.card_insert_of_notMem g2,
            Finset.card_insert_of_notMem g3, Finset.card_insert_of_notMem g4,
            Finset.card_singleton]
        rw [Finset.card_univ, Fintype.card_fin, hcard5] at hcard
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      obtain ⟨hqv, hqa, hqb, hqx, hqy⟩ := hq
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      -- preimages under `q.succAbove` (sub-centre indices, `Fin (t+1)`)
      obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq (Ne.symm hqv)
      obtain ⟨am, ham⟩ := Fin.exists_succAbove_eq (Ne.symm hqa)
      obtain ⟨bm, hbm⟩ := Fin.exists_succAbove_eq (Ne.symm hqb)
      obtain ⟨xm, hxm⟩ := Fin.exists_succAbove_eq (Ne.symm hqx)
      obtain ⟨ym, hym⟩ := Fin.exists_succAbove_eq (Ne.symm hqy)
      -- sub-chart indices (preimages under `v'.succAbove`, `Fin (s-1)`)
      have hamv : am ≠ v' := fun h =>
        (Fin.succAbove_ne v a) (by rw [← ham, h, hv'])
      have hbmv : bm ≠ v' := fun h =>
        (Fin.succAbove_ne v b) (by rw [← hbm, h, hv'])
      have hxmv : xm ≠ v' := fun h =>
        (Fin.succAbove_ne v x) (by rw [← hxm, h, hv'])
      have hymv : ym ≠ v' := fun h =>
        (Fin.succAbove_ne v y) (by rw [← hym, h, hv'])
      obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq hamv
      obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hbmv
      obtain ⟨x', hx'⟩ := Fin.exists_succAbove_eq hxmv
      obtain ⟨y', hy'⟩ := Fin.exists_succAbove_eq hymv
      -- the sub-chart row map back to parent chart indices
      have hzne : ∀ i' : Fin t, q.succAbove (v'.succAbove i') ≠ v :=
        fun i' h =>
          Fin.succAbove_ne v' i'
            (Fin.succAbove_right_injective (h.trans hv'.symm))
      let pIdx : Fin t → Fin (t + 1) := fun i' =>
        Classical.choose (Fin.exists_succAbove_eq (hzne i'))
      have hpIdx : ∀ i' : Fin t,
          v.succAbove (pIdx i') = q.succAbove (v'.succAbove i') :=
        fun i' => Classical.choose_spec (Fin.exists_succAbove_eq (hzne i'))
      have hpa : pIdx a' = a := by
        have h1 := hpIdx a'
        rw [ha', ham] at h1
        exact Fin.succAbove_right_injective h1
      have hpb : pIdx b' = b := by
        have h1 := hpIdx b'
        rw [hb', hbm] at h1
        exact Fin.succAbove_right_injective h1
      have hpx : pIdx x' = x := by
        have h1 := hpIdx x'
        rw [hx', hxm] at h1
        exact Fin.succAbove_right_injective h1
      have hpy : pIdx y' = y := by
        have h1 := hpIdx y'
        rw [hy', hym] at h1
        exact Fin.succAbove_right_injective h1
      have ha'b' : a' ≠ b' := fun h => hab (by rw [← hpa, h, hpb])
      have hxa' : x' ≠ a' := fun h => hxa (by rw [← hpx, h, hpa])
      have hxb' : x' ≠ b' := fun h => hxb (by rw [← hpx, h, hpb])
      have hya' : y' ≠ a' := fun h => hya (by rw [← hpy, h, hpa])
      have hyb' : y' ≠ b' := fun h => hyb (by rw [← hpy, h, hpb])
      have hxy'' : x' ≠ y' := fun h => hxy (by rw [← hpx, h, hpy])
      -- the restricted chart: same reference, `theta` read off `pIdx`
      have hleg' := hleg.erase q
      have C' : SatChart o e n lam (c ∘ q.succAbove) v'
          (fun i' : Fin t => theta (pIdx i')) := by
        refine ⟨he, C.hn3, hlam, hn, hleg', ?_⟩
        intro i'
        obtain ⟨hmem, hoangle⟩ := C.htheta (pIdx i')
        refine ⟨hmem, ?_⟩
        show o.oangle e
            ((c ∘ q.succAbove) (v'.succAbove i') -
              (c ∘ q.succAbove) v') = _
        rw [Function.comp_apply, Function.comp_apply, ← hpIdx i', hv']
        exact hoangle
      have hn2 : 2 ≤ n := by have h3 := C.hn3; omega
      -- the anchor stays saturated under deletion
      have hsat' : rowDefect n lam
          (directionRow o e (c ∘ q.succAbove) v') = 1 := by
        have hle : rowDefect n lam
            (directionRow o e (c ∘ q.succAbove) v') ≤
            rowDefect n lam (directionRow o e c (q.succAbove v')) :=
          rowDefect_le_of_delete o e hlam hn (by omega) q v'
        rw [hv'] at hle
        have hge : 1 ≤ rowDefect n lam
            (directionRow o e (c ∘ q.succAbove) v') :=
          one_le_rowDefect lam hlam n _ (by omega)
            (rowCells_directionRow_le_of_floor_eq o e (c ∘ q.succAbove)
              hlam v' (by omega) hn)
        omega
      -- `a,b` stay defect `2`: each witnessed by the other
      have hda' : rowDefect n lam
          (directionRow o e (c ∘ q.succAbove) (v'.succAbove a')) = 2 := by
        rw [ha']
        exact (deletion_rigidity o e he hn2 hlam hn hleg (by omega)
          hva' hvb' hab' (Ne.symm hqv) (Ne.symm hqb) hsat hda hdb ham).2
      have hdb' : rowDefect n lam
          (directionRow o e (c ∘ q.succAbove) (v'.succAbove b')) = 2 := by
        rw [hb']
        exact (deletion_rigidity o e he hn2 hlam hn hleg (by omega)
          hvb' hva' hab'.symm (Ne.symm hqv) (Ne.symm hqa) hsat hdb hda hbm).2
      have t'a : theta (pIdx a') = theta a := congrArg theta hpa
      have t'b : theta (pIdx b') = theta b := congrArg theta hpb
      have t'x : theta (pIdx x') = theta x := congrArg theta hpx
      have t'y : theta (pIdx y') = theta y := congrArg theta hpy
      have habθ' : (fun i' : Fin t => theta (pIdx i')) a' <
          (fun i' : Fin t => theta (pIdx i')) b' := by
        show theta (pIdx a') < theta (pIdx b')
        rw [t'a, t'b]; exact habθ
      obtain ⟨g1, g2, g3⟩ := IH t (by omega) (by omega) hleg' C'
        hsat' ha'b' hda' hdb' habθ' hxa' hxb' hya' hyb' hxy''
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · exact g1 ⟨by rw [t'x, t'a]; exact h.1,
                  by rw [t'b, t'y]; exact h.2⟩
      · exact g2 ⟨by rw [t'a, t'x]; exact h.1,
                  by rw [t'x, t'b]; exact h.2.1,
                  by rw [t'b, t'y]; exact h.2.2⟩
      · exact g3 ⟨by rw [t'x, t'a]; exact h.1,
                  by rw [t'a, t'y]; exact h.2.1,
                  by rw [t'y, t'b]; exact h.2.2⟩

/-- **Region collapse.**  The three exclusions of
`two_defect_two_theta_clusters` say precisely that at most one of the
θ-regions `(−∞, θ_a)`, `(θ_a, θ_b)`, `(θ_b, ∞)` contains a further
non-anchor row.  Stated as a pure order fact on `theta`; an injective
`theta` hypothesis is what ties regions to row indices. -/
theorem theta_regions_collapse {s : ℕ} {theta : Fin s → ℝ}
    (hinj : Function.Injective theta) {a b : Fin s}
    (habθ : theta a < theta b)
    (H : ∀ {x y : Fin s}, x ≠ a → x ≠ b → y ≠ a → y ≠ b → x ≠ y →
      ¬ (theta x < theta a ∧ theta b < theta y) ∧
      ¬ (theta a < theta x ∧ theta x < theta b ∧ theta b < theta y) ∧
      ¬ (theta x < theta a ∧ theta a < theta y ∧ theta y < theta b)) :
    (∀ z : Fin s, z ≠ a → z ≠ b → theta z < theta a) ∨
    (∀ z : Fin s, z ≠ a → z ≠ b → theta a < theta z ∧ theta z < theta b) ∨
    (∀ z : Fin s, z ≠ a → z ≠ b → theta b < theta z) := by
  classical
  -- every other row sits in exactly one of the three regions
  have hclass (z : Fin s) (hza : z ≠ a) (hzb : z ≠ b) :
      theta z < theta a ∨ (theta a < theta z ∧ theta z < theta b) ∨
        theta b < theta z := by
    rcases lt_trichotomy (theta z) (theta a) with h | h | h
    · exact Or.inl h
    · exact absurd (hinj h) hza
    · rcases lt_trichotomy (theta z) (theta b) with h' | h' | h'
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact absurd (hinj h') hzb
      · exact Or.inr (Or.inr h')
  by_cases hL : ∃ z : Fin s, z ≠ a ∧ z ≠ b ∧ theta z < theta a
  · obtain ⟨x, hxa, hxb, hx⟩ := hL
    left
    intro z hza hzb
    rcases hclass z hza hzb with h | ⟨h1, h2⟩ | h
    · exact h
    · exact absurd ⟨hx, h1, h2⟩
        ((H hxa hxb hza hzb (fun hc =>
          absurd (congrArg theta hc) (ne_of_lt (hx.trans h1)))).2.2)
    · exact absurd ⟨hx, h⟩
        ((H hxa hxb hza hzb (fun hc =>
          absurd (congrArg theta hc)
            (ne_of_lt (hx.trans (habθ.trans h))))).1)
  · by_cases hH : ∃ z : Fin s, z ≠ a ∧ z ≠ b ∧ theta b < theta z
    · obtain ⟨y, hya, hyb, hy⟩ := hH
      right; right
      intro z hza hzb
      rcases hclass z hza hzb with h | ⟨h1, h2⟩ | h
      · exact absurd ⟨z, hza, hzb, h⟩ hL
      · exact absurd ⟨h1, h2, hy⟩
          ((H hza hzb hya hyb (fun hc =>
            absurd (congrArg theta hc) (ne_of_lt (h2.trans hy)))).2.1)
      · exact h
    · right; left
      intro z hza hzb
      rcases hclass z hza hzb with h | h | h
      · exact absurd ⟨z, hza, hzb, h⟩ hL
      · exact h
      · exact absurd ⟨z, hza, hzb, h⟩ hH

/-- **Two-low-row position classification, consumer form.**  At arbitrary
size `s + 1 ≥ 5` with a saturated anchor and two defect-`2` rows `a,b`,
the chart built by `saturated_ray_window` admits a θ-ordering `lo < hi`
of the pair such that every other non-anchor row sits in a single common
region: all below `lo`, all between `lo` and `hi`, or all above `hi`. -/
theorem defect_two_pair_theta_cluster {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs4 : 4 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    {v a b : Fin (s + 1)} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hda : rowDefect n lam (directionRow o e c a) = 2)
    (hdb : rowDefect n lam (directionRow o e c b) = 2) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin s → ℝ,
      SatChart o e' n lam c v theta ∧
      ∃ lo hi : Fin s,
        ((v.succAbove lo = a ∧ v.succAbove hi = b) ∨
          (v.succAbove lo = b ∧ v.succAbove hi = a)) ∧
        theta lo < theta hi ∧
        ((∀ z : Fin s, z ≠ lo → z ≠ hi → theta z < theta lo) ∨
         (∀ z : Fin s, z ≠ lo → z ≠ hi → theta lo < theta z ∧
            theta z < theta hi) ∨
         (∀ z : Fin s, z ≠ lo → z ≠ hi → theta hi < theta z)) := by
  obtain ⟨e', he', theta, htheta⟩ :=
    saturated_ray_window o e he (s := s) (by omega) (by omega) hlam hn
      hleg v hsat
  have C : SatChart o e' n lam c v theta := ⟨he', hn3, hlam, hn, hleg, htheta⟩
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (Ne.symm hva)
  obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq (Ne.symm hvb)
  have hdref : ∀ x : Fin (s + 1),
      rowDefect n lam (directionRow o e' c x) =
        rowDefect n lam (directionRow o e c x) :=
    fun x => rowDefect_directionRow_reference_eq o e' e he' he c
      hleg.inj x hlam (by omega) hn
  have hsat' : rowDefect n lam (directionRow o e' c v) = 1 := by
    rw [hdref]; exact hsat
  have hda' : rowDefect n lam (directionRow o e' c (v.succAbove a')) = 2 := by
    rw [hdref, ha']; exact hda
  have hdb' : rowDefect n lam (directionRow o e' c (v.succAbove b')) = 2 := by
    rw [hdref, hb']; exact hdb
  have ha'b' : a' ≠ b' := fun h => hab (by rw [← ha', ← hb', h])
  -- distinct non-anchor rays give distinct θ (Up is a strict order)
  have hinj : Function.Injective theta := by
    intro i j h
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · exfalso
      rcases up_or_up C hij with hup | hup
      · exact absurd h (ne_of_lt (up_theta_lt C hij hup))
      · exact absurd h.symm (ne_of_lt (up_theta_lt C hij.symm hup))
  have hne : theta a' ≠ theta b' := fun h => ha'b' (hinj h)
  rcases lt_or_gt_of_ne hne with habθ | habθ
  · refine ⟨e', he', theta, C, a', b', Or.inl ⟨ha', hb'⟩, habθ, ?_⟩
    exact theta_regions_collapse hinj habθ
      (two_defect_two_theta_clusters o e' he' hlam hn hs4 hleg C hsat'
        ha'b' hda' hdb' habθ)
  · refine ⟨e', he', theta, C, b', a', Or.inr ⟨hb', ha'⟩, habθ, ?_⟩
    exact theta_regions_collapse hinj habθ
      (two_defect_two_theta_clusters o e' he' hlam hn hs4 hleg C hsat'
        (Ne.symm ha'b') hdb' hda' habθ)

/-- **Five-point residual profile.**  In a five-point saturated-anchor
chart with two defect-`2` rows `a,b`, the remaining two rows are forced
to defect `≥ 3`: a defect-`1` remainder would be a second saturated row
(`rowDefect_ge_three_of_two_saturated` then pushes `a` to defect `≥ 3`,
contradicting `hda`), and a defect-`2` remainder creates a third
defect-`2` row, excluded by `five_point_R_ge_three_impossible`.  Hence
every five-point non-anchor defect profile with a saturated anchor and
two defect-`2` rows is `(2, 2, ≥ 3, ≥ 3)`.  Weight bookkeeping: the
anchor plus the two defect-`2` rows account for exactly
`2^{n−1} + 2·2^{n−2} = 4Q`; the four non-anchor rows together carry at
most `3Q`, so `F ≤ 4Q + 2^{n−c_x} + 2^{n−c_y} ≤ 5Q` once the residual
occupancy is charged.  This is the five-point kernel of the `r = 2`
tail:
any five-point subsample obtained by deleting other centers while
preserving `a,b` has this pinned profile. -/
theorem five_point_residual_defect_ge_three {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin 5 → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin 5) {theta : Fin 4 → ℝ}
    (C : SatChart o e n lam c v theta)
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    {a b x y : Fin 4}
    (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hxy : x ≠ y)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2) :
    3 ≤ rowDefect n lam (directionRow o e c (v.succAbove x)) ∧
      3 ≤ rowDefect n lam (directionRow o e c (v.succAbove y)) := by
  -- No other row can be saturated: a second defect-`1` row would push
  -- `a` to defect `≥ 3`.
  have hn1 : ∀ i : Fin 4, i ≠ a → i ≠ b →
      rowDefect n lam (directionRow o e c (v.succAbove i)) ≠ 1 := by
    intro i hia hib h1
    have hrow := rowDefect_ge_three_of_two_saturated o e he
      (by omega) hlam hn hleg (by omega)
      (i := v) (j := v.succAbove i) (k := v.succAbove a)
      (Fin.succAbove_ne v i).symm (Fin.succAbove_ne v a).symm
      (fun hcon => hia (Fin.succAbove_right_injective hcon))
      hsat h1
    omega
  -- No other row can have defect `2`: `{a, b, i}` would be three
  -- defect-`2` rows with all remaining rows at defect `≥ 3`.
  have hne2 : ∀ i : Fin 4, i ≠ a → i ≠ b →
      rowDefect n lam (directionRow o e c (v.succAbove i)) ≠ 2 := by
    intro i hia hib h2
    apply five_point_R_ge_three_impossible C
      (Finset.univ.filter (fun r : Fin 4 =>
        rowDefect n lam (directionRow o e c (v.succAbove r)) = 2))
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro r hr
      have hra : r ≠ a := fun h =>
        hr (h.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hda⟩)
      have hrb : r ≠ b := fun h =>
        hr (h.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdb⟩)
      have hr1 := hn1 r hra hrb
      have hge : 1 ≤ rowDefect n lam
          (directionRow o e c (v.succAbove r)) :=
        one_le_rowDefect lam hlam n _ (by omega)
          (rowCells_directionRow_le_of_floor_eq o e c hlam _
            (by omega) hn)
      have hrne2 : rowDefect n lam (directionRow o e c
          (v.succAbove r)) ≠ 2 := fun h =>
        hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      omega
    · have hsub : ({a, b, i} : Finset (Fin 4)) ⊆
          Finset.univ.filter (fun r : Fin 4 =>
            rowDefect n lam (directionRow o e c (v.succAbove r)) = 2) := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hda⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdb⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
      have hcard := Finset.card_le_card hsub
      have hc3 : ({a, b, i} : Finset (Fin 4)).card = 3 := by
        rw [Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
        · simp only [Finset.mem_singleton]; exact Ne.symm hib
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hab, Ne.symm hia⟩
      omega
  have hge1 : ∀ i : Fin 4, 1 ≤ rowDefect n lam
      (directionRow o e c (v.succAbove i)) :=
    fun i => one_le_rowDefect lam hlam n _ (by omega)
      (rowCells_directionRow_le_of_floor_eq o e c hlam _ (by omega) hn)
  refine ⟨?_, ?_⟩
  · have h1 := hn1 x hxa hxb
    have h2 := hne2 x hxa hxb
    have h0 := hge1 x
    omega
  · have h1 := hn1 y hya hyb
    have h2 := hne2 y hya hyb
    have h0 := hge1 y
    omega

/-- **Anchor-succession capacity.**  Delete the saturated anchor `v`.
If two distinct non-anchor rows `a, b` of defect `≥ 2` are both
saturated in the deleted configuration `C⁻`, then `F(C) ≤ F(C⁻)`: each
promoted row gains at least `Q = 2^{n−2}` of weight (paying back the
anchor's `2^{n−1}`), and every other surviving row is nondecreasing by
`rowScore_eraseIdx'`.  The deleted two-saturated bound
`potential_le_high_of_two_saturated` then closes the cap. -/
theorem potential_le_high_of_saturated_delete_anchor_sat_pair {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (a b : Fin s) (hab : a ≠ b)
    (hda : 2 ≤ rowDefect n lam (directionRow o e c (v.succAbove a)))
    (hdb : 2 ≤ rowDefect n lam (directionRow o e c (v.succAbove b)))
    (hsa : rowDefect n lam (directionRow o e (c ∘ v.succAbove) a) = 1)
    (hsb : rowDefect n lam (directionRow o e (c ∘ v.succAbove) b) = 1) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hleg' : Section4Legality (c ∘ v.succAbove) lam := hleg.erase v
  have hcap : potential lam (directionRows o e (c ∘ v.succAbove)) ≤
      2 ^ n + 2 ^ (n - 2) :=
    potential_le_high_of_two_saturated o e he (by omega) hn2 hlam hn
      hleg' hab hsa hsb
  -- surviving rows are nondecreasing
  have hmono : ∀ i : Fin s,
      rowScore lam (directionRow o e c (v.succAbove i)) ≤
        rowScore lam (directionRow o e (c ∘ v.succAbove) i) := by
    intro i
    rw [eraseIdx_directionRow o e (c' := c) v i,
      rowScore_eraseIdx' hlam (directionRow_sorted o e c _)
        (fun x hx => Set.mem_Ico.mp (directionRow_mem_Ico o e c hx))
        (deleteIndex_lt o e c (Fin.succAbove_ne v i))
        (by rw [directionRow_length]; omega)]
    exact Nat.le_add_right _ _
  -- score data
  have hcells := fun i : Fin (s + 1) =>
    rowCells_directionRow_le_of_floor_eq o e c hlam i (by omega) hn
  have hcells' := fun i : Fin s =>
    rowCells_directionRow_le_of_floor_eq o e (c ∘ v.succAbove) hlam i
      (by omega) hn
  have hscv : rowScore lam (directionRow o e c v) = n - 1 := by
    rw [rowScore_eq_sub_defect lam hlam n _ (hcells v), hsat]
  have hsc_a : rowScore lam (directionRow o e c (v.succAbove a)) ≤
      n - 2 := by
    have h := rowScore_eq_sub_defect lam hlam n _ (hcells (v.succAbove a))
    omega
  have hsc_b : rowScore lam (directionRow o e c (v.succAbove b)) ≤
      n - 2 := by
    have h := rowScore_eq_sub_defect lam hlam n _ (hcells (v.succAbove b))
    omega
  have hsc_a' : rowScore lam (directionRow o e (c ∘ v.succAbove) a) =
      n - 1 := by
    rw [rowScore_eq_sub_defect lam hlam n _ (hcells' a), hsa]
  have hsc_b' : rowScore lam (directionRow o e (c ∘ v.succAbove) b) =
      n - 1 := by
    rw [rowScore_eq_sub_defect lam hlam n _ (hcells' b), hsb]
  -- sum decomposition over succAbove: peel off a, b
  have hsplit : ∀ f : Fin s → ℕ,
      ∑ i : Fin s, f i =
        f a + f b + ∑ i ∈ (Finset.univ.erase a).erase b, f i := by
    intro f
    conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)]
    rw [add_assoc]
  have hpow : ∀ x y : ℕ, x ≤ y → (2 : ℕ) ^ x ≤ 2 ^ y :=
    fun x y hxy => Nat.pow_le_pow_right (by omega) hxy
  have hsum_le : (∑ i ∈ (Finset.univ.erase a).erase b,
        2 ^ rowScore lam (directionRow o e c (v.succAbove i))) ≤
      ∑ i ∈ (Finset.univ.erase a).erase b,
        2 ^ rowScore lam (directionRow o e (c ∘ v.succAbove) i) :=
    Finset.sum_le_sum fun i _ => hpow _ _ (hmono i)
  have h2ab : 2 ^ rowScore lam (directionRow o e c (v.succAbove a)) +
      2 ^ rowScore lam (directionRow o e c (v.succAbove b)) ≤
      2 ^ (n - 1) := by
    have ha := hpow _ _ hsc_a
    have hb := hpow _ _ hsc_b
    have h2p : (2 : ℕ) ^ (n - 2) + 2 ^ (n - 2) = 2 ^ (n - 1) := by
      conv_rhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
      omega
    omega
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  rw [hsplit (fun i => 2 ^ rowScore lam (directionRow o e c
    (v.succAbove i)))]
  calc 2 ^ rowScore lam (directionRow o e c v)
        + (2 ^ rowScore lam (directionRow o e c (v.succAbove a))
          + 2 ^ rowScore lam (directionRow o e c (v.succAbove b))
          + ∑ i ∈ (Finset.univ.erase a).erase b,
            2 ^ rowScore lam (directionRow o e c (v.succAbove i)))
      ≤ 2 ^ rowScore lam (directionRow o e (c ∘ v.succAbove) a)
        + 2 ^ rowScore lam (directionRow o e (c ∘ v.succAbove) b)
        + ∑ i ∈ (Finset.univ.erase a).erase b,
          2 ^ rowScore lam (directionRow o e (c ∘ v.succAbove) i) := by
        rw [hscv, hsc_a', hsc_b']; omega
    _ = potential lam (directionRows o e (c ∘ v.succAbove)) := by
        unfold potential exponentAt directionRows
        rw [← hsplit (fun i => 2 ^ rowScore lam (directionRow o e
          (c ∘ v.succAbove) i))]
    _ ≤ 2 ^ n + 2 ^ (n - 2) := hcap

/-- **Two double-big-end low rows close the cap.**  If the two defect-`2`
non-anchor rows `a ≠ b` each have both anchored end gaps `≥ λ`, deleting
the saturated anchor promotes both to saturation
(`rowDefect_succAbove_eq_one_of_big_ends`), and the deleted
configuration's two-saturated capacity bounds the original
(`potential_le_high_of_saturated_delete_anchor_sat_pair`).  In the
contrapositive this is the promised input: over-capacity forces at least
one defect-`2` row to have a genuine short end. -/
theorem potential_le_high_of_saturated_two_low_big_ends {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (a b : Fin s) (hab : a ≠ b)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2)
    (hfa : ∀ x ∈ directionRow o e (c ∘ v.succAbove) a, theta a + lam ≤ x)
    (hla : ∀ x ∈ directionRow o e (c ∘ v.succAbove) a,
      x ≤ theta a + Real.pi - lam)
    (hfb : ∀ x ∈ directionRow o e (c ∘ v.succAbove) b, theta b + lam ≤ x)
    (hlb : ∀ x ∈ directionRow o e (c ∘ v.succAbove) b,
      x ≤ theta b + Real.pi - lam) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hβl : Real.pi - n * lam < lam := by nlinarith
  have hβpi : Real.pi - n * lam < Real.pi := by nlinarith [hlam]
  have hlam_pi : lam < Real.pi := by nlinarith [hfloor]
  have hθw : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
    fun i => ⟨⟨(htheta i).1.1, le_trans (htheta i).1.2 hβl.le⟩,
      (htheta i).2⟩
  have hdir : ∀ i j : Fin s, i ≠ j →
      lam ≤ dirRep o e (c ∘ v.succAbove) i j := by
    intro i j hij
    have hsij : v.succAbove i ≠ v.succAbove j :=
      fun heq => hij (Fin.succAbove_right_injective heq)
    have hbnd := chord_in_corridor o he
      (fun hx' => Fin.succAbove_ne v i (hleg.inj hx'))
      (fun hx' => Fin.succAbove_ne v j (hleg.inj hx'))
      (fun hx' => hsij (hleg.inj hx'))
      hβl hβpi
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hsij
        (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hsij.symm
        (Fin.ne_succAbove v i))
    exact hbnd.1
  have hsa := rowDefect_succAbove_eq_one_of_big_ends o e he (by omega)
    (by omega : 1 ≤ n) hlam hlam_pi hn hleg v hθw hdir a hda hfa hla
  have hsb := rowDefect_succAbove_eq_one_of_big_ends o e he (by omega)
    (by omega : 1 ≤ n) hlam hlam_pi hn hleg v hθw hdir b hdb hfb hlb
  exact potential_le_high_of_saturated_delete_anchor_sat_pair o e he hs
    hn2 hlam hn hleg v hsat a b hab hda.ge hdb.ge hsa hsb

/-- **Extreme-receiver clump.**  Let `h` be a θ-minimal non-anchor row
(`theta h ≤ theta i` for all `i`) with defect `2`, a big last anchored
end gap (every element `≤ θ_h + π − λ`), and a genuinely short first
direction: some element `x < θ_h + 2λ` — the geometric input supplied
by a real short chord into `h`.  In the anchored chart its first floor
is exactly `1` and the last-gap floor is forced to `n − 1`, so the whole
row is pinned into `[θ_h + λ, θ_h + λ + β]` where `β = π − nλ`.  After
re-referencing to `e' = P_h − A` (which sends `θ'_h = 0` and is fully
justified by `directionRow_reference_shift` — no reflection transport
is assumed), the row lies in `[λ, λ + β]`, inside bin `0` of the legal
cover width `w₀ = (π − 2λ + β)/n > β`.  Occupancy `1` gives slack
`2^{n−1} − 2^{n−2} = 2^{n−2} = Q` in
`potential_le_high_of_saturated_slack_sum`. -/
theorem potential_le_high_of_saturated_min_receiver_clump {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1)) {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (h : Fin s) (hmin : ∀ i, theta h ≤ theta i)
    (hd2 : rowDefect n lam (directionRow o e c (v.succAbove h)) = 2)
    (hshort : ∃ x ∈ directionRow o e (c ∘ v.succAbove) h,
      x < theta h + 2 * lam)
    (hlast : ∀ x ∈ directionRow o e (c ∘ v.succAbove) h,
      x ≤ theta h + Real.pi - lam) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  classical
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hfloor' := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor'
  have hncast : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  set beta := Real.pi - n * lam with hbeta_def
  have hnl : (0 : ℝ) < (n : ℝ) * lam :=
    mul_pos (Nat.cast_pos.mpr (by omega)) hlam
  have h3l : (3 : ℝ) * lam ≤ (n : ℝ) * lam :=
    mul_le_mul_of_nonneg_right hncast hlam.le
  have hβ0 : 0 ≤ beta := by rw [hbeta_def]; linarith
  have hβl : beta < lam := by rw [hbeta_def]; linarith
  have hβpi : beta < Real.pi := by rw [hbeta_def]; linarith
  have hlam_pi : lam < Real.pi := by linarith [hfloor]
  have hpi : Real.pi = (n : ℝ) * lam + beta := by
    rw [hbeta_def]; ring
  have hleg' : Section4Legality (c ∘ v.succAbove) lam := hleg.erase v
  set l := directionRow o e (c ∘ v.succAbove) h with hl
  have hlne : l ≠ [] := by
    rw [hl, List.ne_nil_iff_length_pos, directionRow_length]; omega
  have hlsort : l.SortedLE := directionRow_sorted o e _ h
  -- per-element endpoint-window bounds
  have hall : ∀ x ∈ l, theta h + lam ≤ x ∧
      x ≤ Real.pi - lam + beta := by
    intro x hx
    rw [hl] at hx
    obtain ⟨j', hjh, rfl⟩ :=
      (mem_directionRow o e (c ∘ v.succAbove)).mp hx
    have hij : v.succAbove h ≠ v.succAbove j' :=
      fun heq => (Ne.symm hjh) (Fin.succAbove_right_injective heq)
    have hji : v.succAbove j' ≠ v.succAbove h := hij.symm
    have hbnd := chord_in_endpoint_window o he
      (fun hx' => Fin.succAbove_ne v h (hleg.inj hx'))
      (fun hx' => Fin.succAbove_ne v j' (hleg.inj hx'))
      (fun hx' => hij (hleg.inj hx')) hβl hβpi (htheta h).1 (htheta j').1
      (htheta h).2 (htheta j').2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v h) hij
        (Fin.ne_succAbove v j'))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j') hji
        (Fin.ne_succAbove v h))
    rcases hbnd with hb | hb
    · exact ⟨hb.1, le_trans hb.2
        (by linarith [(htheta j').1.2] :
          Real.pi - lam + theta j' ≤ Real.pi - lam + beta)⟩
    · exact ⟨le_trans
        (by linarith [hmin j'] : theta h + lam ≤ theta j' + lam) hb.1,
        le_trans hb.2 (by linarith [(htheta h).1.2] :
          Real.pi - lam + theta h ≤ Real.pi - lam + beta)⟩
  -- the pinned row: last ≤ θ_h + λ + β
  have hpin : l.getLast hlne ≤ theta h + lam + beta := by
    have hcorr : ∀ i j : Fin s, i ≠ j →
        lam ≤ dirRep o e (c ∘ v.succAbove) i j := by
      intro i j hij
      have hsij : v.succAbove i ≠ v.succAbove j :=
        fun heq => hij (Fin.succAbove_right_injective heq)
      have hbnd := chord_in_corridor o he
        (fun hx' => Fin.succAbove_ne v i (hleg.inj hx'))
        (fun hx' => Fin.succAbove_ne v j (hleg.inj hx'))
        (fun hx' => hsij (hleg.inj hx'))
        hβl hβpi (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
        (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hsij
          (Fin.ne_succAbove v j))
        (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hsij.symm
          (Fin.ne_succAbove v i))
      exact hbnd.1
    have hθw : ∀ i, theta i ∈ Set.Icc 0 lam ∧
        o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) :=
      fun i => ⟨⟨(htheta i).1.1, le_trans (htheta i).1.2 hβl.le⟩,
        (htheta i).2⟩
    have hlin : rowScore lam (directionRow o e c (v.succAbove h)) =
        linearGapScore lam (theta h) (theta h + Real.pi) l := by
      rw [hl]
      exact anchored_rowScore_eq_linear o e he c hleg.inj v hlam hlam_pi
        theta hθw hcorr h
    have hscF : rowScore lam (directionRow o e c (v.succAbove h)) =
        n - 2 := by
      rw [rowScore_eq_sub_defect lam hlam n _
        (rowCells_directionRow_le_of_floor_eq o e c hlam _ (by omega) hn),
        hd2]
    have hscore : linearGapScore lam (theta h) (theta h + Real.pi) l + 2
        = n := by
      rw [← hlin, hscF]; omega
    have hfloor1 : ⌊(l.head hlne - theta h) / lam⌋₊ = 1 := by
      have hge : lam ≤ l.head hlne - theta h := by
        have hb := (hall _ (List.head_mem hlne)).1; linarith
      have hlt : l.head hlne - theta h < 2 * lam := by
        obtain ⟨x, hx, hxlt⟩ := hshort
        have hhd : l.head hlne ≤ x := SortedLE_head_le hlsort hlne hx
        linarith
      have h1 : 1 ≤ ⌊(l.head hlne - theta h) / lam⌋₊ := by
        rw [Nat.le_floor_iff' one_ne_zero, le_div_iff₀ hlam]
        push_cast
        linarith
      have h2 : ⌊(l.head hlne - theta h) / lam⌋₊ < 2 := by
        rw [Nat.floor_lt' (by omega : (2 : ℕ) ≠ 0), div_lt_iff₀ hlam]
        push_cast
        linarith
      omega
    have hll : lam ≤ theta h + Real.pi - l.getLast hlne := by
      have := hlast _ (List.getLast_mem hlne); linarith
    have hmem' : ∀ x ∈ l, theta h ≤ x ∧ x ≤ theta h + Real.pi := by
      intro x hx
      have hb := hall x hx
      have h0 := (htheta h).1.1
      exact ⟨by linarith [hlam], by linarith [hβl]⟩
    have hfl : ⌊(theta h + Real.pi - theta h) / lam⌋₊ = n := by
      have hsub : theta h + Real.pi - theta h = Real.pi := by ring
      rw [hsub]; exact hn
    have hpin' := linearGapScore_last_le_of_big_ends_floor_one lam
      (theta h) (theta h + Real.pi) hlam hlne hlsort.pairwise hmem'
      hfloor1 hll hfl hscore
    have hconv : theta h + Real.pi - ((n - 1 : ℕ) : ℝ) * lam =
        theta h + lam + beta := by
      rw [hbeta_def, Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
      push_cast
      ring
    rwa [hconv] at hpin'
  -- whole row in [θ_h + λ, θ_h + λ + β]
  have hwin : ∀ x ∈ l, theta h + lam ≤ x ∧ x ≤ theta h + lam + beta :=
    fun x hx => ⟨(hall x hx).1,
      le_trans (SortedLE_le_getLast hlsort hlne hx) hpin⟩
  -- re-reference to e' = P_h − A
  set e' := c (v.succAbove h) - c v with he'_def
  have he' : e' ≠ 0 := sub_ne_zero.mpr
    (fun hx => Fin.succAbove_ne v h (hleg.inj hx))
  have hθh : o.oangle e e' = (theta h : Real.Angle) := (htheta h).2
  have hlcut : linRep (o.oangle e e') = theta h := by
    rw [hθh]
    exact (eq_linRep_of_int_pi
      ⟨(htheta h).1.1,
        lt_of_le_of_lt (htheta h).1.2 (lt_trans hβl hlam_pi)⟩
      ⟨0, by simp⟩).symm
  -- chart under e': θ'_i = θ_i − θ_h
  have htheta' : ∀ i, theta i - theta h ∈
      Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e' (c (v.succAbove i) - c v) =
        ((theta i - theta h : ℝ) : Real.Angle) := by
    intro i
    have hne_i : c (v.succAbove i) - c v ≠ 0 := sub_ne_zero.mpr
      (fun hx => Fin.succAbove_ne v i (hleg.inj hx))
    have ho : o.oangle e' (c (v.succAbove i) - c v) =
        o.oangle e (c (v.succAbove i) - c v) - o.oangle e e' :=
      (o.oangle_sub_left he he' hne_i).symm
    rw [ho, (htheta i).2, hθh, ← Real.Angle.coe_sub]
    exact ⟨⟨sub_nonneg.mpr (hmin i),
      by linarith [(htheta i).1.2, (htheta h).1.1]⟩, rfl⟩
  -- row h under e' is the shifted l
  have hl'eq : directionRow o e' (c ∘ v.succAbove) h =
      l.map (fun x => x - theta h) := by
    have hrange : ∀ a ∈ l, a ∈ Set.Ico 0 Real.pi := by
      intro a ha
      have hb := hall a ha
      have hub : a ≤ theta h + lam + beta :=
        le_trans (SortedLE_le_getLast hlsort hlne ha) hpin
      have h0 := (htheta h).1.1
      have hθ2 := (htheta h).1.2
      refine ⟨by linarith [hlam], ?_⟩
      nlinarith [hβl, hfloor, hlam, h0, hθ2, hub]
    rw [directionRow_reference_shift o e e' he he' _ hleg'.inj h, hlcut,
      ← hl]
    rw [insertionSort_projectiveShift (theta h) l hlsort hrange]
    have htw : l.takeWhile (fun a => decide (a < theta h)) = [] := by
      obtain ⟨x1, xt, hxt⟩ : ∃ x1 xt, l = x1 :: xt :=
        ⟨l.head hlne, l.tail, (List.cons_head_tail hlne).symm⟩
      rw [hxt, List.takeWhile_cons]
      have h1 : ¬ x1 < theta h := by
        have hb := (hall x1 (by rw [hxt]; exact List.mem_cons_self)).1
        linarith
      simp [h1]
    rw [htw, List.length_nil, List.rotate_zero]
    apply List.map_congr_left
    intro x hx
    have hb := (hall x hx).1
    unfold projectiveShift
    rw [if_neg (by linarith : ¬ x < theta h)]
  -- the legal cover width w₀ = (π − 2λ + β)/n satisfies β < w₀ < λ
  set w0 := (Real.pi - 2 * lam + beta) / n with hw0
  have hnn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnn0pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hw0num : 0 < Real.pi - 2 * lam + beta := by
    linarith [hpi, h3l, hβ0]
  have hw0pos : 0 < w0 := by
    rw [hw0]
    exact div_pos hw0num hnn0pos
  have hw0width : w0 < lam := by
    rw [hw0, div_lt_iff₀ hnn0pos]
    linarith [hpi, hβl]
  have hnw0 : (n : ℝ) * w0 = Real.pi - 2 * lam + beta := by
    rw [hw0, mul_comm, div_mul_cancel₀ _ hnn0]
  have hcover : Real.pi - 2 * lam + (Real.pi - n * lam) ≤
      (n : ℝ) * w0 := by
    rw [hnw0]
  have hcoverlt : (n : ℝ) * w0 < Real.pi - lam := by
    rw [hnw0]; linarith [hβl]
  have hβw : beta < w0 := by
    rw [hw0, lt_div_iff₀ hnn0pos]
    have hprod : ((n : ℝ) - 2) * beta < ((n : ℝ) - 2) * lam :=
      mul_lt_mul_of_pos_left hβl (by linarith [hncast])
    nlinarith [hpi, hprod]
  -- occupancy 1 for row h under e': every element falls in bin 0
  have hocc : ((directionRow o e' (c ∘ v.succAbove) h).map
      (uniformBin lam w0 n)).toFinset.card = 1 := by
    rw [hl'eq]
    have hall0 : ∀ y ∈ l.map (fun x => x - theta h),
        uniformBin lam w0 n y = 0 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      have hb := hall x hx
      have hub : x ≤ theta h + lam + beta :=
        le_trans (SortedLE_le_getLast hlsort hlne hx) hpin
      have hfl : ⌊(x - theta h - lam) / w0⌋₊ = 0 := by
        rw [Nat.floor_eq_zero, div_lt_one hw0pos]
        linarith [hb.1, hub, hβw]
      unfold uniformBin
      rw [hfl]
      exact min_eq_left (Nat.zero_le _)
    have hset : ((l.map (fun x => x - theta h)).map
        (uniformBin lam w0 n)).toFinset = {0} := by
      ext y
      rw [List.mem_toFinset, Finset.mem_singleton]
      constructor
      · intro hy
        obtain ⟨z, hz, hzEq⟩ := List.mem_map.mp hy
        rw [← hzEq]; exact hall0 z hz
      · intro hy
        rw [hy]
        apply List.mem_map.mpr
        exact ⟨l.head hlne - theta h,
          List.mem_map.mpr ⟨l.head hlne, List.head_mem hlne, rfl⟩,
          hall0 _ (List.mem_map.mpr
            ⟨l.head hlne, List.head_mem hlne, rfl⟩)⟩
    rw [hset]; simp
  -- defect is reference-invariant
  have hd2' : rowDefect n lam (directionRow o e' c (v.succAbove h)) = 2 := by
    have h := rowDefect_directionRow_reference_eq o e e' he he' c hleg.inj
      (v.succAbove h) hlam (by omega : 2 ≤ s + 1) hn
    rw [← h]; exact hd2
  have hslack : 2 ^ (n - 2) ≤ ∑ i ∈ ({h} : Finset (Fin s)),
      (2 ^ (n - ((directionRow o e' (c ∘ v.succAbove) i).map
          (uniformBin lam w0 n)).toFinset.card) -
       2 ^ (n - rowDefect n lam
         (directionRow o e' c (v.succAbove i)))) := by
    rw [Finset.sum_singleton, hocc, hd2']
    have h2p : (2 : ℕ) ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
      conv_lhs => rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
      omega
    omega
  have hcap := potential_le_high_of_saturated_slack_sum o e' he'
    (by omega : 1 ≤ s) hn3 hlam hn hleg v htheta' hw0pos hw0width
    hcover hcoverlt ({h} : Finset (Fin s)) hslack
  rw [potential_directionRows_reference_eq o e e' he he' c hleg.inj lam]
  exact hcap

#print axioms rowDefect_directionRow_reference_eq
#print axioms potential_le_high_of_saturated_five
#print axioms potential_le_high_cap_of_le_five
#print axioms potential_le_two_pow_of_le_four_low
#print axioms certExists_of_bounded_below
#print axioms certExists_true_of_six_le
#print axioms certExists_false_of_five_le
#print axioms rowScore_le_of_delete
#print axioms rowDefect_le_of_delete
#print axioms saturated_anchor_three_defect_two_impossible
#print axioms defect_two_rows_le_two
#print axioms two_defect_two_theta_clusters
#print axioms theta_regions_collapse
#print axioms defect_two_pair_theta_cluster
#print axioms five_point_residual_defect_ge_three
#print axioms potential_le_high_of_saturated_delete_anchor_sat_pair
#print axioms potential_le_high_of_saturated_two_low_big_ends
#print axioms potential_le_high_of_saturated_min_receiver_clump

end Jsp404
