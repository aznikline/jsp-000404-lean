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

end Jsp404
