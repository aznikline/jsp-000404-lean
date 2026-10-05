import Jsp000404.BandMaximumScorePlateau
import Jsp000404.FlatBandMaximumDeletion

/-!
Actual deletions of a fixed flat band maximizer have boundary constraints.
Every scale strictly above the lower boundary and at most the attained
scale preserves the fixed configuration's legality and flatness. The
one-unit deletion budget therefore bounds each actual deleted row's
score by one and permits at most one positive deleted row.

Testing a common scale arbitrarily close to the lower boundary gives
deleted cyclic gaps at most `3 * rho`, and at most one deleted row with
any cyclic gap strictly larger than `2 * rho`. Equality at `2 * rho`
is excluded from that count. No legality, flatness, potential equality,
or raw-floor equality at `rho` is asserted, and no sharp capacity or
original lower-bound theorem is proved here.
-/

open scoped EuclideanGeometry BigOperators

set_option autoImplicit false

namespace Jsp404.BandMaximumDeletionBoundary

/-- Actual surviving rows of a fixed deletion with a cyclic gap strictly
larger than twice the lower band boundary. -/
noncomputable def deletedLargeGapRows {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (d : Fin (s + 1) → Plane₂) (rho : ℝ) (q : Fin (s + 1)) : Finset (Fin s) :=
  Finset.univ.filter (fun i =>
    ∃ g ∈ cycGaps (directionRow o e (d ∘ q.succAbove) i), 2 * rho < g)

/-- A row of score at most one has every cyclic gap below three scales. -/
theorem cycGaps_lt_three_mul_of_rowScore_le_one {lam : ℝ} (hlam : 0 < lam)
    {l : List ℝ} (hscore : rowScore lam l ≤ 1) :
    ∀ g ∈ cycGaps l, g < 3 * lam := by
  intro g hg
  have hmem : gapScore lam g ∈ (cycGaps l).map (gapScore lam) :=
    List.mem_map.mpr ⟨g, hg, rfl⟩
  have hterm : gapScore lam g ≤ rowScore lam l := List.le_sum_of_mem hmem
  by_cases hg0 : 0 ≤ g
  · have hf : ⌊g / lam⌋₊ ≤ 2 := by
      unfold gapScore at hterm
      omega
    rw [Nat.le_iff_lt_add_one, Nat.floor_lt (div_nonneg hg0 hlam.le),
      div_lt_iff₀ hlam] at hf
    push_cast at hf
    linarith
  · have hgneg : g < 0 := lt_of_not_ge hg0
    linarith

/-- A cyclic gap reaching two scales gives a positive actual row score. -/
theorem rowScore_pos_of_cycGap_ge_two_mul {lam : ℝ} (hlam : 0 < lam)
    {l : List ℝ} {g : ℝ} (hg : g ∈ cycGaps l) (hlarge : 2 * lam ≤ g) :
    1 ≤ rowScore lam l := by
  by_contra hnot
  have hz : rowScore lam l = 0 := by omega
  have hsmall := cycGaps_lt_two_mul_of_rowScore_zero hlam hz g hg
  linarith

/-- The actual deleted row score is exactly the original flat row's gain.
The row is supplied by the geometric deletion, not by a free gain array. -/
theorem actual_flat_delete_rowScore_eq_gain {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {d : Fin (s + 1) → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hflat : Flat lam (directionRows o e d)) (q : Fin (s + 1)) (i : Fin s) :
    rowScore lam (directionRow o e (d ∘ q.succAbove) i) =
      rowGain lam (directionRow o e d (q.succAbove i))
        (deleteIndex o e d q (q.succAbove i)) := by
  rw [eraseIdx_directionRow o e q i]
  rw [rowScore_eraseIdx' hlam (directionRow_sorted o e d (q.succAbove i))
    (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e d hb))
    (deleteIndex_lt o e d (Fin.succAbove_ne q i))
    (by rw [directionRow_length o e d (q.succAbove i)]; omega)]
  have hz : rowScore lam (directionRow o e d (q.succAbove i)) = 0 :=
    hflat (q.succAbove i)
  rw [hz, zero_add]

/-- A single smaller scale in the same open band keeps the fixed actual
model flat and gives score at most one, with at most one positive row,
in every actual deleted configuration. -/
theorem actual_flat_band_maximum_smaller_delete_constraints {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {d : Fin (s + 1) → Plane₂} {rho upper scale scale' : ℝ}
    (hrho : 0 ≤ rho) (hleg : Section4Legality d scale)
    (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e d) = s + 1)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper (s + 1))
    (hflat : Flat scale (directionRows o e d))
    (hlo : rho < scale') (hsmall : scale' ≤ scale) :
    Section4Legality d scale' ∧ Flat scale' (directionRows o e d) ∧
      potential scale' (directionRows o e d) = s + 1 ∧
      ∀ q : Fin (s + 1),
        (∀ i : Fin s, rowScore scale' (directionRow o e (d ∘ q.succAbove) i) ≤ 1) ∧
        (∀ i j : Fin s,
          1 ≤ rowScore scale' (directionRow o e (d ∘ q.succAbove) i) →
          1 ≤ rowScore scale' (directionRow o e (d ∘ q.succAbove) j) → i = j) := by
  classical
  have hpos : 0 < scale' := hrho.trans_lt hlo
  have hleg' : Section4Legality d scale' := by
    refine ⟨hpos, hleg.inj, ?_⟩
    intro i j k hij hjk hik
    have h := hleg.triAngle i j k hij hjk hik
    linarith
  have hplateau := BandMaximumScorePlateau.actual_band_maximum_score_plateau
    (by omega : 3 ≤ s + 1) o e d hrho hleg habove hupper hpot hmax hlo hsmall
  have hflat' := BandMaximumScorePlateau.actual_band_maximum_flat_plateau
    (by omega : 3 ≤ s + 1) o e d hrho hleg habove hupper hpot hmax hflat hlo hsmall
  refine ⟨hleg', hflat', hplateau.1, ?_⟩
  intro q
  have hgain := FlatBandMaximumDeletion.actual_band_maximizer_delete_has_at_most_one_emitter
    hs o e hleg' hflat' hlo (hsmall.trans hupper) hmax q
  have hrow := actual_flat_delete_rowScore_eq_gain (by omega : 2 ≤ s) o e
    hpos hflat' q
  refine ⟨?_, ?_⟩
  · intro i
    rw [hrow i]
    exact hgain.1 (q.succAbove i) (Fin.succAbove_ne q i)
  · intro i j hi hj
    have hmemi : q.succAbove i ∈ (Finset.univ.erase q).filter (fun k =>
        1 ≤ rowGain scale' (directionRow o e d k) (deleteIndex o e d q k)) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_erase.mpr ⟨Fin.succAbove_ne q i, Finset.mem_univ _⟩, ?_⟩
      rwa [hrow i] at hi
    have hmemj : q.succAbove j ∈ (Finset.univ.erase q).filter (fun k =>
        1 ≤ rowGain scale' (directionRow o e d k) (deleteIndex o e d q k)) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_erase.mpr ⟨Fin.succAbove_ne q j, Finset.mem_univ _⟩, ?_⟩
      rwa [hrow j] at hj
    exact Fin.succAbove_right_injective ((Finset.card_le_one.mp hgain.2) _ hmemi _ hmemj)

/-- Every cyclic gap in every actual deleted row is at most three times
the open lower band boundary. This conclusion includes equality. -/
theorem actual_flat_band_maximum_delete_gap_le_three_rho {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {d : Fin (s + 1) → Plane₂} {rho upper scale : ℝ}
    (hrho : 0 ≤ rho) (hleg : Section4Legality d scale)
    (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e d) = s + 1)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper (s + 1))
    (hflat : Flat scale (directionRows o e d)) :
    ∀ q : Fin (s + 1), ∀ i : Fin s,
      ∀ g ∈ cycGaps (directionRow o e (d ∘ q.succAbove) i), g ≤ 3 * rho := by
  intro q i g hg
  by_contra hnot
  have hgt : 3 * rho < g := lt_of_not_ge hnot
  have hmin : rho < min scale (g / 3) := lt_min habove (by linarith)
  let scale' := (rho + min scale (g / 3)) / 2
  have hlo : rho < scale' := by dsimp [scale']; linarith
  have hlt : scale' < min scale (g / 3) := by dsimp [scale']; linarith
  have hsmall : scale' ≤ scale := hlt.le.trans (min_le_left _ _)
  have hrow := (actual_flat_band_maximum_smaller_delete_constraints hs o e hrho
    hleg habove hupper hpot hmax hflat hlo hsmall).2.2.2 q
  have hb := cycGaps_lt_three_mul_of_rowScore_le_one (hrho.trans_lt hlo)
    (hrow.1 i) g hg
  have hltg : scale' < g / 3 := hlt.trans_le (min_le_right _ _)
  linarith

/-- If two actual deleted rows each have a cyclic gap strictly exceeding
twice the boundary, a single common smaller scale makes both scores
positive. The one-unit budget therefore forces the rows to be equal. -/
theorem actual_flat_band_maximum_delete_large_gap_row_unique {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {d : Fin (s + 1) → Plane₂} {rho upper scale : ℝ}
    (hrho : 0 ≤ rho) (hleg : Section4Legality d scale)
    (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e d) = s + 1)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper (s + 1))
    (hflat : Flat scale (directionRows o e d))
    (q : Fin (s + 1)) (i j : Fin s)
    (hi : ∃ g ∈ cycGaps (directionRow o e (d ∘ q.succAbove) i), 2 * rho < g)
    (hj : ∃ g ∈ cycGaps (directionRow o e (d ∘ q.succAbove) j), 2 * rho < g) :
    i = j := by
  obtain ⟨gi, hgi, hlargei⟩ := hi
  obtain ⟨gj, hgj, hlargej⟩ := hj
  have hmin : rho < min scale (min (gi / 2) (gj / 2)) :=
    lt_min habove (lt_min (by linarith) (by linarith))
  let scale' := (rho + min scale (min (gi / 2) (gj / 2))) / 2
  have hlo : rho < scale' := by dsimp [scale']; linarith
  have hlt : scale' < min scale (min (gi / 2) (gj / 2)) := by
    dsimp [scale']; linarith
  have hsmall : scale' ≤ scale := hlt.le.trans (min_le_left _ _)
  have hltgi : scale' < gi / 2 := hlt.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hltgj : scale' < gj / 2 := hlt.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hscorei : 1 ≤ rowScore scale' (directionRow o e (d ∘ q.succAbove) i) :=
    rowScore_pos_of_cycGap_ge_two_mul (hrho.trans_lt hlo) hgi (by linarith)
  have hscorej : 1 ≤ rowScore scale' (directionRow o e (d ∘ q.succAbove) j) :=
    rowScore_pos_of_cycGap_ge_two_mul (hrho.trans_lt hlo) hgj (by linarith)
  exact ((actual_flat_band_maximum_smaller_delete_constraints hs o e hrho
    hleg habove hupper hpot hmax hflat hlo hsmall).2.2.2 q).2 i j hscorei hscorej

/-- For each actual deletion, at most one surviving row has any cyclic
gap strictly above twice the boundary. A gap equal to the threshold
does not satisfy the filtering predicate. -/
theorem actual_flat_band_maximum_delete_large_gap_card_le_one {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {d : Fin (s + 1) → Plane₂} {rho upper scale : ℝ}
    (hrho : 0 ≤ rho) (hleg : Section4Legality d scale)
    (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e d) = s + 1)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper (s + 1))
    (hflat : Flat scale (directionRows o e d)) (q : Fin (s + 1)) :
    (deletedLargeGapRows o e d rho q).card ≤ 1 := by
  classical
  unfold deletedLargeGapRows
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact actual_flat_band_maximum_delete_large_gap_row_unique hs o e hrho
    hleg habove hupper hpot hmax hflat q i j
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Boundary data on the fixed original configuration and all its actual
deletions, with no strip parameter or LOW/HIGH-specific restriction. -/
theorem actual_flat_band_maximum_deletion_boundary {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {d : Fin (s + 1) → Plane₂} {rho upper scale : ℝ}
    (hrho : 0 ≤ rho) (hleg : Section4Legality d scale)
    (habove : rho < scale) (hupper : scale ≤ upper)
    (hpot : potential scale (directionRows o e d) = s + 1)
    (hmax : ActualMaximumMassReduction.BandMaximal o e rho upper (s + 1))
    (hflat : Flat scale (directionRows o e d)) :
    (∀ i : Fin (s + 1), ∀ g ∈ cycGaps (directionRow o e d i), g ≤ 2 * rho) ∧
      (∀ q : Fin (s + 1), ∀ i : Fin s,
        ∀ g ∈ cycGaps (directionRow o e (d ∘ q.succAbove) i), g ≤ 3 * rho) ∧
      ∀ q : Fin (s + 1),
        (deletedLargeGapRows o e d rho q).card ≤ 1 := by
  exact ⟨BandMaximumScorePlateau.actual_flat_band_maximum_gap_le_two_rho
      (by omega : 3 ≤ s + 1) o e d hrho hleg habove hupper hpot hmax hflat,
    actual_flat_band_maximum_delete_gap_le_three_rho hs o e hrho hleg habove hupper
      hpot hmax hflat,
    actual_flat_band_maximum_delete_large_gap_card_le_one hs o e hrho hleg habove hupper
      hpot hmax hflat⟩

#print axioms deletedLargeGapRows
#print axioms cycGaps_lt_three_mul_of_rowScore_le_one
#print axioms rowScore_pos_of_cycGap_ge_two_mul
#print axioms actual_flat_delete_rowScore_eq_gain
#print axioms actual_flat_band_maximum_smaller_delete_constraints
#print axioms actual_flat_band_maximum_delete_gap_le_three_rho
#print axioms actual_flat_band_maximum_delete_large_gap_row_unique
#print axioms actual_flat_band_maximum_delete_large_gap_card_le_one
#print axioms actual_flat_band_maximum_deletion_boundary

end Jsp404.BandMaximumDeletionBoundary
