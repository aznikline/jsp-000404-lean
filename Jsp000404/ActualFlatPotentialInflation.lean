import Jsp000404.ActualPotentialInflation

/-! Genuine inflation to zero-score points with the original potential.
A finite strict-gap margin preserves all terminal zero scores when the
parameter is decreased. No capacity or cardinal exclusion is used.
-/

open scoped EuclideanGeometry BigOperators

namespace Jsp404.ActualFlatPotentialInflation

/-- Equality in the elementary card/potential bound means every score is zero. -/
theorem flat_of_potential_eq_card {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (heq : potential lam row = s) : Flat lam row := by
  classical
  have hpow : ∀ i : Fin s, 1 ≤ 2 ^ rowScore lam (row i) :=
    fun _ => Nat.one_le_pow _ 2 (by decide)
  have hsum : (∑ i : Fin s, (2 ^ rowScore lam (row i) - 1)) = 0 := by
    have hcalc : potential lam row =
        (∑ i : Fin s, (2 ^ rowScore lam (row i) - 1)) + s := by
      calc
        potential lam row = ∑ i : Fin s,
            ((2 ^ rowScore lam (row i) - 1) + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (Nat.sub_add_cancel (hpow i)).symm
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    omega
  intro i
  have hz : 2 ^ rowScore lam (row i) - 1 = 0 :=
    (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
  by_contra hne
  change rowScore lam (row i) ≠ 0 at hne
  have hlt := Nat.one_lt_pow hne (by decide : 1 < (2 : ℕ))
  omega

private theorem exists_smaller_scale_with_gap_bounds (gs : List ℝ)
    {lam tau : ℝ} (hgs : ∀ g ∈ gs, g < 2 * lam)
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧ ∀ g ∈ gs, g < 2 * lam' := by
  induction gs generalizing tau with
  | nil => exact ⟨(tau + lam) / 2, by linarith, by linarith, by simp⟩
  | cons g gs ih =>
    have hg : g / 2 < lam := by have := hgs g (by simp); linarith
    have ht0 : 0 < max tau (g / 2) := htau0.trans_le (le_max_left _ _)
    have ht : max tau (g / 2) < lam := max_lt htau hg
    obtain ⟨lam', hlow, hsmall, hrest⟩ :=
      ih (fun x hx => hgs x (by simp [hx])) ht0 ht
    refine ⟨lam', (le_max_left _ _).trans_lt hlow, hsmall, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      have := (le_max_right tau (g / 2)).trans_lt hlow
      linarith
    · exact hrest x hx

/-- A finite family of zero-score rows stays flat at a slightly smaller scale. -/
theorem exists_smaller_scale_preserving_flat {s : ℕ}
    (row : Fin s → List ℝ) {lam tau : ℝ} (hlam : 0 < lam)
    (hflat : Flat lam row) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧ Flat lam' row := by
  classical
  let gs := (List.ofFn fun i : Fin s => cycGaps (row i)).flatten
  have hgs : ∀ g ∈ gs, g < 2 * lam := by
    intro g hg
    obtain ⟨l, hl, hgl⟩ := List.mem_flatten.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact cycGaps_lt_two_mul_of_rowScore_zero hlam (hflat i) g hgl
  obtain ⟨lam', hlow, hsmall, hbound⟩ :=
    exists_smaller_scale_with_gap_bounds gs hgs htau0 htau
  have hlam' : 0 < lam' := htau0.trans hlow
  refine ⟨lam', hlow, hsmall, ?_⟩
  intro i
  change ((cycGaps (row i)).map (gapScore lam')).sum = 0
  apply List.sum_eq_zero_iff.mpr
  intro q hq
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
  have hgl : g ∈ gs := List.mem_flatten.mpr
    ⟨cycGaps (row i), List.mem_ofFn.mpr ⟨i, rfl⟩, hg⟩
  have hq2 : g / lam' < 2 := (div_lt_iff₀ hlam').mpr (hbound g hgl)
  have hf : ⌊g / lam'⌋₊ < 2 := (Nat.floor_lt' (by decide : (2 : ℕ) ≠ 0)).mpr hq2
  unfold gapScore
  omega

/-- Actual inflation preserving the original potential and ending with
exactly that many distinct points, all of whose scores are zero. -/
theorem exists_exact_flat_actual_inflation {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam tau : ℝ}
    (hleg : Section4Legality c lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lamFinal : ℝ, tau < lamFinal ∧ lamFinal < lam ∧
      ∃ cFinal : Fin (potential lam (directionRows o e c)) → Plane₂,
        Section4Legality cFinal lamFinal ∧
        Flat lamFinal (directionRows o e cFinal) ∧
        potential lamFinal (directionRows o e cFinal) =
          potential lam (directionRows o e c) := by
  classical
  have aux : ∀ d : ℕ, ∀ {t : ℕ} (ht : 3 ≤ t) (p : Fin t → Plane₂)
      {scale threshold : ℝ}, Section4Legality p scale →
      0 < threshold → threshold < scale →
      potential scale (directionRows o e p) - t = d →
      ∃ scaleFinal : ℝ, threshold < scaleFinal ∧ scaleFinal < scale ∧
        ∃ pFinal : Fin (potential scale (directionRows o e p)) → Plane₂,
          Section4Legality pFinal scaleFinal ∧
          Flat scaleFinal (directionRows o e pFinal) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro t ht p scale threshold hp hthreshold0 hthreshold hmeasure
      let F := potential scale (directionRows o e p)
      have hge : t ≤ F := ActualPotentialInflation.card_le_potential scale _
      by_cases hterminal : F = t
      · have hflat : Flat scale (directionRows o e p) :=
          flat_of_potential_eq_card scale _ hterminal
        obtain ⟨scaleFinal, hlow, hsmall, hflatFinal⟩ :=
          exists_smaller_scale_preserving_flat _ hp.lam_pos hflat hthreshold0 hthreshold
        have hpFinal := ActualPotentialInflation.Section4Legality_weaken
          hp (hthreshold0.trans hlow) hsmall
        let E := finCongr hterminal
        refine ⟨scaleFinal, hlow, hsmall, p ∘ E, hpFinal.reindex E, ?_⟩
        intro i
        change rowScore scaleFinal (directionRow o e (p ∘ E) i) = 0
        rw [directionRow_reindex o e p E i]
        exact hflatFinal (E i)
      · have hsurplus : t < potential scale (directionRows o e p) := by
          dsimp [F] at hge hterminal
          omega
        obtain ⟨v, hv⟩ :=
          ActualPotentialInflation.exists_positive_score_of_card_lt_potential scale _ hsurplus
        obtain ⟨scale', hlow, hsmall, p', hp', hpotential⟩ :=
          SingleSplitScorePreservation.exists_single_positive_split_preserving_potential
            o e he ht p hp v hv hthreshold0 hthreshold
        have hsmaller : potential scale' (directionRows o e p') - (t + 1) < d := by omega
        obtain ⟨scaleFinal, hfinalLow, hfinalSmall, pFinal, hlegal, hflat⟩ :=
          ih (potential scale' (directionRows o e p') - (t + 1)) hsmaller
            (by omega : 3 ≤ t + 1) p' hp' hthreshold0 hlow rfl
        let E := finCongr hpotential.symm
        refine ⟨scaleFinal, hfinalLow, hfinalSmall.trans hsmall,
          pFinal ∘ E, hlegal.reindex E, ?_⟩
        intro i
        change rowScore scaleFinal (directionRow o e (pFinal ∘ E) i) = 0
        rw [directionRow_reindex o e pFinal E i]
        exact hflat (E i)
  obtain ⟨lamFinal, hlow, hsmall, cFinal, hlegal, hflat⟩ :=
    aux (potential lam (directionRows o e c) - s) hs c hleg htau0 htau rfl
  refine ⟨lamFinal, hlow, hsmall, cFinal, hlegal, hflat, ?_⟩
  exact flat_potential lamFinal _ hflat

#print axioms flat_of_potential_eq_card
#print axioms exists_smaller_scale_preserving_flat
#print axioms exists_exact_flat_actual_inflation

end Jsp404.ActualFlatPotentialInflation
