import Jsp000404.SingleSplitScorePreservation

/-! Exact genuine point inflation from the original geometric potential.
Strong induction on potential minus point count uses one actual positive
row split at each step. Every axis is extracted afresh from the actual
current configuration. No capacity or ordinary-point count bound is assumed.
-/

open scoped EuclideanGeometry BigOperators

namespace Jsp404.ActualPotentialInflation

/-- Every actual row contributes at least one to the potential. -/
theorem card_le_potential {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ) :
    s ≤ potential lam row := by
  calc
    s = ∑ _ : Fin s, (1 : ℕ) := by simp
    _ ≤ ∑ i : Fin s, 2 ^ rowScore lam (row i) :=
      Finset.sum_le_sum fun i _ => Nat.one_le_pow _ 2 (by decide)
    _ = potential lam row := rfl

/-- Strict surplus supplies an actual positive row, rather than a scalar
profile or a capacity assumption. -/
theorem exists_positive_score_of_card_lt_potential {s : ℕ}
    (lam : ℝ) (row : Fin s → List ℝ) (h : s < potential lam row) :
    ∃ i, 0 < rowScore lam (row i) := by
  classical
  by_contra hnone
  have hz : ∀ i, rowScore lam (row i) = 0 := by
    intro i
    have hnot : ¬0 < rowScore lam (row i) := fun hi => hnone ⟨i, hi⟩
    omega
  have heq : potential lam row = s := by
    unfold potential exponentAt
    simp [hz]
  omega

theorem Section4Legality_weaken {s : ℕ} {c : Fin s → Plane₂}
    {lam lam' : ℝ} (hleg : Section4Legality c lam)
    (hlam' : 0 < lam') (hsmall : lam' < lam) : Section4Legality c lam' where
  lam_pos := hlam'
  inj := hleg.inj
  triAngle := by
    intro i j k hij hjk hik
    have h := hleg.triAngle i j k hij hjk hik
    linarith

/-- Exact finite actual inflation. The final parameter remains above the
caller-specified positive threshold and strictly below the original one.
The configuration has exactly the original potential's many distinct
points by its Fin indexing and Section4Legality injectivity.

The conclusion does not additionally assert score zero at the final
parameter; the terminal base may weaken its angle parameter freely. -/
theorem exists_exact_actual_inflation {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam tau : ℝ}
    (hleg : Section4Legality c lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lamFinal : ℝ, tau < lamFinal ∧ lamFinal < lam ∧
      ∃ cFinal : Fin (potential lam (directionRows o e c)) → Plane₂,
        Section4Legality cFinal lamFinal := by
  have aux : ∀ d : ℕ, ∀ {t : ℕ} (ht : 3 ≤ t) (p : Fin t → Plane₂)
      {scale threshold : ℝ}, Section4Legality p scale →
      0 < threshold → threshold < scale →
      potential scale (directionRows o e p) - t = d →
      ∃ scaleFinal : ℝ, threshold < scaleFinal ∧ scaleFinal < scale ∧
        ∃ pFinal : Fin (potential scale (directionRows o e p)) → Plane₂,
          Section4Legality pFinal scaleFinal := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro t ht p scale threshold hp hthreshold0 hthreshold hmeasure
      let F := potential scale (directionRows o e p)
      have hge : t ≤ F := card_le_potential scale (directionRows o e p)
      by_cases hterminal : F = t
      · let scaleFinal := (threshold + scale) / 2
        have htFinal : threshold < scaleFinal := by dsimp [scaleFinal]; linarith
        have hFinalSmall : scaleFinal < scale := by dsimp [scaleFinal]; linarith
        have hFinal0 : 0 < scaleFinal := hthreshold0.trans htFinal
        have hweak := Section4Legality_weaken hp hFinal0 hFinalSmall
        refine ⟨scaleFinal, htFinal, hFinalSmall, p ∘ finCongr hterminal, ?_⟩
        exact hweak.reindex (finCongr hterminal)
      · have hsurplus : t < potential scale (directionRows o e p) := by
          dsimp [F] at hge hterminal
          omega
        obtain ⟨v, hv⟩ := exists_positive_score_of_card_lt_potential scale
          (directionRows o e p) hsurplus
        obtain ⟨scale', hthreshold', hscale', p', hp', hpotential⟩ :=
          SingleSplitScorePreservation.exists_single_positive_split_preserving_potential
            o e he ht p hp v hv hthreshold0 hthreshold
        have hsmaller : potential scale' (directionRows o e p') - (t + 1) < d := by
          omega
        obtain ⟨scaleFinal, htFinal, hFinalSmall, pFinal, hFinal⟩ :=
          ih (potential scale' (directionRows o e p') - (t + 1)) hsmaller
            (by omega : 3 ≤ t + 1) p' hp' hthreshold0 hthreshold' rfl
        refine ⟨scaleFinal, htFinal, hFinalSmall.trans hscale',
          pFinal ∘ finCongr hpotential.symm, ?_⟩
        exact hFinal.reindex (finCongr hpotential.symm)
  exact aux (potential lam (directionRows o e c) - s) hs c hleg htau0 htau rfl

#print axioms card_le_potential
#print axioms exists_positive_score_of_card_lt_potential
#print axioms Section4Legality_weaken
#print axioms exists_exact_actual_inflation

end Jsp404.ActualPotentialInflation
