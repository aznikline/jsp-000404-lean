import Jsp000404.ActualSingleSplitScoreTable
import Jsp000404.ActualPotentialInflation

/-! Selective actual inflation with arbitrary protected rows.
Only positive rows outside the protected injection are split. The protected
actual points and scores, and the original potential, survive every split.
Every final unprotected row has score zero, and no final tail is discarded.
-/

open scoped EuclideanGeometry BigOperators

namespace Jsp404.ActualProtectedInflation

noncomputable def protectedRows {s p : ℕ} (σ : Fin p → Fin s) : Finset (Fin s) :=
  Finset.univ.image σ

noncomputable def unprotectedRows {s p : ℕ} (σ : Fin p → Fin s) : Finset (Fin s) :=
  (protectedRows σ)ᶜ

noncomputable def protectedMass {s p : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (σ : Fin p → Fin s) : ℕ := ∑ j : Fin p, 2 ^ rowScore lam (row (σ j))

noncomputable def tailMass {s p : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (σ : Fin p → Fin s) : ℕ := ∑ i ∈ unprotectedRows σ, 2 ^ rowScore lam (row i)

noncomputable def tailSurplus {s p : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (σ : Fin p → Fin s) : ℕ :=
  ∑ i ∈ unprotectedRows σ, (2 ^ rowScore lam (row i) - 1)

/-- Required number of final points: protected rows plus all original tail mass. -/
noncomputable def inflatedCard {s p : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (σ : Fin p → Fin s) : ℕ := p + (potential lam row - protectedMass lam row σ)

@[simp] theorem mem_unprotectedRows {s p : ℕ} (σ : Fin p → Fin s) (i : Fin s) :
    i ∈ unprotectedRows σ ↔ ¬ ∃ j : Fin p, σ j = i := by
  classical
  simp [unprotectedRows, protectedRows]

theorem mass_partition {s p : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (σ : Fin p → Fin s) (hσ : Function.Injective σ) :
    protectedMass lam row σ + tailMass lam row σ = potential lam row := by
  classical
  have hprot : (∑ i ∈ protectedRows σ, 2 ^ rowScore lam (row i)) =
      protectedMass lam row σ := by
    unfold protectedRows protectedMass
    exact Finset.sum_image hσ.injOn
  rw [← hprot]
  exact Finset.sum_add_sum_compl (protectedRows σ) (fun i => 2 ^ rowScore lam (row i))

/-- Natural subtraction removes exactly the protected mass, without losing tails. -/
theorem inflatedCard_eq_protected_add_tail_mass {s p : ℕ} (lam : ℝ)
    (row : Fin s → List ℝ) (σ : Fin p → Fin s) (hσ : Function.Injective σ) :
    inflatedCard lam row σ = p + tailMass lam row σ := by
  have hmass := mass_partition lam row σ hσ
  unfold inflatedCard
  omega

theorem protected_card_add_tail_card {s p : ℕ}
    (σ : Fin p → Fin s) (hσ : Function.Injective σ) :
    p + (unprotectedRows σ).card = s := by
  classical
  have hp : (protectedRows σ).card = p := by
    simpa [protectedRows] using Finset.card_image_of_injective Finset.univ hσ
  simpa only [unprotectedRows, hp, Fintype.card_fin] using
    Finset.card_add_card_compl (protectedRows σ)

theorem tail_mass_eq_surplus_add_card {s p : ℕ} (lam : ℝ)
    (row : Fin s → List ℝ) (σ : Fin p → Fin s) :
    tailMass lam row σ = tailSurplus lam row σ + (unprotectedRows σ).card := by
  classical
  calc
    tailMass lam row σ = ∑ i ∈ unprotectedRows σ,
        ((2 ^ rowScore lam (row i) - 1) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Nat.sub_add_cancel (Nat.one_le_pow _ 2 (by decide))).symm
    _ = tailSurplus lam row σ + (unprotectedRows σ).card := by
      rw [Finset.sum_add_distrib]
      simp [tailSurplus]

/-- The decreasing measure counts exactly the unprotected excess mass. -/
theorem inflatedCard_eq_card_add_surplus {s p : ℕ} (lam : ℝ)
    (row : Fin s → List ℝ) (σ : Fin p → Fin s) (hσ : Function.Injective σ) :
    inflatedCard lam row σ = s + tailSurplus lam row σ := by
  have hmass := mass_partition lam row σ hσ
  have hcard := protected_card_add_tail_card σ hσ
  have htail := tail_mass_eq_surplus_add_card lam row σ
  unfold inflatedCard
  omega

theorem card_le_inflatedCard {s p : ℕ} (lam : ℝ)
    (row : Fin s → List ℝ) (σ : Fin p → Fin s) (hσ : Function.Injective σ) :
    s ≤ inflatedCard lam row σ := by
  rw [inflatedCard_eq_card_add_surplus lam row σ hσ]
  omega

/-- Empty protection retains all original potential as the final point count. -/
theorem inflatedCard_empty {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (σ : Fin 0 → Fin s) : inflatedCard lam row σ = potential lam row := by
  simp [inflatedCard, protectedMass]

/-- If all rows are protected, the final domain retains exactly the old size. -/
theorem inflatedCard_all_protected {s : ℕ} (lam : ℝ) (row : Fin s → List ℝ)
    (σ : Fin s → Fin s) (hσ : Function.Injective σ) :
    inflatedCard lam row σ = s := by
  have hcard := protected_card_add_tail_card σ hσ
  have hz : (unprotectedRows σ).card = 0 := by omega
  have hempty : unprotectedRows σ = ∅ := Finset.card_eq_zero.mp hz
  rw [inflatedCard_eq_card_add_surplus lam row σ hσ]
  simp [tailSurplus, hempty]

/-- Terminal point count forces every unprotected actual score to vanish. -/
theorem tail_zero_of_inflatedCard_eq_card {s p : ℕ} (lam : ℝ)
    (row : Fin s → List ℝ) (σ : Fin p → Fin s) (hσ : Function.Injective σ)
    (hterminal : inflatedCard lam row σ = s) :
    ∀ i : Fin s, (¬ ∃ j : Fin p, σ j = i) → rowScore lam (row i) = 0 := by
  classical
  have heq := inflatedCard_eq_card_add_surplus lam row σ hσ
  have hzero : tailSurplus lam row σ = 0 := by omega
  intro i hi
  have hmem : i ∈ unprotectedRows σ := (mem_unprotectedRows σ i).mpr hi
  have hz : 2 ^ rowScore lam (row i) - 1 = 0 :=
    (Finset.sum_eq_zero_iff.mp hzero) i hmem
  by_contra hne
  have hlt := Nat.one_lt_pow hne (by decide : 1 < (2 : ℕ))
  omega

/-- Strict surplus supplies a positive row outside the given injection. -/
theorem exists_unprotected_positive_of_card_lt {s p : ℕ} (lam : ℝ)
    (row : Fin s → List ℝ) (σ : Fin p → Fin s) (hσ : Function.Injective σ)
    (hstrict : s < inflatedCard lam row σ) :
    ∃ i : Fin s, (¬ ∃ j : Fin p, σ j = i) ∧ 0 < rowScore lam (row i) := by
  classical
  by_contra hnone
  have hzero : tailSurplus lam row σ = 0 := by
    apply Finset.sum_eq_zero_iff.mpr
    intro i hi
    have hnot : ¬0 < rowScore lam (row i) := fun hpos =>
      hnone ⟨i, (mem_unprotectedRows σ i).mp hi, hpos⟩
    have hz : rowScore lam (row i) = 0 := by omega
    simp [hz]
  rw [inflatedCard_eq_card_add_surplus lam row σ hσ, hzero, add_zero] at hstrict
  omega

/-- The finite actual gap list gives a strictly smaller scale preserving
all old scores, including positive protected scores in the terminal case. -/
theorem exists_smaller_scale_preserving_actual_scores {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (hs : 3 ≤ s)
    (c : Fin s → Plane₂) {lam tau : ℝ} (hlam : 0 < lam)
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ i : Fin s, rowScore lam' (directionRow o e c i) =
        rowScore lam (directionRow o e c i) := by
  classical
  let gs := (List.ofFn fun i : Fin s => cycGaps (directionRow o e c i)).flatten
  have hnonneg : ∀ g ∈ gs, 0 ≤ g := by
    intro g hg
    obtain ⟨l, hl, hgl⟩ := List.mem_flatten.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    apply cycGaps_nonneg (directionRow_sorted o e c i)
      (fun x hx => directionRow_mem_Ico o e c hx) ?_ g hgl
    intro hnil
    have hlen := directionRow_length o e c i
    rw [hnil] at hlen
    simp at hlen
    omega
  obtain ⟨lam', hlow, hsmall, hfloor⟩ :=
    GapSplitFloorStability.exists_floor_stable_scale gs hlam hnonneg htau0 htau
  refine ⟨lam', hlow, hsmall, ?_⟩
  intro i
  change ((cycGaps (directionRow o e c i)).map (gapScore lam')).sum =
    ((cycGaps (directionRow o e c i)).map (gapScore lam)).sum
  congr 1
  apply List.map_congr_left
  intro g hg
  have hmem : g ∈ gs := List.mem_flatten.mpr
    ⟨cycGaps (directionRow o e c i), List.mem_ofFn.mpr ⟨i, rfl⟩, hg⟩
  unfold gapScore
  rw [hfloor g hmem]

/-- Exact selective actual inflation. Protected original points and their
scores survive under an explicitly returned injection. All final rows
outside that injection have score zero, and the original full potential is
retained. The exact finite domain includes every tail point. -/
theorem exists_exact_protected_actual_inflation {s p : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) (σ : Fin p → Fin s)
    (hσ : Function.Injective σ) {lam tau : ℝ}
    (hleg : Section4Legality c lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lamFinal : ℝ, tau < lamFinal ∧ lamFinal < lam ∧
      ∃ cFinal : Fin (p + (potential lam (directionRows o e c) -
          protectedMass lam (directionRows o e c) σ)) → Plane₂,
        Section4Legality cFinal lamFinal ∧
        ∃ σFinal : Fin p → Fin (p + (potential lam (directionRows o e c) -
            protectedMass lam (directionRows o e c) σ)),
          Function.Injective σFinal ∧
          (∀ j : Fin p, cFinal (σFinal j) = c (σ j)) ∧
          (∀ j : Fin p, rowScore lamFinal (directionRow o e cFinal (σFinal j)) =
            rowScore lam (directionRow o e c (σ j))) ∧
          (∀ r, (¬ ∃ j : Fin p, σFinal j = r) →
            rowScore lamFinal (directionRow o e cFinal r) = 0) ∧
          potential lamFinal (directionRows o e cFinal) =
            potential lam (directionRows o e c) := by
  classical
  have aux : ∀ d : ℕ, ∀ {t : ℕ} (ht : 3 ≤ t) (a : Fin t → Plane₂)
      (ι : Fin p → Fin t), Function.Injective ι →
      ∀ {scale threshold : ℝ}, Section4Legality a scale →
      0 < threshold → threshold < scale →
      inflatedCard scale (directionRows o e a) ι - t = d →
      ∃ scaleFinal : ℝ, threshold < scaleFinal ∧ scaleFinal < scale ∧
        ∃ aFinal : Fin (inflatedCard scale (directionRows o e a) ι) → Plane₂,
          Section4Legality aFinal scaleFinal ∧
          ∃ ιFinal : Fin p → Fin (inflatedCard scale (directionRows o e a) ι),
            Function.Injective ιFinal ∧
            (∀ j, aFinal (ιFinal j) = a (ι j)) ∧
            (∀ j, rowScore scaleFinal (directionRow o e aFinal (ιFinal j)) =
              rowScore scale (directionRow o e a (ι j))) ∧
            (∀ r, (¬ ∃ j, ιFinal j = r) →
              rowScore scaleFinal (directionRow o e aFinal r) = 0) ∧
            potential scaleFinal (directionRows o e aFinal) =
              potential scale (directionRows o e a) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro t ht a ι hι scale threshold ha hthreshold0 hthreshold hmeasure
      let T := inflatedCard scale (directionRows o e a) ι
      have hge : t ≤ T := card_le_inflatedCard scale _ ι hι
      by_cases hterminal : T = t
      · have hflat := tail_zero_of_inflatedCard_eq_card scale
          (directionRows o e a) ι hι hterminal
        obtain ⟨scaleFinal, hlow, hsmall, hscores⟩ :=
          exists_smaller_scale_preserving_actual_scores o e ht a ha.lam_pos
            hthreshold0 hthreshold
        have hlegal := ActualPotentialInflation.Section4Legality_weaken
          ha (hthreshold0.trans hlow) hsmall
        let E : Fin T ≃ Fin t := finCongr hterminal
        let ιFinal : Fin p → Fin T := E.symm ∘ ι
        refine ⟨scaleFinal, hlow, hsmall, a ∘ E, hlegal.reindex E,
          ιFinal, E.symm.injective.comp hι, ?_, ?_, ?_, ?_⟩
        · intro j
          simp [ιFinal]
        · intro j
          rw [directionRow_reindex o e a E]
          simpa [ιFinal] using hscores (ι j)
        · intro r hr
          rw [directionRow_reindex o e a E r, hscores (E r)]
          apply hflat (E r)
          rintro ⟨j, hj⟩
          apply hr
          refine ⟨j, ?_⟩
          simpa [ιFinal] using congrArg E.symm hj
        · rw [potential_directionRows_reindex o e a E]
          unfold potential exponentAt directionRows
          apply Finset.sum_congr rfl
          intro i _
          rw [hscores i]
      · have hstrict : t < inflatedCard scale (directionRows o e a) ι := by
          dsimp [T] at hge hterminal
          omega
        obtain ⟨v, hvoutside, hvpos⟩ :=
          exists_unprotected_positive_of_card_lt scale (directionRows o e a) ι hι hstrict
        obtain ⟨u, _hu, scale', hlow, hsmall, eps, _heps, hlegal', htable, hpotential⟩ :=
          ActualSingleSplitScoreTable.exists_single_positive_split_score_table
            o e he ht a ha v hvpos hthreshold0 hthreshold
        let a' := ActualSingleSplitScoreTable.points v a u eps
        let ι' : Fin p → Fin (t + 1) := ActualSingleSplitScoreTable.originalIndex v ∘ ι
        have hι' : Function.Injective ι' :=
          (ActualSingleSplitScoreTable.originalIndex_injective v).comp hι
        have hpoints (j : Fin p) : a' (ι' j) = a (ι j) := by
          exact ActualSingleSplitScoreTable.points_originalIndex v (ι j) a u eps
        have hscores (j : Fin p) :
            rowScore scale' (directionRow o e a' (ι' j)) =
              rowScore scale (directionRow o e a (ι j)) := by
          apply ActualSingleSplitScoreTable.original_score_of_table o e v a u eps
            scale scale' htable (ι j)
          intro h
          exact hvoutside ⟨j, h⟩
        have hprotected : protectedMass scale' (directionRows o e a') ι' =
            protectedMass scale (directionRows o e a) ι := by
          unfold protectedMass directionRows
          apply Finset.sum_congr rfl
          intro j _
          rw [hscores j]
        have hT : inflatedCard scale' (directionRows o e a') ι' =
            inflatedCard scale (directionRows o e a) ι := by
          unfold inflatedCard
          rw [hpotential, hprotected]
        have hsmaller : inflatedCard scale' (directionRows o e a') ι' - (t + 1) < d := by
          rw [hT]
          omega
        obtain ⟨scaleFinal, hfinalLow, hfinalSmall, aFinal, hfinalLegal,
            ιFinal, hfinalInj, hfinalPoints, hfinalScores, hfinalTail, hfinalPotential⟩ :=
          ih (inflatedCard scale' (directionRows o e a') ι' - (t + 1)) hsmaller
            (by omega : 3 ≤ t + 1) a' ι' hι' hlegal' hthreshold0 hlow rfl
        let E := finCongr hT.symm
        let ιLast := E.symm ∘ ιFinal
        refine ⟨scaleFinal, hfinalLow, hfinalSmall.trans hsmall,
          aFinal ∘ E, hfinalLegal.reindex E, ιLast,
          E.symm.injective.comp hfinalInj, ?_, ?_, ?_, ?_⟩
        · intro j
          have h := (hfinalPoints j).trans (hpoints j)
          simpa [ιLast] using h
        · intro j
          rw [directionRow_reindex o e aFinal E]
          have h := (hfinalScores j).trans (hscores j)
          simpa [ιLast] using h
        · intro r hr
          rw [directionRow_reindex o e aFinal E r]
          apply hfinalTail (E r)
          rintro ⟨j, hj⟩
          apply hr
          refine ⟨j, ?_⟩
          simpa [ιLast] using congrArg E.symm hj
        · rw [potential_directionRows_reindex o e aFinal E]
          exact hfinalPotential.trans hpotential
  exact aux (inflatedCard lam (directionRows o e c) σ - s)
    hs c σ hσ hleg htau0 htau rfl

#print axioms mem_unprotectedRows
#print axioms mass_partition
#print axioms inflatedCard_eq_protected_add_tail_mass
#print axioms protected_card_add_tail_card
#print axioms tail_mass_eq_surplus_add_card
#print axioms inflatedCard_eq_card_add_surplus
#print axioms card_le_inflatedCard
#print axioms inflatedCard_empty
#print axioms inflatedCard_all_protected
#print axioms tail_zero_of_inflatedCard_eq_card
#print axioms exists_unprotected_positive_of_card_lt
#print axioms exists_smaller_scale_preserving_actual_scores
#print axioms exists_exact_protected_actual_inflation

end Jsp404.ActualProtectedInflation
