import Jsp000404.ActualProtectedInflation

/-! Actual strip-4 HIGH selective inflation for the protected score profile
(3,2,2). Original critical potential 21 yields eight actual points and five
zero-score tails; potential 22 yields nine actual points and six tails.
All tail scores concern the complete final configuration. No point subset,
initially pure tail, sharp capacity, or bare finite exclusion is assumed.
-/

open scoped EuclideanGeometry BigOperators

namespace Jsp404.R2N4PureTailInflation

set_option maxHeartbeats 2000000

/-- The protected actual anchor and two actual low rows, in fixed order. -/
def protectedTriple {s : ℕ} (a b d : Fin s) : Fin 3 → Fin s := ![a, b, d]

theorem protectedTriple_injective {s : ℕ} {a b d : Fin s}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Function.Injective (protectedTriple a b d) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [protectedTriple, hab, had, hbd, hab.symm, had.symm, hbd.symm] at hij ⊢

theorem protectedMass_322 {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {lam : ℝ} {a b d : Fin s}
    (ha : rowScore lam (directionRow o e c a) = 3)
    (hb : rowScore lam (directionRow o e c b) = 2)
    (hd : rowScore lam (directionRow o e c d) = 2) :
    ActualProtectedInflation.protectedMass lam (directionRows o e c)
      (protectedTriple a b d) = 16 := by
  norm_num [ActualProtectedInflation.protectedMass, directionRows,
    Fin.sum_univ_three, protectedTriple, ha, hb, hd]

/-- Original floor 4 places the legal scale strictly above pi/5. -/
theorem pi_div_five_lt_of_floor_four {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 4) : Real.pi / 5 < lam := by
  have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn] at hfloor
  have hupper : Real.pi / lam < 5 := by norm_num at hfloor ⊢; exact hfloor
  have hpi : Real.pi < 5 * lam := (div_lt_iff₀ hlam).mp hupper
  exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr (by linarith)

/-- Decreasing the scale above pi/5 retains strip 4 and the HIGH half-band. -/
theorem high_n4_band_of_smaller_scale {lam scale : ℝ}
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    (habove : Real.pi / 5 < scale) (hsmall : scale < lam) :
    Nat.floor (Real.pi / scale) = 4 ∧
      (1 / 2 : ℝ) ≤ Real.pi / scale - 4 ∧ Real.pi / scale - 4 < 1 := by
  have hscale : 0 < scale := (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 5)).trans habove
  have hratio : Real.pi / lam ≤ Real.pi / scale :=
    div_le_div_of_nonneg_left Real.pi_pos.le hscale hsmall.le
  have hhigh' : (1 / 2 : ℝ) ≤ Real.pi / scale - 4 := by linarith
  have hpi : Real.pi < 5 * scale := by
    have h := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 5)).mp habove
    linarith
  have hupper : Real.pi / scale < 5 := (div_lt_iff₀ hscale).mpr hpi
  have hn : Nat.floor (Real.pi / scale) = 4 := by
    apply (Nat.floor_eq_iff (div_nonneg Real.pi_pos.le hscale.le)).mpr
    constructor <;> norm_num <;> linarith
  exact ⟨hn, hhigh', by linarith⟩

/-- A genuine actual pure-tail realization for the original protected
profile (3,2,2), with its complete original potential retained. -/
theorem exists_actual_n4_three_protected_pure_tail {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 6 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    {a b d : Fin s} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : rowScore lam (directionRow o e c a) = 3)
    (hb : rowScore lam (directionRow o e c b) = 2)
    (hd : rowScore lam (directionRow o e c d) = 2) :
    ∃ lamFinal : ℝ, Real.pi / 5 < lamFinal ∧ lamFinal < lam ∧
      Nat.floor (Real.pi / lamFinal) = 4 ∧
      (1 / 2 : ℝ) ≤ Real.pi / lamFinal - 4 ∧ Real.pi / lamFinal - 4 < 1 ∧
      ∃ cFinal : Fin (3 + (potential lam (directionRows o e c) - 16)) → Plane₂,
        Section4Legality cFinal lamFinal ∧
        ∃ σFinal : Fin 3 → Fin (3 + (potential lam (directionRows o e c) - 16)),
          Function.Injective σFinal ∧
          (∀ j, cFinal (σFinal j) = c (protectedTriple a b d j)) ∧
          (∀ j, rowScore lamFinal (directionRow o e cFinal (σFinal j)) =
            rowScore lam (directionRow o e c (protectedTriple a b d j))) ∧
          (∀ r, (¬ ∃ j, σFinal j = r) →
            rowScore lamFinal (directionRow o e cFinal r) = 0) ∧
          potential lamFinal (directionRows o e cFinal) =
            potential lam (directionRows o e c) := by
  have hσ := protectedTriple_injective hab had hbd
  have hmass := protectedMass_322 o e c ha hb hd
  have htau0 : (0 : ℝ) < Real.pi / 5 := div_pos Real.pi_pos (by norm_num)
  have htau := pi_div_five_lt_of_floor_four hleg.lam_pos hn
  have hactual := ActualProtectedInflation.exists_exact_protected_actual_inflation
    o e he (by omega : 3 ≤ s) c (protectedTriple a b d) hσ hleg htau0 htau
  rw [hmass] at hactual
  obtain ⟨lamFinal, hlow, hsmall, cFinal, hlegal, σFinal,
    hinj, hpoints, hscores, htail, hpotential⟩ := hactual
  obtain ⟨hnFinal, hhighFinal, hdeltaFinal⟩ :=
    high_n4_band_of_smaller_scale hhigh hlow hsmall
  exact ⟨lamFinal, hlow, hsmall, hnFinal, hhighFinal, hdeltaFinal,
    cFinal, hlegal, σFinal, hinj, hpoints, hscores, htail, hpotential⟩

/-- Original actual potential 21 gives exactly 8 actual points with the
three protected scores 3,2,2 and all 5 remaining rows of score zero. -/
theorem exists_actual_n4_critical21_pure_tail_eight {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 6 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    {a b d : Fin s} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : rowScore lam (directionRow o e c a) = 3)
    (hb : rowScore lam (directionRow o e c b) = 2)
    (hd : rowScore lam (directionRow o e c d) = 2)
    (hF : potential lam (directionRows o e c) = 21) :
    ∃ lamFinal : ℝ, Real.pi / 5 < lamFinal ∧ lamFinal < lam ∧
      Nat.floor (Real.pi / lamFinal) = 4 ∧
      (1 / 2 : ℝ) ≤ Real.pi / lamFinal - 4 ∧ Real.pi / lamFinal - 4 < 1 ∧
      ∃ cFinal : Fin 8 → Plane₂, Section4Legality cFinal lamFinal ∧
        ∃ σFinal : Fin 3 → Fin 8, Function.Injective σFinal ∧
          (∀ j, cFinal (σFinal j) = c (protectedTriple a b d j)) ∧
          rowScore lamFinal (directionRow o e cFinal (σFinal 0)) = 3 ∧
          rowScore lamFinal (directionRow o e cFinal (σFinal 1)) = 2 ∧
          rowScore lamFinal (directionRow o e cFinal (σFinal 2)) = 2 ∧
          (∀ r, (¬ ∃ j, σFinal j = r) →
            rowScore lamFinal (directionRow o e cFinal r) = 0) ∧
          potential lamFinal (directionRows o e cFinal) = 21 := by
  have hactual := exists_actual_n4_three_protected_pure_tail o e he hs c hleg hn hhigh
    hab had hbd ha hb hd
  obtain ⟨lamFinal, hlow, hsmall, hnFinal, hhighFinal, hdeltaFinal,
    cFinal, hlegal, σFinal, hinj, hpoints, hscores, htail, hpotential⟩ := hactual
  have hcard : 3 + (potential lam (directionRows o e c) - 16) = 8 := by omega
  let E : Fin 8 ≃ Fin (3 + (potential lam (directionRows o e c) - 16)) :=
    finCongr hcard.symm
  let cNew := cFinal ∘ E
  let σNew := E.symm ∘ σFinal
  have hnewscore (j : Fin 3) :
      rowScore lamFinal (directionRow o e cNew (σNew j)) =
        rowScore lam (directionRow o e c (protectedTriple a b d j)) := by
    change rowScore lamFinal (directionRow o e (cFinal ∘ E) (E.symm (σFinal j))) = _
    rw [directionRow_reindex, E.apply_symm_apply]
    exact hscores j
  refine ⟨lamFinal, hlow, hsmall, hnFinal, hhighFinal, hdeltaFinal,
    cNew, hlegal.reindex E, σNew, E.symm.injective.comp hinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    change cFinal (E (E.symm (σFinal j))) = _
    simpa using hpoints j
  · simpa [protectedTriple] using (hnewscore 0).trans (by simpa [protectedTriple] using ha)
  · simpa [protectedTriple] using (hnewscore 1).trans (by simpa [protectedTriple] using hb)
  · simpa [protectedTriple] using (hnewscore 2).trans (by simpa [protectedTriple] using hd)
  · intro r hr
    change rowScore lamFinal (directionRow o e (cFinal ∘ E) r) = 0
    rw [directionRow_reindex]
    apply htail (E r)
    rintro ⟨j, hj⟩
    apply hr
    refine ⟨j, ?_⟩
    change E.symm (σFinal j) = r
    rw [hj, E.symm_apply_apply]
  · change potential lamFinal (directionRows o e (cFinal ∘ E)) = 21
    rw [potential_directionRows_reindex]
    exact hpotential.trans hF

/-- Original actual potential 22 gives exactly 9 actual points with the
three protected scores 3,2,2 and all 6 remaining rows of score zero. -/
theorem exists_actual_n4_critical22_pure_tail_nine {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 6 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    {a b d : Fin s} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : rowScore lam (directionRow o e c a) = 3)
    (hb : rowScore lam (directionRow o e c b) = 2)
    (hd : rowScore lam (directionRow o e c d) = 2)
    (hF : potential lam (directionRows o e c) = 22) :
    ∃ lamFinal : ℝ, Real.pi / 5 < lamFinal ∧ lamFinal < lam ∧
      Nat.floor (Real.pi / lamFinal) = 4 ∧
      (1 / 2 : ℝ) ≤ Real.pi / lamFinal - 4 ∧ Real.pi / lamFinal - 4 < 1 ∧
      ∃ cFinal : Fin 9 → Plane₂, Section4Legality cFinal lamFinal ∧
        ∃ σFinal : Fin 3 → Fin 9, Function.Injective σFinal ∧
          (∀ j, cFinal (σFinal j) = c (protectedTriple a b d j)) ∧
          rowScore lamFinal (directionRow o e cFinal (σFinal 0)) = 3 ∧
          rowScore lamFinal (directionRow o e cFinal (σFinal 1)) = 2 ∧
          rowScore lamFinal (directionRow o e cFinal (σFinal 2)) = 2 ∧
          (∀ r, (¬ ∃ j, σFinal j = r) →
            rowScore lamFinal (directionRow o e cFinal r) = 0) ∧
          potential lamFinal (directionRows o e cFinal) = 22 := by
  have hactual := exists_actual_n4_three_protected_pure_tail o e he hs c hleg hn hhigh
    hab had hbd ha hb hd
  obtain ⟨lamFinal, hlow, hsmall, hnFinal, hhighFinal, hdeltaFinal,
    cFinal, hlegal, σFinal, hinj, hpoints, hscores, htail, hpotential⟩ := hactual
  have hcard : 3 + (potential lam (directionRows o e c) - 16) = 9 := by omega
  let E : Fin 9 ≃ Fin (3 + (potential lam (directionRows o e c) - 16)) :=
    finCongr hcard.symm
  let cNew := cFinal ∘ E
  let σNew := E.symm ∘ σFinal
  have hnewscore (j : Fin 3) :
      rowScore lamFinal (directionRow o e cNew (σNew j)) =
        rowScore lam (directionRow o e c (protectedTriple a b d j)) := by
    change rowScore lamFinal (directionRow o e (cFinal ∘ E) (E.symm (σFinal j))) = _
    rw [directionRow_reindex, E.apply_symm_apply]
    exact hscores j
  refine ⟨lamFinal, hlow, hsmall, hnFinal, hhighFinal, hdeltaFinal,
    cNew, hlegal.reindex E, σNew, E.symm.injective.comp hinj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    change cFinal (E (E.symm (σFinal j))) = _
    simpa using hpoints j
  · simpa [protectedTriple] using (hnewscore 0).trans (by simpa [protectedTriple] using ha)
  · simpa [protectedTriple] using (hnewscore 1).trans (by simpa [protectedTriple] using hb)
  · simpa [protectedTriple] using (hnewscore 2).trans (by simpa [protectedTriple] using hd)
  · intro r hr
    change rowScore lamFinal (directionRow o e (cFinal ∘ E) r) = 0
    rw [directionRow_reindex]
    apply htail (E r)
    rintro ⟨j, hj⟩
    apply hr
    refine ⟨j, ?_⟩
    change E.symm (σFinal j) = r
    rw [hj, E.symm_apply_apply]
  · change potential lamFinal (directionRows o e (cFinal ∘ E)) = 22
    rw [potential_directionRows_reindex]
    exact hpotential.trans hF

#print axioms protectedTriple_injective
#print axioms protectedMass_322
#print axioms pi_div_five_lt_of_floor_four
#print axioms high_n4_band_of_smaller_scale
#print axioms exists_actual_n4_three_protected_pure_tail
#print axioms exists_actual_n4_critical21_pure_tail_eight
#print axioms exists_actual_n4_critical22_pure_tail_nine

end Jsp404.R2N4PureTailInflation
