import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2RowDataReplaySoundness

set_option autoImplicit false
set_option pp.fullNames true

/-! Actual complete-row semantics for the outer-left replay.

Only row 1 is a low row and only rows 2 through 6 are tail rows. Row 0
has no prescribed defect. Literal row orders are independently checked
against the actual word; no checker result is added to GenericModel.
This new module is SOURCE_ONLY until separately verified.
-/

namespace Jsp404.N4R2OuterLeftReplaySoundness

open SatScalarModel N4R2ModelWordSoundness N4R2CriticalReifiedRow
open N4R2CriticalCycleSoundness N4R2SharedCycleChecker

/-- The literal checker retains every actual off-center chord and derives
the actual sorted order. This has no defect-profile premise. -/
theorem checked_rows_perm_sorted (M : GenericModel 7 4) (w : N4R2OuterLeftReplay.Word)
    (hword : WordSound M w) (ord : N4R2OuterLeftReplay.RowsData)
    (hcheck : N4R2OuterLeftReplay.rowsCheck w ord = true) (i : Fin 7) :
    (List.ofFn (ord i)).Perm ((List.finRange 7).erase i) ∧
      ((List.ofFn (ord i)).map (M.d i)).Pairwise (· ≤ ·) :=
  N4R2RowDataReplaySoundness.checked_rows_perm_sorted M w hword ord hcheck i

theorem checked_fullGaps_eq_modelGap (M : GenericModel 7 4)
    (w : N4R2OuterLeftReplay.Word) (hword : WordSound M w)
    (ord : N4R2OuterLeftReplay.RowsData)
    (hcheck : N4R2OuterLeftReplay.rowsCheck w ord = true) (i : Fin 7) :
    fullGaps M i (ord i) = modelGap M i :=
  N4R2RowDataReplaySoundness.checked_fullGaps_eq_modelGap M w hword ord hcheck i

/-- Arbitrary actual-row lower bounds, including zero, interpret the
new literal-row arc without assigning an old endpoint low-row role. -/
theorem lowerArcWithRows_sound (M : GenericModel 7 4) (w : N4R2OuterLeftReplay.Word)
    (hword : WordSound M w) (ord : N4R2OuterLeftReplay.RowsData)
    (hcheck : N4R2OuterLeftReplay.rowsCheck w ord = true)
    (i k : Fin 7) (lower : ℕ) (hlower : (lower : ℝ) ≤ modelGap M i k) :
    N4R2ReifiedArcDecoder.Holds M (N4R2ThinReplaySoundness.toArc
      (N4R2RowDataReplay.lowerArcWithRows ord i k lower)) := by
  have hrows := N4R2RowDataReplaySoundness.checked_rows_eq_actual M w hword ord hcheck
  subst ord
  change N4R2ReifiedArcDecoder.Holds M
    (N4R2ThinReplaySoundness.toArc (N4R2ThinReplay.lowerArc w i k lower))
  rw [N4R2ThinReplaySoundness.lowerArc_eq]
  exact N4R2ReifiedArcDecoder.lowerArc_sound M w hword i k lower hlower

/-- The complete actual tail row supplies the strict upper gap bound.
The tail index is supplied by the new decoder's `1 < i.val` test. -/
theorem upperArcWithRows_sound (M : GenericModel 7 4) (w : N4R2OuterLeftReplay.Word)
    (hword : WordSound M w) (ord : N4R2OuterLeftReplay.RowsData)
    (hcheck : N4R2OuterLeftReplay.rowsCheck w ord = true)
    (i k : Fin 7) (hdef : SatScalarModel.rowDefect M i = 4) :
    N4R2ReifiedArcDecoder.Holds M (N4R2ThinReplaySoundness.toArc
      (N4R2RowDataReplay.upperArcWithRows ord i k)) := by
  have hrows := N4R2RowDataReplaySoundness.checked_rows_eq_actual M w hword ord hcheck
  subst ord
  change N4R2ReifiedArcDecoder.Holds M
    (N4R2ThinReplaySoundness.toArc (N4R2ThinReplay.upperArc w i k))
  rw [N4R2ThinReplaySoundness.upperArc_eq]
  exact N4R2ReifiedArcDecoder.upperArc_sound M w hword i k hdef

theorem lowLowerValue_sound (M : GenericModel 7 4) (p : Option (Fin 28))
    (hprofile : ∀ q, p = some q → N4R2ReifiedArcDecoder.ProfileHolds M 1 q)
    (i k : Fin 7) :
    (N4R2OuterLeftReplay.lowLowerValue p i k : ℝ) ≤ modelGap M i k := by
  by_cases hi : i.val = 1
  · have hi1 : i = (1 : Fin 7) := Fin.ext hi
    subst i
    cases hp : p with
    | none =>
        simpa [N4R2OuterLeftReplay.lowLowerValue, hp] using modelGap_nonneg M 1 k
    | some q =>
        simpa [N4R2OuterLeftReplay.lowLowerValue, hp,
          N4R2OuterLeftReplay.profileLower, N4R2ThinReplaySoundness.profileLower_eq]
          using hprofile q hp k
  · simpa [N4R2OuterLeftReplay.lowLowerValue, hi] using modelGap_nonneg M i k

/-- Every new decoded edge is interpreted at its actual original center.
Row 1 alone uses the chosen necessary profile; rows 2..6 alone use the
zero-score upper bound. The remaining row uses no defect information. -/
theorem decode_sound (M : GenericModel 7 4) (w : N4R2OuterLeftReplay.Word)
    (hword : WordSound M w) (ord : N4R2OuterLeftReplay.RowsData)
    (hrows : N4R2OuterLeftReplay.rowsCheck w ord = true) (p : Option (Fin 28))
    (hprofile : ∀ q, p = some q → N4R2ReifiedArcDecoder.ProfileHolds M 1 q)
    (htails : ∀ i : Fin 7, 1 < i.val → SatScalarModel.rowDefect M i = 4)
    (origin : N4R2OuterLeftReplay.Origin) (a : N4R2OuterLeftReplay.ReifiedArc)
    (hdecode : N4R2OuterLeftReplay.decodeWithRows w ord p origin = some a) :
    N4R2ReifiedArcDecoder.Holds M (N4R2ThinReplaySoundness.toArc a) := by
  cases origin with
  | thetaLower i =>
      simp only [N4R2OuterLeftReplay.decodeWithRows, N4R2ThinReplay.decode,
        Option.some.injEq] at hdecode
      subst a
      simp only [N4R2ReifiedArcDecoder.Holds, N4R2ThinReplaySoundness.toArc,
        N4R2ThinReplaySoundness.toVertex, edgeHolds, value, Bool.false_eq_true,
        ↓reduceIte, Int.cast_zero, zero_add, zero_mul]
      linarith [(M.theta_bounds i).1]
  | thetaUpper i =>
      simp only [N4R2OuterLeftReplay.decodeWithRows, N4R2ThinReplay.decode,
        Option.some.injEq] at hdecode
      subst a
      simp only [N4R2ReifiedArcDecoder.Holds, N4R2ThinReplaySoundness.toArc,
        N4R2ThinReplaySoundness.toVertex, edgeHolds, value, Bool.false_eq_true,
        ↓reduceIte, Int.cast_zero, Int.cast_one, zero_add, one_mul]
      simpa only [sub_zero] using (M.theta_bounds i).2
  | thetaNext i =>
      simp only [N4R2OuterLeftReplay.decodeWithRows, N4R2ThinReplay.decode,
        Option.some.injEq] at hdecode
      subst a
      simp only [N4R2ReifiedArcDecoder.Holds, N4R2ThinReplaySoundness.toArc,
        N4R2ThinReplaySoundness.toVertex, edgeHolds, value, ↓reduceIte,
        Int.cast_zero, zero_mul, zero_add]
      have ht := M.htheta (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
      linarith
  | corridorLower i j =>
      simp only [N4R2OuterLeftReplay.decodeWithRows, N4R2ThinReplay.decode] at hdecode
      split at hdecode
      · rename_i hij
        cases hdecode
        have hc := (M.corridor i j hij).1
        norm_num [N4R2ReifiedArcDecoder.Holds, N4R2ThinReplaySoundness.toArc,
          N4R2ThinReplaySoundness.toVertex, edgeHolds, value]
        linarith
      · cases hdecode
  | corridorUpper i j =>
      simp only [N4R2OuterLeftReplay.decodeWithRows, N4R2ThinReplay.decode] at hdecode
      split at hdecode
      · rename_i hij
        cases hdecode
        have hc := (M.corridor i j hij).2
        norm_num at hc
        norm_num [N4R2ReifiedArcDecoder.Holds, N4R2ThinReplaySoundness.toArc,
          N4R2ThinReplaySoundness.toVertex, edgeHolds, value]
        linarith
      · cases hdecode
  | triangle t part =>
      simp only [N4R2OuterLeftReplay.decodeWithRows, N4R2ThinReplay.decode,
        Option.some.injEq] at hdecode
      subst a
      rw [N4R2ThinReplaySoundness.triangleArc_eq]
      exact N4R2ReifiedArcDecoder.triangleArc_sound M w hword t part
  | gapLower i k =>
      simp only [N4R2OuterLeftReplay.decodeWithRows, Option.some.injEq] at hdecode
      subst a
      exact lowerArcWithRows_sound M w hword ord hrows i k _
        (lowLowerValue_sound M p hprofile i k)
  | gapUpper i k =>
      simp only [N4R2OuterLeftReplay.decodeWithRows] at hdecode
      split at hdecode
      · rename_i hi
        cases hdecode
        exact upperArcWithRows_sound M w hword ord hrows i k (htails i hi)
      · cases hdecode

theorem cycleCheck_sound (C : N4R2OuterLeftReplay.Cycle) (M : GenericModel 7 4)
    (w : N4R2OuterLeftReplay.Word) (hword : WordSound M w)
    (ord : N4R2OuterLeftReplay.RowsData)
    (hrows : N4R2OuterLeftReplay.rowsCheck w ord = true) (p : Option (Fin 28))
    (hprofile : ∀ q, p = some q → N4R2ReifiedArcDecoder.ProfileHolds M 1 q)
    (htails : ∀ i : Fin 7, 1 < i.val → SatScalarModel.rowDefect M i = 4)
    (hcheck : N4R2OuterLeftReplay.cycleCheck C w ord p = true) : False := by
  have hh : N4R2OuterLeftReplay.cycleMatches C w ord p = true ∧
      N4R2ThinReplay.accepts C.data = true := by
    simpa only [N4R2OuterLeftReplay.cycleCheck, Bool.and_eq_true] using hcheck
  have hmatches : ∀ j : Fin C.length,
      N4R2OuterLeftReplay.decodeWithRows w ord p (C.origin j) = some (C.arc j) :=
    of_decide_eq_true hh.1
  apply actual_model_checked_cycle M (N4R2ThinReplaySoundness.toCertificate C.data)
  · rw [N4R2ThinReplaySoundness.accepts_eq]
    exact hh.2
  · intro j
    have h := decode_sound M w hword ord hrows p hprofile htails
      (C.origin j) (C.arc j) (hmatches j)
    simpa only [N4R2ReifiedArcDecoder.Holds, N4R2ThinReplaySoundness.toArc,
      N4R2ThinReplaySoundness.toCertificate, N4R2ThinReplay.Cycle.arc] using h

theorem libraryCheck_sound (library : N4R2OuterLeftReplay.Library) (M : GenericModel 7 4)
    (w : N4R2OuterLeftReplay.Word) (hword : WordSound M w)
    (ord : N4R2OuterLeftReplay.RowsData)
    (hrows : N4R2OuterLeftReplay.rowsCheck w ord = true) (p : Option (Fin 28))
    (hprofile : ∀ q, p = some q → N4R2ReifiedArcDecoder.ProfileHolds M 1 q)
    (htails : ∀ i : Fin 7, 1 < i.val → SatScalarModel.rowDefect M i = 4)
    (id : ℕ) (hcheck : N4R2OuterLeftReplay.libraryCheck library w ord p id = true) : False := by
  cases hlookup : library id with
  | none =>
      simp only [N4R2OuterLeftReplay.libraryCheck, hlookup, Bool.false_eq_true] at hcheck
  | some C =>
      exact cycleCheck_sound C M w hword ord hrows p hprofile htails
        (by simpa only [N4R2OuterLeftReplay.libraryCheck, hlookup] using hcheck)

/-- The chosen profile is obtained from the original complete low row.
Literal-row and cycle checks are validated finite certificate inputs,
not new assumptions or fields about an actual GenericModel. -/
theorem leafCheck_sound (library : N4R2OuterLeftReplay.Library) (M : GenericModel 7 4)
    (w : N4R2OuterLeftReplay.Word) (hword : WordSound M w)
    (hdef1 : SatScalarModel.rowDefect M 1 = 2)
    (htails : ∀ i : Fin 7, 1 < i.val → SatScalarModel.rowDefect M i = 4)
    (data : N4R2OuterLeftReplay.LeafData)
    (hcheck : N4R2OuterLeftReplay.leafCheck library w data = true) : False := by
  have hh : N4R2OuterLeftReplay.rowsCheck w data.rows = true ∧
      N4R2OuterLeftReplay.leafCases library w data.rows data.proof = true := by
    simpa only [N4R2OuterLeftReplay.leafCheck, Bool.and_eq_true] using hcheck
  cases hproof : data.proof with
  | tail id =>
      have hc : N4R2OuterLeftReplay.libraryCheck library w data.rows none id = true := by
        simpa only [hproof, N4R2OuterLeftReplay.leafCases] using hh.2
      exact libraryCheck_sound library M w hword data.rows hh.1 none
        (N4R2SharedLeafChecker.noProfileHolds M 1) htails id hc
  | low cycles =>
      obtain ⟨p, hp⟩ := N4R2ReifiedArcDecoder.exists_low_profile M 1 hdef1
      have hall : ∀ q : Fin 28,
          N4R2OuterLeftReplay.libraryCheck library w data.rows (some q) (cycles q) = true :=
        of_decide_eq_true (by simpa only [hproof, N4R2OuterLeftReplay.leafCases] using hh.2)
      exact libraryCheck_sound library M w hword data.rows hh.1 (some p)
        (N4R2SharedLeafChecker.someProfileHolds M 1 p hp) htails (cycles p) (hall p)

#print axioms checked_rows_perm_sorted
#print axioms checked_fullGaps_eq_modelGap
#print axioms lowerArcWithRows_sound
#print axioms upperArcWithRows_sound
#print axioms lowLowerValue_sound
#print axioms decode_sound
#print axioms cycleCheck_sound
#print axioms libraryCheck_sound
#print axioms leafCheck_sound

end Jsp404.N4R2OuterLeftReplaySoundness
