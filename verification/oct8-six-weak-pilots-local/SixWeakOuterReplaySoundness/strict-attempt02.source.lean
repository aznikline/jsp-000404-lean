import Jsp000404.SixWeakOuterReplay
import Jsp000404.SixWeakOuterFloorProfiles
import Jsp000404.SixOuterReplaySoundness

/-! SOURCE_ONLY lower-only A75/B225 actual semantics. Old PASS modules are
reused without editing. Positive/weak-two profiles come from actual complete
rows; only the concrete pilot will establish literal rows internally. -/
set_option autoImplicit false
set_option pp.fullNames true
namespace Jsp404.SixWeakOuterReplaySoundness
open SatScalarModel SixOuterReplay SixOuterReplaySoundness N4R2CriticalCycleSoundness
abbrev LowerBounds := SixWeakOuterReplay.LowerBounds

/-- No upper-gap premise is accepted or needed by this lower-only decoder. -/
theorem decode_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData) (lower : LowerBounds)
    (hlower : ∀ i k, (lower i k : ℝ) ≤ Gaps M i (ord i) k)
    (origin : Origin) (a : ReifiedArc)
    (hdecode : SixWeakOuterReplay.decode w ord lower origin = some a) : Holds M a := by
  cases origin with
  | thetaLower i =>
    simp only [SixWeakOuterReplay.decode, SixOuterReplay.decode, Option.some.injEq] at hdecode
    subst a
    have ht := (M.theta_bounds i).1
    simp only [Holds, edgeHolds, Bool.false_eq_true, ↓reduceIte, value,
      Int.cast_zero, zero_mul, add_zero]
    linarith
  | thetaUpper i =>
    simp only [SixWeakOuterReplay.decode, SixOuterReplay.decode, Option.some.injEq] at hdecode
    subst a
    have ht := (M.theta_bounds i).2
    simpa [Holds, edgeHolds, value] using ht
  | thetaOrder i =>
    simp only [SixWeakOuterReplay.decode, SixOuterReplay.decode, Option.some.injEq] at hdecode
    subst a
    have ht := M.htheta i.castSucc_lt_succ
    simpa [Holds, edgeHolds, value] using ht
  | corridorLower i j =>
    by_cases hij : i < j
    · simp only [SixWeakOuterReplay.decode, SixOuterReplay.decode, hij, ↓reduceIte, Option.some.injEq] at hdecode
      subst a
      have hc := (M.corridor i j hij).1
      simp only [Holds, edgeHolds, Bool.false_eq_true, ↓reduceIte, value,
        Int.cast_neg, Int.cast_one, Int.cast_zero, zero_mul, add_zero]
      linarith
    · simp [SixWeakOuterReplay.decode, SixOuterReplay.decode, hij] at hdecode
  | corridorUpper i j =>
    by_cases hij : i < j
    · simp only [SixWeakOuterReplay.decode, SixOuterReplay.decode, hij, ↓reduceIte, Option.some.injEq] at hdecode
      subst a
      have hc := (M.corridor i j hij).2
      simp only [Holds, edgeHolds, Bool.false_eq_true, ↓reduceIte, value,
        Int.cast_ofNat, Int.cast_one, one_mul]
      norm_num at hc
      linarith
    · simp [SixWeakOuterReplay.decode, SixOuterReplay.decode, hij] at hdecode
  | triangle t part =>
    simp only [SixWeakOuterReplay.decode, SixOuterReplay.decode, Option.some.injEq] at hdecode
    subst a
    exact SixOuterReplaySoundness.triangleArc_sound M w hword t part
  | gapLower i k =>
    simp only [SixWeakOuterReplay.decode, Option.some.injEq] at hdecode
    subst a
    exact SixOuterReplaySoundness.lowerArc_sound M ord i k _ (hlower i k)
  | gapUpper i k =>
    simp [SixWeakOuterReplay.decode] at hdecode

theorem cycleCheck_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData) (lower : LowerBounds)
    (hlower : ∀ i k, (lower i k : ℝ) ≤ Gaps M i (ord i) k)
    (C : Cycle) (hcheck : SixWeakOuterReplay.cycleCheck C w ord lower = true) : False := by
  have hp : SixWeakOuterReplay.cycleMatches C w ord lower = true ∧
      N4R2ThinReplay.accepts C.data = true := by
    simpa only [SixWeakOuterReplay.cycleCheck, Bool.and_eq_true] using hcheck
  have hm : ∀ j, SixWeakOuterReplay.decode w ord lower (C.origin j) = some (C.arc j) :=
    of_decide_eq_true hp.1
  apply N4R2SharedCycleChecker.accepts_sound (SixOuterReplaySoundness.toCertificate C.data)
    (value M) M.delta M.hdelta.2
  · exact hp.2
  · intro j
    exact decode_sound M w hword ord lower hlower (C.origin j) (C.arc j) (hm j)

theorem libraryCheck_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData) (lower : LowerBounds)
    (hlower : ∀ i k, (lower i k : ℝ) ≤ Gaps M i (ord i) k)
    (library : SixWeakOuterReplay.Library) (id : ℕ)
    (hcheck : SixWeakOuterReplay.libraryCheck library w ord lower id = true) : False := by
  cases hlib : library id with
  | none => simp [SixWeakOuterReplay.libraryCheck, hlib] at hcheck
  | some C =>
    have hc : SixWeakOuterReplay.cycleCheck C w ord lower = true := by
      simpa [SixWeakOuterReplay.libraryCheck, hlib] using hcheck
    exact cycleCheck_sound M w hword ord lower hlower C hc

private theorem gaps_eq_model (M : GenericModel 5 4) (ord : RowsData)
    (hrows : ∀ i, (List.ofFn (ord i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (ord i k))).Pairwise (· ≤ ·)) (i k : Fin 5) :
    Gaps M i (ord i) k = SixOuterFloorProfiles.modelGap M i k :=
  congrFun (SixOuterFloorProfiles.fullGaps_eq_modelGap_of_perm_sorted M i (ord i)
    (hrows i).1 (hrows i).2) k

/-- A75: row1 has at least two score units, row3 is merely positive.
Other rows are unrestricted. All75 profiles are internally produced. -/
theorem leafCheckA_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData)
    (hrows : ∀ i, (List.ofFn (ord i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (ord i k))).Pairwise (· ≤ ·))
    (hdef1 : SatScalarModel.rowDefect M 1 ≤ 2)
    (hdef3 : SatScalarModel.rowDefect M 3 ≤ 3)
    (library : SixWeakOuterReplay.Library) (ids : Fin 15 → Fin 5 → ℕ)
    (hcheck : SixWeakOuterReplay.leafCheckA library w ord ids = true) : False := by
  obtain ⟨p,hp⟩ := SixWeakOuterFloorProfiles.weak_two_profile M 1 hdef1
  obtain ⟨t,ht⟩ := SixWeakOuterFloorProfiles.positive_cell M 3 hdef3
  have hlower (i k : Fin 5) : (SixWeakOuterReplay.lowerA p t i k : ℝ) ≤ Gaps M i (ord i) k := by
    rw [gaps_eq_model M ord hrows]
    by_cases hi : i.val = 1
    · have he : i = (1 : Fin 5) := Fin.ext hi
      subst i
      simpa [SixWeakOuterReplay.lowerA] using hp k
    · by_cases hs : i.val = 3 ∧ k = t
      · have he : i = (3 : Fin 5) := Fin.ext hs.1
        subst i
        have hk : k = t := hs.2
        subst k
        simpa [SixWeakOuterReplay.lowerA] using ht
      · simpa [SixWeakOuterReplay.lowerA, hi, hs] using SixOuterFloorProfiles.modelGap_nonneg M i k
  have hall : ∀ p t, SixWeakOuterReplay.libraryCheck library w ord
      (SixWeakOuterReplay.lowerA p t) (ids p t) = true := of_decide_eq_true hcheck
  exact libraryCheck_sound M w hword ord (SixWeakOuterReplay.lowerA p t) hlower
    library (ids p t) (hall p t)

/-- B225: both original rows0 and2 have at least two score units.
Other rows are unrestricted; no positive or exact tail premise is added. -/
theorem leafCheckB_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData)
    (hrows : ∀ i, (List.ofFn (ord i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (ord i k))).Pairwise (· ≤ ·))
    (hdef0 : SatScalarModel.rowDefect M 0 ≤ 2)
    (hdef2 : SatScalarModel.rowDefect M 2 ≤ 2)
    (library : SixWeakOuterReplay.Library) (ids : Fin 15 → Fin 15 → ℕ)
    (hcheck : SixWeakOuterReplay.leafCheckB library w ord ids = true) : False := by
  obtain ⟨p,hp⟩ := SixWeakOuterFloorProfiles.weak_two_profile M 0 hdef0
  obtain ⟨q,hq⟩ := SixWeakOuterFloorProfiles.weak_two_profile M 2 hdef2
  have hlower (i k : Fin 5) : (SixWeakOuterReplay.lowerB p q i k : ℝ) ≤ Gaps M i (ord i) k := by
    rw [gaps_eq_model M ord hrows]
    by_cases hi : i.val = 0
    · have he : i = (0 : Fin 5) := Fin.ext hi
      subst i
      simpa [SixWeakOuterReplay.lowerB] using hp k
    · by_cases hi2 : i.val = 2
      · have he : i = (2 : Fin 5) := Fin.ext hi2
        subst i
        simpa [SixWeakOuterReplay.lowerB] using hq k
      · simpa [SixWeakOuterReplay.lowerB, hi, hi2] using SixOuterFloorProfiles.modelGap_nonneg M i k
  have hall : ∀ p q, SixWeakOuterReplay.libraryCheck library w ord
      (SixWeakOuterReplay.lowerB p q) (ids p q) = true := of_decide_eq_true hcheck
  exact libraryCheck_sound M w hword ord (SixWeakOuterReplay.lowerB p q) hlower
    library (ids p q) (hall p q)

#print axioms decode_sound
#print axioms cycleCheck_sound
#print axioms libraryCheck_sound
#print axioms leafCheckA_sound
#print axioms leafCheckB_sound
end Jsp404.SixWeakOuterReplaySoundness
