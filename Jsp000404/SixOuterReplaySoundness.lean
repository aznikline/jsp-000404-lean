import Jsp000404.SixOuterReplay
import Jsp000404.SixOuterFloorProfiles
import Jsp000404.N4R2SharedCycleChecker

/-! SOURCE_ONLY. Actual GenericModel5 semantics for the fixed-n4 CORE75.
Every literal order must be proved a complete actual sorted row; the floor
profiles are produced internally from the original row defects. No accepted
cycle, solver result, or acyclic direction word is a field of the model. -/
set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SixOuterReplaySoundness

open SatScalarModel SixOuterReplay N4R2CriticalCycleSoundness

abbrev Gaps := SixOuterFloorProfiles.fullGaps

def value (M : GenericModel 5 4) : Vertex → ℝ
  | .zero => 0
  | .theta i => M.theta i
  | .distance i j => M.d i j

def Holds (M : GenericModel 5 4) (a : ReifiedArc) : Prop :=
  edgeHolds a.strict (value M a.before) (value M a.after)
    a.constant a.coefficient M.delta

@[simp] theorem value_canonical (M : GenericModel 5 4) (v : Vertex) :
    value M (canonical v) = value M v := by
  cases v with
  | zero => rfl
  | theta i => rfl
  | distance i j =>
    by_cases h : i ≤ j
    · simp [canonical, value, h]
    · have hne : j ≠ i := by omega
      simp [canonical, value, h, M.symm j i hne]

/-- Actual meanings of all ten bits, without any assumed acyclicity. -/
def WordSound (M : GenericModel 5 4) (w : Word) : Prop :=
  ∀ t : Fin 10,
    let (i,_,k) := triples t
    value M (triangleLow w t) + 1 ≤ value M (triangleHigh w t) ∧
      value M (triangleLow w t) < M.d i k ∧
      M.d i k < value M (triangleHigh w t)

private theorem triples_sorted : ∀ t : Fin 10,
    (triples t).1 < (triples t).2.1 ∧ (triples t).2.1 < (triples t).2.2 := by decide

/-- The original model itself selects every triangle arm. The eventual
all-word terminal must consume this word or split the ten actual disjunctions. -/
theorem exists_sound_word (M : GenericModel 5 4) : ∃ w : Word, WordSound M w := by
  classical
  let w : Word := fun t =>
    let (i,j,k) := triples t
    decide (M.d j k + 1 ≤ M.d i j ∧ M.d j k < M.d i k ∧ M.d i k < M.d i j)
  refine ⟨w, ?_⟩
  intro t
  rcases htr : triples t with ⟨i,j,k⟩
  have hs := triples_sorted t
  simp only [htr] at hs
  rcases M.triangle i j k hs.1 hs.2 with hf | hb
  · have hn : ¬ (M.d j k + 1 ≤ M.d i j ∧ M.d j k < M.d i k ∧ M.d i k < M.d i j) := by
      intro h
      linarith [hf.1, h.1]
    simpa [WordSound, w, triangleLow, triangleHigh, value, htr, hn] using hf
  · simpa [WordSound, w, triangleLow, triangleHigh, value, htr, hb] using hb

theorem fullGap_affine_coordinates (M : GenericModel 5 4) (ord : RowsData)
    (i k : Fin 5) :
    Gaps M i (ord i) k = value M (rowAfter ord i k) - value M (rowBefore ord i k) +
      (endpointConstant k : ℝ) + (endpointCoefficient k : ℝ) * M.delta := by
  fin_cases k <;>
    norm_num [Gaps, SixOuterFloorProfiles.fullGaps, value, rowBefore, rowAfter,
      endpointConstant, endpointCoefficient, Fin.ofNat] <;> ring

theorem lowerArc_sound (M : GenericModel 5 4) (ord : RowsData) (i k : Fin 5)
    (lower : ℕ) (h : (lower : ℝ) ≤ Gaps M i (ord i) k) :
    Holds M (lowerArc ord i k lower) := by
  have hg := fullGap_affine_coordinates M ord i k
  simp only [Holds, lowerArc, edgeHolds, Bool.false_eq_true, ↓reduceIte,
    value_canonical, Int.cast_sub, Int.cast_natCast]
  linarith

theorem upperArc_sound (M : GenericModel 5 4) (ord : RowsData) (i k : Fin 5)
    (upper : ℕ) (h : Gaps M i (ord i) k < (upper : ℝ)) :
    Holds M (upperArc ord i k upper) := by
  have hg := fullGap_affine_coordinates M ord i k
  simp only [Holds, upperArc, edgeHolds, ↓reduceIte,
    value_canonical, Int.cast_sub, Int.cast_natCast, Int.cast_neg]
  linarith

theorem triangleArc_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (t : Fin 10) (part : Fin 3) : Holds M (triangleArc w t part) := by
  rcases htr : triples t with ⟨i,j,k⟩
  have ht := hword t
  simp only [htr] at ht
  unfold triangleArc
  simp only [htr]
  split_ifs <;>
    simp only [Holds, edgeHolds, value, Bool.false_eq_true, ↓reduceIte,
      Int.cast_neg, Int.cast_one, Int.cast_zero, zero_mul, add_zero] at ht ⊢
  all_goals linarith [ht.1, ht.2.1, ht.2.2]

/-- All decoder branches are interpreted from original coordinates and full
actual gaps. These intermediate profile bounds are produced inside leafCheck_sound. -/
theorem decode_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData) (p : Fin 15) (tail : Fin 5)
    (hlower : ∀ i k, (lowerValue p tail i k : ℝ) ≤ Gaps M i (ord i) k)
    (hupper : ∀ k, Gaps M 3 (ord 3) k < ((if k = tail then 3 else 2 : ℕ) : ℝ))
    (origin : Origin) (a : ReifiedArc) (hdecode : decode w ord p tail origin = some a) :
    Holds M a := by
  cases origin with
  | thetaLower i =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    have ht := (M.theta_bounds i).1
    simp only [Holds, edgeHolds, Bool.false_eq_true, ↓reduceIte, value,
      Int.cast_zero, zero_mul, add_zero]
    linarith
  | thetaUpper i =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    have ht := (M.theta_bounds i).2
    simpa [Holds, edgeHolds, value] using ht
  | thetaOrder i =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    have ht := M.htheta i.castSucc_lt_succ
    simpa [Holds, edgeHolds, value] using ht
  | corridorLower i j =>
    by_cases hij : i < j
    · simp only [decode, hij, ↓reduceIte, Option.some.injEq] at hdecode
      subst a
      have hc := (M.corridor i j hij).1
      simp only [Holds, edgeHolds, Bool.false_eq_true, ↓reduceIte, value,
        Int.cast_neg, Int.cast_one, Int.cast_zero, zero_mul, add_zero]
      linarith
    · simp [decode, hij] at hdecode
  | corridorUpper i j =>
    by_cases hij : i < j
    · simp only [decode, hij, ↓reduceIte, Option.some.injEq] at hdecode
      subst a
      have hc := (M.corridor i j hij).2
      simp only [Holds, edgeHolds, Bool.false_eq_true, ↓reduceIte, value,
        Int.cast_ofNat, Int.cast_one, one_mul]
      norm_num at hc
      linarith
    · simp [decode, hij] at hdecode
  | triangle t part =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    exact triangleArc_sound M w hword t part
  | gapLower i k =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    exact lowerArc_sound M ord i k _ (hlower i k)
  | gapUpper i k =>
    by_cases hi : i.val = 3
    · have he : i = (3 : Fin 5) := Fin.ext hi
      subst i
      simp only [decode, hi, ↓reduceIte, Option.some.injEq] at hdecode
      subst a
      exact upperArc_sound M ord 3 k _ (hupper k)
    · simp [decode, hi] at hdecode

def toCertificate {k : ℕ} (C : Certificate Vertex k) :
    N4R2SharedCycleChecker.Certificate Vertex k :=
  ⟨C.node, C.constant, C.coefficient, C.strict⟩

theorem cycleCheck_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData) (p : Fin 15) (tail : Fin 5)
    (hlower : ∀ i k, (lowerValue p tail i k : ℝ) ≤ Gaps M i (ord i) k)
    (hupper : ∀ k, Gaps M 3 (ord 3) k < ((if k = tail then 3 else 2 : ℕ) : ℝ))
    (C : Cycle) (hcheck : C.check w ord p tail = true) : False := by
  have hp : C.matches w ord p tail = true ∧ N4R2ThinReplay.accepts C.data = true := by
    simpa only [Cycle.check, Bool.and_eq_true] using hcheck
  have hm : ∀ j, decode w ord p tail (C.origin j) = some (C.arc j) :=
    of_decide_eq_true hp.1
  apply N4R2SharedCycleChecker.accepts_sound (toCertificate C.data)
    (value M) M.delta M.hdelta.2
  · exact hp.2
  · intro j
    exact decode_sound M w hword ord p tail hlower hupper (C.origin j) (C.arc j) (hm j)

theorem libraryCheck_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData) (p : Fin 15) (tail : Fin 5)
    (hlower : ∀ i k, (lowerValue p tail i k : ℝ) ≤ Gaps M i (ord i) k)
    (hupper : ∀ k, Gaps M 3 (ord 3) k < ((if k = tail then 3 else 2 : ℕ) : ℝ))
    (library : Library) (id : ℕ) (hcheck : libraryCheck library w ord p tail id = true) :
    False := by
  cases hlib : library id with
  | none => simp [libraryCheck, hlib] at hcheck
  | some C =>
    have hc : C.check w ord p tail = true := by simpa [libraryCheck, hlib] using hcheck
    exact cycleCheck_sound M w hword ord p tail hlower hupper C hc

/-- A checked word leaf chooses both floor profiles from the original model.
The complete literal row-order proof is an ordinary actual permutation/sorting
statement, derived internally in concrete pilot consumers. -/
theorem leafCheck_sound (M : GenericModel 5 4) (w : Word) (hword : WordSound M w)
    (ord : RowsData)
    (hrows : ∀ i, (List.ofFn (ord i)).Perm ((List.finRange 5).erase i) ∧
      (List.ofFn (fun k => M.d i (ord i k))).Pairwise (· ≤ ·))
    (hdef1 : SatScalarModel.rowDefect M 1 = 2)
    (hdef3 : SatScalarModel.rowDefect M 3 = 3)
    (library : Library) (ids : Fin 15 → Fin 5 → ℕ)
    (hcheck : leafCheck library w ord ids = true) : False := by
  obtain ⟨p, hp⟩ := SixOuterFloorProfiles.row1_weak_profile M hdef1
  obtain ⟨tail, ht⟩ := SixOuterFloorProfiles.row3_tail_profile M hdef3
  have hg (i k : Fin 5) : Gaps M i (ord i) k = SixOuterFloorProfiles.modelGap M i k := by
    exact congrFun (SixOuterFloorProfiles.fullGaps_eq_modelGap_of_perm_sorted M i (ord i)
      (hrows i).1 (hrows i).2) k
  have hlower (i k : Fin 5) : (lowerValue p tail i k : ℝ) ≤ Gaps M i (ord i) k := by
    rw [hg]
    by_cases hi : i.val = 1
    · have he : i = (1 : Fin 5) := Fin.ext hi
      subst i
      simpa [lowerValue] using hp k
    · by_cases hsel : i.val = 3 ∧ k = tail
      · have he : i = (3 : Fin 5) := Fin.ext hsel.1
        subst i
        have hk : k = tail := hsel.2
        subst k
        simpa [lowerValue] using ht.1
      · simpa [lowerValue, hi, hsel] using SixOuterFloorProfiles.modelGap_nonneg M i k
  have hupper (k : Fin 5) : Gaps M 3 (ord 3) k < ((if k = tail then 3 else 2 : ℕ) : ℝ) := by
    rw [hg]
    by_cases hk : k = tail
    · subst k
      simpa using ht.2.1
    · simpa [hk] using ht.2.2 k hk
  have hall : ∀ p tail, libraryCheck library w ord p tail (ids p tail) = true :=
    of_decide_eq_true hcheck
  exact libraryCheck_sound M w hword ord p tail hlower hupper library (ids p tail) (hall p tail)

#print axioms exists_sound_word
#print axioms decode_sound
#print axioms cycleCheck_sound
#print axioms libraryCheck_sound
#print axioms leafCheck_sound
end Jsp404.SixOuterReplaySoundness
