import Jsp000404.N4R2SharedCycleChecker
import Jsp000404.N4R2ModelWordSoundness

/-!
Typed interpretation of the exact finite replay's arc origins.
Every decoded inequality follows from the actual model, its internally
chosen direction word and a necessary low-profile branch. Both endpoint
gaps and canonical unordered chord labels are retained. Low upper bounds
and absent low-profile lower bounds are deliberately not decoded.
This module is shared machinery, not the exhaustive catalog exclusion.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2ReifiedArcDecoder

open SatScalarModel N4R2CriticalReifiedRow N4R2CriticalCycleSoundness
open N4R2SharedCycleChecker N4R2ModelWordSoundness

/-- Exact 7 one-gap and 21 two-gap necessary lower profiles. -/
def profileLower : Fin 28 → Fin 7 → ℕ := ![
  ![3, 0, 0, 0, 0, 0, 0],
  ![0, 3, 0, 0, 0, 0, 0],
  ![0, 0, 3, 0, 0, 0, 0],
  ![0, 0, 0, 3, 0, 0, 0],
  ![0, 0, 0, 0, 3, 0, 0],
  ![0, 0, 0, 0, 0, 3, 0],
  ![0, 0, 0, 0, 0, 0, 3],
  ![2, 2, 0, 0, 0, 0, 0],
  ![2, 0, 2, 0, 0, 0, 0],
  ![2, 0, 0, 2, 0, 0, 0],
  ![2, 0, 0, 0, 2, 0, 0],
  ![2, 0, 0, 0, 0, 2, 0],
  ![2, 0, 0, 0, 0, 0, 2],
  ![0, 2, 2, 0, 0, 0, 0],
  ![0, 2, 0, 2, 0, 0, 0],
  ![0, 2, 0, 0, 2, 0, 0],
  ![0, 2, 0, 0, 0, 2, 0],
  ![0, 2, 0, 0, 0, 0, 2],
  ![0, 0, 2, 2, 0, 0, 0],
  ![0, 0, 2, 0, 2, 0, 0],
  ![0, 0, 2, 0, 0, 2, 0],
  ![0, 0, 2, 0, 0, 0, 2],
  ![0, 0, 0, 2, 2, 0, 0],
  ![0, 0, 0, 2, 0, 2, 0],
  ![0, 0, 0, 2, 0, 0, 2],
  ![0, 0, 0, 0, 2, 2, 0],
  ![0, 0, 0, 0, 2, 0, 2],
  ![0, 0, 0, 0, 0, 2, 2]]

def profilePairs : Fin 21 → (Fin 7 × Fin 7) := ![
  (0, 1),
  (0, 2),
  (0, 3),
  (0, 4),
  (0, 5),
  (0, 6),
  (1, 2),
  (1, 3),
  (1, 4),
  (1, 5),
  (1, 6),
  (2, 3),
  (2, 4),
  (2, 5),
  (2, 6),
  (3, 4),
  (3, 5),
  (3, 6),
  (4, 5),
  (4, 6),
  (5, 6)]

def pairProfile (p : Fin 21) : Fin 28 := ⟨7 + p.val, by omega⟩

def ProfileHolds (M : GenericModel 7 4) (i : Fin 7) (p : Fin 28) : Prop :=
  ∀ k, (profileLower p k : ℝ) ≤ modelGap M i k

theorem profile_single_eq : ∀ j k : Fin 7,
    profileLower (Fin.castLE (by decide : 7 ≤ 28) j) k =
      if k = j then 3 else 0 := by decide

theorem profile_pair_eq : ∀ p : Fin 21, ∀ k : Fin 7,
    profileLower (pairProfile p) k =
      if k = (profilePairs p).1 ∨ k = (profilePairs p).2 then 2 else 0 := by decide

theorem profile_pairs_complete : ∀ j k : Fin 7, j < k →
    ∃ p : Fin 21, profilePairs p = (j, k) := by decide

/-- The profile branch is produced by the actual complete low row. -/
theorem exists_low_profile (M : GenericModel 7 4) (i : Fin 7)
    (hdef : SatScalarModel.rowDefect M i = 2) :
    ∃ p : Fin 28, ProfileHolds M i p := by
  rcases low_fullGap_weak_disjunction M i hdef with ⟨j, hj⟩ | ⟨j, k, hjk, hj, hk⟩
  · refine ⟨Fin.castLE (by decide : 7 ≤ 28) j, ?_⟩
    intro k
    rw [profile_single_eq]
    by_cases he : k = j
    · simpa [he] using hj
    · simpa [he] using modelGap_nonneg M i k
  · obtain ⟨p, hp⟩ := profile_pairs_complete j k hjk
    refine ⟨pairProfile p, ?_⟩
    intro l
    rw [profile_pair_eq, hp]
    by_cases hl : l = j ∨ l = k
    · simp only [hl, ↓reduceIte, Nat.cast_ofNat]
      rcases hl with rfl | rfl
      · exact hj
      · exact hk
    · simpa [hl] using modelGap_nonneg M i l

/-- Canonical JSON/data vertices always use d(min i j)(max i j). -/
def canonical : Vertex → Vertex
  | .distance i j => if i ≤ j then .distance i j else .distance j i
  | v => v

@[simp] theorem value_canonical (M : GenericModel 7 4) (v : Vertex) :
    value M (canonical v) = value M v := by
  cases v with
  | zero => rfl
  | theta i => rfl
  | distance i j =>
    by_cases hij : i ≤ j
    · simp [canonical, hij]
    · simp only [canonical, hij, ↓reduceIte, value]
      exact M.symm j i (ne_of_lt (lt_of_not_ge hij))

structure ReifiedArc where
  before : Vertex
  after : Vertex
  constant : ℤ
  coefficient : ℤ
  strict : Bool
  deriving DecidableEq

def Holds (M : GenericModel 7 4) (a : ReifiedArc) : Prop :=
  edgeHolds a.strict (value M a.before) (value M a.after)
    a.constant a.coefficient M.delta

inductive Origin where
  | thetaLower (i : Fin 7)
  | thetaUpper (i : Fin 7)
  | thetaNext (i : Fin 6)
  | corridorLower (i j : Fin 7)
  | corridorUpper (i j : Fin 7)
  | triangle (t : Fin 35) (part : Fin 3)
  | gapLower (i k : Fin 7)
  | gapUpper (i k : Fin 7)
  deriving DecidableEq

def triangleLow (w : Word) (t : Fin 35) : Vertex :=
  if w t then .distance (triples t).2.1 (triples t).2.2
    else .distance (triples t).1 (triples t).2.1

def triangleHigh (w : Word) (t : Fin 35) : Vertex :=
  if w t then .distance (triples t).1 (triples t).2.1
    else .distance (triples t).2.1 (triples t).2.2

def triangleArc (w : Word) (t : Fin 35) (part : Fin 3) : ReifiedArc :=
  if part.val = 0 then ⟨triangleHigh w t, triangleLow w t, -1, 0, false⟩
  else if part.val = 1 then
    ⟨.distance (triples t).1 (triples t).2.2, triangleLow w t, 0, 0, true⟩
  else ⟨triangleHigh w t, .distance (triples t).1 (triples t).2.2, 0, 0, true⟩

def lowerArc (w : Word) (i k : Fin 7) (lower : ℕ) : ReifiedArc :=
  ⟨canonical (rowAfter i (rows w i) k), canonical (rowBefore i (rows w i) k),
    endpointConstant k - (lower : ℤ), endpointCoefficient k, false⟩

def upperArc (w : Word) (i k : Fin 7) : ReifiedArc :=
  ⟨canonical (rowBefore i (rows w i) k), canonical (rowAfter i (rows w i) k),
    2 - endpointConstant k, -endpointCoefficient k, true⟩

def selectedLower (p : Option (Fin 28)) (k : Fin 7) : Option ℕ :=
  p.bind (fun q => if 0 < profileLower q k then some (profileLower q k) else none)

def gapLowerValue (p0 p6 : Option (Fin 28)) (i k : Fin 7) : Option ℕ :=
  if i = 0 then selectedLower p0 k else if i = 6 then selectedLower p6 k else some 0

/-- Invalid index orders, low upper bounds and unselected low gaps have
no decoded arc. The finite checker must compare all fields of a real arc. -/
def decode (w : Word) (p0 p6 : Option (Fin 28)) : Origin → Option ReifiedArc
  | .thetaLower i => some ⟨.theta i, .zero, 0, 0, false⟩
  | .thetaUpper i => some ⟨.zero, .theta i, 0, 1, false⟩
  | .thetaNext i => some ⟨.theta i.succ, .theta i.castSucc, 0, 0, true⟩
  | .corridorLower i j =>
      if i < j then some ⟨.distance i j, .theta i, -1, 0, false⟩ else none
  | .corridorUpper i j =>
      if i < j then some ⟨.theta j, .distance i j, 3, 1, false⟩ else none
  | .triangle t part => some (triangleArc w t part)
  | .gapLower i k => (gapLowerValue p0 p6 i k).map (lowerArc w i k)
  | .gapUpper i k => if 0 < i.val ∧ i.val < 6 then some (upperArc w i k) else none

theorem triangleArc_sound (M : GenericModel 7 4) (w : Word)
    (hsound : WordSound M w) (t : Fin 35) (part : Fin 3) :
    Holds M (triangleArc w t part) := by
  have ht := hsound t
  cases hb : w t <;>
    simp only [TriArm, hb, Bool.false_eq_true, ↓reduceIte] at ht
  all_goals fin_cases part <;>
    simp [Holds, triangleArc, triangleLow, triangleHigh, hb, value, edgeHolds]
  all_goals linarith only [ht.1, ht.2.1, ht.2.2]

theorem lowerArc_sound (M : GenericModel 7 4) (w : Word)
    (hsound : WordSound M w) (i k : Fin 7) (lower : ℕ)
    (hlower : (lower : ℝ) ≤ modelGap M i k) : Holds M (lowerArc w i k lower) := by
  have hgap := fullGap_affine_coordinates M i (rows w i) k
  rw [rows_fullGaps_eq_modelGap M w hsound i] at hgap
  simp only [Holds, lowerArc, value_canonical, edgeHolds, Bool.false_eq_true,
    ↓reduceIte, Int.cast_sub, Int.cast_natCast]
  linarith

theorem upperArc_sound (M : GenericModel 7 4) (w : Word)
    (hsound : WordSound M w) (i k : Fin 7)
    (hdef : SatScalarModel.rowDefect M i = 4) : Holds M (upperArc w i k) := by
  have hupper := tail_fullGap_lt_two M i k hdef
  have hgap := fullGap_affine_coordinates M i (rows w i) k
  rw [rows_fullGaps_eq_modelGap M w hsound i] at hgap
  simp only [Holds, upperArc, value_canonical, edgeHolds, ↓reduceIte,
    Int.cast_sub, Int.cast_neg, Int.cast_ofNat]
  linarith

theorem selectedLower_sound (M : GenericModel 7 4) (i k : Fin 7)
    (p : Option (Fin 28)) (hprofile : ∀ q, p = some q → ProfileHolds M i q)
    (lower : ℕ) (hvalue : selectedLower p k = some lower) :
    (lower : ℝ) ≤ modelGap M i k := by
  cases hp : p with
  | none => simp [selectedLower, hp] at hvalue
  | some q =>
    simp only [selectedLower, hp, Option.bind_some] at hvalue
    split at hvalue
    · cases hvalue
      exact hprofile q hp k
    · cases hvalue

theorem gapLowerValue_sound (M : GenericModel 7 4) (p0 p6 : Option (Fin 28))
    (hprofile0 : ∀ p, p0 = some p → ProfileHolds M 0 p)
    (hprofile6 : ∀ p, p6 = some p → ProfileHolds M 6 p)
    (i k : Fin 7) (lower : ℕ) (hvalue : gapLowerValue p0 p6 i k = some lower) :
    (lower : ℝ) ≤ modelGap M i k := by
  by_cases hi0 : i = 0
  · subst i
    simp only [gapLowerValue, ↓reduceIte] at hvalue
    exact selectedLower_sound M 0 k p0 hprofile0 lower hvalue
  · by_cases hi6 : i = 6
    · subst i
      simp only [gapLowerValue, hi0, ↓reduceIte] at hvalue
      exact selectedLower_sound M 6 k p6 hprofile6 lower hvalue
    · simp only [gapLowerValue, hi0, hi6, ↓reduceIte, Option.some.injEq] at hvalue
      subst lower
      simpa only [Nat.cast_zero] using modelGap_nonneg M i k

/-- Every decoded origin follows from the actual model and an internally
interpreted word. Low-profile premises are local necessary case branches,
produced by exists_low_profile; they are not DBM feasibility assumptions. -/
theorem decode_sound (M : GenericModel 7 4) (w : Word) (hsound : WordSound M w)
    (p0 p6 : Option (Fin 28))
    (hprofile0 : ∀ p, p0 = some p → ProfileHolds M 0 p)
    (hprofile6 : ∀ p, p6 = some p → ProfileHolds M 6 p)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4)
    (origin : Origin) (a : ReifiedArc) (hdecode : decode w p0 p6 origin = some a) :
    Holds M a := by
  cases origin with
  | thetaLower i =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    simp only [Holds, edgeHolds, value, Bool.false_eq_true, ↓reduceIte,
      Int.cast_zero, zero_add, zero_mul]
    linarith [(M.theta_bounds i).1]
  | thetaUpper i =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    simp only [Holds, edgeHolds, value, Bool.false_eq_true, ↓reduceIte,
      Int.cast_zero, Int.cast_one, zero_add, one_mul]
    simpa only [sub_zero] using (M.theta_bounds i).2
  | thetaNext i =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    simp only [Holds, edgeHolds, value, ↓reduceIte, Int.cast_zero, zero_mul, zero_add]
    have ht := M.htheta (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
    linarith
  | corridorLower i j =>
    simp only [decode] at hdecode
    split at hdecode
    · rename_i hij
      cases hdecode
      have hc := (M.corridor i j hij).1
      norm_num [Holds, edgeHolds, value]
      linarith
    · cases hdecode
  | corridorUpper i j =>
    simp only [decode] at hdecode
    split at hdecode
    · rename_i hij
      cases hdecode
      have hc := (M.corridor i j hij).2
      norm_num at hc
      norm_num [Holds, edgeHolds, value]
      linarith
    · cases hdecode
  | triangle t part =>
    simp only [decode, Option.some.injEq] at hdecode
    subst a
    exact triangleArc_sound M w hsound t part
  | gapLower i k =>
    cases hv : gapLowerValue p0 p6 i k with
    | none => simp [decode, hv] at hdecode
    | some lower =>
      simp only [decode, hv, Option.map_some, Option.some.injEq] at hdecode
      subst a
      exact lowerArc_sound M w hsound i k lower
        (gapLowerValue_sound M p0 p6 hprofile0 hprofile6 i k lower hv)
  | gapUpper i k =>
    simp only [decode] at hdecode
    split at hdecode
    · rename_i hi
      cases hdecode
      exact upperArc_sound M w hsound i k (htails i hi.1 hi.2)
    · cases hdecode

#print axioms profile_single_eq
#print axioms profile_pair_eq
#print axioms profile_pairs_complete
#print axioms exists_low_profile
#print axioms value_canonical
#print axioms triangleArc_sound
#print axioms lowerArc_sound
#print axioms upperArc_sound
#print axioms selectedLower_sound
#print axioms gapLowerValue_sound
#print axioms decode_sound

end Jsp404.N4R2ReifiedArcDecoder
