import Jsp000404.N4R2ReifiedArcDecoder

/-!
# Shared semantic checker for all n4 R2 leaf stages

A cycle library contains only finite nodes, integer weights and typed origin
labels. Every checked edge must equal the decoder's actual-model edge. Low
profiles are produced by the actual complete low rows, and all 28 possibilities
are checked. No accepted row, solver result, or capacity bound is a model field.

This is the generic leaf checker. Concrete all-word library and block-check
proofs are separate finite data modules; this source alone claims no complete
24698-word replay or original eight-point theorem.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2SharedLeafChecker

open SatScalarModel N4R2SharedCycleChecker N4R2ModelWordSoundness
open N4R2ReifiedArcDecoder

structure Cycle where
  length : ℕ
  data : Certificate Vertex length
  origin : Fin length → Origin

def Cycle.arc (C : Cycle) (j : Fin C.length) : ReifiedArc where
  before := C.data.node j.castSucc
  after := C.data.node j.succ
  constant := C.data.constant j
  coefficient := C.data.coefficient j
  strict := C.data.strict j

def Cycle.matches (C : Cycle) (w : Word) (p0 p6 : Option (Fin 28)) : Bool :=
  decide (∀ j : Fin C.length, decode w p0 p6 (C.origin j) = some (C.arc j))

def Cycle.check (C : Cycle) (w : Word) (p0 p6 : Option (Fin 28)) : Bool :=
  C.matches w p0 p6 && accepts C.data

theorem Cycle.check_sound (C : Cycle) (M : GenericModel 7 4) (w : Word)
    (hword : WordSound M w) (p0 p6 : Option (Fin 28))
    (hprofile0 : ∀ p, p0 = some p → ProfileHolds M 0 p)
    (hprofile6 : ∀ p, p6 = some p → ProfileHolds M 6 p)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4)
    (hcheck : C.check w p0 p6 = true) : False := by
  have hh : C.matches w p0 p6 = true ∧ accepts C.data = true := by
    simpa only [Cycle.check, Bool.and_eq_true] using hcheck
  have hmatches : ∀ j : Fin C.length, decode w p0 p6 (C.origin j) = some (C.arc j) :=
    of_decide_eq_true hh.1
  apply actual_model_checked_cycle M C.data hh.2
  intro j
  exact decode_sound M w hword p0 p6 hprofile0 hprofile6 htails
    (C.origin j) (C.arc j) (hmatches j)

/-- Indexed library lookup can be implemented by bounded data shards. -/
abbrev Library := ℕ → Option Cycle

def libraryCheck (library : Library) (w : Word) (p0 p6 : Option (Fin 28))
    (id : ℕ) : Bool :=
  match library id with
  | none => false
  | some C => C.check w p0 p6

theorem libraryCheck_sound (library : Library) (M : GenericModel 7 4) (w : Word)
    (hword : WordSound M w) (p0 p6 : Option (Fin 28))
    (hprofile0 : ∀ p, p0 = some p → ProfileHolds M 0 p)
    (hprofile6 : ∀ p, p6 = some p → ProfileHolds M 6 p)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4)
    (id : ℕ) (hcheck : libraryCheck library w p0 p6 id = true) : False := by
  cases hlookup : library id with
  | none => simp only [libraryCheck, hlookup, Bool.false_eq_true] at hcheck
  | some C =>
    exact C.check_sound M w hword p0 p6 hprofile0 hprofile6 htails
      (by simpa only [libraryCheck, hlookup] using hcheck)

/-- All complete finite diagnostic stages, with low profiles retaining their
actual row meaning. Optional single-low exclusions avoid copying pair proofs. -/
inductive LeafProof where
  | tail (cycle : ℕ)
  | low0 (cycles : Fin 28 → ℕ)
  | low6 (cycles : Fin 28 → ℕ)
  | twoLow (cycles0 cycles6 : Fin 28 → Option ℕ) (pairs : Fin 28 → Fin 28 → ℕ)

def pairCycle (cycles0 cycles6 : Fin 28 → Option ℕ) (pairs : Fin 28 → Fin 28 → ℕ)
    (p0 p6 : Fin 28) : ℕ :=
  match cycles0 p0 with
  | some id => id
  | none => match cycles6 p6 with
    | some id => id
    | none => pairs p0 p6

def leafCheck (library : Library) (w : Word) : LeafProof → Bool
  | .tail id => libraryCheck library w none none id
  | .low0 cycles => decide (∀ p : Fin 28, libraryCheck library w (some p) none (cycles p) = true)
  | .low6 cycles => decide (∀ p : Fin 28, libraryCheck library w none (some p) (cycles p) = true)
  | .twoLow cycles0 cycles6 pairs => decide (∀ p0 p6 : Fin 28,
      libraryCheck library w (some p0) (some p6) (pairCycle cycles0 cycles6 pairs p0 p6) = true)

theorem noProfileHolds (M : GenericModel 7 4) (i : Fin 7) :
    ∀ p : Fin 28, (none : Option (Fin 28)) = some p → ProfileHolds M i p := by
  intro p hp
  cases hp

theorem someProfileHolds (M : GenericModel 7 4) (i : Fin 7) (chosen : Fin 28)
    (hchosen : ProfileHolds M i chosen) :
    ∀ p : Fin 28, some chosen = some p → ProfileHolds M i p := by
  intro p hp
  cases Option.some.inj hp
  exact hchosen

/-- A checked leaf excludes every actual model realizing its word and full
critical row defects. Both low profile witnesses are derived internally. -/
theorem leafCheck_sound (library : Library) (M : GenericModel 7 4) (w : Word)
    (hword : WordSound M w)
    (hdef0 : SatScalarModel.rowDefect M 0 = 2)
    (hdef6 : SatScalarModel.rowDefect M 6 = 2)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4)
    (proof : LeafProof) (hcheck : leafCheck library w proof = true) : False := by
  cases proof with
  | tail id =>
    exact libraryCheck_sound library M w hword none none
      (noProfileHolds M 0) (noProfileHolds M 6) htails id hcheck
  | low0 cycles =>
    obtain ⟨p, hp⟩ := exists_low_profile M 0 hdef0
    have hall : ∀ p : Fin 28, libraryCheck library w (some p) none (cycles p) = true :=
      of_decide_eq_true hcheck
    exact libraryCheck_sound library M w hword (some p) none
      (someProfileHolds M 0 p hp) (noProfileHolds M 6) htails (cycles p) (hall p)
  | low6 cycles =>
    obtain ⟨p, hp⟩ := exists_low_profile M 6 hdef6
    have hall : ∀ p : Fin 28, libraryCheck library w none (some p) (cycles p) = true :=
      of_decide_eq_true hcheck
    exact libraryCheck_sound library M w hword none (some p)
      (noProfileHolds M 0) (someProfileHolds M 6 p hp) htails (cycles p) (hall p)
  | twoLow cycles0 cycles6 pairs =>
    obtain ⟨p0, hp0⟩ := exists_low_profile M 0 hdef0
    obtain ⟨p6, hp6⟩ := exists_low_profile M 6 hdef6
    have hall : ∀ p0 p6 : Fin 28,
        libraryCheck library w (some p0) (some p6) (pairCycle cycles0 cycles6 pairs p0 p6) = true :=
      of_decide_eq_true hcheck
    exact libraryCheck_sound library M w hword (some p0) (some p6)
      (someProfileHolds M 0 p0 hp0) (someProfileHolds M 6 p6 hp6) htails
      (pairCycle cycles0 cycles6 pairs p0 p6) (hall p0 p6)

#print axioms Cycle.check_sound
#print axioms libraryCheck_sound
#print axioms noProfileHolds
#print axioms someProfileHolds
#print axioms leafCheck_sound

end Jsp404.N4R2SharedLeafChecker
