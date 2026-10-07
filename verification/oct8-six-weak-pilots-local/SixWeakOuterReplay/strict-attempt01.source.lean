import Jsp000404.SixOuterReplay

/-! SOURCE_ONLY lower-only graded75/225 replay. No upper gap is decoded.
The frozen fixed-n4 geometry, vertices and integer-affine cycle data are reused.
Actual profile production and all-word coverage remain separate obligations. -/
set_option autoImplicit false
namespace Jsp404.SixWeakOuterReplay
open SixOuterReplay

abbrev LowerBounds := Fin 5 → Fin 5 → ℕ
abbrev Library := SixOuterReplay.Library

def lowerA (p : Fin 15) (tail : Fin 5) : LowerBounds :=
  fun i k => if i.val = 1 then profileLower p k
    else if i.val = 3 ∧ k = tail then 2 else 0

def lowerB (p q : Fin 15) : LowerBounds :=
  fun i k => if i.val = 0 then profileLower p k
    else if i.val = 2 then profileLower q k else 0

def decode (w : Word) (ord : RowsData) (lower : LowerBounds) : Origin → Option ReifiedArc
  | .gapLower i k => some (lowerArc ord i k (lower i k))
  | .gapUpper _ _ => none
  | origin => SixOuterReplay.decode w ord 0 0 origin

def cycleMatches (C : Cycle) (w : Word) (ord : RowsData) (lower : LowerBounds) : Bool :=
  decide (∀ j : Fin C.length, decode w ord lower (C.origin j) = some (C.arc j))

def cycleCheck (C : Cycle) (w : Word) (ord : RowsData) (lower : LowerBounds) : Bool :=
  cycleMatches C w ord lower && N4R2ThinReplay.accepts C.data

def libraryCheck (library : Library) (w : Word) (ord : RowsData)
    (lower : LowerBounds) (id : ℕ) : Bool :=
  match library id with
  | none => false
  | some C => cycleCheck C w ord lower

def leafCheckA (library : Library) (w : Word) (ord : RowsData)
    (ids : Fin 15 → Fin 5 → ℕ) : Bool :=
  decide (∀ p : Fin 15, ∀ t : Fin 5,
    libraryCheck library w ord (lowerA p t) (ids p t) = true)

def leafCheckB (library : Library) (w : Word) (ord : RowsData)
    (ids : Fin 15 → Fin 15 → ℕ) : Bool :=
  decide (∀ p q : Fin 15,
    libraryCheck library w ord (lowerB p q) (ids p q) = true)

end Jsp404.SixWeakOuterReplay
