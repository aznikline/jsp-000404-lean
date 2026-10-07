import Jsp000404.N4R2RowDataReplay

/-!
Pure finite replay for the outer-left role assignment. Row 1 carries one
weak28 lower profile, rows 2..6 carry zero-score upper bounds, and row 0 is
unconstrained beyond necessary full-gap nonnegativity. Readiness is recorded
separately by genuine strict and normal receipts. No actual-model conclusion
is asserted by these finite definitions.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2OuterLeftReplay

abbrev Word := N4R2RowDataReplay.Word
abbrev RowsData := N4R2RowDataReplay.RowsData
abbrev Vertex := N4R2RowDataReplay.Vertex
abbrev Origin := N4R2RowDataReplay.Origin
abbrev ReifiedArc := N4R2RowDataReplay.ReifiedArc
abbrev Certificate := N4R2RowDataReplay.Certificate
abbrev Cycle := N4R2RowDataReplay.Cycle
abbrev Library := N4R2RowDataReplay.Library
abbrev profileLower := N4R2ThinReplay.profileLower
abbrev rowsCheck := N4R2RowDataReplay.rowsCheck
abbrev lowerArcWithRows := N4R2RowDataReplay.lowerArcWithRows
abbrev upperArcWithRows := N4R2RowDataReplay.upperArcWithRows

def lowLowerValue (p : Option (Fin 28)) (i k : Fin 7) : ℕ :=
  if i.val = 1 then
    match p with
    | none => 0
    | some q => profileLower q k
  else 0

def decodeWithRows (w : Word) (ord : RowsData) (p : Option (Fin 28)) :
    Origin → Option ReifiedArc
  | .gapLower i k => some (lowerArcWithRows ord i k (lowLowerValue p i k))
  | .gapUpper i k =>
      if 1 < i.val then some (upperArcWithRows ord i k) else none
  | origin => N4R2ThinReplay.decode w none none origin

def cycleMatches (C : Cycle) (w : Word) (ord : RowsData)
    (p : Option (Fin 28)) : Bool :=
  decide (∀ j : Fin C.length,
    decodeWithRows w ord p (C.origin j) = some (C.arc j))

def cycleCheck (C : Cycle) (w : Word) (ord : RowsData)
    (p : Option (Fin 28)) : Bool :=
  cycleMatches C w ord p && N4R2ThinReplay.accepts C.data

def libraryCheck (library : Library) (w : Word) (ord : RowsData)
    (p : Option (Fin 28)) (id : ℕ) : Bool :=
  match library id with
  | none => false
  | some C => cycleCheck C w ord p

inductive LeafProof where
  | tail (cycle : ℕ)
  | low (cycles : Fin 28 → ℕ)

def leafCases (library : Library) (w : Word) (ord : RowsData) : LeafProof → Bool
  | .tail id => libraryCheck library w ord none id
  | .low cycles => decide (∀ p : Fin 28,
      libraryCheck library w ord (some p) (cycles p) = true)

structure LeafData where
  rows : RowsData
  proof : LeafProof

def leafCheck (library : Library) (w : Word) (data : LeafData) : Bool :=
  rowsCheck w data.rows && leafCases library w data.rows data.proof

end Jsp404.N4R2OuterLeftReplay
