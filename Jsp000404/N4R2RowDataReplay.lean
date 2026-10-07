import Jsp000404.N4R2ThinReplay
import Mathlib.Data.List.Nodup

/-!
Pure finite replay with checked complete row certificates. These row orders
are literal finite data, checked for all six neighbors and all pairwise word
comparisons. No accepted row is added to the scalar model. A separate actual
soundness module interprets the checked rows in the real complete model gaps.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2RowDataReplay

abbrev Word := N4R2ThinReplay.Word
abbrev Vertex := N4R2ThinReplay.Vertex
abbrev Origin := N4R2ThinReplay.Origin
abbrev ReifiedArc := N4R2ThinReplay.ReifiedArc
abbrev Certificate := N4R2ThinReplay.Certificate
abbrev Cycle := N4R2ThinReplay.Cycle
abbrev Library := N4R2ThinReplay.Library
abbrev LeafProof := N4R2ThinReplay.LeafProof
abbrev RowsData := Fin 7 → Fin 6 → Fin 7

def rowsCheck (w : Word) (ord : RowsData) : Bool :=
  decide (∀ i : Fin 7,
    (List.ofFn (ord i)).Nodup ∧
    (∀ j : Fin 7, j ∈ List.ofFn (ord i) ↔ j ≠ i) ∧
    (List.ofFn (ord i)).Pairwise (fun u v => N4R2ThinWord.rowCompare w i u v = true))

def lowerArcWithRows (ord : RowsData) (i k : Fin 7) (lower : ℕ) : ReifiedArc :=
  ⟨N4R2ThinReplay.canonical (N4R2ThinReplay.rowAfter i (ord i) k),
    N4R2ThinReplay.canonical (N4R2ThinReplay.rowBefore i (ord i) k),
    N4R2ThinReplay.endpointConstant k - (lower : ℤ),
    N4R2ThinReplay.endpointCoefficient k, false⟩

def upperArcWithRows (ord : RowsData) (i k : Fin 7) : ReifiedArc :=
  ⟨N4R2ThinReplay.canonical (N4R2ThinReplay.rowBefore i (ord i) k),
    N4R2ThinReplay.canonical (N4R2ThinReplay.rowAfter i (ord i) k),
    2 - N4R2ThinReplay.endpointConstant k,
    -N4R2ThinReplay.endpointCoefficient k, true⟩

def decodeWithRows (w : Word) (ord : RowsData) (p0 p6 : Option (Fin 28)) :
    Origin → Option ReifiedArc
  | .gapLower i k =>
      (N4R2ThinReplay.gapLowerValue p0 p6 i k).map (lowerArcWithRows ord i k)
  | .gapUpper i k =>
      if 0 < i.val ∧ i.val < 6 then some (upperArcWithRows ord i k) else none
  | origin => N4R2ThinReplay.decode w p0 p6 origin

def cycleMatches (C : Cycle) (w : Word) (ord : RowsData)
    (p0 p6 : Option (Fin 28)) : Bool :=
  decide (∀ j : Fin C.length,
    decodeWithRows w ord p0 p6 (C.origin j) = some (C.arc j))

def cycleCheck (C : Cycle) (w : Word) (ord : RowsData)
    (p0 p6 : Option (Fin 28)) : Bool :=
  cycleMatches C w ord p0 p6 && N4R2ThinReplay.accepts C.data

def libraryCheck (library : Library) (w : Word) (ord : RowsData)
    (p0 p6 : Option (Fin 28)) (id : ℕ) : Bool :=
  match library id with
  | none => false
  | some C => cycleCheck C w ord p0 p6

def leafCases (library : Library) (w : Word) (ord : RowsData) : LeafProof → Bool
  | .tail id => libraryCheck library w ord none none id
  | .low0 cycles => decide (∀ p : Fin 28,
      libraryCheck library w ord (some p) none (cycles p) = true)
  | .low6 cycles => decide (∀ p : Fin 28,
      libraryCheck library w ord none (some p) (cycles p) = true)
  | .twoLow cycles0 cycles6 pairs => decide (∀ p0 p6 : Fin 28,
      libraryCheck library w ord (some p0) (some p6)
        (N4R2ThinReplay.pairCycle cycles0 cycles6 pairs p0 p6) = true)

def leafCheckWithRows (library : Library) (w : Word) (ord : RowsData)
    (proof : LeafProof) : Bool :=
  rowsCheck w ord && leafCases library w ord proof

structure LeafData where
  rows : RowsData
  proof : LeafProof

def leafCheck (library : Library) (w : Word) (data : LeafData) : Bool :=
  leafCheckWithRows library w data.rows data.proof

end Jsp404.N4R2RowDataReplay
