import Jsp000404.N4R2ThinWord
import Mathlib.Algebra.BigOperators.Fin

/-! Pure finite replay computation. This file imports no scalar or planar model.
A separate soundness module interprets every Boolean check in the actual model.
No external solver result or caller-accepted row is represented by these types. -/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2ThinReplay
open scoped BigOperators

abbrev Word := N4R2WordDefinitions.Word
abbrev triples := N4R2WordDefinitions.triples
abbrev rows := N4R2ThinWord.rows

inductive Vertex where
  | zero
  | theta (i : Fin 7)
  | distance (i j : Fin 7)
  deriving DecidableEq

def canonical : Vertex → Vertex
  | .distance i j => if i ≤ j then .distance i j else .distance j i
  | v => v

def rowBefore (i : Fin 7) (ord : Fin 6 → Fin 7) (k : Fin 7) : Vertex :=
  if k.val = 0 then .theta i else .distance i (ord (Fin.ofNat 6 (k.val - 1)))

def rowAfter (i : Fin 7) (ord : Fin 6 → Fin 7) (k : Fin 7) : Vertex :=
  if k.val = 6 then .theta i else .distance i (ord (Fin.ofNat 6 k.val))

def endpointConstant (k : Fin 7) : ℤ := if k.val = 6 then 4 else 0
def endpointCoefficient (k : Fin 7) : ℤ := if k.val = 6 then 1 else 0

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


structure ReifiedArc where
  before : Vertex
  after : Vertex
  constant : ℤ
  coefficient : ℤ
  strict : Bool
  deriving DecidableEq

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

structure Certificate (α : Type) (k : ℕ) where
  node : Fin (k + 1) → α
  constant : Fin k → ℤ
  coefficient : Fin k → ℤ
  strict : Fin k → Bool

def constantSum {α : Type} {k : ℕ} (C : Certificate α k) : ℤ := ∑ j, C.constant j
def coefficientSum {α : Type} {k : ℕ} (C : Certificate α k) : ℤ := ∑ j, C.coefficient j

def accepts {α : Type} [DecidableEq α] {k : ℕ} (C : Certificate α k) : Bool :=
  decide (C.node (Fin.last k) = C.node 0 ∧
    0 ≤ coefficientSum C ∧ constantSum C + coefficientSum C ≤ 0 ∧
    (constantSum C + coefficientSum C < 0 ∨
      0 < coefficientSum C ∨ ∃ j, C.strict j = true))

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

abbrev Library := ℕ → Option Cycle

def libraryCheck (library : Library) (w : Word) (p0 p6 : Option (Fin 28)) (id : ℕ) : Bool :=
  match library id with
  | none => false
  | some C => C.check w p0 p6

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

end Jsp404.N4R2ThinReplay
