import Jsp000404.N4R2ThinReplay

/-! SOURCE_ONLY. Fixed-n4 finite six-center CORE checker. No model or capacity
assertion is encoded as accepted data. The separate semantic bridge interprets
every decoded arc in actual GenericModel5 coordinates and complete row gaps.
One pilot does not provide all-word coverage. -/
set_option autoImplicit false

namespace Jsp404.SixOuterReplay

abbrev Word := Fin 10 → Bool
abbrev RowsData := Fin 5 → Fin 4 → Fin 5
abbrev Certificate := N4R2ThinReplay.Certificate
abbrev accepts := @N4R2ThinReplay.accepts

inductive Vertex where
  | zero
  | theta (i : Fin 5)
  | distance (i j : Fin 5)
  deriving DecidableEq

def canonical : Vertex → Vertex
  | .distance i j => if i ≤ j then .distance i j else .distance j i
  | v => v

def triples : Fin 10 → (Fin 5 × Fin 5 × Fin 5) := ![
  (0,1,2), (0,1,3), (0,1,4), (0,2,3), (0,2,4),
  (0,3,4), (1,2,3), (1,2,4), (1,3,4), (2,3,4)]

def profileLower : Fin 15 → Fin 5 → ℕ := ![
  ![3,0,0,0,0], ![0,3,0,0,0], ![0,0,3,0,0],
  ![0,0,0,3,0], ![0,0,0,0,3],
  ![2,2,0,0,0], ![2,0,2,0,0], ![2,0,0,2,0],
  ![2,0,0,0,2], ![0,2,2,0,0], ![0,2,0,2,0],
  ![0,2,0,0,2], ![0,0,2,2,0], ![0,0,2,0,2], ![0,0,0,2,2]]

def rowBefore (ord : RowsData) (i k : Fin 5) : Vertex :=
  if k.val = 0 then .theta i else .distance i (ord i (Fin.ofNat 4 (k.val - 1)))

def rowAfter (ord : RowsData) (i k : Fin 5) : Vertex :=
  if k.val = 4 then .theta i else .distance i (ord i (Fin.ofNat 4 k.val))

def endpointConstant (k : Fin 5) : ℤ := if k.val = 4 then 4 else 0
def endpointCoefficient (k : Fin 5) : ℤ := if k.val = 4 then 1 else 0

structure ReifiedArc where
  before : Vertex
  after : Vertex
  constant : ℤ
  coefficient : ℤ
  strict : Bool
  deriving DecidableEq

inductive Origin where
  | thetaLower (i : Fin 5)
  | thetaUpper (i : Fin 5)
  | thetaOrder (i : Fin 4)
  | corridorLower (i j : Fin 5)
  | corridorUpper (i j : Fin 5)
  | triangle (t : Fin 10) (part : Fin 3)
  | gapLower (i k : Fin 5)
  | gapUpper (i k : Fin 5)
  deriving DecidableEq

def triangleLow (w : Word) (t : Fin 10) : Vertex :=
  let (i,j,k) := triples t
  if w t then .distance j k else .distance i j

def triangleHigh (w : Word) (t : Fin 10) : Vertex :=
  let (i,j,k) := triples t
  if w t then .distance i j else .distance j k

def triangleArc (w : Word) (t : Fin 10) (part : Fin 3) : ReifiedArc :=
  let (i,_,k) := triples t
  if part.val = 0 then ⟨triangleHigh w t, triangleLow w t, -1, 0, false⟩
  else if part.val = 1 then ⟨.distance i k, triangleLow w t, 0, 0, true⟩
  else ⟨triangleHigh w t, .distance i k, 0, 0, true⟩

def lowerArc (ord : RowsData) (i k : Fin 5) (lower : ℕ) : ReifiedArc :=
  ⟨canonical (rowAfter ord i k), canonical (rowBefore ord i k),
    endpointConstant k - (lower : ℤ), endpointCoefficient k, false⟩

def upperArc (ord : RowsData) (i k : Fin 5) (upper : ℕ) : ReifiedArc :=
  ⟨canonical (rowBefore ord i k), canonical (rowAfter ord i k),
    (upper : ℤ) - endpointConstant k, -endpointCoefficient k, true⟩

def lowerValue (p : Fin 15) (tail : Fin 5) (i k : Fin 5) : ℕ :=
  if i.val = 1 then profileLower p k
  else if i.val = 3 ∧ k = tail then 2 else 0

def decode (w : Word) (ord : RowsData) (p : Fin 15) (tail : Fin 5) :
    Origin → Option ReifiedArc
  | .thetaLower i => some ⟨.theta i, .zero, 0, 0, false⟩
  | .thetaUpper i => some ⟨.zero, .theta i, 0, 1, false⟩
  | .thetaOrder i => some ⟨.theta i.succ, .theta i.castSucc, 0, 0, true⟩
  | .corridorLower i j =>
      if i < j then some ⟨.distance i j, .theta i, -1, 0, false⟩ else none
  | .corridorUpper i j =>
      if i < j then some ⟨.theta j, .distance i j, 3, 1, false⟩ else none
  | .triangle t part => some (triangleArc w t part)
  | .gapLower i k => some (lowerArc ord i k (lowerValue p tail i k))
  | .gapUpper i k =>
      if i.val = 3 then some (upperArc ord i k (if k = tail then 3 else 2)) else none

structure Cycle where
  length : ℕ
  data : Certificate Vertex length
  origin : Fin length → Origin

def Cycle.arc (C : Cycle) (j : Fin C.length) : ReifiedArc :=
  ⟨C.data.node j.castSucc, C.data.node j.succ, C.data.constant j,
    C.data.coefficient j, C.data.strict j⟩

def Cycle.matches (C : Cycle) (w : Word) (ord : RowsData)
    (p : Fin 15) (tail : Fin 5) : Bool :=
  decide (∀ j : Fin C.length, decode w ord p tail (C.origin j) = some (C.arc j))

def Cycle.check (C : Cycle) (w : Word) (ord : RowsData)
    (p : Fin 15) (tail : Fin 5) : Bool :=
  C.matches w ord p tail && N4R2ThinReplay.accepts C.data

abbrev Library := ℕ → Option Cycle

def libraryCheck (library : Library) (w : Word) (ord : RowsData)
    (p : Fin 15) (tail : Fin 5) (id : ℕ) : Bool :=
  match library id with
  | none => false
  | some C => C.check w ord p tail

/-- Exhaustive finite floor profiles for this fixed direction word.
This checks the 75 low/tail certificates; actual row semantics and exhaustive
triangle-word coverage are separate proof obligations. -/
def leafCheck (library : Library) (w : Word) (ord : RowsData)
    (ids : Fin 15 → Fin 5 → ℕ) : Bool :=
  decide (∀ p : Fin 15, ∀ tail : Fin 5, libraryCheck library w ord p tail (ids p tail) = true)

end Jsp404.SixOuterReplay
