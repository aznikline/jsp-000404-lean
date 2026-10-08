import Jsp000404.N4R2ThinReplay

set_option autoImplicit false
set_option pp.fullNames true

/-! SOURCE_ONLY fixed-m6 lower-only branch-DAG computation.
There is no gauge, HIGH lower bound, delta-lower origin or gap upper bound.
Every literal gap order is checked from the current selected triangle arms.
The separate soundness module must interpret all checks in GenericModel6.
-/

namespace Jsp404.SevenLowerReplay

def triples : Fin 20 → (Fin 6 × Fin 6 × Fin 6) := ![
  (0,1,2),(0,1,3),(0,1,4),(0,1,5),(0,2,3),
  (0,2,4),(0,2,5),(0,3,4),(0,3,5),(0,4,5),
  (1,2,3),(1,2,4),(1,2,5),(1,3,4),(1,3,5),
  (1,4,5),(2,3,4),(2,3,5),(2,4,5),(3,4,5)]

def tripleIndex (i u v : Fin 6) : Fin 20 :=
  let a := min i.val (min u.val v.val)
  let c := max i.val (max u.val v.val)
  let b := i.val + u.val + v.val - a - c
  Fin.ofNat 20 (20 - ((6-a)*(5-a)*(4-a))/6 +
    ((b-a-1)*(10-a-b))/2 + (c-b-1))

def positiveRows : Fin 4 → Fin 6 := ![1,2,3,5]

def profileLower : Fin 21 → Fin 6 → ℕ := ![
  ![3,0,0,0,0,0], ![0,3,0,0,0,0], ![0,0,3,0,0,0],
  ![0,0,0,3,0,0], ![0,0,0,0,3,0], ![0,0,0,0,0,3],
  ![2,2,0,0,0,0], ![2,0,2,0,0,0], ![2,0,0,2,0,0],
  ![2,0,0,0,2,0], ![2,0,0,0,0,2], ![0,2,2,0,0,0],
  ![0,2,0,2,0,0], ![0,2,0,0,2,0], ![0,2,0,0,0,2],
  ![0,0,2,2,0,0], ![0,0,2,0,2,0], ![0,0,2,0,0,2],
  ![0,0,0,2,2,0], ![0,0,0,2,0,2], ![0,0,0,0,2,2]]

structure Context where
  tri : Fin 20 → Option Bool
  heavy : Option (Fin 21)
  positive : Fin 4 → Option (Fin 6)

def emptyContext : Context := ⟨fun _ => none, none, fun _ => none⟩
def setTriangle (ctx : Context) (t : Fin 20) (bit : Bool) : Context :=
  ⟨Function.update ctx.tri t (some bit), ctx.heavy, ctx.positive⟩
def setHeavy (ctx : Context) (p : Fin 21) : Context :=
  ⟨ctx.tri, some p, ctx.positive⟩
def setPositive (ctx : Context) (j : Fin 4) (t : Fin 6) : Context :=
  ⟨ctx.tri, ctx.heavy, Function.update ctx.positive j (some t)⟩

inductive Vertex where
  | zero
  | theta (i : Fin 6)
  | distance (i j : Fin 6)
  deriving DecidableEq

def canonical : Vertex → Vertex
  | .distance i j => if i ≤ j then .distance i j else .distance j i
  | v => v

structure ReifiedArc where
  before : Vertex
  after : Vertex
  constant : ℤ
  coefficient : ℤ
  strict : Bool
  deriving DecidableEq

/-- Only distinct actual noncentral labels have an incident comparison. -/
def rowCompare (ctx : Context) (i u v : Fin 6) : Option Bool :=
  if u = v ∨ u = i ∨ v = i then none
  else if u < v then (ctx.tri (tripleIndex i u v)).map (fun b => !b)
  else ctx.tri (tripleIndex i v u)

def rowsChecked (ctx : Context) (i : Fin 6) (ord : Fin 5 → Fin 6) : Bool :=
  decide ((List.ofFn ord).Nodup ∧
    (∀ j : Fin 6, j ∈ List.ofFn ord ↔ j ≠ i) ∧
    ∀ k : Fin 4, rowCompare ctx i (ord k.castSucc) (ord k.succ) = some true)

def rowBefore (i : Fin 6) (ord : Fin 5 → Fin 6) (k : Fin 6) : Vertex :=
  if k.val = 0 then .theta i else .distance i (ord (Fin.ofNat 5 (k.val - 1)))
def rowAfter (i : Fin 6) (ord : Fin 5 → Fin 6) (k : Fin 6) : Vertex :=
  if k.val = 5 then .theta i else .distance i (ord (Fin.ofNat 5 k.val))
def endpointConstant (k : Fin 6) : ℤ := if k.val = 5 then 4 else 0
def endpointCoefficient (k : Fin 6) : ℤ := if k.val = 5 then 1 else 0

def positiveSlot (i : Fin 6) : Option (Fin 4) :=
  if i = 1 then some 0 else if i = 2 then some 1
  else if i = 3 then some 2 else if i = 5 then some 3 else none

def selectedLower (ctx : Context) (i k : Fin 6) : ℕ :=
  if i = 0 then
    match ctx.heavy with
    | none => 0
    | some p => profileLower p k
  else match positiveSlot i with
    | none => 0
    | some j => match ctx.positive j with
      | none => 0
      | some t => if k = t then 2 else 0

def triangleLow (t : Fin 20) (bit : Bool) : Vertex :=
  if bit then .distance (triples t).2.1 (triples t).2.2
  else .distance (triples t).1 (triples t).2.1
def triangleHigh (t : Fin 20) (bit : Bool) : Vertex :=
  if bit then .distance (triples t).1 (triples t).2.1
  else .distance (triples t).2.1 (triples t).2.2
def triangleArc (t : Fin 20) (bit : Bool) (part : Fin 3) : ReifiedArc :=
  if part.val = 0 then ⟨triangleHigh t bit, triangleLow t bit, -1, 0, false⟩
  else if part.val = 1 then
    ⟨.distance (triples t).1 (triples t).2.2, triangleLow t bit, 0, 0, true⟩
  else ⟨triangleHigh t bit, .distance (triples t).1 (triples t).2.2, 0, 0, true⟩

inductive Origin where
  | thetaLower (i : Fin 6)
  | thetaUpper (i : Fin 6)
  | thetaOrder (i : Fin 5)
  | corridorLower (i j : Fin 6)
  | corridorUpper (i j : Fin 6)
  | triangle (t : Fin 20) (part : Fin 3)
  | gapLower (i k : Fin 6) (ord : Fin 5 → Fin 6)

def decode (ctx : Context) : Origin → Option ReifiedArc
  | .thetaLower i => some ⟨.theta i, .zero, 0, 0, false⟩
  | .thetaUpper i => some ⟨.zero, .theta i, 0, 1, false⟩
  | .thetaOrder i => some ⟨.theta i.succ, .theta i.castSucc, 0, 0, true⟩
  | .corridorLower i j =>
      if i < j then some ⟨.distance i j, .theta i, -1, 0, false⟩ else none
  | .corridorUpper i j =>
      if i < j then some ⟨.theta j, .distance i j, 3, 1, false⟩ else none
  | .triangle t part => (ctx.tri t).map (fun bit => triangleArc t bit part)
  | .gapLower i k ord =>
      if rowsChecked ctx i ord then some
        ⟨canonical (rowAfter i ord k), canonical (rowBefore i ord k),
          endpointConstant k - (selectedLower ctx i k : ℤ), endpointCoefficient k, false⟩
      else none

abbrev Certificate := N4R2ThinReplay.Certificate

structure Cycle where
  length : ℕ
  data : Certificate Vertex length
  origin : Fin length → Origin

def Cycle.arc (C : Cycle) (j : Fin C.length) : ReifiedArc :=
  ⟨C.data.node j.castSucc, C.data.node j.succ,
    C.data.constant j, C.data.coefficient j, C.data.strict j⟩
def Cycle.matches (C : Cycle) (ctx : Context) : Bool :=
  decide (∀ j : Fin C.length, decode ctx (C.origin j) = some (C.arc j))
def Cycle.check (C : Cycle) (ctx : Context) : Bool :=
  C.matches ctx && N4R2ThinReplay.accepts C.data

abbrev CycleLibrary := ℕ → Option Cycle

def cycleLibraryCheck (library : CycleLibrary) (ctx : Context) (id : ℕ) : Bool :=
  match library id with
  | none => false
  | some C => C.check ctx

inductive Node where
  | leaf (cycleId : ℕ)
  | triangle (t : Fin 20) (loId hiId : ℕ)
  | heavy (children : Fin 21 → ℕ)
  | positive (rowSlot : Fin 4) (children : Fin 6 → ℕ)

abbrev NodeLibrary := ℕ → Option Node

/-- Every recursive edge consumes fuel. Reused IDs are rechecked in their
actual context; a cache key or Python pruning result supplies no premise. -/
def check (nodes : NodeLibrary) (cycles : CycleLibrary) : ℕ → Context → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, ctx, id => match nodes id with
    | none => false
    | some (.leaf cid) => cycleLibraryCheck cycles ctx cid
    | some (.triangle t lo hi) =>
        if ctx.tri t = none then
          check nodes cycles fuel (setTriangle ctx t false) lo &&
            check nodes cycles fuel (setTriangle ctx t true) hi
        else false
    | some (.heavy children) =>
        if ctx.heavy = none then
          decide (∀ p : Fin 21, check nodes cycles fuel (setHeavy ctx p) (children p) = true)
        else false
    | some (.positive j children) =>
        if ctx.positive j = none then
          decide (∀ t : Fin 6, check nodes cycles fuel (setPositive ctx j t) (children t) = true)
        else false

end Jsp404.SevenLowerReplay
