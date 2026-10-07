import Jsp000404.N4R2ThinReplay
import Jsp000404.N4R2ThinWordSoundness
import Jsp000404.N4R2SharedLeafChecker

/-!
The small finite checker has exactly the semantics of the already verified
actual-model checker. These are generic equalities for every word and finite
certificate, not an enumeration of words or an external acceptance oracle.
Only the final soundness bridge imports planar geometry.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2ThinReplaySoundness


open SatScalarModel N4R2ModelWordSoundness

private theorem decide_of_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p = decide q := by
  by_cases hp : p
  · have hq := h.mp hp
    simp [hp, hq]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

def toVertex : N4R2ThinReplay.Vertex → N4R2SharedCycleChecker.Vertex
  | .zero => .zero
  | .theta i => .theta i
  | .distance i j => .distance i j

theorem toVertex_injective : Function.Injective toVertex := by
  intro a b h
  cases a <;> cases b <;> simp_all [toVertex]

def toOrigin : N4R2ThinReplay.Origin → N4R2ReifiedArcDecoder.Origin
  | .thetaLower i => .thetaLower i
  | .thetaUpper i => .thetaUpper i
  | .thetaNext i => .thetaNext i
  | .corridorLower i j => .corridorLower i j
  | .corridorUpper i j => .corridorUpper i j
  | .triangle t p => .triangle t p
  | .gapLower i k => .gapLower i k
  | .gapUpper i k => .gapUpper i k

def toArc (a : N4R2ThinReplay.ReifiedArc) : N4R2ReifiedArcDecoder.ReifiedArc :=
  ⟨toVertex a.before, toVertex a.after, a.constant, a.coefficient, a.strict⟩

theorem toArc_injective : Function.Injective toArc := by
  intro a b h
  rcases a with ⟨a1,a2,a3,a4,a5⟩
  rcases b with ⟨b1,b2,b3,b4,b5⟩
  simp only [toArc, N4R2ReifiedArcDecoder.ReifiedArc.mk.injEq, toVertex_injective.eq_iff] at h
  rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩
  rfl

@[simp] theorem canonical_eq (v : N4R2ThinReplay.Vertex) :
    toVertex (N4R2ThinReplay.canonical v) = N4R2ReifiedArcDecoder.canonical (toVertex v) := by
  cases v <;> simp [N4R2ThinReplay.canonical, N4R2ReifiedArcDecoder.canonical, toVertex]

@[simp] theorem rowBefore_eq (i : Fin 7) (ord : Fin 6 → Fin 7) (k : Fin 7) :
    toVertex (N4R2ThinReplay.rowBefore i ord k) = N4R2SharedCycleChecker.rowBefore i ord k := by
  simp only [N4R2ThinReplay.rowBefore, N4R2SharedCycleChecker.rowBefore]
  split_ifs <;> rfl

@[simp] theorem rowAfter_eq (i : Fin 7) (ord : Fin 6 → Fin 7) (k : Fin 7) :
    toVertex (N4R2ThinReplay.rowAfter i ord k) = N4R2SharedCycleChecker.rowAfter i ord k := by
  simp only [N4R2ThinReplay.rowAfter, N4R2SharedCycleChecker.rowAfter]
  split_ifs <;> rfl

theorem profileLower_eq : N4R2ThinReplay.profileLower = N4R2ReifiedArcDecoder.profileLower := rfl

theorem triangleLow_eq (w : N4R2ThinReplay.Word) (t : Fin 35) :
    toVertex (N4R2ThinReplay.triangleLow w t) = N4R2ReifiedArcDecoder.triangleLow w t := by
  simp only [N4R2ThinReplay.triangleLow, N4R2ReifiedArcDecoder.triangleLow]
  split_ifs <;> rfl

theorem triangleHigh_eq (w : N4R2ThinReplay.Word) (t : Fin 35) :
    toVertex (N4R2ThinReplay.triangleHigh w t) = N4R2ReifiedArcDecoder.triangleHigh w t := by
  simp only [N4R2ThinReplay.triangleHigh, N4R2ReifiedArcDecoder.triangleHigh]
  split_ifs <;> rfl

theorem triangleArc_eq (w : N4R2ThinReplay.Word) (t : Fin 35) (p : Fin 3) :
    toArc (N4R2ThinReplay.triangleArc w t p) = N4R2ReifiedArcDecoder.triangleArc w t p := by
  simp only [N4R2ThinReplay.triangleArc, N4R2ReifiedArcDecoder.triangleArc]
  split_ifs <;> simp only [toArc, triangleLow_eq, triangleHigh_eq, toVertex]

theorem lowerArc_eq (w : N4R2ThinReplay.Word) (i k : Fin 7) (n : ℕ) :
    toArc (N4R2ThinReplay.lowerArc w i k n) = N4R2ReifiedArcDecoder.lowerArc w i k n := by
  simp only [N4R2ThinReplay.lowerArc, N4R2ReifiedArcDecoder.lowerArc, toArc, canonical_eq, rowBefore_eq, rowAfter_eq,
    N4R2ThinReplay.rows, N4R2ThinWordSoundness.rows_eq]
  rfl

theorem upperArc_eq (w : N4R2ThinReplay.Word) (i k : Fin 7) :
    toArc (N4R2ThinReplay.upperArc w i k) = N4R2ReifiedArcDecoder.upperArc w i k := by
  simp only [N4R2ThinReplay.upperArc, N4R2ReifiedArcDecoder.upperArc, toArc, canonical_eq, rowBefore_eq, rowAfter_eq,
    N4R2ThinReplay.rows, N4R2ThinWordSoundness.rows_eq]
  rfl

theorem selectedLower_eq (p : Option (Fin 28)) (k : Fin 7) :
    N4R2ThinReplay.selectedLower p k = N4R2ReifiedArcDecoder.selectedLower p k := rfl

theorem gapLowerValue_eq (p0 p6 : Option (Fin 28)) (i k : Fin 7) :
    N4R2ThinReplay.gapLowerValue p0 p6 i k = N4R2ReifiedArcDecoder.gapLowerValue p0 p6 i k := rfl

/-- Every field of the pure decoded arc is transported exactly. -/
theorem decode_eq (w : N4R2ThinReplay.Word) (p0 p6 : Option (Fin 28)) (o : N4R2ThinReplay.Origin) :
    (N4R2ThinReplay.decode w p0 p6 o).map toArc = N4R2ReifiedArcDecoder.decode w p0 p6 (toOrigin o) := by
  cases o with
  | thetaLower i => rfl
  | thetaUpper i => rfl
  | thetaNext i => rfl
  | corridorLower i j =>
    simp only [N4R2ThinReplay.decode, N4R2ReifiedArcDecoder.decode, toOrigin]
    split_ifs <;> rfl
  | corridorUpper i j =>
    simp only [N4R2ThinReplay.decode, N4R2ReifiedArcDecoder.decode, toOrigin]
    split_ifs <;> rfl
  | triangle t p => simp only [N4R2ThinReplay.decode, N4R2ReifiedArcDecoder.decode, toOrigin, Option.map_some, triangleArc_eq]
  | gapLower i k =>
    simp only [N4R2ThinReplay.decode, N4R2ReifiedArcDecoder.decode, toOrigin, gapLowerValue_eq, Option.map_map]
    congr 1
    funext n
    exact lowerArc_eq w i k n
  | gapUpper i k =>
    simp only [N4R2ThinReplay.decode, N4R2ReifiedArcDecoder.decode, toOrigin]
    split_ifs <;> simp only [Option.map_some, Option.map_none, upperArc_eq]

def toCertificate {k : ℕ} (C : N4R2ThinReplay.Certificate N4R2ThinReplay.Vertex k) : N4R2SharedCycleChecker.Certificate N4R2SharedCycleChecker.Vertex k :=
  ⟨fun j => toVertex (C.node j), C.constant, C.coefficient, C.strict⟩

theorem accepts_eq {k : ℕ} (C : N4R2ThinReplay.Certificate N4R2ThinReplay.Vertex k) :
    N4R2SharedCycleChecker.accepts (toCertificate C) = N4R2ThinReplay.accepts C := by
  unfold N4R2SharedCycleChecker.accepts N4R2ThinReplay.accepts
  apply decide_of_iff
  simp only [toCertificate, N4R2SharedCycleChecker.constantSum, N4R2SharedCycleChecker.coefficientSum,
    N4R2ThinReplay.constantSum, N4R2ThinReplay.coefficientSum, toVertex_injective.eq_iff]

def toCycle (C : N4R2ThinReplay.Cycle) : N4R2SharedLeafChecker.Cycle :=
  ⟨C.length, toCertificate C.data, fun j => toOrigin (C.origin j)⟩

theorem cycleArc_eq (C : N4R2ThinReplay.Cycle) (j : Fin C.length) :
    (toCycle C).arc j = toArc (C.arc j) := rfl

private theorem option_map_some_iff {α β : Type} (f : α → β)
    (hf : Function.Injective f) (o : Option α) (a : α) :
    o.map f = some (f a) ↔ o = some a := by
  cases o with
  | none => simp
  | some b => simp only [Option.map_some, Option.some.injEq, hf.eq_iff]

theorem cycleMatches_eq (C : N4R2ThinReplay.Cycle) (w : N4R2ThinReplay.Word) (p0 p6 : Option (Fin 28)) :
    (toCycle C).matches w p0 p6 = C.matches w p0 p6 := by
  unfold N4R2SharedLeafChecker.Cycle.matches N4R2ThinReplay.Cycle.matches
  apply decide_of_iff
  change (∀ j : Fin C.length,
    N4R2ReifiedArcDecoder.decode w p0 p6 (toOrigin (C.origin j)) = some (toArc (C.arc j))) ↔ _
  simp only [← decode_eq, option_map_some_iff toArc toArc_injective]

theorem cycleCheck_eq (C : N4R2ThinReplay.Cycle) (w : N4R2ThinReplay.Word) (p0 p6 : Option (Fin 28)) :
    (toCycle C).check w p0 p6 = C.check w p0 p6 := by
  simp only [N4R2SharedLeafChecker.Cycle.check, N4R2ThinReplay.Cycle.check, cycleMatches_eq, accepts_eq, toCycle]

def toLibrary (library : N4R2ThinReplay.Library) : N4R2SharedLeafChecker.Library :=
  fun id => (library id).map toCycle

theorem libraryCheck_eq (library : N4R2ThinReplay.Library) (w : N4R2ThinReplay.Word) (p0 p6 : Option (Fin 28))
    (id : ℕ) : N4R2SharedLeafChecker.libraryCheck (toLibrary library) w p0 p6 id =
      N4R2ThinReplay.libraryCheck library w p0 p6 id := by
  cases h : library id with
  | none => simp only [N4R2SharedLeafChecker.libraryCheck, N4R2ThinReplay.libraryCheck, toLibrary, h, Option.map_none]
  | some C =>
    simp only [N4R2SharedLeafChecker.libraryCheck, N4R2ThinReplay.libraryCheck, toLibrary, h, Option.map_some, cycleCheck_eq]

def toLeaf : N4R2ThinReplay.LeafProof → N4R2SharedLeafChecker.LeafProof
  | .tail c => .tail c
  | .low0 cs => .low0 cs
  | .low6 cs => .low6 cs
  | .twoLow cs0 cs6 ps => .twoLow cs0 cs6 ps

theorem pairCycle_eq (cs0 cs6 : Fin 28 → Option ℕ) (pairs : Fin 28 → Fin 28 → ℕ)
    (p0 p6 : Fin 28) : N4R2SharedLeafChecker.pairCycle cs0 cs6 pairs p0 p6 =
      N4R2ThinReplay.pairCycle cs0 cs6 pairs p0 p6 := rfl

/-- Exact checker equality avoids any need to trust thin finite data. -/
theorem leafCheck_eq (library : N4R2ThinReplay.Library) (w : N4R2ThinReplay.Word) (proof : N4R2ThinReplay.LeafProof) :
    N4R2SharedLeafChecker.leafCheck (toLibrary library) w (toLeaf proof) = N4R2ThinReplay.leafCheck library w proof := by
  cases proof with
  | tail c => exact libraryCheck_eq library w none none c
  | low0 cs =>
    simp only [toLeaf, N4R2SharedLeafChecker.leafCheck, N4R2ThinReplay.leafCheck]
    apply decide_of_iff
    simp only [libraryCheck_eq]
  | low6 cs =>
    simp only [toLeaf, N4R2SharedLeafChecker.leafCheck, N4R2ThinReplay.leafCheck]
    apply decide_of_iff
    simp only [libraryCheck_eq]
  | twoLow cs0 cs6 ps =>
    simp only [toLeaf, N4R2SharedLeafChecker.leafCheck, N4R2ThinReplay.leafCheck]
    apply decide_of_iff
    simp only [libraryCheck_eq, pairCycle_eq]

/-- A pure checked leaf excludes the actual model, with its direction word
and all complete row defects supplied by the independent actual producers. -/
theorem leafCheck_sound (library : N4R2ThinReplay.Library) (M : GenericModel 7 4) (w : N4R2ThinReplay.Word)
    (hword : WordSound M w)
    (hdef0 : SatScalarModel.rowDefect M 0 = 2)
    (hdef6 : SatScalarModel.rowDefect M 6 = 2)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → SatScalarModel.rowDefect M i = 4)
    (proof : N4R2ThinReplay.LeafProof) (hcheck : N4R2ThinReplay.leafCheck library w proof = true) : False := by
  apply N4R2SharedLeafChecker.leafCheck_sound (toLibrary library) M w hword hdef0 hdef6 htails (toLeaf proof)
  rw [leafCheck_eq]
  exact hcheck

#print axioms toVertex_injective
#print axioms toArc_injective
#print axioms profileLower_eq
#print axioms decode_eq
#print axioms accepts_eq
#print axioms cycleMatches_eq
#print axioms cycleCheck_eq
#print axioms libraryCheck_eq
#print axioms leafCheck_eq
#print axioms leafCheck_sound

end Jsp404.N4R2ThinReplaySoundness
