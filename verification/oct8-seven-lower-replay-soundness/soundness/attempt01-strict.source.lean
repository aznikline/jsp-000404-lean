import Jsp000404.SevenWeakFloorProfiles
import Jsp000404.N4R2SharedCycleChecker
import Jsp000404.SevenLowerReplay
import Jsp000404.SatScalarModel
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic

/-!
SOURCE_ONLY private integration snippet, 2026-10-08.
No Lean/Lake check has been run on this file. Copy the declarations into
SevenLowerReplaySoundness, retaining only one definition of TriArm.
The semantic premise is exactly the selected-triangle part of the caller's
ContextSound; no ContextSound, decoder, oracle, or accepted-order field is
defined here. The four actual adjacent comparisons imply a strict order
by the generic finite-successor theorem.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.SevenLowerReplaySoundness

open SatScalarModel SevenLowerReplay

/-- False is the forward arm, true the reverse arm, in the exact pure
lexicographic Fin20 triangle coordinates. -/
def TriArm (M : GenericModel 6 4) (t : Fin 20) (bit : Bool) : Prop :=
  let a := (triples t).1
  let b := (triples t).2.1
  let c := (triples t).2.2
  if bit then
    M.d b c + 1 ≤ M.d a b ∧ M.d b c < M.d a c ∧ M.d a c < M.d a b
  else
    M.d a b + 1 ≤ M.d b c ∧ M.d a b < M.d a c ∧ M.d a c < M.d b c

/-- Only a finite coordinate identity; no geometric premise or word is used. -/
set_option maxRecDepth 100000 in
theorem tripleIndex_incident : ∀ i u v : Fin 6, u < v → u ≠ i → v ≠ i →
    triples (tripleIndex i u v) =
      if i < u then (i,u,v) else if i < v then (u,i,v) else (u,v,i) := by
  decide

/-- One selected actual triangle arm compares the two incident shared
chords. The middle/last cases use the model's actual symmetry field. -/
theorem incident_comparison (M : GenericModel 6 4) (ctx : Context)
    (htri : ∀ t b, ctx.tri t = some b → TriArm M t b)
    (i u v : Fin 6) (huv : u < v) (hui : u ≠ i) (hvi : v ≠ i)
    (bit : Bool) (hbit : ctx.tri (tripleIndex i u v) = some bit) :
    if bit then M.d i v < M.d i u else M.d i u < M.d i v := by
  have ht := htri (tripleIndex i u v) bit hbit
  have he := tripleIndex_incident i u v huv hui hvi
  by_cases hiu : i < u
  · have he' : triples (tripleIndex i u v) = (i,u,v) := by
      simpa only [hiu, ↓reduceIte] using he
    unfold TriArm at ht
    rw [he'] at ht
    cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢
    · exact ht.2.1
    · exact ht.2.2
  · by_cases hiv : i < v
    · have he' : triples (tripleIndex i u v) = (u,i,v) := by
        simpa only [hiu, hiv, ↓reduceIte] using he
      unfold TriArm at ht
      rw [he'] at ht
      rw [M.symm i u hui.symm]
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢
      all_goals linarith only [ht.1]
    · have he' : triples (tripleIndex i u v) = (u,v,i) := by
        simpa only [hiu, hiv, ↓reduceIte] using he
      unfold TriArm at ht
      rw [he'] at ht
      rw [M.symm i u hui.symm, M.symm i v hvi.symm]
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢
      · exact ht.2.2
      · exact ht.2.1

/-- A successful partial comparison supplies its own selected triangle
arm. Equal labels, the center label, and unselected triangles cannot pass. -/
theorem rowCompare_sound (M : GenericModel 6 4) (ctx : Context)
    (htri : ∀ t b, ctx.tri t = some b → TriArm M t b)
    (i u v : Fin 6) (hcheck : rowCompare ctx i u v = some true) :
    M.d i u < M.d i v := by
  by_cases hbad : u = v ∨ u = i ∨ v = i
  · simp [rowCompare, hbad] at hcheck
  · have hne : u ≠ v := fun h => hbad (Or.inl h)
    have hui : u ≠ i := fun h => hbad (Or.inr (Or.inl h))
    have hvi : v ≠ i := fun h => hbad (Or.inr (Or.inr h))
    by_cases huv : u < v
    · simp only [rowCompare, hbad, huv, ↓reduceIte] at hcheck
      cases ht : ctx.tri (tripleIndex i u v) with
      | none => simp [ht] at hcheck
      | some bit =>
        cases bit with
        | false =>
          have hc := incident_comparison M ctx htri i u v huv hui hvi false ht
          simpa only [Bool.false_eq_true, ↓reduceIte] using hc
        | true => simp [ht] at hcheck
    · have hvu : v < u := by omega
      simp only [rowCompare, hbad, huv, ↓reduceIte] at hcheck
      have hc := incident_comparison M ctx htri i v u hvu hvi hui true hcheck
      simpa only [↓reduceIte] using hc

/-- The finite row check proves all five distinct actual noncentral labels
are present. Four adjacent actual comparisons then imply actual full sorting.
Neither the permutation nor sorting is a separate caller premise. -/
theorem rowsChecked_perm_sorted (M : GenericModel 6 4) (ctx : Context)
    (htri : ∀ t b, ctx.tri t = some b → TriArm M t b)
    (i : Fin 6) (ord : Fin 5 → Fin 6)
    (hcheck : rowsChecked ctx i ord = true) :
    (List.ofFn ord).Perm ((List.finRange 6).erase i) ∧
      ((List.ofFn ord).map (M.d i)).Pairwise (· ≤ ·) := by
  have hh : (List.ofFn ord).Nodup ∧
      (∀ j : Fin 6, j ∈ List.ofFn ord ↔ j ≠ i) ∧
      ∀ k : Fin 4, rowCompare ctx i (ord k.castSucc) (ord k.succ) = some true :=
    of_decide_eq_true hcheck
  have hmono : StrictMono (fun k : Fin 5 => M.d i (ord k)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro k
    exact rowCompare_sound M ctx htri i (ord k.castSucc) (ord k.succ) (hh.2.2 k)
  constructor
  · apply List.Subperm.antisymm
    · apply List.Nodup.subperm hh.1
      intro j hj
      exact (List.nodup_finRange 6).mem_erase_iff.mpr
        ⟨(hh.2.1 j).mp hj, List.mem_finRange j⟩
    · apply List.Nodup.subperm ((List.nodup_finRange 6).erase i)
      intro j hj
      exact (hh.2.1 j).mpr (((List.nodup_finRange 6).mem_erase_iff.mp hj).1)
  · rw [List.pairwise_map]
    apply List.pairwise_ofFn.mpr
    intro a b hab
    exact (hmono hab).le

/-- The checked complete literal order agrees with M.rowxs itself, with all
five chords and their multiplicities. This is the input for a full-gap bridge. -/
theorem rowsChecked_rowxs_eq (M : GenericModel 6 4) (ctx : Context)
    (htri : ∀ t b, ctx.tri t = some b → TriArm M t b)
    (i : Fin 6) (ord : Fin 5 → Fin 6)
    (hcheck : rowsChecked ctx i ord = true) :
    M.rowxs i = (List.ofFn ord).map (M.d i) := by
  have hs := rowsChecked_perm_sorted M ctx htri i ord hcheck
  have hp := (M.row_perm i).trans (hs.1.map (M.d i)).symm
  exact hp.eq_of_pairwise' (M.row_sorted i) hs.2

end Jsp404.SevenLowerReplaySoundness

/-! SOURCE_ONLY semantic interpretation and complete recursive branch cover.
Finite certificates must be checked from emptyContext before a data-specific
terminal can be obtained. No solver conclusion is a premise of these proofs.
-/

namespace Jsp404.SevenLowerReplaySoundness

open SatScalarModel SevenLowerReplay
open scoped BigOperators

abbrev modelGap := SevenWeakFloorProfiles.modelGap

def HeavyHolds (M : GenericModel 6 4) (p : Fin 21) : Prop :=
  ∀ k, (profileLower p k : ℝ) ≤ modelGap M 0 k
def PositiveHolds (M : GenericModel 6 4) (j : Fin 4) (t : Fin 6) : Prop :=
  ∀ k, (SevenWeakFloorProfiles.positiveLower t k : ℝ) ≤ modelGap M (positiveRows j) k

structure ContextSound (M : GenericModel 6 4) (ctx : Context) : Prop where
  tri : ∀ t b, ctx.tri t = some b → TriArm M t b
  heavy : ∀ p, ctx.heavy = some p → HeavyHolds M p
  positive : ∀ j t, ctx.positive j = some t → PositiveHolds M j t

theorem profileLower_eq : profileLower = SevenWeakFloorProfiles.profileLower := rfl

theorem emptyContext_sound (M : GenericModel 6 4) : ContextSound M emptyContext := by
  constructor
  · intro t b h
    simp [emptyContext] at h
  · intro p h
    simp [emptyContext] at h
  · intro j t h
    simp [emptyContext] at h

theorem setTriangle_sound (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (t : Fin 20) (bit : Bool) (hbit : TriArm M t bit) :
    ContextSound M (setTriangle ctx t bit) := by
  refine ⟨?_, hctx.heavy, hctx.positive⟩
  intro u b hu
  by_cases hut : u = t
  · subst u
    have hb : bit = b := by simpa [setTriangle] using hu
    subst b
    exact hbit
  · exact hctx.tri u b (by simpa [setTriangle, hut] using hu)

theorem setHeavy_sound (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (p : Fin 21) (hp : HeavyHolds M p) :
    ContextSound M (setHeavy ctx p) := by
  refine ⟨hctx.tri, ?_, hctx.positive⟩
  intro q hq
  have h : p = q := by simpa [setHeavy] using hq
  subst q
  exact hp

theorem setPositive_sound (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (j : Fin 4) (t : Fin 6) (ht : PositiveHolds M j t) :
    ContextSound M (setPositive ctx j t) := by
  refine ⟨hctx.tri, hctx.heavy, ?_⟩
  intro u k hu
  by_cases huj : u = j
  · subst u
    have h : t = k := by simpa [setPositive] using hu
    subst k
    exact ht
  · exact hctx.positive u k (by simpa [setPositive, huj] using hu)

def value (M : GenericModel 6 4) : Vertex → ℝ
  | .zero => 0
  | .theta i => M.theta i
  | .distance i j => M.d i j

def Holds (M : GenericModel 6 4) (a : ReifiedArc) : Prop :=
  N4R2CriticalCycleSoundness.edgeHolds a.strict
    (value M a.before) (value M a.after) a.constant a.coefficient M.delta

@[simp] theorem value_canonical (M : GenericModel 6 4) (v : Vertex) :
    value M (canonical v) = value M v := by
  cases v with
  | zero => rfl
  | theta i => rfl
  | distance i j =>
      by_cases h : i ≤ j
      · simp [canonical, h]
      · simpa only [canonical, ite_eq_right h, value] using
          (M.symm i j (ne_of_gt (lt_of_not_ge h))).symm

private theorem positiveSlot_spec : ∀ i : Fin 6, ∀ j : Fin 4,
    positiveSlot i = some j → positiveRows j = i := by decide

theorem selectedLower_sound (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (i k : Fin 6) :
    (selectedLower ctx i k : ℝ) ≤ modelGap M i k := by
  by_cases hi : i = 0
  · subst i
    cases hp : ctx.heavy with
    | none =>
        simpa [selectedLower, hp] using SevenWeakFloorProfiles.modelGap_nonneg M 0 k
    | some p => simpa [selectedLower, hp] using hctx.heavy p hp k
  · cases hs : positiveSlot i with
    | none =>
        simpa [selectedLower, hi, hs] using SevenWeakFloorProfiles.modelGap_nonneg M i k
    | some j =>
        have hrow := positiveSlot_spec i j hs
        cases ht : ctx.positive j with
        | none =>
            simpa [selectedLower, hi, hs, ht] using SevenWeakFloorProfiles.modelGap_nonneg M i k
        | some t =>
            have h := hctx.positive j t ht k
            rw [hrow] at h
            simpa [selectedLower, hi, hs, ht, SevenWeakFloorProfiles.positiveLower] using h

private def fullGaps (M : GenericModel 6 4) (i : Fin 6)
    (ord : Fin 5 → Fin 6) : Fin 6 → ℝ := ![
  M.d i (ord 0) - M.theta i,
  M.d i (ord 1) - M.d i (ord 0),
  M.d i (ord 2) - M.d i (ord 1),
  M.d i (ord 3) - M.d i (ord 2),
  M.d i (ord 4) - M.d i (ord 3),
  M.theta i + (4 + M.delta) - M.d i (ord 4)]

private theorem ofFn_fullGaps (M : GenericModel 6 4) (i : Fin 6) (ord : Fin 5 → Fin 6) :
    List.ofFn (fullGaps M i ord) = StrongGapBudget.linearGaps (M.theta i)
      (M.theta i + (4 + M.delta)) (List.ofFn (fun k => M.d i (ord k))) := by
  norm_num [List.ofFn_succ, fullGaps, StrongGapBudget.linearGaps]

private theorem checked_fullGaps_eq_modelGap (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (i : Fin 6) (ord : Fin 5 → Fin 6)
    (hrows : rowsChecked ctx i ord = true) : fullGaps M i ord = modelGap M i := by
  have he := rowsChecked_rowxs_eq M ctx hctx.tri i ord hrows
  have hl : List.ofFn (fullGaps M i ord) = SevenWeakFloorProfiles.modelGaps M i := by
    rw [ofFn_fullGaps]
    change StrongGapBudget.linearGaps _ _ _ = StrongGapBudget.linearGaps _ _ (M.rowxs i)
    rw [he, List.map_ofFn]
    rfl
  exact List.ofFn_injective (hl.trans (SevenWeakFloorProfiles.ofFn_modelGap M i).symm)

private theorem fullGap_affine (M : GenericModel 6 4) (i : Fin 6)
    (ord : Fin 5 → Fin 6) (k : Fin 6) :
    fullGaps M i ord k = value M (rowAfter i ord k) - value M (rowBefore i ord k) +
      (endpointConstant k : ℝ) + (endpointCoefficient k : ℝ) * M.delta := by
  fin_cases k <;>
    norm_num [fullGaps, value, rowBefore, rowAfter, endpointConstant, endpointCoefficient,
      Fin.ofNat] <;> ring

private theorem gapLower_sound (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (i k : Fin 6) (ord : Fin 5 → Fin 6)
    (hrows : rowsChecked ctx i ord = true) :
    Holds M ⟨canonical (rowAfter i ord k), canonical (rowBefore i ord k),
      endpointConstant k - (selectedLower ctx i k : ℤ), endpointCoefficient k, false⟩ := by
  have hgap := fullGap_affine M i ord k
  rw [checked_fullGaps_eq_modelGap M ctx hctx i ord hrows] at hgap
  have hlower := selectedLower_sound M ctx hctx i k
  simp only [Holds, N4R2CriticalCycleSoundness.edgeHolds, value_canonical,
    Bool.false_eq_true, ↓reduceIte, Int.cast_sub, Int.cast_natCast]
  linarith

private theorem triangleArc_sound (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (t : Fin 20) (bit : Bool)
    (hbit : ctx.tri t = some bit) (part : Fin 3) : Holds M (triangleArc t bit part) := by
  have ht := hctx.tri t bit hbit
  cases bit <;> simp only [TriArm, Bool.false_eq_true, ↓reduceIte] at ht
  all_goals fin_cases part <;>
    norm_num [Holds, triangleArc, triangleLow, triangleHigh,
      N4R2CriticalCycleSoundness.edgeHolds, value] <;>
    linarith [ht.1, ht.2.1, ht.2.2]

/-- Every accepted origin has a true model interpretation. In particular,
gap endpoints are decoded only after the current context proves the full row. -/
theorem decode_sound (M : GenericModel 6 4) (ctx : Context) (hctx : ContextSound M ctx)
    (origin : Origin) (a : ReifiedArc) (hdecode : decode ctx origin = some a) : Holds M a := by
  cases origin with
  | thetaLower i =>
      simp only [decode, Option.some.injEq] at hdecode
      subst a
      norm_num [Holds, N4R2CriticalCycleSoundness.edgeHolds, value]
      linarith [(M.theta_bounds i).1]
  | thetaUpper i =>
      simp only [decode, Option.some.injEq] at hdecode
      subst a
      norm_num [Holds, N4R2CriticalCycleSoundness.edgeHolds, value]
      linarith [(M.theta_bounds i).2]
  | thetaOrder i =>
      simp only [decode, Option.some.injEq] at hdecode
      subst a
      norm_num [Holds, N4R2CriticalCycleSoundness.edgeHolds, value]
      have ht := M.htheta (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
      linarith
  | corridorLower i j =>
      simp only [decode] at hdecode
      split at hdecode
      · rename_i hij
        cases hdecode
        have hc := (M.corridor i j hij).1
        norm_num [Holds, N4R2CriticalCycleSoundness.edgeHolds, value]
        linarith
      · cases hdecode
  | corridorUpper i j =>
      simp only [decode] at hdecode
      split at hdecode
      · rename_i hij
        cases hdecode
        have hc := (M.corridor i j hij).2
        norm_num at hc
        norm_num [Holds, N4R2CriticalCycleSoundness.edgeHolds, value]
        linarith
      · cases hdecode
  | triangle t part =>
      simp only [decode] at hdecode
      cases hb : ctx.tri t with
      | none => simp [hb] at hdecode
      | some bit =>
          have h : triangleArc t bit part = a := by simpa [hb] using hdecode
          subst a
          exact triangleArc_sound M ctx hctx t bit hb part
  | gapLower i k ord =>
      simp only [decode] at hdecode
      split at hdecode
      · rename_i hrows
        cases hdecode
        exact gapLower_sound M ctx hctx i k ord hrows
      · cases hdecode

private def toCertificate {α : Type} {k : ℕ} (C : Certificate α k) :
    N4R2SharedCycleChecker.Certificate α k := ⟨C.node, C.constant, C.coefficient, C.strict⟩

private theorem accepts_eq {α : Type} [DecidableEq α] {k : ℕ} (C : Certificate α k) :
    N4R2SharedCycleChecker.accepts (toCertificate C) = N4R2ThinReplay.accepts C := rfl

theorem cycleCheck_sound (C : Cycle) (M : GenericModel 6 4) (ctx : Context)
    (hctx : ContextSound M ctx) (hcheck : C.check ctx = true) : False := by
  have hh : C.matches ctx = true ∧ N4R2ThinReplay.accepts C.data = true := by
    simpa only [Cycle.check, Bool.and_eq_true] using hcheck
  have hm : ∀ j : Fin C.length, decode ctx (C.origin j) = some (C.arc j) :=
    of_decide_eq_true hh.1
  apply N4R2SharedCycleChecker.accepts_sound (toCertificate C.data) (value M) M.delta M.hdelta.2
  · simpa only [accepts_eq] using hh.2
  · intro j
    have h := decode_sound M ctx hctx (C.origin j) (C.arc j) (hm j)
    simpa only [Holds, Cycle.arc, toCertificate] using h

theorem cycleLibraryCheck_sound (library : CycleLibrary) (M : GenericModel 6 4)
    (ctx : Context) (hctx : ContextSound M ctx) (id : ℕ)
    (hcheck : cycleLibraryCheck library ctx id = true) : False := by
  cases hc : library id with
  | none => simp [cycleLibraryCheck, hc] at hcheck
  | some C =>
      exact cycleCheck_sound C M ctx hctx (by simpa [cycleLibraryCheck, hc] using hcheck)

private theorem exists_triangle_arm (M : GenericModel 6 4) (t : Fin 20) :
    ∃ bit : Bool, TriArm M t bit := by
  have ho : (triples t).1 < (triples t).2.1 ∧
      (triples t).2.1 < (triples t).2.2 := by
    have hall : ∀ u : Fin 20, (triples u).1 < (triples u).2.1 ∧
        (triples u).2.1 < (triples u).2.2 := by decide
    exact hall t
  rcases M.triangle (triples t).1 (triples t).2.1 (triples t).2.2 ho.1 ho.2 with hf | hr
  · exact ⟨false, by simpa [TriArm] using hf⟩
  · exact ⟨true, by simpa [TriArm] using hr⟩

/-- Actual triangle ORs and internally chosen necessary profiles cover
every branch. Library IDs never replace the current context or fuel. -/
theorem check_sound (nodes : NodeLibrary) (cycles : CycleLibrary) (M : GenericModel 6 4)
    (hheavy : SatScalarModel.rowDefect M 0 ≤ 2)
    (hpositive : ∀ j : Fin 4, SatScalarModel.rowDefect M (positiveRows j) ≤ 3) :
    ∀ fuel ctx id, ContextSound M ctx → check nodes cycles fuel ctx id = true → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro ctx id _hctx hcheck
      simp [check] at hcheck
  | succ fuel ih =>
      intro ctx id hctx hcheck
      cases hn : nodes id with
      | none => simp [check, hn] at hcheck
      | some node =>
          cases node with
          | leaf cid =>
              exact cycleLibraryCheck_sound cycles M ctx hctx cid
                (by simpa only [check, hn] using hcheck)
          | triangle t lo hi =>
              simp only [check, hn] at hcheck
              split at hcheck
              · have hh := Bool.and_eq_true.mp hcheck
                obtain ⟨bit, hb⟩ := exists_triangle_arm M t
                cases bit with
                | false => exact ih (setTriangle ctx t false) lo
                    (setTriangle_sound M ctx hctx t false hb) hh.1
                | true => exact ih (setTriangle ctx t true) hi
                    (setTriangle_sound M ctx hctx t true hb) hh.2
              · cases hcheck
          | heavy children =>
              simp only [check, hn] at hcheck
              split at hcheck
              · have hall : ∀ p : Fin 21,
                    check nodes cycles fuel (setHeavy ctx p) (children p) = true :=
                  of_decide_eq_true hcheck
                obtain ⟨p, hp⟩ := SevenWeakFloorProfiles.weak_two_profile M 0 hheavy
                have hprof : HeavyHolds M p := by
                  simpa only [HeavyHolds, profileLower_eq] using hp
                exact ih (setHeavy ctx p) (children p) (setHeavy_sound M ctx hctx p hprof) (hall p)
              · cases hcheck
          | positive j children =>
              simp only [check, hn] at hcheck
              split at hcheck
              · have hall : ∀ t : Fin 6,
                    check nodes cycles fuel (setPositive ctx j t) (children t) = true :=
                  of_decide_eq_true hcheck
                obtain ⟨t, ht⟩ := SevenWeakFloorProfiles.positive_profile M (positiveRows j) (hpositive j)
                exact ih (setPositive ctx j t) (children t)
                  (setPositive_sound M ctx hctx j t ht) (hall t)
              · cases hcheck

/-- Data-specific root checks can discharge the necessary scalar target.
This helper is not itself a claim that any finite data library has passed. -/
theorem checked_root_impossible (nodes : NodeLibrary) (cycles : CycleLibrary)
    (fuel root : ℕ) (hcheck : check nodes cycles fuel emptyContext root = true)
    (M : GenericModel 6 4) (hheavy : SatScalarModel.rowDefect M 0 ≤ 2)
    (h1 : SatScalarModel.rowDefect M 1 ≤ 3) (h2 : SatScalarModel.rowDefect M 2 ≤ 3)
    (h3 : SatScalarModel.rowDefect M 3 ≤ 3) (h5 : SatScalarModel.rowDefect M 5 ≤ 3) : False := by
  have hp : ∀ j : Fin 4, SatScalarModel.rowDefect M (positiveRows j) ≤ 3 := by
    intro j
    fin_cases j
    · simpa [positiveRows] using h1
    · simpa [positiveRows] using h2
    · simpa [positiveRows] using h3
    · simpa [positiveRows] using h5
  exact check_sound nodes cycles M hheavy hp fuel emptyContext root (emptyContext_sound M) hcheck

#print axioms rowsChecked_rowxs_eq
#print axioms selectedLower_sound
#print axioms decode_sound
#print axioms cycleCheck_sound
#print axioms check_sound
#print axioms checked_root_impossible

end Jsp404.SevenLowerReplaySoundness
