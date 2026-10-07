import Jsp000404.N4R2CriticalCycleSoundness

/-!
# Shared checked affine cycles and actual complete n4 rows

The checker is an ordinary finite Boolean computation. Its soundness theorem
uses actual real edge inequalities, and never adds a DBM acceptance field to a
model. Every actual row order below is obtained from the model's permutation
and sorting fields, with all six entries and both endpoint gaps retained.

This module provides shared proof machinery, not a kernel theorem covering
the external 24698-word data catalog. The word-to-concrete-order and exhaustive
packet-trie replay obligations remain separate from these shared bridges.
-/

set_option autoImplicit false
set_option pp.fullNames true

namespace Jsp404.N4R2SharedCycleChecker

open SatScalarModel N4R2CriticalReifiedRow N4R2CriticalCycleSoundness
open scoped BigOperators

/-- The finite data contain a complete node path and exact integer weights. -/
structure Certificate (α : Type) (k : ℕ) where
  node : Fin (k + 1) → α
  constant : Fin k → ℤ
  coefficient : Fin k → ℤ
  strict : Fin k → Bool

def constantSum {α : Type} {k : ℕ} (C : Certificate α k) : ℤ :=
  ∑ j, C.constant j

def coefficientSum {α : Type} {k : ℕ} (C : Certificate α k) : ℤ :=
  ∑ j, C.coefficient j

/-- A shared sufficient endpoint test, valid for every actual delta<1.
For zero total weight and zero coefficient, a strict edge is necessary. -/
def accepts {α : Type} [DecidableEq α] {k : ℕ} (C : Certificate α k) : Bool :=
  decide (C.node (Fin.last k) = C.node 0 ∧
    0 ≤ coefficientSum C ∧ constantSum C + coefficientSum C ≤ 0 ∧
    (constantSum C + coefficientSum C < 0 ∨
      0 < coefficientSum C ∨ ∃ j, C.strict j = true))

/-- Finite checker acceptance plus genuinely interpreted edges is sound.
The model supplies delta<1; no external solver result supplies arithmetic. -/
theorem accepts_sound {α : Type} [DecidableEq α] {k : ℕ}
    (C : Certificate α k) (value : α → ℝ) (delta : ℝ)
    (hdelta : delta < 1) (haccepts : accepts C = true)
    (hstep : ∀ j : Fin k, edgeHolds (C.strict j)
      (value (C.node j.castSucc)) (value (C.node j.succ))
      (C.constant j) (C.coefficient j) delta) : False := by
  have hdata : C.node (Fin.last k) = C.node 0 ∧
      0 ≤ coefficientSum C ∧ constantSum C + coefficientSum C ≤ 0 ∧
      (constantSum C + coefficientSum C < 0 ∨
        0 < coefficientSum C ∨ ∃ j, C.strict j = true) :=
    of_decide_eq_true haccepts
  obtain ⟨hclosed, hb, htotal, hcase⟩ := hdata
  have hbR : 0 ≤ ∑ j : Fin k, (C.coefficient j : ℝ) := by
    exact_mod_cast hb
  have htotalR : (∑ j : Fin k, (C.constant j : ℝ)) +
      (∑ j : Fin k, (C.coefficient j : ℝ)) ≤ 0 := by
    exact_mod_cast htotal
  have hmul : (∑ j : Fin k, (C.coefficient j : ℝ)) * delta ≤
      (∑ j : Fin k, (C.coefficient j : ℝ)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_of_lt hdelta) hbR
  apply closed_affine_cycle_exclusion k (fun j => value (C.node j))
    (fun j => (C.constant j : ℝ)) (fun j => (C.coefficient j : ℝ))
    C.strict delta
  · exact congrArg value hclosed
  · exact hstep
  · rcases hcase with hlt | hpos | hstrict
    · left
      have hltR : (∑ j : Fin k, (C.constant j : ℝ)) +
          (∑ j : Fin k, (C.coefficient j : ℝ)) < 0 := by
        exact_mod_cast hlt
      linarith
    · left
      have hposR : 0 < ∑ j : Fin k, (C.coefficient j : ℝ) := by
        exact_mod_cast hpos
      have hmulStrict : (∑ j : Fin k, (C.coefficient j : ℝ)) * delta <
          (∑ j : Fin k, (C.coefficient j : ℝ)) := by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hdelta hposR
      linarith
    · right
      exact ⟨by linarith, hstrict⟩

/-- Any sorted actual scalar row can be lifted to its original six labels.
This existence assertion retains multiplicity and needs no caller order. -/
theorem exists_actual_row_order (M : GenericModel 7 4) (i : Fin 7) :
    ∃ ord : Fin 6 → Fin 7,
      (List.ofFn ord).Perm ((List.finRange 7).erase i) ∧
      (List.ofFn (fun k => M.d i (ord k))).Pairwise (· ≤ ·) := by
  have hex : Relation.Comp
      (fun (ys : List ℝ) (ord : List (Fin 7)) => ys = ord.map (M.d i))
      List.Perm (M.rowxs i) ((List.finRange 7).erase i) := by
    rw [List.eq_map_comp_perm (M.d i)]
    exact M.row_perm i
  obtain ⟨labels, hmap, hperm⟩ := hex
  have hlength : labels.length = 6 := by
    have h := hperm.length_eq
    have hm : i ∈ List.finRange 7 := List.mem_finRange i
    simp only [List.length_erase_of_mem hm, List.length_finRange] at h
    exact h
  let ord : Fin 6 → Fin 7 := fun k => labels.get (Fin.cast hlength.symm k)
  have hofn : List.ofFn ord = labels := by
    have h := List.ofFn_congr hlength labels.get
    exact h.symm.trans (List.ofFn_get labels)
  refine ⟨ord, ?_, ?_⟩
  · rw [hofn]
    exact hperm
  · have hsorted : (labels.map (M.d i)).Pairwise (· ≤ ·) := by
      rw [← hmap]
      exact M.row_sorted i
    rw [List.ofFn_comp' ord (M.d i), hofn]
    exact hsorted

noncomputable def actualRowOrder (M : GenericModel 7 4) (i : Fin 7) : Fin 6 → Fin 7 :=
  Classical.choose (exists_actual_row_order M i)

theorem actualRowOrder_perm (M : GenericModel 7 4) (i : Fin 7) :
    (List.ofFn (actualRowOrder M i)).Perm ((List.finRange 7).erase i) :=
  (Classical.choose_spec (exists_actual_row_order M i)).1

theorem actualRowOrder_sorted (M : GenericModel 7 4) (i : Fin 7) :
    (List.ofFn (fun k => M.d i (actualRowOrder M i k))).Pairwise (· ≤ ·) :=
  (Classical.choose_spec (exists_actual_row_order M i)).2

theorem actualRowOrder_gaps (M : GenericModel 7 4) (i : Fin 7) :
    fullGaps M i (actualRowOrder M i) = modelGap M i :=
  fullGaps_eq_modelGap_of_perm_sorted M i (actualRowOrder M i)
    (actualRowOrder_perm M i) (actualRowOrder_sorted M i)

/-- Named real coordinates; no feasibility or gap information is a field. -/
inductive Vertex where
  | zero
  | theta (i : Fin 7)
  | distance (i j : Fin 7)
  deriving DecidableEq

def value (M : GenericModel 7 4) : Vertex → ℝ
  | .zero => 0
  | .theta i => M.theta i
  | .distance i j => M.d i j

def rowBefore (i : Fin 7) (ord : Fin 6 → Fin 7) (k : Fin 7) : Vertex :=
  if k.val = 0 then .theta i else .distance i (ord (Fin.ofNat 6 (k.val - 1)))

def rowAfter (i : Fin 7) (ord : Fin 6 → Fin 7) (k : Fin 7) : Vertex :=
  if k.val = 6 then .theta i else .distance i (ord (Fin.ofNat 6 k.val))

def endpointConstant (k : Fin 7) : ℤ := if k.val = 6 then 4 else 0
def endpointCoefficient (k : Fin 7) : ℤ := if k.val = 6 then 1 else 0

theorem fullGap_affine_coordinates (M : GenericModel 7 4) (i : Fin 7)
    (ord : Fin 6 → Fin 7) (k : Fin 7) :
    fullGaps M i ord k = value M (rowAfter i ord k) - value M (rowBefore i ord k) +
      (endpointConstant k : ℝ) + (endpointCoefficient k : ℝ) * M.delta := by
  fin_cases k <;>
    norm_num [fullGaps, value, rowBefore, rowAfter, endpointConstant, endpointCoefficient,
      Fin.ofNat] <;> ring

/-- A lower arc is derived from an actual complete gap, including the last
endpoint's 4+delta term, rather than an accepted DBM row. -/
theorem actual_gap_lower_arc (M : GenericModel 7 4) (i k : Fin 7) (lower : ℕ)
    (hlower : (lower : ℝ) ≤ modelGap M i k) :
    edgeHolds false
      (value M (rowAfter i (actualRowOrder M i) k))
      (value M (rowBefore i (actualRowOrder M i) k))
      (endpointConstant k - (lower : ℤ)) (endpointCoefficient k) M.delta := by
  have hrow := actualRowOrder_gaps M i
  have hgap := fullGap_affine_coordinates M i (actualRowOrder M i) k
  rw [hrow] at hgap
  simp only [edgeHolds, Bool.false_eq_true, ↓reduceIte, Int.cast_sub, Int.cast_natCast]
  linarith

/-- Exact tail defect4 produces all seven strict upper arcs internally. -/
theorem actual_tail_upper_arc (M : GenericModel 7 4) (i k : Fin 7)
    (hdef : SatScalarModel.rowDefect M i = 4) :
    edgeHolds true
      (value M (rowBefore i (actualRowOrder M i) k))
      (value M (rowAfter i (actualRowOrder M i) k))
      (2 - endpointConstant k) (-endpointCoefficient k) M.delta := by
  have hupper := tail_fullGap_lt_two M i k hdef
  have hrow := actualRowOrder_gaps M i
  have hgap := fullGap_affine_coordinates M i (actualRowOrder M i) k
  rw [hrow] at hgap
  simp only [edgeHolds, ↓reduceIte, Int.cast_sub, Int.cast_neg, Int.cast_ofNat]
  linarith

/-- The complete 28 necessary low profiles are translated to actual lower
arcs; no selected-gap budget or externally accepted profile is assumed. -/
theorem actual_low_lower_arc_cover (M : GenericModel 7 4) (i : Fin 7)
    (hdef : SatScalarModel.rowDefect M i = 2) :
    (∃ k : Fin 7, edgeHolds false
      (value M (rowAfter i (actualRowOrder M i) k))
      (value M (rowBefore i (actualRowOrder M i) k))
      (endpointConstant k - 3) (endpointCoefficient k) M.delta) ∨
    (∃ j k : Fin 7, j < k ∧
      edgeHolds false (value M (rowAfter i (actualRowOrder M i) j))
        (value M (rowBefore i (actualRowOrder M i) j))
        (endpointConstant j - 2) (endpointCoefficient j) M.delta ∧
      edgeHolds false (value M (rowAfter i (actualRowOrder M i) k))
        (value M (rowBefore i (actualRowOrder M i) k))
        (endpointConstant k - 2) (endpointCoefficient k) M.delta) := by
  rcases low_fullGap_weak_disjunction M i hdef with ⟨k, hk⟩ | ⟨j, k, hjk, hj, hk⟩
  · exact Or.inl ⟨k, actual_gap_lower_arc M i k 3 hk⟩
  · exact Or.inr ⟨j, k, hjk, actual_gap_lower_arc M i j 2 hj,
      actual_gap_lower_arc M i k 2 hk⟩

/-- Actual scalar interpretation of the shared checker. This is a helper:
the finite replay must derive each step from model/row/triangle semantics. -/
theorem actual_model_checked_cycle (M : GenericModel 7 4) {k : ℕ}
    (C : Certificate Vertex k) (haccepts : accepts C = true)
    (hstep : ∀ j : Fin k, edgeHolds (C.strict j)
      (value M (C.node j.castSucc)) (value M (C.node j.succ))
      (C.constant j) (C.coefficient j) M.delta) : False :=
  accepts_sound C (value M) M.delta M.hdelta.2 haccepts hstep

/-- A replay made of tail-gap origins obtains every real premise from the
actual model. Only finite source/target/weight equalities are helper premises;
no real edge inequality or accepted row is supplied by the caller. -/
theorem actual_tail_cycle_checked (M : GenericModel 7 4) {k : ℕ}
    (C : Certificate Vertex k) (rows gaps : Fin k → Fin 7)
    (hdef : ∀ j, SatScalarModel.rowDefect M (rows j) = 4)
    (hbefore : ∀ j, C.node j.castSucc =
      rowBefore (rows j) (actualRowOrder M (rows j)) (gaps j))
    (hafter : ∀ j, C.node j.succ =
      rowAfter (rows j) (actualRowOrder M (rows j)) (gaps j))
    (hconstant : ∀ j, C.constant j = 2 - endpointConstant (gaps j))
    (hcoefficient : ∀ j, C.coefficient j = -endpointCoefficient (gaps j))
    (hstrict : ∀ j, C.strict j = true)
    (haccepts : accepts C = true) : False := by
  apply actual_model_checked_cycle M C haccepts
  intro j
  rw [hbefore j, hafter j, hconstant j, hcoefficient j, hstrict j]
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_ofNat] using
    actual_tail_upper_arc M (rows j) (gaps j) (hdef j)

/-- One fixed certificate exercises the shared integer checker on the
ascending adjacent chain, using actual corridors and theta bounds internally.
This helper is one necessary direction subcase, not full word coverage. -/
def ascendingCertificate : Certificate Vertex 9 where
  node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6,
    .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
  constant := ![-1, 0, 0, 3, -1, -1, -1, -1, -1]
  coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
  strict := fun _ => false

theorem ascendingCertificate_accepts : accepts ascendingCertificate = true := by
  decide

theorem ascending_adjacent_chain_checked (M : GenericModel 7 4)
    (h012 : M.d 0 1 + 1 ≤ M.d 1 2)
    (h123 : M.d 1 2 + 1 ≤ M.d 2 3)
    (h234 : M.d 2 3 + 1 ≤ M.d 3 4)
    (h345 : M.d 3 4 + 1 ≤ M.d 4 5)
    (h456 : M.d 4 5 + 1 ≤ M.d 5 6) : False := by
  have hc01 := (M.corridor 0 1 (by decide)).1
  have hc56 := (M.corridor 5 6 (by decide)).2
  norm_num at hc56
  have ht0 := (M.theta_bounds 0).1
  have ht6 := (M.theta_bounds 6).2
  apply actual_model_checked_cycle M ascendingCertificate ascendingCertificate_accepts
  intro j
  fin_cases j <;> norm_num [ascendingCertificate, value, edgeHolds]
  all_goals linarith

#print axioms accepts_sound
#print axioms exists_actual_row_order
#print axioms actualRowOrder_perm
#print axioms actualRowOrder_sorted
#print axioms actualRowOrder_gaps
#print axioms fullGap_affine_coordinates
#print axioms actual_gap_lower_arc
#print axioms actual_tail_upper_arc
#print axioms actual_low_lower_arc_cover
#print axioms actual_model_checked_cycle
#print axioms actual_tail_cycle_checked
#print axioms ascendingCertificate_accepts
#print axioms ascending_adjacent_chain_checked

end Jsp404.N4R2SharedCycleChecker
