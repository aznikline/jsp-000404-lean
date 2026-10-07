import Jsp000404.SatScalarModel
import Jsp000404.SixModelReflection

/-!
# Reflection of generic necessary scalar models

Kernel-validation status is recorded in the dedicated producer receipt.
The whole source requires strict and genuine own-target normal checks.

The affine reflection has height `(n : ℝ) + 2 * M.delta` and reverses the
finite row indices.  It preserves the complete row multiset, every actual
linear gap (in reverse order), and the full row defect.  No realization or
additional model field is introduced.  The two seven-row profile wrappers
only transport profiles; they contain no terminal impossibility claim.
-/

set_option autoImplicit false

namespace Jsp404.SatScalarModelReflection

open SatScalarModel StrongGapBudget

/-- Index reflection retains exactly the complementary row indices,
with their full multiplicities. This holds for every `m`. -/
theorem erase_finRange_rev_perm {m : ℕ} (i : Fin m) :
    ((List.finRange m).erase i.rev).Perm
      (((List.finRange m).erase i).map Fin.rev) := by
  apply List.Subperm.antisymm
  · apply List.Nodup.subperm ((List.nodup_finRange m).erase i.rev)
    intro x hx
    rw [(List.nodup_finRange m).mem_erase_iff] at hx
    refine List.mem_map.mpr ⟨x.rev, ?_, Fin.rev_rev x⟩
    rw [(List.nodup_finRange m).mem_erase_iff]
    exact ⟨fun h => hx.1 (Fin.rev_eq_iff.mp h), List.mem_finRange _⟩
  · apply List.Nodup.subperm
      (((List.nodup_finRange m).erase i).map Fin.rev_injective)
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rw [(List.nodup_finRange m).mem_erase_iff] at hj ⊢
    exact ⟨fun h => hj.1 (Fin.rev_injective h), List.mem_finRange _⟩

/-- Reflect all necessary scalar data, without a cardinality restriction
or a planar-realizability premise. -/
noncomputable def reflect {m n : ℕ} (M : GenericModel m n) : GenericModel m n where
  hn3 := M.hn3
  delta := M.delta
  hdelta := M.hdelta
  theta i := M.delta - M.theta i.rev
  htheta := by
    intro i j hij
    have h := M.htheta (Fin.rev_lt_rev.mpr hij)
    linarith
  theta_bounds i := by
    have h := M.theta_bounds i.rev
    constructor <;> linarith
  d i j := (n : ℝ) + 2 * M.delta - M.d i.rev j.rev
  symm i j hij := by
    rw [M.symm i.rev j.rev (fun h => hij (Fin.rev_injective h))]
  corridor i j hij := by
    have h := M.corridor j.rev i.rev (Fin.rev_lt_rev.mpr hij)
    rw [M.symm i.rev j.rev
      (fun h => (ne_of_lt hij) (Fin.rev_injective h))]
    constructor <;> linarith [h.1, h.2]
  triangle i j k hij hjk := by
    have hsij := M.symm i.rev j.rev
      (fun h => (ne_of_lt hij) (Fin.rev_injective h))
    have hsjk := M.symm j.rev k.rev
      (fun h => (ne_of_lt hjk) (Fin.rev_injective h))
    have hsik := M.symm i.rev k.rev
      (fun h => (ne_of_lt (lt_trans hij hjk)) (Fin.rev_injective h))
    rw [hsij, hsjk, hsik]
    rcases M.triangle k.rev j.rev i.rev
      (Fin.rev_lt_rev.mpr hjk) (Fin.rev_lt_rev.mpr hij) with h | h
    · exact Or.inl ⟨by linarith only [h.1], by linarith only [h.2.2],
        by linarith only [h.2.1]⟩
    · exact Or.inr ⟨by linarith only [h.1], by linarith only [h.2.2],
        by linarith only [h.2.1]⟩
  rowxs i := (M.rowxs i.rev).reverse.map
    (fun x => (n : ℝ) + 2 * M.delta - x)
  row_sorted i := by
    rw [List.pairwise_map, List.pairwise_reverse]
    exact (M.row_sorted i.rev).imp (fun h => by linarith)
  row_perm i := by
    have hrows := ((M.rowxs i.rev).reverse_perm.trans (M.row_perm i.rev)).map
      (fun x => (n : ℝ) + 2 * M.delta - x)
    have hindices := (erase_finRange_rev_perm i).map
      (fun j => (n : ℝ) + 2 * M.delta - M.d i.rev j)
    exact hrows.trans (by
      simpa only [List.map_map, Function.comp_def] using hindices)

/-- Every full linear gap is reflected, including both endpoint gaps. -/
theorem reflect_linearGaps {m n : ℕ} (M : GenericModel m n) (i : Fin m) :
    linearGaps ((reflect M).theta i)
      ((reflect M).theta i + ((n : ℝ) + (reflect M).delta))
      ((reflect M).rowxs i) =
      (linearGaps (M.theta i.rev)
        (M.theta i.rev + ((n : ℝ) + M.delta)) (M.rowxs i.rev)).reverse := by
  have hgaps := SixModelReflection.linearGaps_reflect_reverse
    ((n : ℝ) + 2 * M.delta) (M.theta i.rev)
    (M.theta i.rev + ((n : ℝ) + M.delta)) (M.rowxs i.rev)
  have hleft : (n : ℝ) + 2 * M.delta -
      (M.theta i.rev + ((n : ℝ) + M.delta)) = M.delta - M.theta i.rev := by ring
  have hright : (n : ℝ) + 2 * M.delta - M.theta i.rev =
      (M.delta - M.theta i.rev) + ((n : ℝ) + M.delta) := by ring
  change linearGaps (M.delta - M.theta i.rev)
    ((M.delta - M.theta i.rev) + ((n : ℝ) + M.delta))
    ((M.rowxs i.rev).reverse.map fun x => (n : ℝ) + 2 * M.delta - x) = _
  simpa only [hleft, hright] using hgaps

/-- The full score is invariant at every scale, before taking its
complement in `n`. -/
theorem reflect_linearGapScore {m n : ℕ} (M : GenericModel m n)
    (lam : ℝ) (i : Fin m) :
    linearGapScore lam ((reflect M).theta i)
      ((reflect M).theta i + ((n : ℝ) + (reflect M).delta))
      ((reflect M).rowxs i) =
      linearGapScore lam (M.theta i.rev)
        (M.theta i.rev + ((n : ℝ) + M.delta)) (M.rowxs i.rev) := by
  have hscore := SixModelReflection.linearGapScore_reflect_reverse lam
    ((n : ℝ) + 2 * M.delta) (M.theta i.rev)
    (M.theta i.rev + ((n : ℝ) + M.delta)) (M.rowxs i.rev)
  have hleft : (n : ℝ) + 2 * M.delta -
      (M.theta i.rev + ((n : ℝ) + M.delta)) = M.delta - M.theta i.rev := by ring
  have hright : (n : ℝ) + 2 * M.delta - M.theta i.rev =
      (M.delta - M.theta i.rev) + ((n : ℝ) + M.delta) := by ring
  change linearGapScore lam (M.delta - M.theta i.rev)
    ((M.delta - M.theta i.rev) + ((n : ℝ) + M.delta))
    ((M.rowxs i.rev).reverse.map fun x => (n : ℝ) + 2 * M.delta - x) = _
  simpa only [hleft, hright] using hscore

/-- Exact full-row defects are transported along `Fin.rev`. -/
theorem reflect_rowDefect {m n : ℕ} (M : GenericModel m n) (i : Fin m) :
    rowDefect (reflect M) i = rowDefect M i.rev := by
  exact congrArg (fun s : ℕ => n - s) (reflect_linearGapScore M 1 i)

theorem reflect_twice_rowDefect {m n : ℕ} (M : GenericModel m n) (i : Fin m) :
    rowDefect (reflect (reflect M)) i = rowDefect M i := by
  rw [reflect_rowDefect, reflect_rowDefect, Fin.rev_rev]

/-- Low ranks `0,1` become low ranks `5,6`; all other five row defects
are transported as well. This is only a profile transport theorem. -/
theorem reflect_outer01_to_outer56 {n : ℕ} (M : GenericModel 7 n)
    (hdef0 : rowDefect M 0 = 2) (hdef1 : rowDefect M 1 = 2)
    (htails : ∀ i : Fin 7, 1 < i.val → rowDefect M i = 4) :
    rowDefect (reflect M) 5 = 2 ∧ rowDefect (reflect M) 6 = 2 ∧
      (∀ i : Fin 7, i.val < 5 → rowDefect (reflect M) i = 4) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [reflect_rowDefect]
    change rowDefect M 1 = 2
    exact hdef1
  · rw [reflect_rowDefect]
    change rowDefect M 0 = 2
    exact hdef0
  · intro i hi
    rw [reflect_rowDefect]
    apply htails i.rev
    rw [Fin.val_rev]
    omega

/-- Low ranks `5,6` become low ranks `0,1`, with all five remaining
row defects retained. -/
theorem reflect_outer56_to_outer01 {n : ℕ} (M : GenericModel 7 n)
    (hdef5 : rowDefect M 5 = 2) (hdef6 : rowDefect M 6 = 2)
    (htails : ∀ i : Fin 7, i.val < 5 → rowDefect M i = 4) :
    rowDefect (reflect M) 0 = 2 ∧ rowDefect (reflect M) 1 = 2 ∧
      (∀ i : Fin 7, 1 < i.val → rowDefect (reflect M) i = 4) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [reflect_rowDefect]
    change rowDefect M 6 = 2
    exact hdef6
  · rw [reflect_rowDefect]
    change rowDefect M 5 = 2
    exact hdef5
  · intro i hi
    rw [reflect_rowDefect]
    apply htails i.rev
    rw [Fin.val_rev]
    omega

/-- Equivalence of the two reflected profiles, without any terminal
contradiction premise. -/
theorem outer01_iff_reflect_outer56 {n : ℕ} (M : GenericModel 7 n) :
    (rowDefect M 0 = 2 ∧ rowDefect M 1 = 2 ∧
      (∀ i : Fin 7, 1 < i.val → rowDefect M i = 4)) ↔
    (rowDefect (reflect M) 5 = 2 ∧ rowDefect (reflect M) 6 = 2 ∧
      (∀ i : Fin 7, i.val < 5 → rowDefect (reflect M) i = 4)) := by
  constructor
  · rintro ⟨h0, h1, ht⟩
    exact reflect_outer01_to_outer56 M h0 h1 ht
  · rintro ⟨h5, h6, ht⟩
    have h := reflect_outer56_to_outer01 (reflect M) h5 h6 ht
    simpa only [reflect_twice_rowDefect] using h

#print axioms reflect
#print axioms reflect_linearGaps
#print axioms reflect_rowDefect
#print axioms reflect_twice_rowDefect
#print axioms reflect_outer01_to_outer56
#print axioms reflect_outer56_to_outer01
#print axioms outer01_iff_reflect_outer56

end Jsp404.SatScalarModelReflection
