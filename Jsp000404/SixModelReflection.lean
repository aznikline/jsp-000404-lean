import Jsp000404.StrongGapBudget
import Mathlib.Data.Fin.Rev

/-!
# Reflection and reversed angle order of the necessary six-centre model

Reflection reverses the actual list of consecutive gaps, including both
endpoint gaps. Lists retain every repeated chord direction. This gives an
ordinary mathematical symmetry of `ModelSix n` and preserves every row
defect after the index involution `Fin.rev`. No solver premise is used.
-/

namespace Jsp404.SixModelReflection

open SixModelCompression StrongGapBudget

theorem linearGaps_append_singleton (left right x : ℝ) (xs : List ℝ) :
    linearGaps left right (xs ++ [x]) =
      linearGaps left x xs ++ [right - x] := by
  induction xs generalizing left with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, linearGaps, ih]

/-- Affine reflection reverses every actual linear gap, including both
ends. No sorting, distinctness, positivity, or deduplication is needed. -/
theorem linearGaps_reflect_reverse (height left right : ℝ) (xs : List ℝ) :
    linearGaps (height - right) (height - left)
      (xs.reverse.map fun x => height - x) =
      (linearGaps left right xs).reverse := by
  induction xs generalizing left with
  | nil =>
    simpa only [List.reverse_nil, List.map_nil, linearGaps,
      List.reverse_cons, List.nil_append] using
      congrArg (fun g : ℝ => [g])
        (show height - left - (height - right) = right - left by ring)
  | cons x xs ih =>
    simp only [List.reverse_cons, List.map_append, List.map_singleton]
    rw [linearGaps_append_singleton, ih]
    rw [show height - left - (height - x) = x - left by ring]
    simp only [linearGaps, List.reverse_cons]

theorem linearGapScore_eq_sum (lam left right : ℝ) (xs : List ℝ) :
    linearGapScore lam left right xs =
      ((linearGaps left right xs).map (gapScore lam)).sum := by
  induction xs generalizing left with
  | nil => simp [linearGapScore, linearGaps]
  | cons x xs ih =>
    simp only [linearGapScore, linearGaps, List.map_cons, List.sum_cons, ih]

/-- The full linear score is reflection invariant for any scale. -/
theorem linearGapScore_reflect_reverse (lam height left right : ℝ)
    (xs : List ℝ) :
    linearGapScore lam (height - right) (height - left)
      (xs.reverse.map fun x => height - x) =
      linearGapScore lam left right xs := by
  rw [linearGapScore_eq_sum, linearGaps_reflect_reverse, linearGapScore_eq_sum]
  simp only [List.map_reverse, List.sum_reverse]

/-- Reversing the finite row indices gives exactly the other four
indices, with no multiplicity loss. -/
theorem erase_finRange_rev_perm (i : Fin 5) :
    ((List.finRange 5).erase i.rev).Perm
      (((List.finRange 5).erase i).map Fin.rev) := by
  apply List.Subperm.antisymm
  · apply List.Nodup.subperm ((List.nodup_finRange 5).erase i.rev)
    intro x hx
    rw [(List.nodup_finRange 5).mem_erase_iff] at hx
    refine List.mem_map.mpr ⟨x.rev, ?_, Fin.rev_rev x⟩
    rw [(List.nodup_finRange 5).mem_erase_iff]
    exact ⟨fun h => hx.1 (Fin.rev_eq_iff.mp h), List.mem_finRange _⟩
  · apply List.Nodup.subperm
      (((List.nodup_finRange 5).erase i).map Fin.rev_injective)
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rw [(List.nodup_finRange 5).mem_erase_iff] at hj ⊢
    exact ⟨fun h => hj.1 (Fin.rev_injective h), List.mem_finRange _⟩

/-- The reflected necessary scalar model. This does not assert a new
planar realization of the scalar coordinates. -/
noncomputable def reflectedModel {n : ℕ} (M : ModelSix n) : ModelSix n where
  hn := M.hn
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

/-- All five row defects survive the reflection, with the angle ranks
reversed. The equality is proved from the full actual linear score. -/
theorem reflectedModel_rowDefect {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    SixModelCompression.rowDefect (reflectedModel M) i =
      SixModelCompression.rowDefect M i.rev := by
  have hscore := linearGapScore_reflect_reverse 1 ((n : ℝ) + 2 * M.delta)
    (M.theta i.rev) (M.theta i.rev + ((n : ℝ) + M.delta)) (M.rowxs i.rev)
  have hleft : (n : ℝ) + 2 * M.delta -
      (M.theta i.rev + ((n : ℝ) + M.delta)) = M.delta - M.theta i.rev := by ring
  have hright : (n : ℝ) + 2 * M.delta - M.theta i.rev =
      (M.delta - M.theta i.rev) + ((n : ℝ) + M.delta) := by ring
  change n - linearGapScore 1 (M.delta - M.theta i.rev)
    ((M.delta - M.theta i.rev) + ((n : ℝ) + M.delta))
    ((M.rowxs i.rev).reverse.map fun x => (n : ℝ) + 2 * M.delta - x) =
      n - linearGapScore 1 (M.theta i.rev)
        (M.theta i.rev + ((n : ℝ) + M.delta)) (M.rowxs i.rev)
  simpa only [hleft, hright] using congrArg (fun s : ℕ => n - s) hscore

theorem reflectedModel_twice_rowDefect {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    SixModelCompression.rowDefect (reflectedModel (reflectedModel M)) i =
      SixModelCompression.rowDefect M i := by
  rw [reflectedModel_rowDefect, reflectedModel_rowDefect, Fin.rev_rev]

#print axioms linearGaps_reflect_reverse
#print axioms linearGapScore_reflect_reverse
#print axioms erase_finRange_rev_perm
#print axioms reflectedModel
#print axioms reflectedModel_rowDefect
#print axioms reflectedModel_twice_rowDefect

end Jsp404.SixModelReflection
