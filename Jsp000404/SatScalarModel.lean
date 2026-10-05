import Jsp000404.IntervalPacking

/-!
# Generic necessary scalar data for an anchored chart

`GenericModel m n` has m non-anchor rows.  Shared chords, strict theta
order, all corridors/triples, and the full sorted row multisets are its
only geometric constraints.  It contains no defect-profile, capacity,
solver conclusion, or planar-realizability field.  Row defects use the
existing full linear-gap score, with both actual linear endpoints.
-/

set_option autoImplicit false

namespace Jsp404.SatScalarModel

/-- Necessary normalized scalar data for m non-anchor centres. -/
structure GenericModel (m n : ℕ) where
  hn3 : 3 ≤ n
  delta : ℝ
  hdelta : delta ∈ Set.Ico 0 1
  theta : Fin m → ℝ
  htheta : StrictMono theta
  theta_bounds : ∀ i, 0 ≤ theta i ∧ theta i ≤ delta
  d : Fin m → Fin m → ℝ
  symm : ∀ i j, i ≠ j → d i j = d j i
  corridor : ∀ i j, i < j → theta i + 1 ≤ d i j ∧
    d i j ≤ (n : ℝ) + delta - 1 + theta j
  triangle : ∀ i j k, i < j → j < k →
    (d i j + 1 ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + 1 ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)
  rowxs : Fin m → List ℝ
  row_sorted : ∀ i, (rowxs i).Pairwise (· ≤ ·)
  row_perm : ∀ i, (rowxs i).Perm (((List.finRange m).erase i).map (d i))

/-- The exact full-row score complement, including both linear ends. -/
noncomputable def rowDefect {m n : ℕ} (M : GenericModel m n) (i : Fin m) : ℕ :=
  n - linearGapScore 1 (M.theta i) (M.theta i + ((n : ℝ) + M.delta)) (M.rowxs i)

/-- Every off-diagonal shared chord lies strictly inside the full period. -/
theorem chord_bounds {m n : ℕ} (M : GenericModel m n)
    (i j : Fin m) (hne : i ≠ j) :
    1 ≤ M.d i j ∧ M.d i j < (n : ℝ) + M.delta := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hc := M.corridor i j hij
    have hi := M.theta_bounds i
    have hj := M.theta_bounds j
    have hj1 : M.theta j < 1 := lt_of_le_of_lt hj.2 M.hdelta.2
    constructor <;> linarith
  · rw [M.symm i j hne]
    have hc := M.corridor j i hji
    have hi := M.theta_bounds i
    have hj := M.theta_bounds j
    have hi1 : M.theta i < 1 := lt_of_le_of_lt hi.2 M.hdelta.2
    constructor <;> linarith

/-- These bounds concern every retained list entry, not a chosen gap subset. -/
theorem row_mem_bounds {m n : ℕ} (M : GenericModel m n) (i : Fin m) :
    ∀ x ∈ M.rowxs i, 1 ≤ x ∧ x < (n : ℝ) + M.delta := by
  intro x hx
  have hm := (M.row_perm i).mem_iff.mp hx
  rcases List.mem_map.mp hm with ⟨j, hj, rfl⟩
  have hji : j ≠ i := ((List.nodup_finRange m).mem_erase_iff.mp hj).1
  exact chord_bounds M i j hji.symm

/-- No chord is lost from a row: all m-1 entries, including repeated
values if present, are retained by its list permutation. -/
theorem rowxs_length {m n : ℕ} (M : GenericModel m n) (i : Fin m) :
    (M.rowxs i).length = m - 1 := by
  have h := (M.row_perm i).length_eq
  rw [List.length_map, List.length_erase_of_mem (List.mem_finRange i),
    List.length_finRange] at h
  exact h

#print axioms chord_bounds
#print axioms row_mem_bounds
#print axioms rowxs_length

end Jsp404.SatScalarModel
