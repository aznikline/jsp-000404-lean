import Jsp000404.ActualN4SixSaturatedCapacity
import Jsp000404.ActualMinimumDeletionNormalForm

set_option autoImplicit false

/-!
# Actual seven-centre zero-row deletion rigidity at floor four

SOURCE_ONLY pending guarded compilation and dependency axiom audit.
The deleted configuration's capacity is supplied internally by the thin
actual six-centre theorem. Neither HIGH, uniqueness of the zero row,
a heavy row, positivity, nor a Model/capacity callback is assumed.
This theorem is an equality normal form, not a terminal contradiction.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualZeroDeletionRigidity

/-- A zero-score deletion of an actual weight-21 seven-centre configuration
with one saturated centre has weight exactly 20 and zero gain in every
surviving row. All six actual surviving scores are preserved. -/
theorem actual_seven_zero_delete_normal_form
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 7 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = 4)
    (v z : Fin 7)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hz : rowScore lam (directionRow o e c z) = 0)
    (hmass : potential lam (directionRows o e c) = 21) :
    potential lam (directionRows o e (c ∘ z.succAbove)) = 20 ∧
      (∀ i : Fin 7, i ≠ z →
        rowGain lam (directionRow o e c i) (deleteIndex o e c z i) = 0) ∧
      (∀ i : Fin 6,
        rowScore lam (directionRow o e (c ∘ z.succAbove) i) =
          rowScore lam (directionRow o e c (z.succAbove i))) := by
  classical
  have hvscore : rowScore lam (directionRow o e c v) = 3 := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos v
      (by decide : 2 ≤ 7) hn
    have hscore := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hcells
    omega
  have hvz : v ≠ z := by
    intro h
    rw [h, hz] at hvscore
    omega
  obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq hvz
  have hdeleted : Section4Legality (c ∘ z.succAbove) lam := hleg.erase z
  have hmono (i : Fin 6) :
      rowScore lam (directionRow o e c (z.succAbove i)) ≤
        rowScore lam (directionRow o e (c ∘ z.succAbove) i) :=
    PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos
      (by decide : 2 ≤ 6) z.succAbove Fin.succAbove_right_injective i
  have hsat' : rowDefect 4 lam (directionRow o e (c ∘ z.succAbove) v') = 1 := by
    have hge := hmono v'
    rw [hv', hvscore] at hge
    have hcells := rowCells_directionRow_le_of_floor_eq o e (c ∘ z.succAbove)
      hleg.lam_pos v' (by decide : 2 ≤ 6) hn
    have hscore := rowScore_eq_sub_defect lam hleg.lam_pos 4 _ hcells
    have hbound := one_le_rowDefect lam hleg.lam_pos 4 _
      (by decide : 1 ≤ 4) hcells
    omega
  have hdelete := ThinSixCapacity.actual_six_sat_capacity
    o e he hdeleted hn v' hsat'
  have hmin (i : Fin 7) :
      rowScore lam (directionRow o e c z) ≤ rowScore lam (directionRow o e c i) := by
    rw [hz]
    exact Nat.zero_le _
  have hdiv : 2 ^ rowScore lam (directionRow o e c z) ∣ 20 := by
    simp [hz]
  obtain ⟨_, hred, hgain, hpreserve⟩ :=
    ActualMinimumDeletionNormalForm.actual_minimum_delete_normal_form
      (by decide : 2 ≤ 6) o e hleg z 20 hmin hdiv (by omega) hdelete
  exact ⟨hred, hgain, hpreserve⟩

#print axioms actual_seven_zero_delete_normal_form

end Jsp404.ActualZeroDeletionRigidity
