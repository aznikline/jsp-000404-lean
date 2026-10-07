import Jsp000404.ActualHullSmallScoreTypes

set_option autoImplicit false

/-!
Actual physical window width gives an actual row-score lower bound.

The score scale may differ from the scale recorded by the physical Window.
This supports both a narrow retained clump at the original scale and the
double-scale rigid-row application. No caller supplies a gap or score bound.

Prepared statically; verification is recorded separately.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualHullWindowScoreLower

/-- Repackage an already actual Window using only its public fields. This
avoids references to private full-row lemmas in the checked Types module. -/
private noncomputable def supportOfWindow {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (hlam : 0 < lam) : ActualHullSmallScoreTypes.Support o c lam p := by
  classical
  let l := directionRow o W.base c p
  have hdir (j : Fin s) (hj : j ≠ p) :
      dirRep o W.base c p j = W.theta j := by
    unfold dirRep
    rw [W.actual_direction j hj]
    exact (eq_linRep_of_int_pi
      ⟨(W.theta_mem j hj).1, ((W.theta_mem j hj).2).trans_lt W.width_lt_pi⟩
      ⟨0, by simp⟩).symm
  have hmem : ∀ x ∈ l, x ∈ Set.Icc 0 W.width := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_directionRow o W.base c).mp hx
    rw [hdir j hj]
    exact W.theta_mem j hj
  have hzero : (0 : ℝ) ∈ l := by
    apply (mem_directionRow o W.base c).mpr
    refine ⟨W.left, W.left_ne_center, ?_⟩
    rw [hdir W.left W.left_ne_center, W.left_coordinate]
  have hwidth : W.width ∈ l := by
    apply (mem_directionRow o W.base c).mpr
    refine ⟨W.right, W.right_ne_center, ?_⟩
    rw [hdir W.right W.right_ne_center, W.right_coordinate]
  have hne : l ≠ [] := List.ne_nil_of_mem hzero
  have hsort : l.SortedLE := directionRow_sorted o W.base c p
  have hhead : l.head hne = 0 := by
    have hlow := (hmem _ (List.head_mem hne)).1
    have hhigh : l.head hne ≤ 0 := by simpa using hsort.pairwise.rel_head hzero
    exact le_antisymm hhigh hlow
  have hlast : l.getLast hne = W.width := by
    have hhigh := (hmem _ (List.getLast_mem hne)).2
    have hlow : W.width ≤ l.getLast hne := by
      simpa using hsort.pairwise.rel_getLast hwidth
    exact le_antisymm hhigh hlow
  have hwrap : wrapGap l hne = Real.pi - W.width := by
    have hnot : ¬ ∀ x ∈ l, x = l.head hne := by
      intro h
      have h := h W.width hwidth
      rw [hhead] at h
      linarith [W.width_pos]
    rw [wrapGap, if_neg hnot, hhead, hlast]
    simp [cyclicDiff, ne_of_gt W.width_pos, not_lt_of_ge W.width_pos.le]
  exact {
    window := W
    nonempty := hne
    dirRep_eq := hdir
    head_eq := hhead
    last_eq := hlast
    wrap_eq := hwrap
    wrap_mem := by
      change Real.pi - W.width ∈ cycGaps l
      rw [cycGaps_eq_map_append_wrap l hne, hwrap]
      exact List.mem_append_right _ (by simp)
    outside_ge_scale := by linarith [W.width_le_legality]
    outside_floor_pos := (one_le_floor_iff_ge lam _ hlam).mpr
      (by linarith [W.width_le_legality]) }

/-- The certified original wrap gap supplies the bound at any positive
score scale. Injectivity is used only for changing the actual reference. -/
theorem rowScore_ge_sub_one_of_actual_support {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {windowLam : ℝ} {p : Fin s}
    (S : ActualHullSmallScoreTypes.Support o c windowLam p)
    (hinj : Function.Injective c) {mu : ℝ} (hmu : 0 < mu)
    (k : ℕ) (hk : 1 ≤ k)
    (hwidth : S.window.width ≤ Real.pi - (k : ℝ) * mu) :
    k - 1 ≤ rowScore mu (directionRow o e c p) := by
  have hgap : (k : ℝ) * mu ≤ Real.pi - S.window.width := by linarith
  have hfloor : k ≤ ⌊(Real.pi - S.window.width) / mu⌋₊ :=
    (Nat.le_floor_iff' (by omega : k ≠ 0)).mpr ((le_div_iff₀ hmu).mpr hgap)
  have hscore : k - 1 ≤ gapScore mu (Real.pi - S.window.width) := by
    unfold gapScore
    omega
  have hterm : gapScore mu (Real.pi - S.window.width) ≤
      rowScore mu (directionRow o S.window.base c p) :=
    List.le_sum_of_mem (List.mem_map.mpr
      ⟨Real.pi - S.window.width, S.wrap_mem, rfl⟩)
  rw [rowScore_directionRow_reference_eq o e S.window.base he
    S.window.base_ne_zero c hinj p mu]
  exact hscore.trans hterm

/-- A caller supplies the actual physical Window, not an abstract gap or
the desired score conclusion. Its complete-row support is built internally. -/
theorem rowScore_ge_sub_one_of_actual_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {windowLam : ℝ} {p : Fin s}
    (hleg : Section4Legality c windowLam)
    (W : ActualHullRayWindow.Window o c windowLam p)
    {mu : ℝ} (hmu : 0 < mu) (k : ℕ) (hk : 1 ≤ k)
    (hwidth : W.width ≤ Real.pi - (k : ℝ) * mu) :
    k - 1 ≤ rowScore mu (directionRow o e c p) := by
  exact rowScore_ge_sub_one_of_actual_support o e he
    (supportOfWindow W hleg.lam_pos) hleg.inj hmu k hk hwidth

/-- The retained R-width clump gives score at least three. No floor-four
premise or inherited criticality of a restricted configuration is used. -/
theorem rowScore_ge_three_of_remainder_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {windowLam : ℝ} {p : Fin s}
    (hleg : Section4Legality c windowLam)
    (W : ActualHullRayWindow.Window o c windowLam p)
    {mu : ℝ} (hmu : 0 < mu)
    (hwidth : W.width ≤ Real.pi - 4 * mu) :
    3 ≤ rowScore mu (directionRow o e c p) := by
  simpa using rowScore_ge_sub_one_of_actual_window o e he hleg W hmu
    4 (by decide) (by simpa using hwidth)

#print axioms rowScore_ge_sub_one_of_actual_support
#print axioms rowScore_ge_sub_one_of_actual_window
#print axioms rowScore_ge_three_of_remainder_window

end Jsp404.ActualHullWindowScoreLower
