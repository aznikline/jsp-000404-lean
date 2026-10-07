import Jsp000404.ActualMixedRigidCardinality
import Jsp000404.ActualRigidCardinality
import Jsp000404.ActualHullWindowScoreLower
import Jsp000404.ActualPotentialInflation
import Jsp000404.SecondStrip

set_option autoImplicit false

/-! Actual geometry of four original rigid centers.
All doubled-scale scores and hull windows are outputs of the producer.
The angle lower bound concerns each complete subset-hull window; it
is not a lower bound on every angle of every selected triangle.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualRigidFourGeometry

/-- Output data for the actual four-point restriction at twice the
original scale. No caller supplies any of these score or hull facts. -/
structure Data {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (lam : ℝ) (pick : Fin 4 → Fin s) where
  double_legality : Section4Legality (c ∘ pick) (2*lam)
  double_floor : Nat.floor (Real.pi/(2*lam)) = 2
  double_potential : potential (2*lam) (directionRows o e (c ∘ pick)) = 4
  double_score_zero : ∀ i : Fin 4, rowScore (2*lam) (directionRow o e (c ∘ pick) i) = 0
  selected_hull : ∀ i : Fin 4, IsHullVertex (c ∘ pick) i
  window : ∀ i : Fin 4, ActualHullRayWindow.Window o (c ∘ pick) (2*lam) i
  window_lower : ∀ i : Fin 4, 2*lam ≤ (window i).width

private theorem four_scores_zero_of_potential_le_four
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (d : Fin 4 → Plane₂) (mu : ℝ)
    (hcap : potential mu (directionRows o e d) ≤ 4) :
    potential mu (directionRows o e d) = 4 ∧
      ∀ i : Fin 4, rowScore mu (directionRow o e d i) = 0 := by
  have hge := ActualPotentialInflation.card_le_potential mu (directionRows o e d)
  have hmass : potential mu (directionRows o e d) = 4 := by omega
  let w (i : Fin 4) : ℕ := 2 ^ rowScore mu (directionRow o e d i)
  have hsum : (∑ i : Fin 4, (1 : ℕ)) = ∑ i : Fin 4, w i := by
    change (∑ _i : Fin 4, (1 : ℕ)) = potential mu (directionRows o e d)
    simpa using hmass.symm
  have hterms : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (1 : ℕ) = w i :=
    (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun _i : Fin 4 => (1 : ℕ)) (g := w)
      (fun i _ => Nat.one_le_two_pow)).mp hsum
  refine ⟨hmass,?_⟩
  intro i
  have hpow : 2 ^ rowScore mu (directionRow o e d i) = 1 := (hterms i (Finset.mem_univ i)).symm
  exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (by simpa using hpow)

/-- The original n4 LOW model and four selected original rigid profiles
produce actual doubled legality, zero doubled scores, the full selected
hull, and actual selected hull windows of width at least twice lambda. -/
theorem actual_rigid_four_geometry {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (pick : Fin 4 → Fin s) (hpick : Function.Injective pick)
    (hselected : ∀ a : Fin 4,
      (¬ IsHullVertex c (pick a) ∧ rowScore lam (directionRow o e c (pick a)) = 1) ∨
      (rowScore lam (directionRow o e c (pick a)) = 2 ∧
        ∃ u v : Fin s, u ≠ pick a ∧ v ≠ pick a ∧ u ≠ v ∧
          2*lam ≤ ∠ (c u) (c (pick a)) (c v))) :
    Nonempty (Data o e c lam pick) := by
  classical
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  have hlo : 2*Real.pi/9 < lam := by rw [← hrho]; exact H.scale_lower
  have hgap : ∀ i j k : Fin 4, i ≠ j → j ≠ k → i ≠ k →
      ∠ ((c ∘ pick) i) ((c ∘ pick) j) ((c ∘ pick) k) ≤ Real.pi-4*lam ∨
        2*lam ≤ ∠ ((c ∘ pick) i) ((c ∘ pick) j) ((c ∘ pick) k) := by
    intro i j k hij hjk _hik
    have hij' : pick i ≠ pick j := hpick.ne hij
    have hkj' : pick k ≠ pick j := (hpick.ne hjk).symm
    rcases hselected j with ⟨hnot,hscore⟩ | ⟨hscore,hwide⟩
    · exact ActualInteriorOneAngleGap.actual_interior_one_angle_gap
        (by have := H.card_ge_three; omega) o e he H.legality hlo
        (pick j) hnot hscore hij' hkj'
    · exact ActualMixedRigidCardinality.actual_heavy_large_angle_gap
        H.card_ge_three o e he H.legality hlo H.scale_upper
        (pick j) hscore hwide (pick i) (pick k) hij' hkj'
  have hleg := H.legality.restrict_injective pick hpick
  have hdouble := ActualRigidCardinality.legality_at_double_scale hleg hlo hgap
  have hmu : 0 < 2*lam := hdouble.lam_pos
  have hratio0 : 0 ≤ Real.pi/(2*lam) := div_nonneg Real.pi_pos.le hmu.le
  have hratioLo : (2 : ℝ) ≤ Real.pi/(2*lam) :=
    (le_div_iff₀ hmu).mpr (by linarith [H.scale_upper])
  have hratioHi : Real.pi/(2*lam) < (9/4 : ℝ) :=
    (div_lt_iff₀ hmu).mpr (by linarith)
  have hfloor : Nat.floor (Real.pi/(2*lam)) = 2 := by
    apply (Nat.floor_eq_iff hratio0).mpr
    constructor
    · simpa using hratioLo
    · norm_num
      linarith
  have hdelta : Real.pi/(2*lam)-2 < 1/2 := by linarith
  have hcap := potential_le_four_of_second_strip_low o e he
    (by decide : 2 ≤ 4) hmu hfloor hdelta hdouble
  obtain ⟨hmass,hscores⟩ := four_scores_zero_of_potential_le_four
    o e (c ∘ pick) (2*lam) hcap
  have hhull (i : Fin 4) : IsHullVertex (c ∘ pick) i := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e (c ∘ pick) hmu i
      (by decide : 2 ≤ 4) hfloor
    have hdef := rowDefect_le (2*lam) hmu 2 (directionRow o e (c ∘ pick) i) hcells
    exact FullHullInteriorDefect.low_defect_is_full_hull_vertex
      o e he hdouble hfloor i hdef
  have hex (i : Fin 4) : Nonempty (ActualHullRayWindow.Window o (c ∘ pick) (2*lam) i) :=
    ActualHullRayWindow.exists_actual_hull_ray_window o (by decide : 3 ≤ 4) hdouble i (hhull i)
  let window (i : Fin 4) := Classical.choice (hex i)
  have hwindow (i : Fin 4) : 2*lam ≤ (window i).width := by
    let W := window i
    have hpair := hgap W.left i W.right W.left_ne_center
      W.right_ne_center.symm W.boundary_distinct
    rw [← W.width_eq_actual_angle] at hpair
    rcases hpair with hsmall | hlarge
    · have hpos : 1 ≤ rowScore (2*lam) (directionRow o e (c ∘ pick) i) := by
        simpa using ActualHullWindowScoreLower.rowScore_ge_sub_one_of_actual_window
          o e he hdouble W (mu := 2*lam) hmu 2 (by decide : 1 ≤ 2)
          (by nlinarith : W.width ≤ Real.pi-(2 : ℝ)*(2*lam))
      have hz := hscores i
      omega
    · exact hlarge
  exact ⟨{
    double_legality := hdouble
    double_floor := hfloor
    double_potential := hmass
    double_score_zero := hscores
    selected_hull := hhull
    window := window
    window_lower := hwindow }⟩

#print axioms actual_rigid_four_geometry

end Jsp404.ActualRigidFourGeometry
