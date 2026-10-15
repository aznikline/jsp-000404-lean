import Jsp000404.K3bGeometryPart2

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- Complement branch of the projective correspondence: a clockwise
sweep (`oangle.toReal < 0`) means the forward arc is `π − ∠uiv`. -/
theorem dirRep_arc_eq_pi_sub_angle {s : ℕ} {c : Fin s → Plane₂}
    (he : e ≠ 0) {i u v : Fin s}
    (hcu : c u ≠ c i) (hcv : c v ≠ c i)
    (hcw : (o.oangle (c u - c i) (c v - c i)).toReal < 0) :
    ∠ (c u) (c i) (c v) =
      Real.pi - cyclicDiff (dirRep o e c i u) (dirRep o e c i v) := by
  have hangle : ∠ (c u) (c i) (c v) =
      |(o.oangle (c u - c i) (c v - c i)).toReal| := by
    show InnerProductGeometry.angle (c u -ᵥ c i) (c v -ᵥ c i) = _
    rw [vsub_eq_sub, vsub_eq_sub]
    exact o.angle_eq_abs_oangle_toReal
      (sub_ne_zero.mpr hcu) (sub_ne_zero.mpr hcv)
  have hrep : linRep (o.oangle (c u - c i) (c v - c i)) =
      Real.pi - ∠ (c u) (c i) (c v) := by
    unfold linRep
    rw [if_pos hcw, hangle, abs_of_neg hcw]
    ring
  rw [cyclicDiff_dirRep o e c he hcu hcv, hrep]
  ring

/-- On `[0, π)`, the forward arc is zero only for equal endpoints. -/
theorem cyclicDiff_eq_zero_of_Ico {a b : ℝ}
    (ha : a ∈ Set.Ico 0 Real.pi) (hb : b ∈ Set.Ico 0 Real.pi)
    (h : cyclicDiff a b = 0) : a = b := by
  by_contra hne
  obtain ⟨-, ha1⟩ := ha; obtain ⟨hb0, -⟩ := hb
  rw [cyclicDiff, if_neg hne] at h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos hlt] at h; linarith
  · rw [if_neg (not_lt.mpr hgt.le)] at h; linarith [Real.pi_pos]

/-- `b` on the forward arc `a → c` splits it. -/
theorem cyclicDiff_eq_add_of_le {a b c : ℝ}
    (ha : a ∈ Set.Ico 0 Real.pi) (hb : b ∈ Set.Ico 0 Real.pi)
    (hc : c ∈ Set.Ico 0 Real.pi)
    (h : cyclicDiff a b ≤ cyclicDiff a c) :
    cyclicDiff a c = cyclicDiff a b + cyclicDiff b c := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hc0, hc1⟩ := hc
  rcases eq_or_ne a c with rfl | hac
  · have haa : cyclicDiff a a = (0 : ℝ) := by simp [cyclicDiff]
    rw [haa] at h
    have hab0 : cyclicDiff a b = 0 :=
      le_antisymm h (cyclicDiff_nonneg ha1 hb0)
    have hab : a = b :=
      cyclicDiff_eq_zero_of_Ico ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hab0
    subst hab; simp [cyclicDiff]
  rcases eq_or_ne a b with rfl | hab
  · simp [cyclicDiff]
  rcases eq_or_ne b c with rfl | hbc
  · have hbb : cyclicDiff b b = (0 : ℝ) := by simp [cyclicDiff]
    rw [hbb]; simp
  rcases lt_or_gt_of_ne hab with h12 | h21 <;>
    rcases lt_or_gt_of_ne hac with h13 | h31 <;>
    rcases lt_or_gt_of_ne hbc with h23 | h32 <;>
    unfold cyclicDiff at h ⊢ <;>
    split_ifs at h ⊢ <;> (try contradiction) <;>
    linarith [Real.pi_pos]

/-- The two complementary arcs between distinct points sum to `π`. -/
theorem cyclicDiff_add_rev {a b : ℝ} (h : a ≠ b) :
    cyclicDiff a b + cyclicDiff b a = Real.pi := by
  unfold cyclicDiff
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [if_neg h, if_pos hlt, if_neg h.symm,
      if_neg (not_lt.mpr hlt.le)]
    linarith [Real.pi_pos]
  · rw [if_neg h, if_neg (not_lt.mpr hgt.le), if_neg h.symm,
      if_pos hgt]
    linarith [Real.pi_pos]

/-- Four-term cyclic chain: with `x2, x3, x4` in that order on the
forward arc from `x1`, the four consecutive arcs telescope to `π`.
This is the model's `order` datum for a 4-gap fan. -/
theorem cyclicDiff_chain4 {x1 x2 x3 x4 : ℝ}
    (h1 : x1 ∈ Set.Ico 0 Real.pi) (h2 : x2 ∈ Set.Ico 0 Real.pi)
    (h3 : x3 ∈ Set.Ico 0 Real.pi) (h4 : x4 ∈ Set.Ico 0 Real.pi)
    (h23 : cyclicDiff x1 x2 ≤ cyclicDiff x1 x3)
    (h34 : cyclicDiff x1 x3 ≤ cyclicDiff x1 x4)
    (h14 : 0 < cyclicDiff x1 x4) :
    cyclicDiff x1 x2 + cyclicDiff x2 x3 + cyclicDiff x3 x4 +
      cyclicDiff x4 x1 = Real.pi := by
  have e1 := cyclicDiff_eq_add_of_le h1 h2 h3 h23
  have e2 := cyclicDiff_eq_add_of_le h1 h3 h4 h34
  have hne : x1 ≠ x4 := by
    intro he
    rw [he, show cyclicDiff x4 x4 = 0 from if_pos rfl] at h14
    exact lt_irrefl _ h14
  have e3 := cyclicDiff_add_rev hne
  linarith


end Jsp404
