import Jsp000404.SatScalarExtraction
import Jsp000404.SixExactFloorKernelSymbolicBetweenTerminal
import Jsp000404.ChartInvariance
import Jsp000404.FivePointCapacity

/-!
Actual six-point consumers of the uniform between exclusion.
The angle-rank permutation and saturated ray chart are constructed from
the original points. The middle row has no prescribed defect.
This excludes one actual profile; it does not prove the whole R2 capacity.
-/

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualSixBetweenClosure

/-- No actual saturated chart has defects 2,3,*,3,2 in angle order. -/
theorem actual_chart_between_impossible {n : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 6 → Plane₂} {v : Fin 6} {theta : Fin 5 → ℝ}
    (C : SatChart o e n lam c v theta) (hn4 : 4 ≤ n)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - (n : ℝ))
    (hdef0 : rowDefect n lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C 0))) = 2)
    (hdef1 : rowDefect n lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C 1))) = 3)
    (hdef3 : rowDefect n lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C 3))) = 3)
    (hdef4 : rowDefect n lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C 4))) = 2) :
    False := by
  let M := SatScalarExtraction.toModelSix (SatScalarExtraction.model C)
  have hdef (i : Fin 5) : SixModelCompression.rowDefect M i =
      rowDefect n lam
        (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C i))) :=
    (SatScalarExtraction.toModelSix_rowDefect (SatScalarExtraction.model C) i).trans
      (SatScalarExtraction.model_rowDefect C (by decide) i)
  exact SixExactFloorKernel.symbolic_between_impossible M hn4 hhigh
    ((hdef 0).trans hdef0) ((hdef 1).trans hdef1)
    ((hdef 3).trans hdef3) ((hdef 4).trans hdef4)

/-- Actual saturation supplies an angle-ordered permutation of every other
point. In that real permutation the between profile is impossible, and
the defects are measured in the caller's original reference chart. -/
theorem exists_actual_ranked_profile_exclusion {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) (hn4 : 4 ≤ n)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - (n : ℝ))
    (v : Fin 6) (hsat : rowDefect n lam (directionRow o e c v) = 1) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin 5 → ℝ, ∃ sigma : Fin 5 → Fin 5,
      Function.Bijective sigma ∧ StrictMono (theta ∘ sigma) ∧
      (∀ i, theta i ∈ Set.Icc 0 (Real.pi - (n : ℝ) * lam) ∧
        o.oangle e' (c (v.succAbove i) - c v) = (theta i : Real.Angle)) ∧
      ¬ (rowDefect n lam (directionRow o e c (v.succAbove (sigma 0))) = 2 ∧
        rowDefect n lam (directionRow o e c (v.succAbove (sigma 1))) = 3 ∧
        rowDefect n lam (directionRow o e c (v.succAbove (sigma 3))) = 3 ∧
        rowDefect n lam (directionRow o e c (v.succAbove (sigma 4))) = 2) := by
  obtain ⟨e', he', theta, htheta⟩ := saturated_ray_window o e he
    (s := 5) (by decide) (by omega) hleg.lam_pos hn hleg v hsat
  let C : SatChart o e' n lam c v theta :=
    ⟨he', by omega, hleg.lam_pos, hn, hleg, htheta⟩
  refine ⟨e', he', theta, SatScalarExtraction.sigma C,
    SatScalarExtraction.sigma_bijective C, ?_, htheta, ?_⟩
  · intro i j hij
    change theta (SatScalarExtraction.sigma C i) < theta (SatScalarExtraction.sigma C j)
    rw [SatScalarExtraction.sigma_spec C i, SatScalarExtraction.sigma_spec C j]
    exact SatScalarExtraction.sortedTheta_strictMono C hij
  · intro hprofile
    have hreference (i : Fin 6) :
        rowDefect n lam (directionRow o e' c i) =
          rowDefect n lam (directionRow o e c i) :=
      rowDefect_directionRow_reference_eq o e' e he' he c hleg.inj i
        hleg.lam_pos (by decide) hn
    exact actual_chart_between_impossible C hn4 hhigh
      ((hreference _).trans hprofile.1)
      ((hreference _).trans hprofile.2.1)
      ((hreference _).trans hprofile.2.2.1)
      ((hreference _).trans hprofile.2.2.2)

#print axioms actual_chart_between_impossible
#print axioms exists_actual_ranked_profile_exclusion

end Jsp404.ActualSixBetweenClosure
