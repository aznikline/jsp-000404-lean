import Jsp000404.N4R2BetweenTerminal
import Jsp000404.SatScalarExtraction
import Jsp000404.FivePointCapacity

/-!
Actual eight-center consumers of the complete between zero-tail model.
All directions, ranking and full original row defects come from the actual
saturated configuration. This only excludes the stated between profile;
other placements and the original all-N theorem are separate obligations.
-/

set_option autoImplicit false
set_option pp.fullNames true
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualN4BetweenZeroTailClosure

/-- No actual chart has two outer defect-two rows and five zero-score tails. -/
theorem actual_chart_between_zero_tail_impossible
    {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
    {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
    (C : SatChart o e 4 lam c v theta)
    (hdef0 : rowDefect 4 lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C 0))) = 2)
    (hdef6 : rowDefect 4 lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C 6))) = 2)
    (htails : ∀ i : Fin 7, 0 < i.val → i.val < 6 → rowDefect 4 lam
      (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C i))) = 4) :
    False := by
  have hdef (i : Fin 7) :
      SatScalarModel.rowDefect (SatScalarExtraction.model C) i = rowDefect 4 lam
        (directionRow o e c (v.succAbove (SatScalarExtraction.sigma C i))) :=
    SatScalarExtraction.model_rowDefect C (by decide) i
  exact N4R2BetweenTerminal.between_pure_tail_impossible (SatScalarExtraction.model C)
    ((hdef 0).trans hdef0) ((hdef 6).trans hdef6)
    (fun i hi0 hi6 => (hdef i).trans (htails i hi0 hi6))

/-- The actual anchor ray window and all seven ranks are constructed
internally, and the excluded profile is measured in the original reference. -/
theorem exists_actual_ranked_zero_tail_profile_exclusion
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {c : Fin 8 → Plane₂} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = 4)
    (v : Fin 8) (hsat : rowDefect 4 lam (directionRow o e c v) = 1) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin 7 → ℝ, ∃ sigma : Fin 7 → Fin 7,
      Function.Bijective sigma ∧ StrictMono (theta ∘ sigma) ∧
      (∀ i, theta i ∈ Set.Icc 0 (Real.pi - 4 * lam) ∧
        o.oangle e' (c (v.succAbove i) - c v) = (theta i : Real.Angle)) ∧
      ¬ (rowDefect 4 lam (directionRow o e c (v.succAbove (sigma 0))) = 2 ∧
        rowDefect 4 lam (directionRow o e c (v.succAbove (sigma 6))) = 2 ∧
        ∀ i : Fin 7, 0 < i.val → i.val < 6 → rowDefect 4 lam
          (directionRow o e c (v.succAbove (sigma i))) = 4) := by
  obtain ⟨e', he', theta, htheta⟩ := saturated_ray_window o e he
    (s := 7) (by decide) (by decide) hleg.lam_pos hn hleg v hsat
  let C : SatChart o e' 4 lam c v theta :=
    ⟨he', by decide, hleg.lam_pos, hn, hleg, htheta⟩
  refine ⟨e', he', theta, SatScalarExtraction.sigma C,
    SatScalarExtraction.sigma_bijective C, ?_, htheta, ?_⟩
  · intro i j hij
    change theta (SatScalarExtraction.sigma C i) < theta (SatScalarExtraction.sigma C j)
    rw [SatScalarExtraction.sigma_spec C i, SatScalarExtraction.sigma_spec C j]
    exact SatScalarExtraction.sortedTheta_strictMono C hij
  · intro hprofile
    have hreference (i : Fin 8) :
        rowDefect 4 lam (directionRow o e' c i) =
          rowDefect 4 lam (directionRow o e c i) :=
      rowDefect_directionRow_reference_eq o e' e he' he c hleg.inj i
        hleg.lam_pos (by decide) hn
    exact actual_chart_between_zero_tail_impossible C
      ((hreference _).trans hprofile.1) ((hreference _).trans hprofile.2.1)
      (fun i hi0 hi6 => (hreference _).trans (hprofile.2.2 i hi0 hi6))

#print axioms actual_chart_between_zero_tail_impossible
#print axioms exists_actual_ranked_zero_tail_profile_exclusion

end Jsp404.ActualN4BetweenZeroTailClosure
