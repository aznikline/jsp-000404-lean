import Jsp000404.ActualF18Frame
import Jsp000404.ActualHullSmallScoreTypes
import Jsp000404.ActualHullConeDeletion

/-!
Candidate actual F18 light-hull producer. Verification is recorded separately.
The original minimum-counter normal form excludes the narrow LB cone, so
each original hull light point internally supplies an actual LI two-clump
certificate. No caller supplies a window, clump, or zero-gain certificate.
-/

set_option autoImplicit false
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualF18LightHullClumps

theorem exists_actual_F18_hull_light_clumps {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s + 1)) (hp : IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1) :
    Nonempty (Sigma fun W : ActualHullRayWindow.Window o c lam p =>
      ActualHullSmallScoreTypes.Clumps W 1 (2 * lam) (Real.pi - 3 * lam)) := by
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  have hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c p) ≤ rowScore lam (directionRow o e c i) := by
    intro i
    have hi := F.score_one_or_two i
    omega
  have hdiv : 2 ^ rowScore lam (directionRow o e c p) ∣ 16 := by
    norm_num [hscore]
  obtain ⟨_, _, hzero, _⟩ :=
    ActualMinimalBandCounterexample.actual_minimum_score_critical_form hs o e H p hmin hdiv
  obtain ⟨⟨W, kind⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_one_type
    (by omega : 3 ≤ s + 1) o e he H.legality p hp hscore
  cases kind with
  | LB _ hwidth =>
      obtain ⟨u, hu, hcone⟩ := ActualHullConeDeletion.exists_common_cone_of_actual_window
        o H.legality p W hwidth
      exact False.elim ((ConeDeletionProgress.not_common_cone_of_zero_incoming
        (by omega : 2 ≤ s) o e he H.legality p hzero u hu) hcone)
  | LI _ _ clumps => exact ⟨⟨W, clumps⟩⟩

#print axioms exists_actual_F18_hull_light_clumps

end Jsp404.ActualF18LightHullClumps
