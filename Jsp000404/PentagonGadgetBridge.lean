import Jsp000404.GeomSkeleton
import Jsp000404.GadgetCounterexample
import Jsp000404.GeometricDeletion

/-! # Pentagon result → `GadgetSelectionHighP` bridge

The opponent's 2026-09-23 snapshot proves, for any five-centre finite
cluster model with `1 ≤ t < 3` and angle cap `(1 - 1/t)·π`, that the
total label count is exactly five.  When `t < 5/2` the angle bound is
impossible.  Here `t = π / λ` is the same parameter that gives
`n = ⌊π / λ⌋₊` and `δ = t - n` in the gadget pipeline.

This file records the interface between that geometric fact and the
skeleton-level `GadgetSelectionHighP 5 2` proposition.  The geometric
input itself (`opponent_pentagon_high_bound`) is left as an open
obligation, to be discharged by porting the opponent's convex-position
/ exterior-angle / Radon argument or by constructing the gadget directly.
-/

namespace Jsp404

open scoped EuclideanGeometry

noncomputable section

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
  (c : Fin 5 → Plane₂) (lam : ℝ)

/-- Geometric input from the opponent's 9.23 pentagon-order development:
    any legal 5-point configuration with `⌊π/λ⌋₊ = 2` and `π/λ < 3` has
    Section-4 potential at most `5`.  This is exactly the high-band cap
    `2^2 + 2^{0}` for `n = 2`.  The proof uses convex independence,
    strict separation, slope sorting, and the exterior-angle budget
    (`exterior_sum = 2`).  It is open here because the opponent's code
    lives in a separate namespace/project. -/
theorem opponent_pentagon_high_bound
    (hlam : 0 < lam) (he : e ≠ 0)
    (hleg : Section4Legality c lam)
    (hn : ⌊Real.pi / lam⌋₊ = 2) (ht3 : Real.pi / lam < 3) :
    potential lam (directionRows o e c) ≤ 5 := by
  sorry

/-- For `s = 5`, `n = 2`, every geometric bridge skeleton satisfies
    `W ≤ 5/2`.  Hence `GadgetSelectionHighP` is vacuously true on the
    geometric subcase: the hypothesis `W > 5/2` cannot be met. -/
theorem pentagonHigh_geometric_vacuous
    (hlam : 0 < lam) (he : e ≠ 0)
    (hleg : Section4Legality c lam)
    (hn : ⌊Real.pi / lam⌋₊ = 2) (ht3 : Real.pi / lam < 3) :
    (bridgeSkeleton o e c lam (show 2 ≤ (5 : ℕ) by norm_num)).W 2 ≤ (5 : ℚ) / 2 := by
  have hw := bridgeSkeleton_W o e c lam 2 hlam
    (show 2 ≤ (5 : ℕ) by norm_num) hn (by norm_num)
  rw [hw]
  have hpow : (2 : ℚ) ^ (2 - 1 : ℕ) = 2 := by norm_num
  rw [hpow]
  have hpot := opponent_pentagon_high_bound o e c lam hlam he hleg hn ht3
  have hQ : ((potential lam (directionRows o e c) : ℕ) : ℚ) ≤ (5 : ℚ) := by
    exact_mod_cast hpot
  linarith

/-- The opponent's pentagon result supplies `GadgetSelectionHighP 5 2`
    for all bridge skeletons arising from a legal 5-point configuration.
    The full `GadgetSelectionHighP` still requires the same statement for
    arbitrary proper consistent `Skeleton 5`, not only geometric ones. -/
theorem pentagonGadgetHighP_geometric
    (hlam : 0 < lam) (he : e ≠ 0)
    (hleg : Section4Legality c lam)
    (hn : ⌊Real.pi / lam⌋₊ = 2) (ht3 : Real.pi / lam < 3)
    (_r : Fin 5 → Fin 4 → ℝ) (_δ : ℝ)
    (_hA : ModeA 2 (bridgeSkeleton o e c lam (show 2 ≤ (5 : ℕ) by norm_num)) _r _δ)
    (_hδ0 : 0 ≤ _δ) (_hδ1 : _δ < 1)
    (hW : (5 : ℚ) / 2 < (bridgeSkeleton o e c lam (show 2 ≤ (5 : ℕ) by norm_num)).W 2) :
    ∃ g : Gadget 5, g.Valid 2 (bridgeSkeleton o e c lam (show 2 ≤ (5 : ℕ) by norm_num)) ∧
      (1 : ℚ) ≤ g.bound 2 (bridgeSkeleton o e c lam (show 2 ≤ (5 : ℕ) by norm_num)) := by
  have hle := pentagonHigh_geometric_vacuous o e c lam hlam he hleg hn ht3
  linarith

end

end Jsp404
