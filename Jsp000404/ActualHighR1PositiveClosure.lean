import Jsp000404.ActualHighR1SevenLowerAdapter
import Jsp000404.SevenLowerComplete

set_option autoImplicit false

/-!
SOURCE_ONLY final actual consumers. SevenLowerComplete must pass its own
independent strict and genuine normal checks before this source is validated.
The former explicit scalar-terminal parameter is filled internally here.
No unconditional claim is made while that provider is pending verification.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualHighR1PositiveClosure

/-- Original actual seven-point positive R1 profile, with no caller terminal. -/
theorem actual_seven_positive_r1_false
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 7 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 4)
    (hhigh : (1/2 : ℝ) ≤ Real.pi/lam-4)
    (v a : Fin 7) (hva : v ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (ha : rowScore lam (directionRow o e c a) = 2)
    (htail : ∀ q : Fin 7, q ≠ v → q ≠ a →
      rowScore lam (directionRow o e c q) = 1) : False :=
  ActualHighR1SevenLowerAdapter.actual_seven_positive_r1_false_of_terminal
    SevenLowerComplete.complete o e he hleg hn hhigh v a hva hsat ha htail

/-- Original positive HIGH4 minimal cap20 Model, with no caller terminal,
potential, cardinality, partition, chart, ordering or gain hypothesis. -/
theorem actual_high_r1_positive_model_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/5) (Real.pi/((4 : ℝ)+1/2)) 20 (s+1) c lam)
    (v : Fin (s+1)) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (a : Fin (s+1)) (ha : rowScore lam (directionRow o e c a) = 2)
    (hpositive : ∀ q : Fin (s+1), 1 ≤ rowScore lam (directionRow o e c q)) : False :=
  ActualHighR1SevenLowerAdapter.actual_high_r1_positive_model_false_of_terminal
    SevenLowerComplete.complete o e he H v hsat a ha hpositive

#print axioms actual_seven_positive_r1_false
#print axioms actual_high_r1_positive_model_false

end Jsp404.ActualHighR1PositiveClosure
