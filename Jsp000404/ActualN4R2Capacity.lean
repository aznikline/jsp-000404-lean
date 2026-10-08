import Jsp000404.SixWeakAllComplete
import Jsp000404.SixDoubleAllComplete
import Jsp000404.ActualN4R2Critical22Adapter
import Jsp000404.ActualN4R2CapacityFromCrit22

/-! SOURCE_ONLY: the all62 scalar terminals and this final actual consumer
must pass their own strict and genuine normal checks before acceptance.
No unconditional R2 result is claimed while those dependencies are pending.
-/

set_option autoImplicit false
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualN4R2Capacity

theorem actual_no_critical22_six
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4) :
    ActualN4R2CapacityAssembly.NamedNoCrit22Six o e lam := by
  exact ActualN4R2Critical22Adapter.named_no_critical22_six_of_weak_closures
    SixWeakAllComplete.complete SixDoubleAllComplete.complete o e he hn hhigh

/-- Actual HIGH R2 capacity at floor four and every point count. All scalar
word coverage, critical exclusions and finite-capacity inputs are internal. -/
theorem actual_r2_capacity
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    {t : ℕ} {c : Fin t → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin t) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    {a b : Fin t} (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2) :
    potential lam (directionRows o e c) ≤ 20 := by
  exact ActualN4R2CapacityFromCrit22.actual_r2_capacity_of_crit22
    o e he hn hhigh (actual_no_critical22_six o e he hn hhigh)
    hleg v hsat hav hbv hab hda hdb

#print axioms actual_no_critical22_six
#print axioms actual_r2_capacity

end Jsp404.ActualN4R2Capacity
