import Jsp000404.ActualN4R2CriticalClosure
import Jsp000404.ActualN4R2CapacityAssembly

/-! SOURCE_ONLY conditional actual strip-four HIGH R2 capacity consumer.

The actual potential-21 producer is supplied internally from the separately
checked original-point closure. The sole remaining critical input is the
explicit actual six-point potential-22 profile exclusion. Neither that input
nor unconditional R2 capacity is certified by this source-only wrapper.
-/

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualN4R2CapacityFromCrit22

private theorem produced_no_critical21
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4) :
    ActualN4R2CapacityAssembly.NamedNoCrit21 o e lam := by
  intro s hs c hleg v a b hva hvb hab hv ha hb hF
  exact ActualN4R2CriticalClosure.actual_n4_high_critical21_impossible
    o e he hs c hleg hn hhigh (a := v) (b := a) (d := b)
    hva hvb hab hv ha hb hF

/-- Actual R2 capacity at arbitrary point count, conditional only on the
original six-point potential-22 profile exclusion. The caller supplies no
potential-21 exclusion, minimum model, finite capacity, word, or certificate. -/
theorem actual_r2_capacity_of_crit22
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    (h22 : ActualN4R2CapacityAssembly.NamedNoCrit22Six o e lam)
    {t : ℕ} {c : Fin t → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin t) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    {a b : Fin t} (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2) :
    potential lam (directionRows o e c) ≤ 20 := by
  exact ActualN4R2CapacityAssembly.actual_r2_capacity_of_critical_exclusions
    o e he hn hhigh (produced_no_critical21 o e he hn hhigh) h22
    hleg v hsat hav hbv hab hda hdb

#print axioms actual_r2_capacity_of_crit22
end Jsp404.ActualN4R2CapacityFromCrit22
