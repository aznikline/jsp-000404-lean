import Jsp000404.ActualF18AllLight
import Jsp000404.ActualF18UniqueHeavyAcute
import Jsp000404.DevinF18TwoHeavyApex
import Jsp000404.ActualF18ThreeHeavy

set_option autoImplicit false

/-!
SOURCE_ONLY: whole original F18 minimum-countermodel exclusion.
The Frame supplies every original score and the heavy-count bound.
The three-heavy dependency is still awaiting its own strict/normal
verification; this assembly is not a checked overall F18 result.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualF18Complete

/-- The original n4 LOW cap16 model cannot have potential18.
All original heavy-count cases and the unique-heavy profile are derived
internally. This remains SOURCE_ONLY until all dependencies and this
consumer have passed actual strict and genuine normal checks. -/
theorem actual_F18_impossible {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  let T := ActualF18Frame.heavyIndices o e c lam
  have hbound : T.card ≤ 3 := F.heavy_count_le_three
  have hcases : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 ∨ T.card = 3 := by omega
  have hmem (q : Fin (s+1)) (hq : rowScore lam (directionRow o e c q) = 2) : q ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q,hq⟩
  rcases hcases with h0 | h1 | h2 | h3
  · have hempty : T = ∅ := Finset.card_eq_zero.mp h0
    have hall (q : Fin (s+1)) : rowScore lam (directionRow o e c q) = 1 := by
      rcases F.score_one_or_two q with hq | hq
      · exact hq
      · have hqmem := hmem q hq
        rw [hempty] at hqmem
        exact False.elim (Finset.not_mem_empty q hqmem)
    exact ActualF18AllLight.actual_F18_all_light_false o e he H hF hall
  · obtain ⟨h,hsingle⟩ := Finset.card_eq_one.mp h1
    have hhmem : h ∈ T := by rw [hsingle]; simp
    have hh : rowScore lam (directionRow o e c h) = 2 := (Finset.mem_filter.mp hhmem).2
    have hlight (q : Fin (s+1)) (hqh : q ≠ h) :
        rowScore lam (directionRow o e c q) = 1 := by
      rcases F.score_one_or_two q with hq | hq
      · exact hq
      · have hqmem := hmem q hq
        rw [hsingle,Finset.mem_singleton] at hqmem
        exact False.elim (hqh hqmem)
    exact ActualF18UniqueHeavyAcute.actual_F18_unique_heavy_false o e he H hF h hh hlight
  · exact DevinF18TwoHeavyApex.actual_F18_two_heavy_false
      o e he H hF (by simpa only [T] using h2)
  · exact ActualF18ThreeHeavy.actual_F18_three_heavy_false
      o e he H hF (by simpa only [T] using h3)

#print axioms actual_F18_impossible

end Jsp404.ActualF18Complete
