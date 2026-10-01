import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Jsp000404.Statement

/-!
Checked arithmetic reductions for the AIR completion plan.
These are not the missing arbitrary-configuration geometric capacity theorem.
In this file `defect` means geometric `n - rowScore`, not skeleton deficit.
-/

namespace Jsp404.AirDerived

open scoped EuclideanGeometry

theorem tail_weight_le {n d : ℕ} (hd : 3 ≤ d) :
    2 ^ (n - d) ≤ 2 ^ (n - 3) := by
  apply Nat.pow_le_pow_right (by omega)
  omega

theorem tail_budget_of_small_card {α : Type*} [DecidableEq α]
    (T : Finset α) (defect : α → ℕ) {n r : ℕ}
    (hn : 3 ≤ n) (hdef : ∀ i ∈ T, 3 ≤ defect i)
    (hcard : T.card ≤ 2 * (3 - r)) :
    ∑ i ∈ T, 2 ^ (n - defect i) ≤ (3 - r) * 2 ^ (n - 2) := by
  have hexp : n - 2 = (n - 3) + 1 := by omega
  calc
    ∑ i ∈ T, 2 ^ (n - defect i)
        ≤ ∑ _i ∈ T, 2 ^ (n - 3) :=
      Finset.sum_le_sum fun i hi => tail_weight_le (hdef i hi)
    _ = T.card * 2 ^ (n - 3) := by simp
    _ ≤ (2 * (3 - r)) * 2 ^ (n - 3) := Nat.mul_le_mul_right _ hcard
    _ = (3 - r) * 2 ^ (n - 2) := by rw [hexp, pow_succ]; ring

theorem high_cap_of_tail_budget {F tail Q r : ℕ}
    (hr : r ≤ 3) (hF : F = 2 * Q + r * Q + tail)
    (htail : tail ≤ (3 - r) * Q) : F ≤ 5 * Q := by
  have hcoeff : r + (3 - r) = 3 := by omega
  calc
    F = 2 * Q + r * Q + tail := hF
    _ ≤ 2 * Q + r * Q + (3 - r) * Q := Nat.add_le_add_left htail _
    _ = 5 * Q := by nlinarith

/-- A positive dyadic excess bounded by its least lattice unit is exactly
that unit. Divisibility must be established from the actual row powers. -/
theorem minimal_excess_eq_least_weight {F cap least : ℕ}
    (hFdiv : least ∣ F) (hcapdiv : least ∣ cap)
    (hover : cap < F) (hupper : F ≤ cap + least) :
    F = cap + least := by
  have hdiv : least ∣ F - cap := Nat.dvd_sub hFdiv hcapdiv
  have hpositive : 0 < F - cap := by omega
  have hleast : least ≤ F - cap := Nat.le_of_dvd hpositive hdiv
  omega

/-- Once the excess equals a minimum victim weight, any deletion capped by
the induction hypothesis must have zero aggregate positive gain. -/
theorem aggregate_gain_eq_zero {F cap least gain : ℕ}
    (hexcess : F = cap + least) (hdelete : F - least + gain ≤ cap) :
    gain = 0 := by omega

/-- An original-point lower bound at a jump cardinality transfers to every
larger ordinary configuration by taking a genuine distinct subconfiguration.
This is independent of any weighted geometric capacity assumption. -/
theorem lower_bound_mono_by_take {M N : ℕ} {theta : ℝ}
    (hM3 : 3 ≤ M) (hMN : M ≤ N)
    (hM : ∀ D : PtCfg, D.pts.length = M →
      ∃ p q r : Plane₂, p ∈ D.pts ∧ q ∈ D.pts ∧ r ∈ D.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ theta ≤ ∠ p q r) :
    ∀ C : PtCfg, C.pts.length = N →
      ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ theta ≤ ∠ p q r := by
  intro C hlen
  let D : PtCfg := {
    pts := C.pts.take M
    nodup := List.Pairwise.sublist (List.take_sublist M C.pts) C.nodup
    len := by simpa [List.length_take, hlen, Nat.min_eq_left hMN] using hM3
  }
  have hDlen : D.pts.length = M := by
    simp [D, List.length_take, hlen, Nat.min_eq_left hMN]
  obtain ⟨p, q, r, hp, hq, hr, hpq, hrq, hpr, hangle⟩ := hM D hDlen
  exact ⟨p, q, r, List.mem_of_mem_take hp, List.mem_of_mem_take hq,
    List.mem_of_mem_take hr, hpq, hrq, hpr, hangle⟩

#print axioms tail_budget_of_small_card
#print axioms high_cap_of_tail_budget
#print axioms minimal_excess_eq_least_weight
#print axioms aggregate_gain_eq_zero
#print axioms lower_bound_mono_by_take

end Jsp404.AirDerived
