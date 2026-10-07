import Jsp000404.ActualMinimalBandCounterexample
import Jsp000404.PositiveRowCount

/-!
The expense of deleting any proper set of actual points is bounded directly
by the original minimum counter-cardinality. The restricted configuration is
never assumed to be critical or to preserve any original score.
-/

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualProperSubsetDeletionBudget

noncomputable section

def removedWeight {s r : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ) (pick : Fin r → Fin s) : ℕ :=
  ∑ i ∈ (Finset.univ.image pick)ᶜ, 2 ^ rowScore lam (directionRow o e c i)

def restrictionGain {s r : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ) (pick : Fin r → Fin s)
    (i : Fin r) : ℕ :=
  rowScore lam (directionRow o e (c ∘ pick) i) -
    rowScore lam (directionRow o e c (pick i))

def restrictionExpense {s r : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ) (pick : Fin r → Fin s) : ℕ :=
  ∑ i : Fin r, 2 ^ rowScore lam (directionRow o e c (pick i)) *
    (2 ^ restrictionGain o e c lam pick i - 1)

/-- Original retained mass and actual deleted mass partition the original
potential, using the injective indexing of the retained points. -/
theorem original_mass_partition {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (lam : ℝ)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick) :
    (∑ i : Fin r, 2 ^ rowScore lam (directionRow o e c (pick i))) +
      removedWeight o e c lam pick = potential lam (directionRows o e c) := by
  classical
  have hselected :
      (∑ i ∈ Finset.univ.image pick, 2 ^ rowScore lam (directionRow o e c i)) =
        ∑ i : Fin r, 2 ^ rowScore lam (directionRow o e c (pick i)) :=
    Finset.sum_image hpick.injOn
  rw [← hselected]
  exact Finset.sum_add_sum_compl (Finset.univ.image pick)
    (fun i => 2 ^ rowScore lam (directionRow o e c i))

/-- Every retained gain is actual score growth. The full restricted potential
equals original retained mass plus its weighted expense. -/
theorem actual_restriction_potential_ledger {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) {lam : ℝ} (hlam : 0 < lam) (hr : 2 ≤ r)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick) :
    potential lam (directionRows o e (c ∘ pick)) =
      (∑ i : Fin r, 2 ^ rowScore lam (directionRow o e c (pick i))) +
        restrictionExpense o e c lam pick := by
  classical
  have hscore (i : Fin r) :
      rowScore lam (directionRow o e (c ∘ pick) i) =
        rowScore lam (directionRow o e c (pick i)) +
          restrictionGain o e c lam pick i := by
    have hm := PositiveRowCount.rowScore_le_restrict o e c hlam hr pick hpick i
    dsimp only [restrictionGain]
    omega
  change (∑ i : Fin r, 2 ^ rowScore lam (directionRow o e (c ∘ pick) i)) = _
  simp only [hscore, pow_add]
  unfold restrictionExpense
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hg : 1 ≤ 2 ^ restrictionGain o e c lam pick i :=
    Nat.one_le_pow _ 2 (by decide)
  calc
    2 ^ rowScore lam (directionRow o e c (pick i)) *
        2 ^ restrictionGain o e c lam pick i =
      2 ^ rowScore lam (directionRow o e c (pick i)) *
        ((2 ^ restrictionGain o e c lam pick i - 1) + 1) := by
          rw [Nat.sub_add_cancel hg]
    _ = _ := by ring

/-- The original minimal counter supplies the cap for every proper actual
restriction leaving at least three points. -/
theorem actual_proper_restriction_cap {s r cap : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin s → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper cap s c lam)
    (hr : 3 ≤ r) (hrs : r < s)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick) :
    potential lam (directionRows o e (c ∘ pick)) ≤ cap := by
  by_contra hnot
  have hover : cap < potential lam (directionRows o e (c ∘ pick)) := by omega
  have hcard := H.minimum_card hr (c ∘ pick) lam H.scale_lower H.scale_upper
    (H.legality.restrict_injective pick hpick) hover
  omega

/-- Expense and the original excess together fit inside the actual deleted
weight. This statement retains the original counter throughout all deletions. -/
theorem actual_proper_subset_gain_budget {s r cap : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin s → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper cap s c lam)
    (hr : 3 ≤ r) (hrs : r < s)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick) :
    restrictionExpense o e c lam pick +
        (potential lam (directionRows o e c) - cap) ≤
      removedWeight o e c lam pick := by
  have hmass := original_mass_partition o e c lam pick hpick
  have hledger := actual_restriction_potential_ledger o e c
    H.legality.lam_pos (by omega : 2 ≤ r) pick hpick
  have hcap := actual_proper_restriction_cap o e H hr hrs pick hpick
  have hover := H.over_cap
  omega

/-- In an actual potential-eighteen counter to cap sixteen, every proper
deletion must pay the original two-unit excess. -/
theorem actual_F18_proper_subset_gain_budget {s r : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin s → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 s c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (hr : 3 ≤ r) (hrs : r < s)
    (pick : Fin r → Fin s) (hpick : Function.Injective pick) :
    restrictionExpense o e c lam pick + 2 ≤ removedWeight o e c lam pick := by
  simpa only [hF, show 18 - 16 = 2 by decide] using
    actual_proper_subset_gain_budget o e H hr hrs pick hpick

#print axioms original_mass_partition
#print axioms actual_restriction_potential_ledger
#print axioms actual_proper_restriction_cap
#print axioms actual_proper_subset_gain_budget
#print axioms actual_F18_proper_subset_gain_budget

end

end Jsp404.ActualProperSubsetDeletionBudget
