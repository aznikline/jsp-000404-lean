import Jsp000404.ActualMinimalBandCounterexample
import Jsp000404.FlatDeletionBudget

/-! The actual two-zero deletion budget at potential 17.

The first zero-score deletion is critical. The second deletion is bounded
directly by the original minimum counter-cardinality, not by assuming that
the intermediate potential-16 configuration is critical. All gains in the
conclusion are the actual row gains of that intermediate configuration.
-/

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualZeroPairDeletionBudget

/-- Isolate the weighted expense of a one-unit multiplicative budget. -/
theorem weighted_gain_budget_le_one {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (k g : ι → ℕ)
    (hcap : (∑ i ∈ T, 2 ^ k i * 2 ^ g i) ≤ (∑ i ∈ T, 2 ^ k i) + 1) :
    (∑ i ∈ T, 2 ^ k i * (2 ^ g i - 1)) ≤ 1 := by
  have hid : (∑ i ∈ T, 2 ^ k i * 2 ^ g i) =
      (∑ i ∈ T, 2 ^ k i * (2 ^ g i - 1)) + (∑ i ∈ T, 2 ^ k i) := by
    calc
      (∑ i ∈ T, 2 ^ k i * 2 ^ g i) =
          ∑ i ∈ T, (2 ^ k i * (2 ^ g i - 1) + 2 ^ k i) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          2 ^ k i * 2 ^ g i = 2 ^ k i * ((2 ^ g i - 1) + 1) := by
            rw [Nat.sub_add_cancel (Nat.one_le_pow _ 2 (by decide))]
          _ = _ := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := Finset.sum_add_distrib
  omega

/-- Unit lower bounds on the weights also give the unweighted expense. -/
theorem unweighted_gain_budget_le_one {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (k g : ι → ℕ)
    (hbudget : (∑ i ∈ T, 2 ^ k i * (2 ^ g i - 1)) ≤ 1) :
    (∑ i ∈ T, (2 ^ g i - 1)) ≤ 1 := by
  have hle : (∑ i ∈ T, (2 ^ g i - 1)) ≤
      ∑ i ∈ T, 2 ^ k i * (2 ^ g i - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have hw : 1 ≤ 2 ^ k i := Nat.one_le_pow _ 2 (by decide)
    simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ g i - 1) hw
  exact hle.trans hbudget

/-- A positive original score makes any positive gain cost at least two. -/
theorem positive_score_gain_eq_zero {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (k g : ι → ℕ)
    (hbudget : (∑ i ∈ T, 2 ^ k i * (2 ^ g i - 1)) ≤ 1)
    {i : ι} (hi : i ∈ T) (hk : 1 ≤ k i) : g i = 0 := by
  by_contra hnot
  have hg : 1 ≤ g i := by omega
  have hpk : 2 ^ 1 ≤ 2 ^ k i := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hpg : 2 ^ 1 ≤ 2 ^ g i := Nat.pow_le_pow_right (by decide : 0 < 2) hg
  norm_num at hpk hpg
  have hcost : 1 ≤ 2 ^ g i - 1 := by omega
  have hprod : 2 ≤ 2 ^ k i * (2 ^ g i - 1) := by
    calc
      2 = 2 * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul hpk hcost
  have hterm : 2 ^ k i * (2 ^ g i - 1) ≤
      ∑ j ∈ T, 2 ^ k j * (2 ^ g j - 1) :=
    Finset.single_le_sum (f := fun j => 2 ^ k j * (2 ^ g j - 1))
      (fun _ _ => Nat.zero_le _) hi
  omega

/-- Two actual zero-score deletions have only one unit of retained expense.
The original potential 17 is derived from the first critical zero deletion.
No deletion-cap or gain-array hypothesis is supplied by the caller. -/
theorem actual_zero_pair_deletion_budget {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0)
    (hqzero : rowScore lam (directionRow o e c (p.succAbove q)) = 0) :
    let d : Fin (s + 1) → Plane₂ := c ∘ p.succAbove
    let k : Fin (s + 1) → ℕ := fun i =>
      rowScore lam (directionRow o e c (p.succAbove i))
    let g : Fin (s + 1) → ℕ := fun i =>
      rowGain lam (directionRow o e d i) (deleteIndex o e d q i)
    potential lam (directionRows o e c) = 17 ∧
      potential lam (directionRows o e d) = 16 ∧
      (∑ i ∈ Finset.univ.erase q, 2 ^ k i) = 15 ∧
      ((∑ i ∈ Finset.univ.erase q, 2 ^ k i * 2 ^ g i) ≤
        (∑ i ∈ Finset.univ.erase q, 2 ^ k i) + 1) ∧
      (∀ i : Fin (s + 1), i ≠ q → 1 ≤ k i → g i = 0) ∧
      (∀ i : Fin (s + 1), i ≠ q → g i ≤ 1) ∧
      ((Finset.univ.erase q).filter (fun i => 1 ≤ g i)).card ≤ 1 ∧
      (∀ i : Fin (s + 1), i ≠ q → 1 ≤ g i → k i = 0) ∧
      (potential lam (directionRows o e (d ∘ q.succAbove)) = 15 ∨
        potential lam (directionRows o e (d ∘ q.succAbove)) = 16) := by
  classical
  dsimp only
  let d : Fin (s + 1) → Plane₂ := c ∘ p.succAbove
  let k : Fin (s + 1) → ℕ := fun i =>
    rowScore lam (directionRow o e c (p.succAbove i))
  let g : Fin (s + 1) → ℕ := fun i =>
    rowGain lam (directionRow o e d i) (deleteIndex o e d q i)
  let T : Finset (Fin (s + 1)) := Finset.univ.erase q
  have hmin : ∀ i : Fin (s + 2),
      rowScore lam (directionRow o e c p) ≤ rowScore lam (directionRow o e c i) := by
    intro i
    rw [hpzero]
    exact Nat.zero_le _
  have hdiv : 2 ^ rowScore lam (directionRow o e c p) ∣ 16 := by
    rw [hpzero, pow_zero]
    exact one_dvd _
  obtain ⟨hF, hfirst, _, hrows⟩ :=
    ActualMinimalBandCounterexample.actual_minimum_score_critical_form
      (s := s + 1) (by omega : 3 ≤ s + 1) o e H p hmin hdiv
  have hF17 : potential lam (directionRows o e c) = 17 := by
    simpa [hpzero] using hF
  have hfirst16 : potential lam (directionRows o e d) = 16 := hfirst
  have hrowsd (i : Fin (s + 1)) : rowScore lam (directionRow o e d i) = k i := hrows i
  have hsumFirst : (∑ i : Fin (s + 1), 2 ^ k i) = 16 := by
    simpa only [potential, exponentAt, directionRows, hrows] using hfirst
  have hkq : k q = 0 := hqzero
  have hsumT : (∑ i ∈ T, 2 ^ k i) = 15 := by
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset (Fin (s + 1))) (fun i => 2 ^ k i) (Finset.mem_univ q)
    rw [hkq, pow_zero, hsumFirst] at hsplit
    dsimp only [T]
    omega
  have hsecondCap : potential lam (directionRows o e (d ∘ q.succAbove)) ≤ 16 := by
    by_contra hnot
    have hover : 16 < potential lam (directionRows o e (d ∘ q.succAbove)) := by omega
    have hcard := H.minimum_card hs (d ∘ q.succAbove) lam
      H.scale_lower H.scale_upper ((H.legality.erase p).erase q) hover
    omega
  have hledgerRaw :=
    ActualMinimumDeletionNormalForm.actual_delete_potential_eq_sum_pow_gain
      (s := s) (by omega : 2 ≤ s) o e (c := d) H.legality.lam_pos q
  have hledger : potential lam (directionRows o e (d ∘ q.succAbove)) =
      ∑ i ∈ T, 2 ^ k i * 2 ^ g i := by
    simpa only [T, g, hrowsd] using hledgerRaw
  have hcap : (∑ i ∈ T, 2 ^ k i * 2 ^ g i) ≤ (∑ i ∈ T, 2 ^ k i) + 1 := by
    rw [hsumT, ← hledger]
    exact hsecondCap
  have hweighted := weighted_gain_budget_le_one T k g hcap
  have hunweighted := unweighted_gain_budget_le_one T k g hweighted
  have hmem (i : Fin (s + 1)) (hi : i ≠ q) : i ∈ T :=
    Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  have hpositive : ∀ i : Fin (s + 1), i ≠ q → 1 ≤ k i → g i = 0 := by
    intro i hi hk
    exact positive_score_gain_eq_zero T k g hweighted (hmem i hi) hk
  have hgain : ∀ i : Fin (s + 1), i ≠ q → g i ≤ 1 := by
    intro i hi
    exact FlatDeletionBudget.gain_le_one_of_budget T g hunweighted (hmem i hi)
  have hcard : (T.filter (fun i => 1 ≤ g i)).card ≤ 1 :=
    FlatDeletionBudget.positive_gain_card_le_one T g hunweighted
  have hsource : ∀ i : Fin (s + 1), i ≠ q → 1 ≤ g i → k i = 0 := by
    intro i hi hg
    by_contra hk
    have hkpos : 1 ≤ k i := by omega
    have hz := hpositive i hi hkpos
    omega
  have hbase : (∑ i ∈ T, 2 ^ k i) ≤ ∑ i ∈ T, 2 ^ k i * 2 ^ g i := by
    apply Finset.sum_le_sum
    intro i _
    have hp : 1 ≤ 2 ^ g i := Nat.one_le_pow _ 2 (by decide)
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ k i) hp
  have hsecondLow : 15 ≤ potential lam (directionRows o e (d ∘ q.succAbove)) := by
    rw [← hsumT, hledger]
    exact hbase
  have hsecond : potential lam (directionRows o e (d ∘ q.succAbove)) = 15 ∨
      potential lam (directionRows o e (d ∘ q.succAbove)) = 16 := by
    omega
  exact ⟨hF17, hfirst16, hsumT, hcap, hpositive, hgain, hcard, hsource, hsecond⟩

#print axioms weighted_gain_budget_le_one
#print axioms unweighted_gain_budget_le_one
#print axioms positive_score_gain_eq_zero
#print axioms actual_zero_pair_deletion_budget

end Jsp404.ActualZeroPairDeletionBudget
