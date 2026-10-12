import Jsp000404.ConeDeletionProgress
import Jsp000404.FivePointCapacity

/-!
# The actual fixed-minimum deletion normal form

The deletion cap below is a hypothesis about one actual configuration
`c ∘ q.succAbove`. All gains are the original row gains for that fixed
deleted point `q`. No capacity theorem, same-strip cardinal bound, or gain
array shared across different deletions is assumed.

The existing dyadic arithmetic is connected to the actual row deletion
identity. Least original score and divisibility of the explicit cap pin
the excess to the least weight and force every surviving actual gain to
zero. The common-cone obstruction is then a proved geometric consequence.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualMinimumDeletionNormalForm

/-- Exact multiplicative ledger for deleting one actual point. -/
theorem actual_delete_potential_eq_sum_pow_gain {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (q : Fin (s + 1)) :
    potential lam (directionRows o e (c ∘ q.succAbove)) =
      ∑ i ∈ Finset.univ.erase q,
        2 ^ rowScore lam (directionRow o e c i) *
          2 ^ rowGain lam (directionRow o e c i) (deleteIndex o e c q i) := by
  classical
  have hpe : potentialErase lam (fun v i => deleteIndex o e c v i) q
        (directionRows o e c) =
      ∑ i ∈ Finset.univ.erase q,
        2 ^ rowScore lam ((directionRow o e c i).eraseIdx (deleteIndex o e c q i)) := by
    unfold potentialErase directionRows
    rw [Finset.sum_ite]
    simp only [Finset.filter_eq', Finset.mem_univ, ite_true,
      Finset.sum_singleton, Finset.filter_ne']
    simp
  rw [potential_sub_config o e q lam, hpe]
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i ≠ q := (Finset.mem_erase.mp hi).1
  rw [rowScore_eraseIdx' hlam (directionRow_sorted o e c i)
    (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
    (deleteIndex_lt o e c hiq)
    (by rw [directionRow_length o e c i]; omega), pow_add]

/-- One actual minimum-score deletion below a divisible explicit cap
forces exact excess, exact deleted potential, and all actual gains zero. -/
theorem actual_minimum_delete_normal_form {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (q : Fin (s + 1)) (cap : ℕ)
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i))
    (hdiv : 2 ^ rowScore lam (directionRow o e c q) ∣ cap)
    (hover : cap < potential lam (directionRows o e c))
    (hdelete : potential lam (directionRows o e (c ∘ q.succAbove)) ≤ cap) :
    potential lam (directionRows o e c) =
        cap + 2 ^ rowScore lam (directionRow o e c q) ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = cap ∧
      (∀ i : Fin (s + 1), i ≠ q →
        rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0) ∧
      (∀ i : Fin s,
        rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
          rowScore lam (directionRow o e c (q.succAbove i))) := by
  classical
  let w (i : Fin (s + 1)) : ℕ := 2 ^ rowScore lam (directionRow o e c i)
  let g (i : Fin (s + 1)) : ℕ :=
    rowGain lam (directionRow o e c i) (deleteIndex o e c q i)
  have hledger := actual_delete_potential_eq_sum_pow_gain hs o e (c := c) hleg.lam_pos q
  have hcap : ∑ i ∈ Finset.univ.erase q, w i * 2 ^ g i ≤ cap := by
    rw [← hledger]
    exact hdelete
  have hdvd : ∀ i ∈ (Finset.univ : Finset (Fin (s + 1))), w q ∣ w i := by
    intro i _
    exact pow_dvd_pow 2 (hmin i)
  obtain ⟨hF, hgain, hred⟩ := minimal_excess_single_delete
    (Finset.univ : Finset (Fin (s + 1))) w g cap
    (fun i _ => by dsimp [w]; positivity) (Finset.mem_univ q)
    hcap hdvd hdiv hover
  have hz : ∀ i : Fin (s + 1), i ≠ q →
      rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0 := by
    intro i hi
    exact hgain i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  refine ⟨hF, hledger.trans hred, hz, ?_⟩
  intro i
  rw [eraseIdx_directionRow o e q i]
  have hrow := rowScore_eraseIdx' hleg.lam_pos
    (directionRow_sorted o e c (q.succAbove i))
    (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
    (deleteIndex_lt o e c (Fin.succAbove_ne q i))
    (by rw [directionRow_length o e c (q.succAbove i)]; omega)
  rw [hz _ (Fin.succAbove_ne q i)] at hrow
  simpa only [Nat.add_zero] using hrow

/-- For the original power-of-two cap, its divisibility follows from
the actual floor strip rather than a freely chosen exponent bound. -/
theorem actual_power_cap_minimum_delete_normal_form {s n : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (q : Fin (s + 1))
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i))
    (hover : 2 ^ n < potential lam (directionRows o e c))
    (hdelete : potential lam (directionRows o e (c ∘ q.succAbove)) ≤ 2 ^ n) :
    potential lam (directionRows o e c) =
        2 ^ n + 2 ^ rowScore lam (directionRow o e c q) ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = 2 ^ n ∧
      (∀ i : Fin (s + 1), i ≠ q →
        rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0) ∧
      (∀ i : Fin s,
        rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
          rowScore lam (directionRow o e c (q.succAbove i))) := by
  have hcells := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos q
    (by omega) hn
  have hscore := rowScore_eq_sub_defect lam hleg.lam_pos n _ hcells
  have hk : rowScore lam (directionRow o e c q) ≤ n := by omega
  exact actual_minimum_delete_normal_form hs o e hleg q (2 ^ n) hmin
    (pow_dvd_pow 2 hk) hover hdelete

/-- Every nonzero proposed cone axis has an actual ray outside the cone
in the fixed-minimum overfull normal form. -/
theorem actual_minimum_delete_has_outside_ray {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (q : Fin (s + 1)) (cap : ℕ)
    (hmin : ∀ i : Fin (s + 1),
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c i))
    (hdiv : 2 ^ rowScore lam (directionRow o e c q) ∣ cap)
    (hover : cap < potential lam (directionRows o e c))
    (hdelete : potential lam (directionRows o e (c ∘ q.succAbove)) ≤ cap)
    (u : Plane₂) (hu : u ≠ 0) :
    ∃ j : Fin (s + 1), j ≠ q ∧
      Real.pi / 2 - lam < InnerProductGeometry.angle (c j - c q) u := by
  obtain ⟨_, _, hzero, _⟩ :=
    actual_minimum_delete_normal_form hs o e hleg q cap hmin hdiv hover hdelete
  have hnot := ConeDeletionProgress.not_common_cone_of_zero_incoming
    hs o e he hleg q hzero u hu
  push Not at hnot
  exact hnot

#print axioms actual_delete_potential_eq_sum_pow_gain
#print axioms actual_minimum_delete_normal_form
#print axioms actual_power_cap_minimum_delete_normal_form
#print axioms actual_minimum_delete_has_outside_ray

end Jsp404.ActualMinimumDeletionNormalForm
