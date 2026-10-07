import Jsp000404.ActualMinimalBandCounterexample
import Jsp000404.FullHullInteriorDefect
import Jsp000404.GlobalFiveLowCapacity
import Jsp000404.N3SaturatedBounds

set_option autoImplicit false

/-!
The actual original-configuration frame for an F18 minimum counter-model.

Saturation is excluded by the independently proved one-saturated LOW bound.
Four heavy original centers are excluded by an actual five-point restriction
and the independently proved five-center LOW capacity. Hull membership and
the light/heavy partition always refer to the full original configuration.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18Frame

/-- Original score-one indices. -/
noncomputable def lightIndices {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (lam : ℝ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => rowScore lam (directionRow o e c i) = 1)

/-- Original score-two indices. No subset scores are used in this definition. -/
noncomputable def heavyIndices {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (lam : ℝ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => rowScore lam (directionRow o e c i) = 2)

/-- The original actual facts consumed by the later F18 case split. -/
structure Frame {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (lam : ℝ) : Prop where
  scale_lower : 2 * Real.pi / 9 < lam
  scale_upper : lam ≤ Real.pi / 4
  floor_four : Nat.floor (Real.pi / lam) = 4
  score_one_or_two : ∀ i, rowScore lam (directionRow o e c i) = 1 ∨
    rowScore lam (directionRow o e c i) = 2
  heavy_full_hull : ∀ i, rowScore lam (directionRow o e c i) = 2 → IsHullVertex c i
  heavy_count_le_three : (heavyIndices o e c lam).card ≤ 3
  light_heavy_partition : (lightIndices o e c lam).card + (heavyIndices o e c lam).card = s
  light_plus_twice_heavy :
    (lightIndices o e c lam).card + 2 * (heavyIndices o e c lam).card = 9
  card_plus_heavy : s + (heavyIndices o e c lam).card = 9
  card_eq_nine_sub_heavy : s = 9 - (heavyIndices o e c lam).card
  card_ge_six : 6 ≤ s

private theorem scores_le_two {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam) :
    ∀ i, rowScore lam (directionRow o e c i) ≤ 2 := by
  obtain ⟨hn, _, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hdef := ActualMinimalBandCounterexample.low_model_nonsaturated
    (by decide : 2 ≤ 4) o e he H
  intro i
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos i
    (by have := H.card_ge_three; omega) hn
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
  have hi := hdef i
  omega

private theorem card_ge_five_of_F18_scores_le_two {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (hF : potential lam (directionRows o e c) = 18)
    (hupper : ∀ i, rowScore lam (directionRow o e c i) ≤ 2) : 5 ≤ s := by
  have hweight (i : Fin s) : 2 ^ rowScore lam (directionRow o e c i) ≤ 4 := by
    calc
      2 ^ rowScore lam (directionRow o e c i) ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (hupper i)
      _ = 4 := by decide
  have hsum : potential lam (directionRows o e c) ≤ 4 * s := by
    unfold potential exponentAt directionRows
    calc
      (∑ i : Fin s, 2 ^ rowScore lam (directionRow o e c i)) ≤ ∑ _i : Fin s, 4 :=
        Finset.sum_le_sum (fun i _ => hweight i)
      _ = 4 * s := by simp [Nat.mul_comm]
  omega

private theorem scores_ge_one {s : ℕ} (hs : 5 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hF : potential lam (directionRows o e c) = 18) :
    ∀ i, 1 ≤ rowScore lam (directionRow o e c i) := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  obtain ⟨m, hmin⟩ := Finite.exists_min
    (fun i : Fin (u + 1) => rowScore lam (directionRow o e c i))
  have hcrit := ActualMinimalBandCounterexample.low_minimum_score_critical_form
    (n := 4) (by omega : 3 ≤ u) (by decide : 2 ≤ 4) o e H m hmin
  have hpow : 2 ^ rowScore lam (directionRow o e c m) = 2 := by
    have h := hcrit.1
    rw [hF] at h
    norm_num at h
    omega
  have hm : rowScore lam (directionRow o e c m) = 1 :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (by simpa using hpow)
  intro i
  simpa only [hm] using hmin i

/-- This restriction argument uses only original heavy scores and actual
score monotonicity. No full-hull fact is transferred to the five-point subset. -/
private theorem heavy_count_le_three {s : ℕ} (hs : 5 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = 4)
    (hlow : Real.pi / lam - (4 : ℝ) < 1 / 2) :
    (heavyIndices o e c lam).card ≤ 3 := by
  classical
  by_contra hnot
  have hfour : 4 ≤ (heavyIndices o e c lam).card := by omega
  obtain ⟨K, hKP, hKcard⟩ := Finset.exists_subset_card_eq hfour
  obtain ⟨pick, hpick, hkeep⟩ := N3SaturatedBounds.exists_restriction_containing
    K (by omega : K.card ≤ 5) hs
  let S : Finset (Fin 5) := Finset.univ.filter (fun i => pick i ∈ K)
  have himage : S.image pick = K := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      obtain ⟨i, hi⟩ := hkeep v hv
      refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, hi⟩
      simpa only [hi] using hv
  have hS : S.card = 4 := by
    calc
      S.card = (S.image pick).card := (Finset.card_image_of_injective S hpick).symm
      _ = K.card := congrArg Finset.card himage
      _ = 4 := hKcard
  have hweight (i : Fin 5) :
      1 + (if i ∈ S then 3 else 0) ≤
        2 ^ rowScore lam (directionRow o e (c ∘ pick) i) := by
    by_cases hi : i ∈ S
    · have hiK : pick i ∈ K := (Finset.mem_filter.mp hi).2
      have hiheavy : rowScore lam (directionRow o e c (pick i)) = 2 :=
        (Finset.mem_filter.mp (hKP hiK)).2
      have hmono := PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos
        (by decide : 2 ≤ 5) pick hpick i
      have hge : 2 ≤ rowScore lam (directionRow o e (c ∘ pick) i) := by
        simpa only [hiheavy] using hmono
      have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hge
      simpa [hi] using hpow
    · simpa only [if_neg hi, Nat.add_zero] using
        (Nat.one_le_two_pow : 1 ≤ 2 ^ rowScore lam (directionRow o e (c ∘ pick) i))
  have hfilter : (Finset.univ : Finset (Fin 5)).filter (fun i => i ∈ S) = S := by
    ext i
    simp
  have hsum : (∑ i : Fin 5, (1 + if i ∈ S then 3 else 0)) = 17 := by
    rw [Finset.sum_add_distrib, Finset.sum_ite, hfilter]
    simp [hS]
  have hge17 : 17 ≤ potential lam (directionRows o e (c ∘ pick)) := by
    rw [← hsum]
    unfold potential exponentAt directionRows
    exact Finset.sum_le_sum (fun i _ => hweight i)
  have hcap : potential lam (directionRows o e (c ∘ pick)) ≤ 16 := by
    simpa using GlobalFiveLowCapacity.potential_le_two_pow_of_five_low
      o e he (by decide : 3 ≤ 4) hleg.lam_pos hn hlow
      (hleg.restrict_injective pick hpick)
  omega

private theorem binary_count_identities {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (hbinary : ∀ i, rowScore lam (directionRow o e c i) = 1 ∨
      rowScore lam (directionRow o e c i) = 2) :
    (lightIndices o e c lam).card + (heavyIndices o e c lam).card = s ∧
      potential lam (directionRows o e c) = 2 * s + 2 * (heavyIndices o e c lam).card := by
  classical
  have hlight : lightIndices o e c lam =
      Finset.univ.filter (fun i => ¬ rowScore lam (directionRow o e c i) = 2) := by
    ext i
    simp only [lightIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hbinary i with hi | hi <;> simp [hi]
  have hpartition : (lightIndices o e c lam).card + (heavyIndices o e c lam).card = s := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin s))) (fun i => rowScore lam (directionRow o e c i) = 2)
    rw [← hlight] at h
    simpa only [heavyIndices, Finset.card_univ, Fintype.card_fin, Nat.add_comm] using h
  have hweight (i : Fin s) : 2 ^ rowScore lam (directionRow o e c i) =
      2 + if i ∈ heavyIndices o e c lam then 2 else 0 := by
    rcases hbinary i with hi | hi <;> simp [heavyIndices, hi]
  have hfilter : (Finset.univ : Finset (Fin s)).filter
      (fun i => i ∈ heavyIndices o e c lam) = heavyIndices o e c lam := by
    ext i
    simp
  have hboost : (∑ i : Fin s, if i ∈ heavyIndices o e c lam then 2 else 0) =
      (heavyIndices o e c lam).card * 2 := by
    rw [Finset.sum_ite, hfilter]
    simp
  refine ⟨hpartition, ?_⟩
  unfold potential exponentAt directionRows
  simp_rw [hweight]
  rw [Finset.sum_add_distrib, hboost]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The F18 original frame is internally derived from the actual LOW
minimum counter-model. Neither the binary scores, the heavy bound, nor
full-hull membership is a caller premise. -/
theorem actual_f18_frame {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 s c lam)
    (hF : potential lam (directionRows o e c) = 18) : Frame o e c lam := by
  classical
  obtain ⟨hn, hlow, _⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hupper := scores_le_two o e he H
  have hs5 := card_ge_five_of_F18_scores_le_two o e hF hupper
  have hpositive := scores_ge_one hs5 o e H hF
  have hbinary (i : Fin s) : rowScore lam (directionRow o e c i) = 1 ∨
      rowScore lam (directionRow o e c i) = 2 := by
    have := hpositive i
    have := hupper i
    omega
  have hhull (i : Fin s) (hi : rowScore lam (directionRow o e c i) = 2) : IsHullVertex c i := by
    have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos i
      (by omega : 2 ≤ s) hn
    have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
    have hsmall : rowDefect 4 lam (directionRow o e c i) ≤ 2 := by omega
    exact FullHullInteriorDefect.low_defect_is_full_hull_vertex o e he H.legality hn i hsmall
  have hheavy := heavy_count_le_three hs5 o e he H.legality hn hlow
  obtain ⟨hpartition, hmass⟩ := binary_count_identities o e hbinary
  have hcard : s + (heavyIndices o e c lam).card = 9 := by omega
  have hrho : Real.pi / ((4 : ℝ) + 1 / 2) = 2 * Real.pi / 9 := by ring
  exact {
    scale_lower := by rw [← hrho]; exact H.scale_lower
    scale_upper := H.scale_upper
    floor_four := hn
    score_one_or_two := hbinary
    heavy_full_hull := hhull
    heavy_count_le_three := hheavy
    light_heavy_partition := hpartition
    light_plus_twice_heavy := by omega
    card_plus_heavy := hcard
    card_eq_nine_sub_heavy := by omega
    card_ge_six := by omega }

#print axioms actual_f18_frame

end Jsp404.ActualF18Frame
