import JSP404.BinaryEncoding
import Mathlib.Data.Finset.Sort

/-!
Two-coordinate projection of a finite Boolean subcube packing.

The counting theorem is imported from the existing attributed Sendov source
`ThirdParty/Sendov/JSP404/BinaryEncoding.lean` (Erdős--Szekeres finite encoding).
This new projection lemma makes no geometric or interval-cover assertion.
-/

namespace Jsp404.TwoCoordinatePacking

open scoped BigOperators

/-- Remove two universally specified coordinates when every pair is already
separated outside them.  Local exponents come from the original full specified
set; no aggregate-weight or physical shorter-interval premise is assumed. -/
theorem two_coordinate_weighted_bound
    {V : Type*} [Fintype V] {n : ℕ}
    (fullSpecified : V → Finset (Fin n)) (bit : V → Fin n → Bool)
    (ka kb : Fin n) (hab : ka ≠ kb)
    (hfixed : ∀ v, ka ∈ fullSpecified v ∧ kb ∈ fullSpecified v)
    (separates : ∀ u v, u ≠ v → ∃ i,
      i ∈ fullSpecified u ∧ i ∈ fullSpecified v ∧
        i ≠ ka ∧ i ≠ kb ∧ bit u i ≠ bit v i)
    (ks : V → ℕ)
    (hlocal : ∀ v, ks v ≤ n - (fullSpecified v).card) :
    ∑ v, 2 ^ ks v ≤ 2 ^ (n - 2) := by
  classical
  let removed : Finset (Fin n) := {ka, kb}
  have hremoved : removed.card = 2 := by
    exact Finset.card_pair hab
  let retainedCoords : Finset (Fin n) := Finset.univ \ removed
  have hcoords : retainedCoords.card = n - 2 := by
    dsimp [retainedCoords]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ removed),
      Finset.card_univ, Fintype.card_fin, hremoved]
  let keep : Fin (n - 2) ↪o Fin n := retainedCoords.orderEmbOfFin hcoords
  have hkeep_mem (j : Fin (n - 2)) : keep j ∈ retainedCoords :=
    Finset.orderEmbOfFin_mem retainedCoords hcoords j
  have hkeep_surj {i : Fin n} (hi : i ∈ retainedCoords) :
      ∃ j : Fin (n - 2), keep j = i := by
    have hmem : i ∈ Set.range (keep : Fin (n - 2) → Fin n) := by
      dsimp [keep]
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hi
    exact hmem
  let specified : V → Finset (Fin (n - 2)) := fun v =>
    Finset.univ.filter (fun j => keep j ∈ fullSpecified v)
  let retainedBit : V → Fin (n - 2) → Bool := fun v j => bit v (keep j)
  have hsubset (v : V) : removed ⊆ fullSpecified v := by
    intro i hi
    change i ∈ ({ka, kb} : Finset (Fin n)) at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact (hfixed v).1
    · exact (hfixed v).2
  have himage (v : V) :
      (specified v).image (fun j => keep j) = fullSpecified v \ removed := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hs : keep j ∈ fullSpecified v := (Finset.mem_filter.mp hj).2
      have hr : keep j ∉ removed := (Finset.mem_sdiff.mp (hkeep_mem j)).2
      exact Finset.mem_sdiff.mpr ⟨hs, hr⟩
    · intro hi
      obtain ⟨hs, hr⟩ := Finset.mem_sdiff.mp hi
      have hrc : i ∈ retainedCoords := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hr⟩
      obtain ⟨j, rfl⟩ := hkeep_surj hrc
      apply Finset.mem_image.mpr
      exact ⟨j, by simp [specified, hs], rfl⟩
  have hspecified_card (v : V) :
      (specified v).card = (fullSpecified v).card - 2 := by
    have hi := Finset.card_image_of_injective (specified v) keep.injective
    rw [himage, Finset.card_sdiff_of_subset (hsubset v), hremoved] at hi
    exact hi.symm
  have hseparate : ∀ u v, u ≠ v → ∃ j,
      j ∈ specified u ∧ j ∈ specified v ∧ retainedBit u j ≠ retainedBit v j := by
    intro u v huv
    obtain ⟨i, hiu, hiv, hia, hib, hbits⟩ := separates u v huv
    have hr : i ∈ retainedCoords := by
      simp [retainedCoords, removed, hia, hib]
    obtain ⟨j, hj⟩ := hkeep_surj hr
    refine ⟨j, ?_, ?_, ?_⟩
    · simp [specified, hj, hiu]
    · simp [specified, hj, hiv]
    · simpa [retainedBit, hj] using hbits
  have hlocal_retained (v : V) : ks v ≤ (n - 2) - (specified v).card := by
    have htwo : 2 ≤ (fullSpecified v).card := by
      have h := Finset.card_le_card (hsubset v)
      rwa [hremoved] at h
    have htop : (fullSpecified v).card ≤ n := by
      simpa using Finset.card_le_univ (fullSpecified v)
    have hk := hlocal v
    rw [hspecified_card]
    omega
  have hpacking := JSP404.sum_free_binary_coordinates_le
    (n - 2) specified retainedBit hseparate
  calc
    ∑ v, 2 ^ ks v ≤ ∑ v, 2 ^ ((n - 2) - (specified v).card) :=
      Finset.sum_le_sum (fun v _ => Nat.pow_le_pow_right (by omega) (hlocal_retained v))
    _ ≤ 2 ^ (n - 2) := hpacking

#print axioms two_coordinate_weighted_bound

end Jsp404.TwoCoordinatePacking
