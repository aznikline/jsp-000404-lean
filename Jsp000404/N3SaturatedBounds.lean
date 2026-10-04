import Jsp000404.N3R01Extraction
import Jsp000404.PositiveRowCount
import Jsp000404.R2N3Capacity

/-! Actual third-strip bounds with a saturated row. Restrictions retain the
original row score and legality; the finite terminal is consumed only after
the retained anchor has been proved saturated in the restricted geometry. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.N3SaturatedBounds

/-- Select a fixed-size actual subconfiguration containing specified centers. -/
lemma exists_restriction_containing {s t : ℕ} (K : Finset (Fin s))
    (hKt : K.card ≤ t) (hts : t ≤ s) :
    ∃ pick : Fin t → Fin s, Function.Injective pick ∧
      ∀ v ∈ K, ∃ i : Fin t, pick i = v := by
  classical
  obtain ⟨P, hKP, -, hP⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ K) hKt (by simpa using hts)
  let E := P.orderIsoOfFin hP
  let pick : Fin t → Fin s := fun i => (E i).val
  refine ⟨pick, Subtype.val_injective.comp E.injective, ?_⟩
  intro v hv
  let w : ↥P := ⟨v, hKP hv⟩
  refine ⟨E.symm w, ?_⟩
  simp [pick, w]

/-- A retained saturated anchor stays saturated under any actual restriction
with at least two centers. -/
lemma saturated_restrict {s t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3) (hs : 2 ≤ s) (ht : 2 ≤ t)
    (pick : Fin t → Fin s) (hpick : Function.Injective pick) (i : Fin t)
    (hsat : rowDefect 3 lam (directionRow o e c (pick i)) = 1) :
    rowDefect 3 lam (directionRow o e (c ∘ pick) i) = 1 := by
  have hc := rowCells_directionRow_le_of_floor_eq o e c hlam (pick i) hs hn
  have hsc := rowScore_eq_sub_defect lam hlam 3 _ hc
  have hge := PositiveRowCount.rowScore_le_restrict o e c hlam ht pick hpick i
  have hc' := rowCells_directionRow_le_of_floor_eq o e (c ∘ pick) hlam i ht hn
  have hsc' := rowScore_eq_sub_defect lam hlam 3 _ hc'
  have hdef := one_le_rowDefect lam hlam 3 _ (by omega) hc'
  omega

/-- In the whole third strip, any actual configuration admitting a saturated
row has at most seven centers. No minimality or tail assumptions are used. -/
theorem saturated_card_le_seven {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3) (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect 3 lam (directionRow o e c v) = 1) :
    s ≤ 7 := by
  classical
  by_contra hb
  have hs : 8 ≤ s := by omega
  obtain ⟨pick, hpick, hkeep⟩ := exists_restriction_containing
    ({v} : Finset (Fin s)) (by simp) hs
  obtain ⟨i, hi⟩ := hkeep v (by simp)
  have hsat' := saturated_restrict o e hlam hn (by omega) (by omega : 2 ≤ 8)
    pick hpick i (hi.symm ▸ hsat)
  exact N3R01Extraction.eight_centre_n3_saturated_impossible o e he hlam hn
    (hleg.restrict_injective pick hpick) i hsat'

/-- If the anchor is the only positive row, its weight four and the flat
rows' weights one fit the third-strip HIGH cap. -/
theorem saturated_flat_tail_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin s → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3) (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect 3 lam (directionRow o e c v) = 1)
    (hflat : ∀ w, w ≠ v → rowScore lam (directionRow o e c w) = 0) :
    potential lam (directionRows o e c) ≤ 10 := by
  classical
  have hcard := saturated_card_le_seven o e he hlam hn hleg v hsat
  have hv : rowScore lam (directionRow o e c v) = 2 := by
    have hc := rowCells_directionRow_le_of_floor_eq o e c hlam v hs hn
    rw [rowScore_eq_sub_defect lam hlam 3 _ hc, hsat]
  have hf : ∀ i, 2 ^ rowScore lam (directionRow o e c i) =
      1 + if i = v then 3 else 0 := by
    intro i
    by_cases hi : i = v
    · subst i; simp [hv]
    · simp [hi, hflat i hi]
  have hp : potential lam (directionRows o e c) = 4 + (s-1) := by
    unfold potential exponentAt directionRows
    simp_rw [hf]
    rw [Finset.sum_add_distrib]
    simp
    omega
  omega

/-- With one score-two row and at most one other positive row of score one,
the potential is bounded by the number of centers plus four. -/
lemma potential_le_card_add_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ} (v a : Fin s)
    (hv : rowScore lam (directionRow o e c v) = 2)
    (hother : ∀ i, i ≠ v → rowScore lam (directionRow o e c i) ≤ 1)
    (hflat : ∀ i, i ≠ v → i ≠ a →
      rowScore lam (directionRow o e c i) = 0) :
    potential lam (directionRows o e c) ≤ s + 4 := by
  classical
  have hf : ∀ i, 2 ^ rowScore lam (directionRow o e c i) ≤
      1 + (if i = v then 3 else 0) + (if i = a then 1 else 0) := by
    intro i
    by_cases hiv : i = v
    · subst i
      simp [hv]
    · by_cases hia : i = a
      · have hp := Nat.pow_le_pow_right (by norm_num : (0:ℕ)<2) (hother i hiv)
        simpa only [ite_eq_right hiv, ite_eq_left hia, Nat.reduceAdd] using hp
      · simp [hiv, hia, hflat i hiv hia]
  calc
    potential lam (directionRows o e c) ≤
        ∑ i : Fin s, (1 + (if i = v then 3 else 0) +
          (if i = a then 1 else 0)) := by
      unfold potential exponentAt directionRows
      exact Finset.sum_le_sum (fun i _ => hf i)
    _ = s + 4 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp

/-- The existing actual six-center R2 exclusion closes every saturated
third-strip configuration of at most six centers. -/
theorem saturated_le_six_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hs6 : s ≤ 6) {c : Fin s → Plane₂} {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hleg : Section4Legality c lam) (v : Fin s)
    (hsat : rowDefect 3 lam (directionRow o e c v) = 1) :
    potential lam (directionRows o e c) ≤ 10 := by
  classical
  by_cases hs5 : s ≤ 5
  · have h := potential_le_high_cap_of_le_five o e he hs hs5 (by omega)
      hlam hn hleg
    norm_num at h
    exact h
  have hs_eq : s = 6 := by omega
  have hc (i : Fin s) := rowCells_directionRow_le_of_floor_eq o e c hlam i
    (by omega : 2 ≤ s) hn
  have hsc (i : Fin s) := rowScore_eq_sub_defect lam hlam 3 _ (hc i)
  have h1 (i : Fin s) := one_le_rowDefect lam hlam 3 _ (by omega) (hc i)
  have hv : rowScore lam (directionRow o e c v) = 2 := by
    rw [hsc, hsat]
  by_cases hsecond : ∃ w, w ≠ v ∧ rowDefect 3 lam (directionRow o e c w) = 1
  · obtain ⟨w, hw, hd⟩ := hsecond
    have h := potential_le_high_of_two_saturated o e he hs (by omega : 2 ≤ 3)
      hlam hn hleg hw hd hsat
    norm_num at h
    exact h
  have hother : ∀ i, i ≠ v → rowScore lam (directionRow o e c i) ≤ 1 := by
    intro i hiv
    have hd : rowDefect 3 lam (directionRow o e c i) ≠ 1 :=
      fun h => hsecond ⟨i, hiv, h⟩
    have := h1 i
    have := hsc i
    omega
  by_cases hpos : ∃ a, a ≠ v ∧ 0 < rowScore lam (directionRow o e c a)
  · obtain ⟨a, hav, ha⟩ := hpos
    have hda : rowDefect 3 lam (directionRow o e c a) = 2 := by
      have := hother a hav
      have := hsc a
      omega
    have hflat : ∀ i, i ≠ v → i ≠ a → rowScore lam (directionRow o e c i) = 0 := by
      intro i hiv hia
      by_contra hi
      have hdi : rowDefect 3 lam (directionRow o e c i) = 2 := by
        have := hother i hiv
        have := hsc i
        omega
      exact r2_n3_six_plus_impossible (by omega : 6 ≤ s) hlam hn hleg he
        v hsat hav hiv hia.symm hda hdi
    have h := potential_le_card_add_four o e v a hv hother hflat
    omega
  · have hflat : ∀ i, i ≠ v → rowScore lam (directionRow o e c i) = 0 := by
      intro i hiv
      by_contra hi
      exact hpos ⟨i, hiv, by omega⟩
    have h := potential_le_card_add_four o e v v hv hother
      (fun i hiv _ => hflat i hiv)
    omega

/-- The whole third strip with a saturated row obeys the HIGH cap ten,
at every number of actual centers and every delta in `[0,1)`. -/
theorem saturated_high_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3) (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect 3 lam (directionRow o e c v) = 1) :
    potential lam (directionRows o e c) ≤ 10 := by
  have hcard := saturated_card_le_seven o e he hlam hn hleg v hsat
  by_cases hs6 : s ≤ 6
  · exact saturated_le_six_capacity o e he hs hs6 hlam hn hleg v hsat
  · have hs7 : s = 7 := by omega
    subst s
    exact saturated_flat_tail_capacity o e he (by omega) hlam hn hleg v hsat
      (N3R01Extraction.seven_centre_n3_nonanchor_score_zero o e he hlam hn hleg v hsat)

/-- Both original strip caps with saturation; the LOW branch uses its
actual delta premise and the HIGH branch uses the new unconditional bound. -/
theorem saturated_strip_capacity {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3) (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect 3 lam (directionRow o e c v) = 1)
    (big : Bool) (hbig : big = false → Real.pi / lam - 3 < 1/2) :
    potential lam (directionRows o e c) ≤ sendovCap 3 big := by
  cases big with
  | false =>
      have h := potential_le_two_pow_of_saturated o e he (by omega : 2 ≤ s)
        (by omega : 2 ≤ 3) hlam hn hleg v hsat (by simpa using hbig rfl)
      simpa [sendovCap] using h
  | true =>
      simpa [sendovCap] using saturated_high_capacity o e he hs hlam hn hleg v hsat

#print axioms exists_restriction_containing
#print axioms saturated_restrict
#print axioms saturated_card_le_seven
#print axioms saturated_flat_tail_capacity
#print axioms potential_le_card_add_four
#print axioms saturated_le_six_capacity
#print axioms saturated_high_capacity
#print axioms saturated_strip_capacity
end Jsp404.N3SaturatedBounds
