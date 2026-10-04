import Jsp000404.ThirdStripNormalForm

/-!
Actual no-saturation consumers in the third strip. The row weights are
exactly one plus the indicator of a positive row. Hence every actual
minimal counterexample has one of finitely many cardinality/positive-count
profiles. These are reductions, not the missing capacity theorem.
-/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.N3NoSaturatedBound

/-- For actual rows with score at most one, the potential equals the number
of centers plus the number of positive rows. -/
theorem potential_eq_card_add_positive {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (hscore : ∀ i, rowScore lam (directionRow o e c i) ≤ 1) :
    potential lam (directionRows o e c) = s +
      (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card := by
  classical
  unfold potential exponentAt directionRows
  have hw (i : Fin s) : 2 ^ rowScore lam (directionRow o e c i) =
      1 + if 0 < rowScore lam (directionRow o e c i) then 1 else 0 := by
    have h := hscore i
    interval_cases rowScore lam (directionRow o e c i) <;> norm_num
  rw [Finset.sum_congr rfl (fun i _ => hw i), Finset.sum_add_distrib]
  simp

/-- At n=3, no saturation supplies the score-zero/score-one identity. -/
theorem nonsaturated_potential_eq_card_add_positive {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (hs : 2 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)) :
    potential lam (directionRows o e c) = s +
      (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card :=
  potential_eq_card_add_positive o e
    (ThirdStripNormalForm.nonsaturated_score_le_one o e hs hlam hn hns)

/-- LOW no-saturation potential is at most the actual cardinality plus
four. The positive-row bound is consumed on the original points. -/
theorem low_potential_le_card_add_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hlow : 2*Real.pi/7 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)) :
    potential lam (directionRows o e c) ≤ s+4 := by
  rw [nonsaturated_potential_eq_card_add_positive o e hs hleg.lam_pos hn hns]
  exact Nat.add_le_add_left (PositiveRowCount.positive_card_le_four o e he hleg hlow) s

/-- HIGH no-saturation potential is at most the actual cardinality plus
five, with no assumption about the zero rows' geometry. -/
theorem high_potential_le_card_add_five {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hquarter : Real.pi/4 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)) :
    potential lam (directionRows o e c) ≤ s+5 := by
  rw [nonsaturated_potential_eq_card_add_positive o e hs hleg.lam_pos hn hns]
  exact Nat.add_le_add_left (PositiveRowCount.positive_card_le_five o e he hleg hquarter) s

/-- A LOW actual minimal no-saturation counterexample has potential nine,
5..9 centers, and exactly 9-s positive centers. -/
theorem low_minimal_counter_profile {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hlow : 2*Real.pi/7 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 8 < potential lam (directionRows o e c))
    (hdel : ∀ q : Fin (s+1),
      potential lam (directionRows o e (c ∘ q.succAbove)) ≤ 8) :
    potential lam (directionRows o e c) = 9 ∧
      5 ≤ s+1 ∧ s+1 ≤ 9 ∧
      (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 4 ∧
      s+1+(Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card = 9 := by
  obtain ⟨q, hq, hF, hchild, hsame⟩ :=
    ThirdStripNormalForm.low_counter_zero_victim_normal_form o e he hs hleg hn hlow hns hover hdel
  have hcard := PositiveRowCount.positive_card_le_four o e he hleg hlow
  have hweight := nonsaturated_potential_eq_card_add_positive o e (by omega) hleg.lam_pos hn hns
  exact ⟨hF, by omega, by omega, hcard, by omega⟩

/-- HIGH counterpart: potential eleven, 6..11 centers, exactly 11-s
positive centers, and at most five positive centers. -/
theorem high_minimal_counter_profile {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hquarter : Real.pi/4 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 10 < potential lam (directionRows o e c))
    (hdel : ∀ q : Fin (s+1),
      potential lam (directionRows o e (c ∘ q.succAbove)) ≤ 10) :
    potential lam (directionRows o e c) = 11 ∧
      6 ≤ s+1 ∧ s+1 ≤ 11 ∧
      (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 5 ∧
      s+1+(Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card = 11 := by
  obtain ⟨q, hq, hF, hchild, hsame⟩ :=
    ThirdStripNormalForm.high_counter_zero_victim_normal_form o e he hs hleg hn hquarter hns hover hdel
  have hcard := PositiveRowCount.positive_card_le_five o e he hleg hquarter
  have hweight := nonsaturated_potential_eq_card_add_positive o e (by omega) hleg.lam_pos hn hns
  exact ⟨hF, by omega, by omega, hcard, by omega⟩

#print axioms potential_eq_card_add_positive
#print axioms nonsaturated_potential_eq_card_add_positive
#print axioms low_potential_le_card_add_four
#print axioms high_potential_le_card_add_five
#print axioms low_minimal_counter_profile
#print axioms high_minimal_counter_profile
end Jsp404.N3NoSaturatedBound
