import Jsp000404.TwoSaturatedDeficit
import Mathlib.Analysis.Convex.Caratheodory

set_option autoImplicit false

/-! Actual interior centers lose three score cells in their original full row.
The existing three-ray identity resolves all projective lifts and wrap cases;
the existing full-row restriction keeps every other center and multiplicity.
No saturation, supplied row score, or capacity hypothesis is used.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.InteriorRowDefect

/-- An actual strictly nested three-ray fan bounds the original full row. -/
theorem rowScore_add_three_le_of_nested {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) {q a b d : Fin s}
    (hqa : q ≠ a) (hqb : q ≠ b) (hqd : q ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    {E : Plane₂} (hE : Sbtw ℝ (c a) E (c b)) (hq : Sbtw ℝ (c d) (c q) E) :
    rowScore lam (directionRow o e c q) + 3 ≤ n := by
  have hAB := hleg.triAngle a q b hqa.symm hqb hab
  have hAD := hleg.triAngle a q d hqa.symm hqd had
  have hBD := hleg.triAngle b q d hqb.symm hqd hbd
  have hrestrict := rowScore_le_sorted_three_directions o e c hleg.lam_pos
    hqa hqb hqd hab had hbd
  have hid := rowScore_inner_nested_three_directions o e c he hleg.inj
    hqa.symm hqb.symm hqd.symm hE hq
    (by linarith [hleg.lam_pos]) (by linarith [hleg.lam_pos])
    (by linarith [hleg.lam_pos]) lam
  rw [hid] at hrestrict
  have hbound := inner_supplement_gapScore_add_three_le hleg.lam_pos hn
    hE hq hAB hAD hBD
  omega

/-- Containment in a triangle of three distinct actual other centers gives
the three-cell bound on the full original row, not merely a selected row. -/
theorem rowScore_add_three_le_of_mem_triangle {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) {q a b d : Fin s}
    (hqa : q ≠ a) (hqb : q ≠ b) (hqd : q ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hmem : c q ∈ convexHull ℝ ({c a, c b, c d} : Set Plane₂)) :
    rowScore lam (directionRow o e c q) + 3 ≤ n := by
  obtain ⟨E, hE, hq⟩ := strict_nested_of_mem_convexHull hmem (hleg.inj.ne hqd)
    (legal_triple_not_collinear hleg hqd.symm had.symm hqa)
    (legal_triple_not_collinear hleg hqd.symm hbd.symm hqb)
    (legal_triple_not_collinear hleg hqa.symm hab hqb)
  exact rowScore_add_three_le_of_nested o e he hleg hn
    hqa hqb hqd hab had hbd hE hq

theorem rowDefect_ge_three_of_mem_triangle {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) {q a b d : Fin s}
    (hqa : q ≠ a) (hqb : q ≠ b) (hqd : q ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hmem : c q ∈ convexHull ℝ ({c a, c b, c d} : Set Plane₂)) :
    3 ≤ rowDefect n lam (directionRow o e c q) := by
  have h := rowScore_add_three_le_of_mem_triangle o e he hleg hn
    hqa hqb hqd hab had hbd hmem
  have hs2 : 2 ≤ s := by
    have hqv := q.isLt
    have hav := a.isLt
    have hne : q.val ≠ a.val := fun hv => hqa (Fin.ext hv)
    omega
  have hc := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos q hs2 hn
  have heq := rowScore_eq_sub_defect lam hleg.lam_pos n (directionRow o e c q) hc
  have hd := rowDefect_le lam hleg.lam_pos n (directionRow o e c q) hc
  omega

/-- Caratheodory reduces membership in the actual others' hull to three
actual centers. Legal noncollinearity excludes supports of size at most two. -/
theorem exists_containing_actual_triangle {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hleg : Section4Legality c lam) (q : Fin s)
    (hmem : c q ∈ convexHull ℝ (c '' ({q} : Set (Fin s))ᶜ)) :
    ∃ a b d : Fin s, q ≠ a ∧ q ≠ b ∧ q ≠ d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      c q ∈ convexHull ℝ ({c a, c b, c d} : Set Plane₂) := by
  classical
  rw [convexHull_eq_union] at hmem
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨T, hT, hAI, hQT⟩ := hmem
  have hcard : T.card ≤ 3 := by
    have hc := hAI.card_le_finrank_succ
    have hv := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : T → Plane₂)))
    have hd : Module.finrank ℝ Plane₂ = 2 := by simp
    rw [hd] at hv
    simp only [Fintype.card_coe] at hc
    omega
  have hnot : c q ∉ T := by
    intro hqT
    obtain ⟨i, hi, heq⟩ := hT hqT
    have hiq := hleg.inj heq
    subst i
    simp at hi
  have hthree : T.card = 3 := by
    by_contra hn3
    have hsmall : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
    rcases hsmall with h0 | h1 | h2
    · have hT0 := Finset.card_eq_zero.mp h0
      simp [hT0] at hQT
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      have hxq : c q = x := by simpa [hx] using hQT
      exact hnot (by simp [hx, hxq])
    · obtain ⟨x, y, hxy, hT2⟩ := Finset.card_eq_two.mp h2
      obtain ⟨a, ha, rfl⟩ := hT (by simp [hT2] : x ∈ T)
      obtain ⟨b, hb, rfl⟩ := hT (by simp [hT2] : y ∈ T)
      have haq : a ≠ q := by simpa using ha
      have hbq : b ≠ q := by simpa using hb
      have hab : a ≠ b := fun h => hxy (congrArg c h)
      have hseg : Wbtw ℝ (c a) (c q) (c b) := by
        apply mem_segment_iff_wbtw.mp
        simpa [hT2, convexHull_pair] using hQT
      exact (legal_triple_not_collinear hleg haq hab hbq.symm) hseg.collinear
  obtain ⟨x, y, z, hxy, hxz, hyz, hT3⟩ := Finset.card_eq_three.mp hthree
  obtain ⟨a, ha, rfl⟩ := hT (by simp [hT3] : x ∈ T)
  obtain ⟨b, hb, rfl⟩ := hT (by simp [hT3] : y ∈ T)
  obtain ⟨d, hd, rfl⟩ := hT (by simp [hT3] : z ∈ T)
  refine ⟨a, b, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ne_comm] using ha
  · simpa [ne_comm] using hb
  · simpa [ne_comm] using hd
  · exact fun h => hxy (congrArg c h)
  · exact fun h => hxz (congrArg c h)
  · exact fun h => hyz (congrArg c h)
  · simpa [hT3] using hQT

theorem rowDefect_ge_three_of_mem_hull_others {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) (q : Fin s)
    (hmem : c q ∈ convexHull ℝ (c '' ({q} : Set (Fin s))ᶜ)) :
    3 ≤ rowDefect n lam (directionRow o e c q) := by
  obtain ⟨a, b, d, hqa, hqb, hqd, hab, had, hbd, htri⟩ :=
    exists_containing_actual_triangle hleg q hmem
  exact rowDefect_ge_three_of_mem_triangle o e he hleg hn
    hqa hqb hqd hab had hbd htri

#print axioms rowScore_add_three_le_of_nested
#print axioms rowScore_add_three_le_of_mem_triangle
#print axioms rowDefect_ge_three_of_mem_triangle
#print axioms exists_containing_actual_triangle
#print axioms rowDefect_ge_three_of_mem_hull_others

end Jsp404.InteriorRowDefect
