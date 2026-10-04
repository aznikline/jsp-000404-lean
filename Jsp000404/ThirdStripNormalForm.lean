import Jsp000404.PositiveRowCount

/-!
Actual third-strip normal forms. The minimality premise is expressed as the
capacity of each real deleted configuration, not a free gain array. An actual
zero-score victim then gives the exact one-unit excess and zero score change
in every surviving row. No global capacity conclusion is assumed or proved.
-/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.ThirdStripNormalForm

lemma nonsaturated_score_le_one {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (hs : 2 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i)) :
    ∀ i, rowScore lam (directionRow o e c i) ≤ 1 := by
  intro i
  have hc := rowCells_directionRow_le_of_floor_eq o e c hlam i hs hn
  have hsc := rowScore_eq_sub_defect lam hlam 3 _ hc
  have hdi := hns i
  omega

lemma potential_le_two_card {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (hscore : ∀ i, rowScore lam (directionRow o e c i) ≤ 1) :
    potential lam (directionRows o e c) ≤ 2*s := by
  unfold potential exponentAt directionRows
  calc
    ∑ i : Fin s, 2 ^ rowScore lam (directionRow o e c i) ≤ ∑ _i : Fin s, 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hp := Nat.pow_le_pow_right (by norm_num : (0:ℕ)<2) (hscore i)
      norm_num at hp
      exact hp
    _ = 2*s := by simp; omega

/-- Every actual LOW unsaturated over-capacity configuration has a flat row. -/
theorem low_counter_has_zero_row {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hlow : 2*Real.pi/7 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 8 < potential lam (directionRows o e c)) :
    ∃ q, rowScore lam (directionRow o e c q) = 0 := by
  have hb := potential_le_two_card o e
    (nonsaturated_score_le_one o e (by omega) hleg.lam_pos hn hns)
  by_contra h
  push Not at h
  have hpos : ∀ i, 0 < rowScore lam (directionRow o e c i) := fun i => by
    have hh := h i; omega
  have hc := PositiveRowCount.all_positive_card_le_four o e he hleg hlow hpos
  omega

/-- The analogous HIGH unsaturated counterexample also has a flat row. -/
theorem high_counter_has_zero_row {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hquarter : Real.pi/4 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 10 < potential lam (directionRows o e c)) :
    ∃ q, rowScore lam (directionRow o e c q) = 0 := by
  have hb := potential_le_two_card o e
    (nonsaturated_score_le_one o e (by omega) hleg.lam_pos hn hns)
  by_contra h
  push Not at h
  have hpos : ∀ i, 0 < rowScore lam (directionRow o e c i) := fun i => by
    have hh := h i; omega
  have hc := PositiveRowCount.all_positive_card_le_five o e he hleg hquarter hpos
  omega

/-- A zero-score deletion in an actual minimal counterexample gives exact
excess one and unchanged scores at all surviving actual centers. -/
theorem zero_victim_normal_form {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (hs : 2 ≤ s) {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (hlam : 0 < lam) (cap : ℕ) (q : Fin (s+1))
    (hover : cap < potential lam (directionRows o e c))
    (hq : rowScore lam (directionRow o e c q) = 0)
    (hdel : potential lam (directionRows o e (c ∘ q.succAbove)) ≤ cap) :
    potential lam (directionRows o e c) = cap+1 ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = cap ∧
      ∀ i : Fin s,
        rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
          rowScore lam (directionRow o e c (q.succAbove i)) := by
  classical
  let w (i : Fin s) := 2 ^ rowScore lam (directionRow o e c (q.succAbove i))
  let w' (i : Fin s) := 2 ^ rowScore lam (directionRow o e (c ∘ q.succAbove) i)
  have hmono (i : Fin s) : w i ≤ w' i := by
    have hh := PositiveRowCount.rowScore_le_restrict o e c hlam hs
      q.succAbove Fin.succAbove_right_injective i
    exact Nat.pow_le_pow_right (by norm_num) hh
  have hparent : potential lam (directionRows o e c) = (∑ i, w i)+1 := by
    unfold potential exponentAt directionRows
    rw [Fin.sum_univ_succAbove _ q, hq]
    simp only [pow_zero]
    simp only [w, Nat.add_comm]
  have hchild : potential lam (directionRows o e (c ∘ q.succAbove)) = ∑ i, w' i := rfl
  have hsum : ∑ i, w i ≤ ∑ i, w' i := Finset.sum_le_sum (fun i _ => hmono i)
  have hsumeq : ∑ i, w i = cap := by omega
  have hsumeq' : ∑ i, w' i = cap := by omega
  refine ⟨by omega, by omega, ?_⟩
  intro i
  have hwe : w i = w' i := by
    have hsum_eq : ∑ j ∈ Finset.univ, w j = ∑ j ∈ Finset.univ, w' j := by omega
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hmono j)).mp hsum_eq i (Finset.mem_univ i)
  dsimp [w,w'] at hwe
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ (2:ℕ)) hwe).symm

/-- In a LOW no-saturation counterexample whose every one-point deletion
falls below the LOW cap, some actual zero-score victim has exact excess one
and preserves every survivor score after deletion. -/
theorem low_counter_zero_victim_normal_form {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hlow : 2*Real.pi/7 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 8 < potential lam (directionRows o e c))
    (hdel : ∀ q : Fin (s+1),
      potential lam (directionRows o e (c ∘ q.succAbove)) ≤ 8) :
    ∃ q : Fin (s+1),
      rowScore lam (directionRow o e c q) = 0 ∧
      potential lam (directionRows o e c) = 9 ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = 8 ∧
      ∀ i : Fin s,
        rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
          rowScore lam (directionRow o e c (q.succAbove i)) := by
  obtain ⟨q, hq⟩ := low_counter_has_zero_row o e he (by omega : 3 ≤ s+1)
    hleg hn hlow hns hover
  obtain ⟨hparent, hchild, hscore⟩ :=
    zero_victim_normal_form o e hs hleg.lam_pos 8 q hover hq (hdel q)
  exact ⟨q, hq, hparent, hchild, hscore⟩

/-- The HIGH analogue of `low_counter_zero_victim_normal_form`, with cap 10. -/
theorem high_counter_zero_victim_normal_form {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hquarter : Real.pi/4 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 10 < potential lam (directionRows o e c))
    (hdel : ∀ q : Fin (s+1),
      potential lam (directionRows o e (c ∘ q.succAbove)) ≤ 10) :
    ∃ q : Fin (s+1),
      rowScore lam (directionRow o e c q) = 0 ∧
      potential lam (directionRows o e c) = 11 ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = 10 ∧
      ∀ i : Fin s,
        rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
          rowScore lam (directionRow o e c (q.succAbove i)) := by
  obtain ⟨q, hq⟩ := high_counter_has_zero_row o e he (by omega : 3 ≤ s+1)
    hleg hn hquarter hns hover
  obtain ⟨hparent, hchild, hscore⟩ :=
    zero_victim_normal_form o e hs hleg.lam_pos 10 q hover hq (hdel q)
  exact ⟨q, hq, hparent, hchild, hscore⟩


/-- LOW minimal-counterexample wrapper: if every strictly smaller actual
configuration satisfies the LOW cap, the deletion hypotheses required by
`low_counter_zero_victim_normal_form` are automatic. -/
theorem low_minimal_counter_zero_victim_normal_form {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hs3 : 3 ≤ s) {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hlow : 2*Real.pi/7 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 8 < potential lam (directionRows o e c))
    (hsmall : ∀ t : ℕ, 3 ≤ t → t < s+1 → ∀ c' : Fin t → Plane₂,
      Section4Legality c' lam → potential lam (directionRows o e c') ≤ 8) :
    ∃ q : Fin (s+1),
      rowScore lam (directionRow o e c q) = 0 ∧
      potential lam (directionRows o e c) = 9 ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = 8 ∧
      ∀ i : Fin s,
        rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
          rowScore lam (directionRow o e c (q.succAbove i)) := by
  apply low_counter_zero_victim_normal_form o e he hs hleg hn hlow hns hover
  intro q
  exact hsmall s hs3 (by omega) (c ∘ q.succAbove)
    (hleg.restrict_injective q.succAbove Fin.succAbove_right_injective)

/-- HIGH minimal-counterexample wrapper: smaller-configuration capacity
immediately supplies every one-point deletion cap. -/
theorem high_minimal_counter_zero_victim_normal_form {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hs3 : 3 ≤ s) {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 3)
    (hquarter : Real.pi/4 < lam)
    (hns : ∀ i, 2 ≤ rowDefect 3 lam (directionRow o e c i))
    (hover : 10 < potential lam (directionRows o e c))
    (hsmall : ∀ t : ℕ, 3 ≤ t → t < s+1 → ∀ c' : Fin t → Plane₂,
      Section4Legality c' lam → potential lam (directionRows o e c') ≤ 10) :
    ∃ q : Fin (s+1),
      rowScore lam (directionRow o e c q) = 0 ∧
      potential lam (directionRows o e c) = 11 ∧
      potential lam (directionRows o e (c ∘ q.succAbove)) = 10 ∧
      ∀ i : Fin s,
        rowScore lam (directionRow o e (c ∘ q.succAbove) i) =
          rowScore lam (directionRow o e c (q.succAbove i)) := by
  apply high_counter_zero_victim_normal_form o e he hs hleg hn hquarter hns hover
  intro q
  exact hsmall s hs3 (by omega) (c ∘ q.succAbove)
    (hleg.restrict_injective q.succAbove Fin.succAbove_right_injective)

/-- Select an actual least-cardinality counterexample at the fixed lambda.
All smaller actual configurations of at least three centers obey the cap.
This is a logical minimality construction, not an assumed global theorem. -/
theorem exists_minimal_counterexample {s0 : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {lam : ℝ} (cap : ℕ) {c0 : Fin s0 → Plane₂}
    (hs0 : 3 ≤ s0) (hleg0 : Section4Legality c0 lam)
    (hover0 : cap < potential lam (directionRows o e c0)) :
    ∃ s : ℕ, 3 ≤ s ∧ s ≤ s0 ∧ ∃ c : Fin s → Plane₂,
      Section4Legality c lam ∧ cap < potential lam (directionRows o e c) ∧
        ∀ t : ℕ, 3 ≤ t → t < s → ∀ c' : Fin t → Plane₂,
          Section4Legality c' lam → potential lam (directionRows o e c') ≤ cap := by
  classical
  let P (s : ℕ) : Prop := 3 ≤ s ∧ ∃ c : Fin s → Plane₂,
    Section4Legality c lam ∧ cap < potential lam (directionRows o e c)
  have h0 : P s0 := ⟨hs0, c0, hleg0, hover0⟩
  have hex : ∃ s, P s := ⟨s0,h0⟩
  obtain ⟨hm3,c,hmleg,hmover⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex,hm3,Nat.find_min' hex h0,c,hmleg,hmover,?_⟩
  intro t ht3 htm c' hleg'
  by_contra hb
  have hbad : P t := ⟨ht3,c',hleg',lt_of_not_ge hb⟩
  exact Nat.find_min hex htm hbad

#print axioms exists_minimal_counterexample
#print axioms low_counter_has_zero_row
#print axioms high_counter_has_zero_row
#print axioms zero_victim_normal_form
#print axioms low_counter_zero_victim_normal_form
#print axioms high_counter_zero_victim_normal_form
#print axioms low_minimal_counter_zero_victim_normal_form
#print axioms high_minimal_counter_zero_victim_normal_form
end Jsp404.ThirdStripNormalForm
