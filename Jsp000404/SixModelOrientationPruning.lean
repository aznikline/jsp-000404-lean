import Jsp000404.SixModelBudget

/-!
A decreasing shared-chord triangle forces defect at least three at its
middle centre. The proof uses the complete sorted four-chord row: each
adjacent change of side forces a unit gap, so subdivisions are accounted for.
-/

namespace Jsp404.SixModelOrientationPruning

open SixModelCompression SixModelBudget

private theorem row_indexing {n : ℕ} (M : ModelSix n) (i : Fin 5) :
    ∃ idx : Fin 4 → Fin 5,
      M.rowxs i = List.ofFn (fun p => M.d i (idx p)) ∧
      Monotone (fun p => M.d i (idx p)) ∧
      (∀ p, idx p ≠ i) ∧ (∀ j, j ≠ i → ∃ p, idx p = j) := by
  have hp := M.row_perm i
  have hp' : Relation.Comp (fun (xs : List ℝ) (js : List (Fin 5)) => xs = js.map (M.d i))
      (fun (js ks : List (Fin 5)) => js.Perm ks) (M.rowxs i) ((List.finRange 5).erase i) :=
    (congrFun (congrFun (List.eq_map_comp_perm (M.d i)) (M.rowxs i))
      ((List.finRange 5).erase i)).mpr hp
  obtain ⟨js, hrow, hperm⟩ := hp'
  have hlen : js.length = 4 := by
    rw [hperm.length_eq, List.length_erase_of_mem (List.mem_finRange i), List.length_finRange]
  let idx : Fin 4 → Fin 5 := fun p => js.get (Fin.cast hlen.symm p)
  have hofn : List.ofFn idx = js := by
    exact (List.ofFn_congr hlen js.get).symm.trans (List.ofFn_get js)
  have hrow' : M.rowxs i = List.ofFn (fun p => M.d i (idx p)) := by
    rw [List.ofFn_comp', hofn]
    exact hrow
  refine ⟨idx, hrow', ?_, ?_, ?_⟩
  · have hs := M.row_sorted i
    rw [hrow', List.pairwise_ofFn] at hs
    intro p q hpq
    rcases eq_or_lt_of_le hpq with h | h
    · rw [h]
    · exact hs h
  · intro p
    have hm : idx p ∈ js := by
      rw [← hofn]
      exact List.mem_ofFn.mpr ⟨p, rfl⟩
    have hj := hperm.mem_iff.mp hm
    exact ((List.nodup_finRange 5).mem_erase_iff.mp hj).1
  · intro j hji
    have hm : j ∈ js := hperm.mem_iff.mpr
      ((List.nodup_finRange 5).mem_erase_iff.mpr ⟨hji, List.mem_finRange j⟩)
    rw [← hofn] at hm
    exact List.mem_ofFn.mp hm

private theorem unit_indicator {g : ℝ} (hg : 1 ≤ g) : min ⌊g⌋₊ 1 = 1 := by
  have h : 1 ≤ ⌊g⌋₊ := (Nat.le_floor_iff' (R := ℝ) one_ne_zero).mpr (by simpa using hg)
  omega

private theorem braid_forces_three (b : Fin 4 → Bool)
    (hb : ∃ r l, r < l ∧ b r = true ∧ b l = false) :
    3 ≤ (if b 0 then 1 else 0) +
      (if b 0 = b 1 then 0 else 1) +
      (if b 1 = b 2 then 0 else 1) +
      (if b 2 = b 3 then 0 else 1) +
      (if b 3 then 0 else 1 : ℕ) := by
  have h : ∀ b : Fin 4 → Bool, (∃ r l, r < l ∧ b r = true ∧ b l = false) →
      3 ≤ (if b 0 then 1 else 0) +
        (if b 0 = b 1 then 0 else 1) +
        (if b 1 = b 2 then 0 else 1) +
        (if b 2 = b 3 then 0 else 1) +
        (if b 3 then 0 else 1 : ℕ) := by decide
  exact h b hb

private theorem braid_support (left right : ℝ) (x : Fin 4 → ℝ) (b : Fin 4 → Bool)
    (hfirst : b 0 = true → left + 1 ≤ x 0)
    (hlast : b 3 = false → x 3 + 1 ≤ right)
    (h01 : b 0 ≠ b 1 → x 0 + 1 ≤ x 1)
    (h12 : b 1 ≠ b 2 → x 1 + 1 ≤ x 2)
    (h23 : b 2 ≠ b 3 → x 2 + 1 ≤ x 3)
    (hb : ∃ r l, r < l ∧ b r = true ∧ b l = false) :
    3 ≤ linearBigCount 1 left right (List.ofFn x) := by
  have h0 : (if b 0 then 1 else 0 : ℕ) ≤ min ⌊x 0 - left⌋₊ 1 := by
    cases h : b 0 with
    | false => exact Nat.zero_le _
    | true =>
      change 1 ≤ _
      rw [unit_indicator (by linarith [hfirst h] : 1 ≤ x 0 - left)]
  have h1 : (if b 0 = b 1 then 0 else 1 : ℕ) ≤ min ⌊x 1 - x 0⌋₊ 1 := by
    by_cases h : b 0 = b 1
    · simp [h]
    · simp [h, unit_indicator (by linarith [h01 h] : 1 ≤ x 1 - x 0)]
  have h2 : (if b 1 = b 2 then 0 else 1 : ℕ) ≤ min ⌊x 2 - x 1⌋₊ 1 := by
    by_cases h : b 1 = b 2
    · simp [h]
    · simp [h, unit_indicator (by linarith [h12 h] : 1 ≤ x 2 - x 1)]
  have h3 : (if b 2 = b 3 then 0 else 1 : ℕ) ≤ min ⌊x 3 - x 2⌋₊ 1 := by
    by_cases h : b 2 = b 3
    · simp [h]
    · simp [h, unit_indicator (by linarith [h23 h] : 1 ≤ x 3 - x 2)]
  have h4 : (if b 3 then 0 else 1 : ℕ) ≤ min ⌊right - x 3⌋₊ 1 := by
    cases h : b 3 with
    | false =>
      change 1 ≤ _
      rw [unit_indicator (by linarith [hlast h] : 1 ≤ right - x 3)]
    | true => exact Nat.zero_le _
  have hc := braid_forces_three b hb
  simp only [List.ofFn_succ, List.ofFn_zero, linearBigCount, div_one]
  change 3 ≤ min ⌊x 0 - left⌋₊ 1 + (min ⌊x 1 - x 0⌋₊ 1 +
    (min ⌊x 2 - x 1⌋₊ 1 + (min ⌊x 3 - x 2⌋₊ 1 + min ⌊right - x 3⌋₊ 1)))
  omega

private theorem opposite_unit {n : ℕ} (M : ModelSix n) (i a b : Fin 5)
    (hne_a : a ≠ i) (hne_b : b ≠ i)
    (hopp : decide (i < a) ≠ decide (i < b))
    (hab : M.d i a ≤ M.d i b) : M.d i a + 1 ≤ M.d i b := by
  by_cases ha : i < a
  · have hb : b < i := by
      have hh : ¬i < b := by intro h; exact hopp (by simp [ha, h])
      exact lt_of_le_of_ne (le_of_not_gt hh) hne_b
    rcases M.triangle b i a hb ha with h | h
    · have hs := M.symm i b hne_b.symm
      linarith [h.1]
    · have hs := M.symm i b hne_b.symm
      linarith [h.1]
  · have hia : a < i := lt_of_le_of_ne (le_of_not_gt ha) hne_a
    have hib : i < b := by
      by_contra h
      exact hopp (by simp [ha, h])
    rcases M.triangle a i b hia hib with h | h
    · have hs := M.symm i a hne_a.symm
      linarith [h.1]
    · have hs := M.symm i a hne_a.symm
      linarith [h.1]

/-- Every decreasing middle triangle forces at least three genuine active gaps
in that centre's complete sorted row, hence defect at least three. -/
theorem decreasing_middle_defect_ge_three {n : ℕ} (M : ModelSix n)
    (i j k : Fin 5) (hij : i < j) (hjk : j < k)
    (hdec : M.d j k < M.d i j) :
    3 ≤ SixModelCompression.rowDefect M j := by
  obtain ⟨idx, hrow, hmono, hne, hcover⟩ := row_indexing M j
  let x : Fin 4 → ℝ := fun p => M.d j (idx p)
  let b : Fin 4 → Bool := fun p => decide (j < idx p)
  have hfirst : b 0 = true → M.theta j + 1 ≤ x 0 := by
    intro h
    have hj : j < idx 0 := of_decide_eq_true h
    exact (M.corridor j (idx 0) hj).1
  have hlast : b 3 = false → x 3 + 1 ≤ M.theta j + ((n : ℝ) + M.delta) := by
    intro h
    have hj : idx 3 < j := by
      have hh : ¬j < idx 3 := of_decide_eq_false h
      exact lt_of_le_of_ne (le_of_not_gt hh) (hne 3)
    have hc := (M.corridor (idx 3) j hj).2
    have hs := M.symm j (idx 3) (hne 3).symm
    dsimp [x]
    linarith
  have hadj (p q : Fin 4) (hpq : p ≤ q) : b p ≠ b q → x p + 1 ≤ x q := by
    intro h
    exact opposite_unit M j (idx p) (idx q) (hne p) (hne q) h (hmono hpq)
  obtain ⟨l, hl⟩ := hcover i (ne_of_lt hij)
  obtain ⟨r, hr⟩ := hcover k (ne_of_gt hjk)
  have hx : x r < x l := by
    dsimp [x]
    rw [hr, hl, M.symm j i (ne_of_gt hij)]
    exact hdec
  have hrl : r < l := by
    by_contra h
    have hh := hmono (le_of_not_gt h)
    exact (not_le_of_gt hx) hh
  have hb : ∃ r l, r < l ∧ b r = true ∧ b l = false := by
    refine ⟨r, l, hrl, ?_, ?_⟩
    · simp [b, hr, hjk]
    · simp [b, hl, not_lt_of_gt hij]
  have hs := braid_support (M.theta j) (M.theta j + ((n : ℝ) + M.delta)) x b
    hfirst hlast (hadj 0 1 (by decide)) (hadj 1 2 (by decide)) (hadj 2 3 (by decide)) hb
  have hbig : 3 ≤ support M j := by
    change 3 ≤ linearBigCount 1 (M.theta j) (M.theta j + ((n : ℝ) + M.delta)) (M.rowxs j)
    rw [hrow]
    exact hs
  exact le_trans hbig (support_le_defect M j)

/-- In a defect-two row every ordered triangle through that middle centre
has the increasing orientation. -/
theorem defect_two_middle_increasing {n : ℕ} (M : ModelSix n)
    (i j k : Fin 5) (hij : i < j) (hjk : j < k)
    (hdef : SixModelCompression.rowDefect M j = 2) :
    M.d i j + 1 ≤ M.d j k ∧ M.d i j < M.d i k ∧ M.d i k < M.d j k := by
  rcases M.triangle i j k hij hjk with h | h
  · exact h
  · have h3 := decreasing_middle_defect_ge_three M i j k hij hjk
      (lt_trans h.2.1 h.2.2)
    omega

#print axioms decreasing_middle_defect_ge_three
#print axioms defect_two_middle_increasing

end Jsp404.SixModelOrientationPruning
