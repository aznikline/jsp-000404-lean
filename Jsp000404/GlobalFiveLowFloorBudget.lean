import Jsp000404.GapDefectStructure

namespace Jsp404.GlobalFiveLowFloorBudget

/-- Necessary coarse budget for four genuine cyclic gaps. -/
def CoarseBudget (n : ℕ) (g : Fin 4 → ℝ) : Prop :=
  (∃ i, (n : ℝ)-1 ≤ g i) ∨
    ∃ i j, i ≠ j ∧ 1 ≤ g i ∧ 1 ≤ g j ∧ (n : ℝ) ≤ g i+g j

/-- Defect two yields the coarse one-gap / two-gap budget with no
anchored-row, positive-window, or saturation assumptions. -/
theorem coarseBudget_of_floor {n : ℕ} (hn : 3 ≤ n) (g : Fin 4 → ℝ)
    (hg : ∀ i, 0 ≤ g i)
    (hcells : (∑ i : Fin 4, ⌊g i⌋₊) ≤ n)
    (hdef : (∑ i : Fin 4, if 1 ≤ ⌊g i⌋₊ then (1 : ℕ) else 0) +
      (n-(∑ i : Fin 4, ⌊g i⌋₊)) = 2) : CoarseBudget n g := by
  let q0 : ℕ := ⌊g 0⌋₊
  have hf0 : (q0 : ℝ) ≤ g 0 := Nat.floor_le (hg 0)
  let q1 : ℕ := ⌊g 1⌋₊
  have hf1 : (q1 : ℝ) ≤ g 1 := Nat.floor_le (hg 1)
  let q2 : ℕ := ⌊g 2⌋₊
  have hf2 : (q2 : ℝ) ≤ g 2 := Nat.floor_le (hg 2)
  let q3 : ℕ := ⌊g 3⌋₊
  have hf3 : (q3 : ℝ) ≤ g 3 := Nat.floor_le (hg 3)
  have hcells' : q0+q1+q2+q3 ≤ n := by
    simpa only [Fin.sum_univ_four, q0, q1, q2, q3] using hcells
  have hdef' : (if 1 ≤ q0 then 1 else 0) + (if 1 ≤ q1 then 1 else 0) +
      (if 1 ≤ q2 then 1 else 0) + (if 1 ≤ q3 then 1 else 0) +
      (n-(q0+q1+q2+q3)) = 2 := by
    simpa only [Fin.sum_univ_four, q0, q1, q2, q3] using hdef
  by_cases hq0 : 1 ≤ q0
  ·
    by_cases hq1 : 1 ≤ q1
    ·
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          exfalso; omega
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqsum : q0+q1=n := by omega
          have hsum : (q0 : ℝ)+(q1 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q0 := by exact_mod_cast hq0
          have hb : (1 : ℝ) ≤ q1 := by exact_mod_cast hq1
          exact Or.inr ⟨0, 1, by decide, by linarith [hf0], by linarith [hf1], by linarith [hf0, hf1]⟩
    ·
      have hz1 : q1=0 := by omega
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqsum : q0+q2=n := by omega
          have hsum : (q0 : ℝ)+(q2 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q0 := by exact_mod_cast hq0
          have hb : (1 : ℝ) ≤ q2 := by exact_mod_cast hq2
          exact Or.inr ⟨0, 2, by decide, by linarith [hf0], by linarith [hf2], by linarith [hf0, hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqsum : q0+q3=n := by omega
          have hsum : (q0 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q0 := by exact_mod_cast hq0
          have hb : (1 : ℝ) ≤ q3 := by exact_mod_cast hq3
          exact Or.inr ⟨0, 3, by decide, by linarith [hf0], by linarith [hf3], by linarith [hf0, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqa : q0=n-1 := by omega
          have hr : (q0 : ℝ) = (n : ℝ)-1 := by
            rw [hqa, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          exact Or.inl ⟨0, by linarith [hf0]⟩
  ·
    have hz0 : q0=0 := by omega
    by_cases hq1 : 1 ≤ q1
    ·
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqsum : q1+q2=n := by omega
          have hsum : (q1 : ℝ)+(q2 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q1 := by exact_mod_cast hq1
          have hb : (1 : ℝ) ≤ q2 := by exact_mod_cast hq2
          exact Or.inr ⟨1, 2, by decide, by linarith [hf1], by linarith [hf2], by linarith [hf1, hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqsum : q1+q3=n := by omega
          have hsum : (q1 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q1 := by exact_mod_cast hq1
          have hb : (1 : ℝ) ≤ q3 := by exact_mod_cast hq3
          exact Or.inr ⟨1, 3, by decide, by linarith [hf1], by linarith [hf3], by linarith [hf1, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqa : q1=n-1 := by omega
          have hr : (q1 : ℝ) = (n : ℝ)-1 := by
            rw [hqa, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          exact Or.inl ⟨1, by linarith [hf1]⟩
    ·
      have hz1 : q1=0 := by omega
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          have hqsum : q2+q3=n := by omega
          have hsum : (q2 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q2 := by exact_mod_cast hq2
          have hb : (1 : ℝ) ≤ q3 := by exact_mod_cast hq3
          exact Or.inr ⟨2, 3, by decide, by linarith [hf2], by linarith [hf3], by linarith [hf2, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqa : q2=n-1 := by omega
          have hr : (q2 : ℝ) = (n : ℝ)-1 := by
            rw [hqa, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          exact Or.inl ⟨2, by linarith [hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqa : q3=n-1 := by omega
          have hr : (q3 : ℝ) = (n : ℝ)-1 := by
            rw [hqa, Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          exact Or.inl ⟨3, by linarith [hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          exfalso; omega


/-- The same genuine cyclic budget holds for defect at most two,
including a saturated row. -/
theorem coarseBudget_of_floor_le_two {n : ℕ} (hn : 3 ≤ n) (g : Fin 4 → ℝ)
    (hg : ∀ i, 0 ≤ g i)
    (hcells : (∑ i : Fin 4, ⌊g i⌋₊) ≤ n)
    (hdef : (∑ i : Fin 4, if 1 ≤ ⌊g i⌋₊ then (1 : ℕ) else 0) +
      (n-(∑ i : Fin 4, ⌊g i⌋₊)) ≤ 2) : CoarseBudget n g := by
  let q0 : ℕ := ⌊g 0⌋₊
  have hf0 : (q0 : ℝ) ≤ g 0 := Nat.floor_le (hg 0)
  let q1 : ℕ := ⌊g 1⌋₊
  have hf1 : (q1 : ℝ) ≤ g 1 := Nat.floor_le (hg 1)
  let q2 : ℕ := ⌊g 2⌋₊
  have hf2 : (q2 : ℝ) ≤ g 2 := Nat.floor_le (hg 2)
  let q3 : ℕ := ⌊g 3⌋₊
  have hf3 : (q3 : ℝ) ≤ g 3 := Nat.floor_le (hg 3)
  have hcells' : q0+q1+q2+q3 ≤ n := by
    simpa only [Fin.sum_univ_four, q0, q1, q2, q3] using hcells
  have hdef' : (if 1 ≤ q0 then 1 else 0) + (if 1 ≤ q1 then 1 else 0) +
      (if 1 ≤ q2 then 1 else 0) + (if 1 ≤ q3 then 1 else 0) +
      (n-(q0+q1+q2+q3)) ≤ 2 := by
    simpa only [Fin.sum_univ_four, q0, q1, q2, q3] using hdef
  by_cases hq0 : 1 ≤ q0
  ·
    by_cases hq1 : 1 ≤ q1
    ·
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          exfalso; omega
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqsum : q0+q1=n := by omega
          have hsum : (q0 : ℝ)+(q1 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q0 := by exact_mod_cast hq0
          have hb : (1 : ℝ) ≤ q1 := by exact_mod_cast hq1
          exact Or.inr ⟨0, 1, by decide, by linarith [hf0], by linarith [hf1], by linarith [hf0, hf1]⟩
    ·
      have hz1 : q1=0 := by omega
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqsum : q0+q2=n := by omega
          have hsum : (q0 : ℝ)+(q2 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q0 := by exact_mod_cast hq0
          have hb : (1 : ℝ) ≤ q2 := by exact_mod_cast hq2
          exact Or.inr ⟨0, 2, by decide, by linarith [hf0], by linarith [hf2], by linarith [hf0, hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqsum : q0+q3=n := by omega
          have hsum : (q0 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q0 := by exact_mod_cast hq0
          have hb : (1 : ℝ) ≤ q3 := by exact_mod_cast hq3
          exact Or.inr ⟨0, 3, by decide, by linarith [hf0], by linarith [hf3], by linarith [hf0, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqa : n-1 ≤ q0 := by omega
          have hr : (n : ℝ)-1 ≤ (q0 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨0, by linarith [hf0]⟩
  ·
    have hz0 : q0=0 := by omega
    by_cases hq1 : 1 ≤ q1
    ·
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqsum : q1+q2=n := by omega
          have hsum : (q1 : ℝ)+(q2 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q1 := by exact_mod_cast hq1
          have hb : (1 : ℝ) ≤ q2 := by exact_mod_cast hq2
          exact Or.inr ⟨1, 2, by decide, by linarith [hf1], by linarith [hf2], by linarith [hf1, hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqsum : q1+q3=n := by omega
          have hsum : (q1 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q1 := by exact_mod_cast hq1
          have hb : (1 : ℝ) ≤ q3 := by exact_mod_cast hq3
          exact Or.inr ⟨1, 3, by decide, by linarith [hf1], by linarith [hf3], by linarith [hf1, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqa : n-1 ≤ q1 := by omega
          have hr : (n : ℝ)-1 ≤ (q1 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨1, by linarith [hf1]⟩
    ·
      have hz1 : q1=0 := by omega
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          have hqsum : q2+q3=n := by omega
          have hsum : (q2 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
          have ha : (1 : ℝ) ≤ q2 := by exact_mod_cast hq2
          have hb : (1 : ℝ) ≤ q3 := by exact_mod_cast hq3
          exact Or.inr ⟨2, 3, by decide, by linarith [hf2], by linarith [hf3], by linarith [hf2, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqa : n-1 ≤ q2 := by omega
          have hr : (n : ℝ)-1 ≤ (q2 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q2 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨2, by linarith [hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqa : n-1 ≤ q3 := by omega
          have hr : (n : ℝ)-1 ≤ (q3 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q3 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨3, by linarith [hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          exfalso; omega

#print axioms coarseBudget_of_floor_le_two
#print axioms coarseBudget_of_floor

/-- Integer floors strengthen the two-gap alternative from one to two.
If an active floor is one, the other floor already supplies a single
gap of size at least n-1. -/
def StrongBudget (n : ℕ) (g : Fin 4 → ℝ) : Prop :=
  (∃ i, (n : ℝ)-1 ≤ g i) ∨
    ∃ i j, i ≠ j ∧ 2 ≤ g i ∧ 2 ≤ g j ∧ (n : ℝ) ≤ g i+g j

theorem strongBudget_of_floor_le_two {n : ℕ} (hn : 3 ≤ n) (g : Fin 4 → ℝ)
    (hg : ∀ i, 0 ≤ g i)
    (hcells : (∑ i : Fin 4, ⌊g i⌋₊) ≤ n)
    (hdef : (∑ i : Fin 4, if 1 ≤ ⌊g i⌋₊ then (1 : ℕ) else 0) +
      (n-(∑ i : Fin 4, ⌊g i⌋₊)) ≤ 2) : StrongBudget n g := by
  let q0 : ℕ := ⌊g 0⌋₊
  have hf0 : (q0 : ℝ) ≤ g 0 := Nat.floor_le (hg 0)
  let q1 : ℕ := ⌊g 1⌋₊
  have hf1 : (q1 : ℝ) ≤ g 1 := Nat.floor_le (hg 1)
  let q2 : ℕ := ⌊g 2⌋₊
  have hf2 : (q2 : ℝ) ≤ g 2 := Nat.floor_le (hg 2)
  let q3 : ℕ := ⌊g 3⌋₊
  have hf3 : (q3 : ℝ) ≤ g 3 := Nat.floor_le (hg 3)
  have hcells' : q0+q1+q2+q3 ≤ n := by
    simpa only [Fin.sum_univ_four, q0, q1, q2, q3] using hcells
  have hdef' : (if 1 ≤ q0 then 1 else 0) + (if 1 ≤ q1 then 1 else 0) +
      (if 1 ≤ q2 then 1 else 0) + (if 1 ≤ q3 then 1 else 0) +
      (n-(q0+q1+q2+q3)) ≤ 2 := by
    simpa only [Fin.sum_univ_four, q0, q1, q2, q3] using hdef
  by_cases hq0 : 1 ≤ q0
  ·
    by_cases hq1 : 1 ≤ q1
    ·
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          exfalso; omega
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqsum : q0+q1=n := by omega
          by_cases hqa1 : q0=1
          ·
            have hqb : n-1 ≤ q1 := by omega
            have hr : (n : ℝ)-1 ≤ (q1 : ℝ) := by
              have hc : ((n-1 : ℕ) : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hqb
              simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
            exact Or.inl ⟨1, by linarith [hf1]⟩
          ·
            by_cases hqb1 : q1=1
            ·
              have hqa : n-1 ≤ q0 := by omega
              have hr : (n : ℝ)-1 ≤ (q0 : ℝ) := by
                have hc : ((n-1 : ℕ) : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hqa
                simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
              exact Or.inl ⟨0, by linarith [hf0]⟩
            ·
              have hsum : (q0 : ℝ)+(q1 : ℝ) = n := by exact_mod_cast hqsum
              have hqa2 : 2 ≤ q0 := by omega
              have hqb2 : 2 ≤ q1 := by omega
              have ha : (2 : ℝ) ≤ q0 := by exact_mod_cast hqa2
              have hb : (2 : ℝ) ≤ q1 := by exact_mod_cast hqb2
              exact Or.inr ⟨0, 1, by decide, by linarith [hf0], by linarith [hf1], by linarith [hf0, hf1]⟩
    ·
      have hz1 : q1=0 := by omega
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqsum : q0+q2=n := by omega
          by_cases hqa1 : q0=1
          ·
            have hqb : n-1 ≤ q2 := by omega
            have hr : (n : ℝ)-1 ≤ (q2 : ℝ) := by
              have hc : ((n-1 : ℕ) : ℝ) ≤ (q2 : ℝ) := by exact_mod_cast hqb
              simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
            exact Or.inl ⟨2, by linarith [hf2]⟩
          ·
            by_cases hqb1 : q2=1
            ·
              have hqa : n-1 ≤ q0 := by omega
              have hr : (n : ℝ)-1 ≤ (q0 : ℝ) := by
                have hc : ((n-1 : ℕ) : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hqa
                simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
              exact Or.inl ⟨0, by linarith [hf0]⟩
            ·
              have hsum : (q0 : ℝ)+(q2 : ℝ) = n := by exact_mod_cast hqsum
              have hqa2 : 2 ≤ q0 := by omega
              have hqb2 : 2 ≤ q2 := by omega
              have ha : (2 : ℝ) ≤ q0 := by exact_mod_cast hqa2
              have hb : (2 : ℝ) ≤ q2 := by exact_mod_cast hqb2
              exact Or.inr ⟨0, 2, by decide, by linarith [hf0], by linarith [hf2], by linarith [hf0, hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqsum : q0+q3=n := by omega
          by_cases hqa1 : q0=1
          ·
            have hqb : n-1 ≤ q3 := by omega
            have hr : (n : ℝ)-1 ≤ (q3 : ℝ) := by
              have hc : ((n-1 : ℕ) : ℝ) ≤ (q3 : ℝ) := by exact_mod_cast hqb
              simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
            exact Or.inl ⟨3, by linarith [hf3]⟩
          ·
            by_cases hqb1 : q3=1
            ·
              have hqa : n-1 ≤ q0 := by omega
              have hr : (n : ℝ)-1 ≤ (q0 : ℝ) := by
                have hc : ((n-1 : ℕ) : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hqa
                simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
              exact Or.inl ⟨0, by linarith [hf0]⟩
            ·
              have hsum : (q0 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
              have hqa2 : 2 ≤ q0 := by omega
              have hqb2 : 2 ≤ q3 := by omega
              have ha : (2 : ℝ) ≤ q0 := by exact_mod_cast hqa2
              have hb : (2 : ℝ) ≤ q3 := by exact_mod_cast hqb2
              exact Or.inr ⟨0, 3, by decide, by linarith [hf0], by linarith [hf3], by linarith [hf0, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_left hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqa : n-1 ≤ q0 := by omega
          have hr : (n : ℝ)-1 ≤ (q0 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨0, by linarith [hf0]⟩
  ·
    have hz0 : q0=0 := by omega
    by_cases hq1 : 1 ≤ q1
    ·
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          exfalso; omega
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqsum : q1+q2=n := by omega
          by_cases hqa1 : q1=1
          ·
            have hqb : n-1 ≤ q2 := by omega
            have hr : (n : ℝ)-1 ≤ (q2 : ℝ) := by
              have hc : ((n-1 : ℕ) : ℝ) ≤ (q2 : ℝ) := by exact_mod_cast hqb
              simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
            exact Or.inl ⟨2, by linarith [hf2]⟩
          ·
            by_cases hqb1 : q2=1
            ·
              have hqa : n-1 ≤ q1 := by omega
              have hr : (n : ℝ)-1 ≤ (q1 : ℝ) := by
                have hc : ((n-1 : ℕ) : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hqa
                simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
              exact Or.inl ⟨1, by linarith [hf1]⟩
            ·
              have hsum : (q1 : ℝ)+(q2 : ℝ) = n := by exact_mod_cast hqsum
              have hqa2 : 2 ≤ q1 := by omega
              have hqb2 : 2 ≤ q2 := by omega
              have ha : (2 : ℝ) ≤ q1 := by exact_mod_cast hqa2
              have hb : (2 : ℝ) ≤ q2 := by exact_mod_cast hqb2
              exact Or.inr ⟨1, 2, by decide, by linarith [hf1], by linarith [hf2], by linarith [hf1, hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqsum : q1+q3=n := by omega
          by_cases hqa1 : q1=1
          ·
            have hqb : n-1 ≤ q3 := by omega
            have hr : (n : ℝ)-1 ≤ (q3 : ℝ) := by
              have hc : ((n-1 : ℕ) : ℝ) ≤ (q3 : ℝ) := by exact_mod_cast hqb
              simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
            exact Or.inl ⟨3, by linarith [hf3]⟩
          ·
            by_cases hqb1 : q3=1
            ·
              have hqa : n-1 ≤ q1 := by omega
              have hr : (n : ℝ)-1 ≤ (q1 : ℝ) := by
                have hc : ((n-1 : ℕ) : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hqa
                simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
              exact Or.inl ⟨1, by linarith [hf1]⟩
            ·
              have hsum : (q1 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
              have hqa2 : 2 ≤ q1 := by omega
              have hqb2 : 2 ≤ q3 := by omega
              have ha : (2 : ℝ) ≤ q1 := by exact_mod_cast hqa2
              have hb : (2 : ℝ) ≤ q3 := by exact_mod_cast hqb2
              exact Or.inr ⟨1, 3, by decide, by linarith [hf1], by linarith [hf3], by linarith [hf1, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_left hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          have hqa : n-1 ≤ q1 := by omega
          have hr : (n : ℝ)-1 ≤ (q1 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q1 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨1, by linarith [hf1]⟩
    ·
      have hz1 : q1=0 := by omega
      by_cases hq2 : 1 ≤ q2
      ·
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_left hq3] at hdef'
          have hqsum : q2+q3=n := by omega
          by_cases hqa1 : q2=1
          ·
            have hqb : n-1 ≤ q3 := by omega
            have hr : (n : ℝ)-1 ≤ (q3 : ℝ) := by
              have hc : ((n-1 : ℕ) : ℝ) ≤ (q3 : ℝ) := by exact_mod_cast hqb
              simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
            exact Or.inl ⟨3, by linarith [hf3]⟩
          ·
            by_cases hqb1 : q3=1
            ·
              have hqa : n-1 ≤ q2 := by omega
              have hr : (n : ℝ)-1 ≤ (q2 : ℝ) := by
                have hc : ((n-1 : ℕ) : ℝ) ≤ (q2 : ℝ) := by exact_mod_cast hqa
                simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
              exact Or.inl ⟨2, by linarith [hf2]⟩
            ·
              have hsum : (q2 : ℝ)+(q3 : ℝ) = n := by exact_mod_cast hqsum
              have hqa2 : 2 ≤ q2 := by omega
              have hqb2 : 2 ≤ q3 := by omega
              have ha : (2 : ℝ) ≤ q2 := by exact_mod_cast hqa2
              have hb : (2 : ℝ) ≤ q3 := by exact_mod_cast hqb2
              exact Or.inr ⟨2, 3, by decide, by linarith [hf2], by linarith [hf3], by linarith [hf2, hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_left hq2, ite_eq_right hq3] at hdef'
          have hqa : n-1 ≤ q2 := by omega
          have hr : (n : ℝ)-1 ≤ (q2 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q2 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨2, by linarith [hf2]⟩
      ·
        have hz2 : q2=0 := by omega
        by_cases hq3 : 1 ≤ q3
        ·
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_left hq3] at hdef'
          have hqa : n-1 ≤ q3 := by omega
          have hr : (n : ℝ)-1 ≤ (q3 : ℝ) := by
            have hc : ((n-1 : ℕ) : ℝ) ≤ (q3 : ℝ) := by exact_mod_cast hqa
            simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc
          exact Or.inl ⟨3, by linarith [hf3]⟩
        ·
          have hz3 : q3=0 := by omega
          simp only [ite_eq_right hq0, ite_eq_right hq1, ite_eq_right hq2, ite_eq_right hq3] at hdef'
          exfalso; omega

#print axioms strongBudget_of_floor_le_two

end Jsp404.GlobalFiveLowFloorBudget
