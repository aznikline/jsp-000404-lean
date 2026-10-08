import Mathlib

set_option maxHeartbeats 1600000

namespace R2N4

open List

/-- **Scalar model of the `n = 4` six-centre terminal geometry.** -/
structure N4Model where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 4 * lam <= p ∧ p < 5 * lam
  t : Fin 5 → ℝ
  ht : StrictMono t
  ht0 : 0 <= t 0
  ht4 : t 4 <= p - 4 * lam
  d : Fin 5 → Fin 5 → ℝ
  hcor : ∀ i j : Fin 5, i < j →
    t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin 5, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)
abbrev RowSig1 (lam p tl : ℝ) (x0 x1 x2 x3 : ℝ) : Prop :=
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)

abbrev RowSig2 (lam p tl : ℝ) (x0 x1 x2 x3 : ℝ) : Prop :=
    (3 * lam <= (x0 - tl) ∧ (x0 - tl) < 4 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 3 * lam <= (x1 - x0) ∧ (x1 - x0) < 4 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 3 * lam <= (x2 - x1) ∧ (x2 - x1) < 4 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 3 * lam <= (x3 - x2) ∧ (x3 - x2) < 4 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 3 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 4 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)


theorem mem4or {u x0 x1 x2 x3 : ℝ} (h : u ∈ [x0, x1, x2, x3]) :
    u = x0 ∨ u = x1 ∨ u = x2 ∨ u = x3 := by
  simpa using h

/-- A value occurring twice in a 4-list occupies an ordered pair of slots. -/
theorem two_slots {v c0 c1 c2 c3 : ℝ} (h : 2 ≤ List.count v [c0, c1, c2, c3]) :
    (c0 = v ∧ c1 = v) ∨ (c0 = v ∧ c2 = v) ∨ (c0 = v ∧ c3 = v) ∨
    (c1 = v ∧ c2 = v) ∨ (c1 = v ∧ c3 = v) ∨ (c2 = v ∧ c3 = v) := by
  classical
  by_cases h0 : c0 = v <;> by_cases h1 : c1 = v <;> by_cases h2 : c2 = v <;>
    by_cases h3 : c3 = v <;> simp_all [List.count]


abbrev MSig1_0 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ z - tl) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 6 * lam) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig1_1 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig1_2 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig1_3 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig1_4 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ tl + p - z) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 6 * lam) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam)

abbrev MSig2_0 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 3 * lam ≤ z - tl) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 6 * lam) ∧
    (c0 - tl < 4 * lam ∨ c1 - tl < 4 * lam ∨ c2 - tl < 4 * lam ∨ c3 - tl < 4 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig2_1 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 3 * lam ≤ c1 - c0 ∧ c1 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 3 * lam ≤ c2 - c0 ∧ c2 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 3 * lam ≤ c3 - c0 ∧ c3 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 3 * lam ≤ c0 - c1 ∧ c0 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 3 * lam ≤ c2 - c1 ∧ c2 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 3 * lam ≤ c3 - c1 ∧ c3 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 3 * lam ≤ c0 - c2 ∧ c0 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 3 * lam ≤ c1 - c2 ∧ c1 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 3 * lam ≤ c3 - c2 ∧ c3 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 3 * lam ≤ c0 - c3 ∧ c0 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 3 * lam ≤ c1 - c3 ∧ c1 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 3 * lam ≤ c2 - c3 ∧ c2 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 8 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig2_2 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 3 * lam ≤ c1 - c0 ∧ c1 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 3 * lam ≤ c2 - c0 ∧ c2 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 3 * lam ≤ c3 - c0 ∧ c3 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 3 * lam ≤ c0 - c1 ∧ c0 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 3 * lam ≤ c2 - c1 ∧ c2 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 3 * lam ≤ c3 - c1 ∧ c3 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 3 * lam ≤ c0 - c2 ∧ c0 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 3 * lam ≤ c1 - c2 ∧ c1 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 3 * lam ≤ c3 - c2 ∧ c3 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 3 * lam ≤ c0 - c3 ∧ c0 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 3 * lam ≤ c1 - c3 ∧ c1 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 3 * lam ≤ c2 - c3 ∧ c2 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 8 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig2_3 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    ((c0 < c1 ∧ 3 * lam ≤ c1 - c0 ∧ c1 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 3 * lam ≤ c2 - c0 ∧ c2 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 3 * lam ≤ c3 - c0 ∧ c3 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 3 * lam ≤ c0 - c1 ∧ c0 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 3 * lam ≤ c2 - c1 ∧ c2 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 3 * lam ≤ c3 - c1 ∧ c3 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 3 * lam ≤ c0 - c2 ∧ c0 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 3 * lam ≤ c1 - c2 ∧ c1 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 3 * lam ≤ c3 - c2 ∧ c3 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 3 * lam ≤ c0 - c3 ∧ c0 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 3 * lam ≤ c1 - c3 ∧ c1 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 3 * lam ≤ c2 - c3 ∧ c2 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 8 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam)

abbrev MSig2_4 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 3 * lam ≤ tl + p - z) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 6 * lam) ∧
    (tl + p - c0 < 4 * lam ∨ tl + p - c1 < 4 * lam ∨ tl + p - c2 < 4 * lam ∨ tl + p - c3 < 4 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam)

abbrev MSig2_0_1 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam) ∧
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam)

abbrev MSig2_0_2 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam) ∧
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam)

abbrev MSig2_0_3 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam) ∧
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam)

abbrev MSig2_0_4 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 6 * lam)

abbrev MSig2_1_2 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam) ∧
    (((c0 < c1 ∧ c1 < c2 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w)) ∨
          (c0 < c1 ∧ c1 < c3 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w)) ∨
          (c0 < c2 ∧ c2 < c1 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w)) ∨
          (c0 < c2 ∧ c2 < c3 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w)) ∨
          (c0 < c3 ∧ c3 < c1 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w)) ∨
          (c0 < c3 ∧ c3 < c2 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w)) ∨
          (c1 < c0 ∧ c0 < c2 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w)) ∨
          (c1 < c0 ∧ c0 < c3 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w)) ∨
          (c1 < c2 ∧ c2 < c0 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w)) ∨
          (c1 < c2 ∧ c2 < c3 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w)) ∨
          (c1 < c3 ∧ c3 < c0 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w)) ∨
          (c1 < c3 ∧ c3 < c2 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w)) ∨
          (c2 < c0 ∧ c0 < c1 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w)) ∨
          (c2 < c0 ∧ c0 < c3 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w)) ∨
          (c2 < c1 ∧ c1 < c0 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w)) ∨
          (c2 < c1 ∧ c1 < c3 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w)) ∨
          (c2 < c3 ∧ c3 < c0 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w)) ∨
          (c2 < c3 ∧ c3 < c1 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w)) ∨
          (c3 < c0 ∧ c0 < c1 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w)) ∨
          (c3 < c0 ∧ c0 < c2 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w)) ∨
          (c3 < c1 ∧ c1 < c0 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w)) ∨
          (c3 < c1 ∧ c1 < c2 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w)) ∨
          (c3 < c2 ∧ c2 < c0 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w)) ∨
          (c3 < c2 ∧ c2 < c1 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w))) ∨
      ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ (c1 ≤ c2 ∨ c3 ≤ c0)) ∨
          (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ (c1 ≤ c3 ∨ c2 ≤ c0)) ∨
          (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ (c2 ≤ c1 ∨ c3 ≤ c0)) ∨
          (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ (c2 ≤ c3 ∨ c1 ≤ c0)) ∨
          (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ (c3 ≤ c1 ∨ c2 ≤ c0)) ∨
          (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ (c3 ≤ c2 ∨ c1 ≤ c0)) ∨
          (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ (c0 ≤ c2 ∨ c3 ≤ c1)) ∨
          (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ (c0 ≤ c3 ∨ c2 ≤ c1)) ∨
          (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ (c2 ≤ c0 ∨ c3 ≤ c1)) ∨
          (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ (c2 ≤ c3 ∨ c0 ≤ c1)) ∨
          (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ (c3 ≤ c0 ∨ c2 ≤ c1)) ∨
          (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ (c3 ≤ c2 ∨ c0 ≤ c1)) ∨
          (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ (c0 ≤ c1 ∨ c3 ≤ c2)) ∨
          (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ (c0 ≤ c3 ∨ c1 ≤ c2)) ∨
          (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ (c1 ≤ c0 ∨ c3 ≤ c2)) ∨
          (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ (c1 ≤ c3 ∨ c0 ≤ c2)) ∨
          (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ (c3 ≤ c0 ∨ c1 ≤ c2)) ∨
          (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ (c3 ≤ c1 ∨ c0 ≤ c2)) ∨
          (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ (c0 ≤ c1 ∨ c2 ≤ c3)) ∨
          (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ (c0 ≤ c2 ∨ c1 ≤ c3)) ∨
          (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ (c1 ≤ c0 ∨ c2 ≤ c3)) ∨
          (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ (c1 ≤ c2 ∨ c0 ≤ c3)) ∨
          (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ (c2 ≤ c0 ∨ c1 ≤ c3)) ∨
          (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ (c2 ≤ c1 ∨ c0 ≤ c3)))) ∧
    ((c0 ≤ c1 ∧ c1 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 ≤ c2 ∧ c2 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 ≤ c3 ∧ c3 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 ≤ c0 ∧ c0 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 ≤ c2 ∧ c2 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 ≤ c3 ∧ c3 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 ≤ c0 ∧ c0 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 ≤ c1 ∧ c1 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 ≤ c3 ∧ c3 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 ≤ c0 ∧ c0 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 ≤ c1 ∧ c1 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 ≤ c2 ∧ c2 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 8 * lam)

abbrev MSig2_1_3 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam) ∧
    (((c0 < c1 ∧ c1 < c2 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w)) ∨
          (c0 < c1 ∧ c1 < c3 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w)) ∨
          (c0 < c2 ∧ c2 < c1 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w)) ∨
          (c0 < c2 ∧ c2 < c3 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w)) ∨
          (c0 < c3 ∧ c3 < c1 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w)) ∨
          (c0 < c3 ∧ c3 < c2 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w)) ∨
          (c1 < c0 ∧ c0 < c2 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w)) ∨
          (c1 < c0 ∧ c0 < c3 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w)) ∨
          (c1 < c2 ∧ c2 < c0 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w)) ∨
          (c1 < c2 ∧ c2 < c3 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w)) ∨
          (c1 < c3 ∧ c3 < c0 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w)) ∨
          (c1 < c3 ∧ c3 < c2 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w)) ∨
          (c2 < c0 ∧ c0 < c1 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w)) ∨
          (c2 < c0 ∧ c0 < c3 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w)) ∨
          (c2 < c1 ∧ c1 < c0 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w)) ∨
          (c2 < c1 ∧ c1 < c3 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w)) ∨
          (c2 < c3 ∧ c3 < c0 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w)) ∨
          (c2 < c3 ∧ c3 < c1 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w)) ∨
          (c3 < c0 ∧ c0 < c1 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w)) ∨
          (c3 < c0 ∧ c0 < c2 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w)) ∨
          (c3 < c1 ∧ c1 < c0 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w)) ∨
          (c3 < c1 ∧ c1 < c2 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w)) ∨
          (c3 < c2 ∧ c2 < c0 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w)) ∨
          (c3 < c2 ∧ c2 < c1 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w))) ∨
      ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ (c1 ≤ c2 ∨ c3 ≤ c0)) ∨
          (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ (c1 ≤ c3 ∨ c2 ≤ c0)) ∨
          (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ (c2 ≤ c1 ∨ c3 ≤ c0)) ∨
          (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ (c2 ≤ c3 ∨ c1 ≤ c0)) ∨
          (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ (c3 ≤ c1 ∨ c2 ≤ c0)) ∨
          (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ (c3 ≤ c2 ∨ c1 ≤ c0)) ∨
          (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ (c0 ≤ c2 ∨ c3 ≤ c1)) ∨
          (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ (c0 ≤ c3 ∨ c2 ≤ c1)) ∨
          (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ (c2 ≤ c0 ∨ c3 ≤ c1)) ∨
          (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ (c2 ≤ c3 ∨ c0 ≤ c1)) ∨
          (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ (c3 ≤ c0 ∨ c2 ≤ c1)) ∨
          (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ (c3 ≤ c2 ∨ c0 ≤ c1)) ∨
          (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ (c0 ≤ c1 ∨ c3 ≤ c2)) ∨
          (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ (c0 ≤ c3 ∨ c1 ≤ c2)) ∨
          (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ (c1 ≤ c0 ∨ c3 ≤ c2)) ∨
          (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ (c1 ≤ c3 ∨ c0 ≤ c2)) ∨
          (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ (c3 ≤ c0 ∨ c1 ≤ c2)) ∨
          (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ (c3 ≤ c1 ∨ c0 ≤ c2)) ∨
          (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ (c0 ≤ c1 ∨ c2 ≤ c3)) ∨
          (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ (c0 ≤ c2 ∨ c1 ≤ c3)) ∨
          (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ (c1 ≤ c0 ∨ c2 ≤ c3)) ∨
          (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ (c1 ≤ c2 ∨ c0 ≤ c3)) ∨
          (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ (c2 ≤ c0 ∨ c1 ≤ c3)) ∨
          (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ (c2 ≤ c1 ∨ c0 ≤ c3)))) ∧
    ((c0 ≤ c1 ∧ c1 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 ≤ c2 ∧ c2 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 ≤ c3 ∧ c3 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 ≤ c0 ∧ c0 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 ≤ c2 ∧ c2 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 ≤ c3 ∧ c3 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 ≤ c0 ∧ c0 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 ≤ c1 ∧ c1 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 ≤ c3 ∧ c3 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 ≤ c0 ∧ c0 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 ≤ c1 ∧ c1 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 ≤ c2 ∧ c2 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 8 * lam)

abbrev MSig2_1_4 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam) ∧
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam)

abbrev MSig2_2_3 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam) ∧
    (((c0 < c1 ∧ c1 < c2 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w)) ∨
          (c0 < c1 ∧ c1 < c3 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w)) ∨
          (c0 < c2 ∧ c2 < c1 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w)) ∨
          (c0 < c2 ∧ c2 < c3 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w)) ∨
          (c0 < c3 ∧ c3 < c1 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w)) ∨
          (c0 < c3 ∧ c3 < c2 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w)) ∨
          (c1 < c0 ∧ c0 < c2 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w)) ∨
          (c1 < c0 ∧ c0 < c3 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w)) ∨
          (c1 < c2 ∧ c2 < c0 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w)) ∨
          (c1 < c2 ∧ c2 < c3 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w)) ∨
          (c1 < c3 ∧ c3 < c0 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w)) ∨
          (c1 < c3 ∧ c3 < c2 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w)) ∨
          (c2 < c0 ∧ c0 < c1 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w)) ∨
          (c2 < c0 ∧ c0 < c3 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w)) ∨
          (c2 < c1 ∧ c1 < c0 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w)) ∨
          (c2 < c1 ∧ c1 < c3 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w)) ∨
          (c2 < c3 ∧ c3 < c0 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w)) ∨
          (c2 < c3 ∧ c3 < c1 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w)) ∨
          (c3 < c0 ∧ c0 < c1 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w)) ∨
          (c3 < c0 ∧ c0 < c2 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w)) ∨
          (c3 < c1 ∧ c1 < c0 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w)) ∨
          (c3 < c1 ∧ c1 < c2 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w)) ∨
          (c3 < c2 ∧ c2 < c0 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w)) ∨
          (c3 < c2 ∧ c2 < c1 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w))) ∨
      ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ (c1 ≤ c2 ∨ c3 ≤ c0)) ∨
          (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ (c1 ≤ c3 ∨ c2 ≤ c0)) ∨
          (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ (c2 ≤ c1 ∨ c3 ≤ c0)) ∨
          (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ (c2 ≤ c3 ∨ c1 ≤ c0)) ∨
          (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ (c3 ≤ c1 ∨ c2 ≤ c0)) ∨
          (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ (c3 ≤ c2 ∨ c1 ≤ c0)) ∨
          (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ (c0 ≤ c2 ∨ c3 ≤ c1)) ∨
          (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ (c0 ≤ c3 ∨ c2 ≤ c1)) ∨
          (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ (c2 ≤ c0 ∨ c3 ≤ c1)) ∨
          (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ (c2 ≤ c3 ∨ c0 ≤ c1)) ∨
          (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ (c3 ≤ c0 ∨ c2 ≤ c1)) ∨
          (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ (c3 ≤ c2 ∨ c0 ≤ c1)) ∨
          (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c3 ≤ w) ∧ (c0 ≤ c1 ∨ c3 ≤ c2)) ∨
          (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ (c0 ≤ c3 ∨ c1 ≤ c2)) ∨
          (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c3 ≤ w) ∧ (c1 ≤ c0 ∨ c3 ≤ c2)) ∨
          (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ (c1 ≤ c3 ∨ c0 ≤ c2)) ∨
          (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ (c3 ≤ c0 ∨ c1 ≤ c2)) ∨
          (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c3 ≤ w) ∧ c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ (c3 ≤ c1 ∨ c0 ≤ c2)) ∨
          (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c2 ≤ w) ∧ (c0 ≤ c1 ∨ c2 ≤ c3)) ∨
          (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c0 ≤ w) ∧ c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c1 ≤ w) ∧ (c0 ≤ c2 ∨ c1 ≤ c3)) ∨
          (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c2 ≤ w) ∧ (c1 ≤ c0 ∨ c2 ≤ c3)) ∨
          (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c1 ≤ w) ∧ c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c2 ∨ c0 ≤ w) ∧ (c1 ≤ c2 ∨ c0 ≤ c3)) ∨
          (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c0 ∨ c1 ≤ w) ∧ (c2 ≤ c0 ∨ c1 ≤ c3)) ∨
          (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c3 ∨ c2 ≤ w) ∧ c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ w ∈ [c0, c1, c2, c3], w ≤ c1 ∨ c0 ≤ w) ∧ (c2 ≤ c1 ∨ c0 ≤ c3)))) ∧
    ((c0 ≤ c1 ∧ c1 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 ≤ c2 ∧ c2 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 ≤ c3 ∧ c3 - c0 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 ≤ c0 ∧ c0 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 ≤ c2 ∧ c2 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 ≤ c3 ∧ c3 - c1 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 ≤ c0 ∧ c0 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 ≤ c1 ∧ c1 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 ≤ c3 ∧ c3 - c2 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 ≤ c0 ∧ c0 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 ≤ c1 ∧ c1 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 ≤ c2 ∧ c2 - c3 < 2 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 8 * lam)

abbrev MSig2_2_4 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam) ∧
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam)

abbrev MSig2_3_4 (lam p tl c0 c1 c2 c3 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam) ∧
    ((c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z))) ∧
    (∀ x ∈ [c0, c1, c2, c3], ∀ y ∈ [c0, c1, c2, c3], y - x < 7 * lam)

theorem msig1_0_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : 2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig1_0 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig1_1_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig1_1 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm1 := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig1_2_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig1_2 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm1 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig1_3_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig1_3 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm1 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig1_4_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig1_4 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig2_0_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : 3 * lam <= (x0 - tl) ∧ (x0 - tl) < 4 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_0 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig2_1_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ 3 * lam <= (x1 - x0) ∧ (x1 - x0) < 4 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_1 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm1 := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig2_2_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 3 * lam <= (x2 - x1) ∧ (x2 - x1) < 4 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_2 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm1 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig2_3_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 3 * lam <= (x3 - x2) ∧ (x3 - x2) < 4 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_3 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm1 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

theorem msig2_4_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 3 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 4 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_4 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))

set_option maxHeartbeats 8000000 in
theorem msig2_0_1_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : 2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_0_1 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_0_2_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : 2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_0_2 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_0_3_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : 2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_0_3 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_0_4_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : 2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_0_4 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_1_2_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_1_2 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm3 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))
        · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))
        · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))))
        · exfalso; linarith
        · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))))))
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))))))))
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))))))
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
  · have hm1 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · have heq : x2 = x3 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x3 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x3]
          by_cases e0 : x0 = x3 <;> by_cases e1 : x1 = x3 <;>
            by_cases e2 : x2 = x3 <;> by_cases e3 : x3 = x3 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))
      · have heq : x2 = x3 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x3 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x3]
          by_cases e0 : x0 = x3 <;> by_cases e1 : x1 = x3 <;>
            by_cases e2 : x2 = x3 <;> by_cases e3 : x3 = x3 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))))
      · have heq : x2 = x3 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x3 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x3]
          by_cases e0 : x0 = x3 <;> by_cases e1 : x1 = x3 <;>
            by_cases e2 : x2 = x3 <;> by_cases e3 : x3 = x3 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, hnb⟩))))))))))))
      · have heq : x2 = x3 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x3 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x3]
          by_cases e0 : x0 = x3 <;> by_cases e1 : x1 = x3 <;>
            by_cases e2 : x2 = x3 <;> by_cases e3 : x3 = x3 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_1_3_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_1_3 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm3 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    have hm4 := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)) | exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)) | exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)) | exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)) | exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))))
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))))))
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))) | exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))))
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))))))
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))))))))))
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))))))))))))
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩)))))))))))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
              intro z hz
              rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, by linarith, hnbB, Or.inl (by linarith)⟩))))))))))))))))))))))))
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
          · exfalso; linarith
        · rcases hm4 with h4 | h4 | h4 | h4
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩))))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · obtain ⟨hvp, hvq⟩ := h
              have hnbA0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB0 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbA1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              have hnbB1 : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
                intro z hz
                rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
                  first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
              first | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA0, by linarith, by linarith, by linarith, hnbB0, Or.inl (by linarith)⟩)))))))))))))))))))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnbA1, by linarith, by linarith, by linarith, hnbB1, Or.inl (by linarith)⟩)))))))))))))))))))))) | exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
          · have heq : x1 = x2 := h2.trans h3.symm
            have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
              rw [← hp.count_eq x2]
              by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
                by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
                simp_all [List.count]
            rcases two_slots hcnt with h | h | h | h | h | h
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
            · exfalso; linarith
  · have hm1 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · have heq : x1 = x2 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x2]
          by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
            by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))
      · have heq : x1 = x2 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x2]
          by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
            by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))))
      · have heq : x1 = x2 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x2]
          by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
            by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, hnb⟩))))))))))))
      · have heq : x1 = x2 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x2 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x2]
          by_cases e0 : x0 = x2 <;> by_cases e1 : x1 = x2 <;>
            by_cases e2 : x2 = x2 <;> by_cases e3 : x3 = x2 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_1_4_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_1_4 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_2_3_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (tl + p - x3) < 2 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_2_3 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    have hm3 := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))
        · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))
        · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))
        · exfalso; linarith
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))))
        · exfalso; linarith
        · exfalso; linarith
    · rcases hm2 with h2 | h2 | h2 | h2
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))))))
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))))
        · exfalso; linarith
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩)))))))))))))))))))))))
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))))))
        · have hnbA : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          have hnbB : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
            intro z hz
            rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
              first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
          exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, by linarith, hnbA, by linarith, by linarith, hnbB⟩))))))))))))))))))))))))
        · exfalso; linarith
        · exfalso; linarith
      · rcases hm3 with h3 | h3 | h3 | h3
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
        · exfalso; linarith
  · have hm1 := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · have heq : x0 = x1 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x1 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x1]
          by_cases e0 : x0 = x1 <;> by_cases e1 : x1 = x1 <;>
            by_cases e2 : x2 = x1 <;> by_cases e3 : x3 = x1 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))
      · have heq : x0 = x1 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x1 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x1]
          by_cases e0 : x0 = x1 <;> by_cases e1 : x1 = x1 <;>
            by_cases e2 : x2 = x1 <;> by_cases e3 : x3 = x1 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))))
      · have heq : x0 = x1 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x1 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x1]
          by_cases e0 : x0 = x1 <;> by_cases e1 : x1 = x1 <;>
            by_cases e2 : x2 = x1 <;> by_cases e3 : x3 = x1 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, hnb⟩))))))))))))
      · have heq : x0 = x1 := h1.trans h2.symm
        have hcnt : 2 ≤ List.count x1 [c0, c1, c2, c3] := by
          rw [← hp.count_eq x1]
          by_cases e0 : x0 = x1 <;> by_cases e1 : x1 = x1 <;>
            by_cases e2 : x2 = x1 <;> by_cases e3 : x3 = x1 <;>
            simp_all [List.count]
        rcases two_slots hcnt with h | h | h | h | h | h
        · exact (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))
        · exact (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))
        · exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c0).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c1).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩)))))))
        · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, (fun z hz => (le_total z c2).elim (fun hh => Or.inl (by linarith)) (fun hh => Or.inr (by linarith)))⟩))))))))))
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_2_4_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_2_4 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x1 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

set_option maxHeartbeats 8000000 in
theorem msig2_3_4_of_pos {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ 2 * lam <= (tl + p - x3) ∧ (tl + p - x3) < 3 * lam)
    {c0 c1 c2 c3 : ℝ} (hp : List.Perm [x0, x1, x2, x3] [c0, c1, c2, c3]) :
    MSig2_3_4 lam p tl c0 c1 c2 c3 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hm := mem4or (hp.subset (show x0 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · intro z hz
    rcases (mem4or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm with h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (by linarith))))
  · have hm1 := mem4or (hp.subset (show x2 ∈ [x0, x1, x2, x3] by simp))
    have hm2 := mem4or (hp.subset (show x3 ∈ [x0, x1, x2, x3] by simp))
    rcases hm1 with h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem4or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · exfalso; linarith
  · intro x hx y hy
    rcases (mem4or (hp.symm.subset hx)) with rfl | rfl | rfl | rfl <;>
      rcases (mem4or (hp.symm.subset hy)) with rfl | rfl | rfl | rfl <;>
      linarith

end R2N4
