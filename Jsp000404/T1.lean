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

end R2N4
