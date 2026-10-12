import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.Perm.Basic

set_option maxHeartbeats 1600000

namespace R2N4

open List


/-- **Scalar model of the `n = 4` 8-centre terminal geometry
(`8` centres = anchor + 7 non-anchor vertices).** -/
structure N8Model where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 4 * lam <= p ∧ p < 5 * lam
  t : Fin 7 → ℝ
  ht : StrictMono t
  ht0 : 0 <= t 0
  ht6 : t 6 <= p - 4 * lam
  d : Fin 7 → Fin 7 → ℝ
  hcor : ∀ i j : Fin 7, i < j →
    t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin 7, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)

theorem n8_chord_bounds (m : N8Model) {i j : Fin 7} (hij : i < j) :
    m.lam ≤ m.d i j ∧ m.d i j < 5 * m.lam := by
  obtain ⟨hb1, hb2⟩ := m.hcor i j hij
  obtain ⟨hplo, hphi⟩ := m.hp
  have h0 : m.t 0 ≤ m.t i := m.ht.monotone (Fin.zero_le _)
  have h5 : m.t j ≤ m.t 6 := m.ht.monotone (Fin.le_last j)
  have h0b := m.ht0
  have h5b := m.ht6
  constructor <;> linarith



theorem mem6or {u x0 x1 x2 x3 x4 x5 : ℝ}
    (h : u ∈ [x0, x1, x2, x3, x4, x5]) :
    u = x0 ∨ u = x1 ∨ u = x2 ∨ u = x3 ∨ u = x4 ∨ u = x5 := by
  simpa using h


abbrev RowSig1_8 (lam p tl : ℝ) (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 3 * lam)

abbrev RowSig2_8 (lam p tl : ℝ) (x0 x1 x2 x3 x4 x5 : ℝ) : Prop :=
    (3 * lam <= (x0 - tl) ∧ (x0 - tl) < 4 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 3 * lam <= (x1 - x0) ∧ (x1 - x0) < 4 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 3 * lam <= (x2 - x1) ∧ (x2 - x1) < 4 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 3 * lam <= (x3 - x2) ∧ (x3 - x2) < 4 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 3 * lam <= (x4 - x3) ∧ (x4 - x3) < 4 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 3 * lam <= (x5 - x4) ∧ (x5 - x4) < 4 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 3 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 4 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (tl + p - x5) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ 2 * lam <= (tl + p - x5) ∧ (tl + p - x5) < 3 * lam)

abbrev CMSig2_8_H_L (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 3 * lam ≤ z - tl) ∧
    (c0 - tl < 4 * lam ∨ c1 - tl < 4 * lam ∨ c2 - tl < 4 * lam ∨ c3 - tl < 4 * lam ∨ c4 - tl < 4 * lam ∨ c5 - tl < 4 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam)

abbrev CMSig2_8_H_I (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    ((c0 < c0 ∧ 3 * lam ≤ c0 - c0 ∧ c0 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 3 * lam ≤ c1 - c0 ∧ c1 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 3 * lam ≤ c2 - c0 ∧ c2 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 3 * lam ≤ c3 - c0 ∧ c3 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 3 * lam ≤ c4 - c0 ∧ c4 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 3 * lam ≤ c5 - c0 ∧ c5 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c1 < c0 ∧ 3 * lam ≤ c0 - c1 ∧ c0 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 3 * lam ≤ c1 - c1 ∧ c1 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 3 * lam ≤ c2 - c1 ∧ c2 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 3 * lam ≤ c3 - c1 ∧ c3 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 3 * lam ≤ c4 - c1 ∧ c4 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 3 * lam ≤ c5 - c1 ∧ c5 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c2 < c0 ∧ 3 * lam ≤ c0 - c2 ∧ c0 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 3 * lam ≤ c1 - c2 ∧ c1 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 3 * lam ≤ c2 - c2 ∧ c2 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 3 * lam ≤ c3 - c2 ∧ c3 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 3 * lam ≤ c4 - c2 ∧ c4 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 3 * lam ≤ c5 - c2 ∧ c5 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c3 < c0 ∧ 3 * lam ≤ c0 - c3 ∧ c0 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 3 * lam ≤ c1 - c3 ∧ c1 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 3 * lam ≤ c2 - c3 ∧ c2 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 3 * lam ≤ c3 - c3 ∧ c3 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 3 * lam ≤ c4 - c3 ∧ c4 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 3 * lam ≤ c5 - c3 ∧ c5 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c4 < c0 ∧ 3 * lam ≤ c0 - c4 ∧ c0 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 3 * lam ≤ c1 - c4 ∧ c1 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 3 * lam ≤ c2 - c4 ∧ c2 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 3 * lam ≤ c3 - c4 ∧ c3 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 3 * lam ≤ c4 - c4 ∧ c4 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 3 * lam ≤ c5 - c4 ∧ c5 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c5 < c0 ∧ 3 * lam ≤ c0 - c5 ∧ c0 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 3 * lam ≤ c1 - c5 ∧ c1 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 3 * lam ≤ c2 - c5 ∧ c2 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 3 * lam ≤ c3 - c5 ∧ c3 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 3 * lam ≤ c4 - c5 ∧ c4 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 3 * lam ≤ c5 - c5 ∧ c5 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c5 ≤ z))) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam)

abbrev CMSig2_8_H_R (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 3 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 4 * lam ∨ tl + p - c1 < 4 * lam ∨ tl + p - c2 < 4 * lam ∨ tl + p - c3 < 4 * lam ∨ tl + p - c4 < 4 * lam ∨ tl + p - c5 < 4 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam)

abbrev CMSig2_8_M_LI (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam ∨ c4 - tl < 3 * lam ∨ c5 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam) ∧
    ((c0 < c0 ∧ 2 * lam ≤ c0 - c0 ∧ c0 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 2 * lam ≤ c4 - c0 ∧ c4 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 2 * lam ≤ c5 - c0 ∧ c5 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 2 * lam ≤ c1 - c1 ∧ c1 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 2 * lam ≤ c4 - c1 ∧ c4 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 2 * lam ≤ c5 - c1 ∧ c5 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 2 * lam ≤ c2 - c2 ∧ c2 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 2 * lam ≤ c4 - c2 ∧ c4 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 2 * lam ≤ c5 - c2 ∧ c5 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 2 * lam ≤ c3 - c3 ∧ c3 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 2 * lam ≤ c4 - c3 ∧ c4 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 2 * lam ≤ c5 - c3 ∧ c5 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c4 < c0 ∧ 2 * lam ≤ c0 - c4 ∧ c0 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 2 * lam ≤ c1 - c4 ∧ c1 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 2 * lam ≤ c2 - c4 ∧ c2 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 2 * lam ≤ c3 - c4 ∧ c3 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 2 * lam ≤ c4 - c4 ∧ c4 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 2 * lam ≤ c5 - c4 ∧ c5 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c5 < c0 ∧ 2 * lam ≤ c0 - c5 ∧ c0 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 2 * lam ≤ c1 - c5 ∧ c1 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 2 * lam ≤ c2 - c5 ∧ c2 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 2 * lam ≤ c3 - c5 ∧ c3 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 2 * lam ≤ c4 - c5 ∧ c4 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 2 * lam ≤ c5 - c5 ∧ c5 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c5 ≤ z)))

abbrev CMSig2_8_M_LR (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam ∨ c4 - tl < 3 * lam ∨ c5 - tl < 3 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam ∨ tl + p - c4 < 3 * lam ∨ tl + p - c5 < 3 * lam)

abbrev CMSig2_8_M_IR (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam ∨ tl + p - c4 < 3 * lam ∨ tl + p - c5 < 3 * lam) ∧
    ((c0 < c0 ∧ 2 * lam ≤ c0 - c0 ∧ c0 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 2 * lam ≤ c4 - c0 ∧ c4 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 2 * lam ≤ c5 - c0 ∧ c5 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 2 * lam ≤ c1 - c1 ∧ c1 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 2 * lam ≤ c4 - c1 ∧ c4 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 2 * lam ≤ c5 - c1 ∧ c5 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 2 * lam ≤ c2 - c2 ∧ c2 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 2 * lam ≤ c4 - c2 ∧ c4 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 2 * lam ≤ c5 - c2 ∧ c5 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 2 * lam ≤ c3 - c3 ∧ c3 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 2 * lam ≤ c4 - c3 ∧ c4 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 2 * lam ≤ c5 - c3 ∧ c5 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c4 < c0 ∧ 2 * lam ≤ c0 - c4 ∧ c0 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 2 * lam ≤ c1 - c4 ∧ c1 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 2 * lam ≤ c2 - c4 ∧ c2 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 2 * lam ≤ c3 - c4 ∧ c3 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 2 * lam ≤ c4 - c4 ∧ c4 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 2 * lam ≤ c5 - c4 ∧ c5 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c5 < c0 ∧ 2 * lam ≤ c0 - c5 ∧ c0 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 2 * lam ≤ c1 - c5 ∧ c1 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 2 * lam ≤ c2 - c5 ∧ c2 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 2 * lam ≤ c3 - c5 ∧ c3 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 2 * lam ≤ c4 - c5 ∧ c4 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 2 * lam ≤ c5 - c5 ∧ c5 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c5 ≤ z)))

abbrev CMSig1_8_L_0 (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam ∨ c4 - tl < 3 * lam ∨ c5 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam)

abbrev CMSig1_8_L_I (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    ((c0 < c0 ∧ 2 * lam ≤ c0 - c0 ∧ c0 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 2 * lam ≤ c4 - c0 ∧ c4 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 2 * lam ≤ c5 - c0 ∧ c5 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 2 * lam ≤ c1 - c1 ∧ c1 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 2 * lam ≤ c4 - c1 ∧ c4 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 2 * lam ≤ c5 - c1 ∧ c5 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 2 * lam ≤ c2 - c2 ∧ c2 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 2 * lam ≤ c4 - c2 ∧ c4 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 2 * lam ≤ c5 - c2 ∧ c5 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 2 * lam ≤ c3 - c3 ∧ c3 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 2 * lam ≤ c4 - c3 ∧ c4 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 2 * lam ≤ c5 - c3 ∧ c5 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c4 < c0 ∧ 2 * lam ≤ c0 - c4 ∧ c0 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 2 * lam ≤ c1 - c4 ∧ c1 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 2 * lam ≤ c2 - c4 ∧ c2 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 2 * lam ≤ c3 - c4 ∧ c3 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 2 * lam ≤ c4 - c4 ∧ c4 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 2 * lam ≤ c5 - c4 ∧ c5 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c5 < c0 ∧ 2 * lam ≤ c0 - c5 ∧ c0 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 2 * lam ≤ c1 - c5 ∧ c1 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 2 * lam ≤ c2 - c5 ∧ c2 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 2 * lam ≤ c3 - c5 ∧ c3 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 2 * lam ≤ c4 - c5 ∧ c4 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 2 * lam ≤ c5 - c5 ∧ c5 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c5 ≤ z))) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam)

abbrev CMSig1_8_L_R (lam p tl c0 c1 c2 c3 c4 c5 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam ∨ tl + p - c4 < 3 * lam ∨ tl + p - c5 < 3 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam)

theorem msig2_8_H_L_of_pos_0 {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ tl + p)
    (hs : 3 * lam <= (x0 - tl) ∧ (x0 - tl) < 4 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam)
    {c0 c1 c2 c3 c4 c5 : ℝ} (hp : List.Perm [x0, x1, x2, x3, x4, x5] [c0, c1, c2, c3, c4, c5]) :
    CMSig2_8_H_L lam p tl c0 c1 c2 c3 c4 c5 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases (mem6or (hp.symm.subset hz)) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith
  · have hm := mem6or (hp.subset (show x0 ∈ [x0, x1, x2, x3, x4, x5] by simp))
    rcases hm with h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))
  · have hm := mem6or (hp.subset (show x5 ∈ [x0, x1, x2, x3, x4, x5] by simp))
    rcases hm with h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))

theorem msig2_8_H_I_of_pos_1 {lam p tl : ℝ} (hl : 0 < lam)
    {x0 x1 x2 x3 x4 x5 : ℝ}
    (hord : tl ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ x4 ∧ x4 ≤ x5 ∧ x5 ≤ tl + p)
    (hs : (x0 - tl) < 2 * lam ∧ 3 * lam <= (x1 - x0) ∧ (x1 - x0) < 4 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (tl + p - x5) < 2 * lam)
    {c0 c1 c2 c3 c4 c5 : ℝ} (hp : List.Perm [x0, x1, x2, x3, x4, x5] [c0, c1, c2, c3, c4, c5]) :
    CMSig2_8_H_I lam p tl c0 c1 c2 c3 c4 c5 := by
  classical
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6⟩ := hord
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · have hm1 := mem6or (hp.subset (show x0 ∈ [x0, x1, x2, x3, x4, x5] by simp))
    have hm2 := mem6or (hp.subset (show x1 ∈ [x0, x1, x2, x3, x4, x5] by simp))
    rcases hm1 with h1 | h1 | h1 | h1 | h1 | h1
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c0 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c1 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c2 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c3 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))
      · exfalso; linarith
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c4 ∨ c5 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))
    · rcases hm2 with h2 | h2 | h2 | h2 | h2 | h2
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c0 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c1 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c2 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c3 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩)))))))))))))))))))))))))))))))))))
      · have hnb : ∀ z ∈ [c0, c1, c2, c3, c4, c5], z ≤ c5 ∨ c4 ≤ z := by
          intro z hz
          rcases (mem6or (hp.symm.subset hz)) with hz' | hz' | hz' | hz' | hz' | hz' <;>
            first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
        exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by linarith, by linarith, by linarith, hnb⟩))))))))))))))))))))))))))))))))))))
      · exfalso; linarith
  · have hm := mem6or (hp.subset (show x0 ∈ [x0, x1, x2, x3, x4, x5] by simp))
    rcases hm with h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))
  · have hm := mem6or (hp.subset (show x5 ∈ [x0, x1, x2, x3, x4, x5] by simp))
    rcases hm with h | h | h | h | h | h
    · exact (Or.inl (by linarith))
    · exact (Or.inr (Or.inl (by linarith)))
    · exact (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))))


end R2N4
