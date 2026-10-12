import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Fin.Basic
set_option maxHeartbeats 1600000

namespace R2N4

open List

/-- **Scalar model of the `n = 4` 9-centre terminal geometry
(`9` centres = anchor + 8 non-anchor vertices).** -/
structure N9Model where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 4 * lam <= p ∧ p < 5 * lam
  t : Fin 8 → ℝ
  ht : StrictMono t
  ht0 : 0 <= t 0
  ht7 : t 7 <= p - 4 * lam
  d : Fin 8 → Fin 8 → ℝ
  hcor : ∀ i j : Fin 8, i < j →
    t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin 8, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)

theorem n9_chord_bounds (m : N9Model) {i j : Fin 8} (hij : i < j) :
    m.lam ≤ m.d i j ∧ m.d i j < 5 * m.lam := by
  obtain ⟨hb1, hb2⟩ := m.hcor i j hij
  obtain ⟨hplo, hphi⟩ := m.hp
  have h0 : m.t 0 ≤ m.t i := m.ht.monotone (Fin.zero_le _)
  have h5 : m.t j ≤ m.t 7 := m.ht.monotone (Fin.le_last j)
  have h0b := m.ht0
  have h5b := m.ht7
  constructor <;> linarith



theorem mem7or {u x0 x1 x2 x3 x4 x5 x6 : ℝ}
    (h : u ∈ [x0, x1, x2, x3, x4, x5, x6]) :
    u = x0 ∨ u = x1 ∨ u = x2 ∨ u = x3 ∨ u = x4 ∨ u = x5 ∨ u = x6 := by
  simpa using h


abbrev RowSig1_9 (lam p tl : ℝ) (x0 x1 x2 x3 x4 x5 x6 : ℝ) : Prop :=
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam)

abbrev RowSig2_9 (lam p tl : ℝ) (x0 x1 x2 x3 x4 x5 x6 : ℝ) : Prop :=
    (3 * lam <= (x0 - tl) ∧ (x0 - tl) < 4 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 3 * lam <= (x1 - x0) ∧ (x1 - x0) < 4 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 3 * lam <= (x2 - x1) ∧ (x2 - x1) < 4 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 3 * lam <= (x3 - x2) ∧ (x3 - x2) < 4 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 3 * lam <= (x4 - x3) ∧ (x4 - x3) < 4 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 3 * lam <= (x5 - x4) ∧ (x5 - x4) < 4 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 3 * lam <= (x6 - x5) ∧ (x6 - x5) < 4 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 3 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 4 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    (2 * lam <= (x0 - tl) ∧ (x0 - tl) < 3 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ 2 * lam <= (x1 - x0) ∧ (x1 - x0) < 3 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ 2 * lam <= (x2 - x1) ∧ (x2 - x1) < 3 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ 2 * lam <= (x3 - x2) ∧ (x3 - x2) < 3 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ 2 * lam <= (x4 - x3) ∧ (x4 - x3) < 3 * lam ∧ (x5 - x4) < 2 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ (tl + p - x6) < 2 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ 2 * lam <= (x5 - x4) ∧ (x5 - x4) < 3 * lam ∧ (x6 - x5) < 2 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam) ∨
    ((x0 - tl) < 2 * lam ∧ (x1 - x0) < 2 * lam ∧ (x2 - x1) < 2 * lam ∧ (x3 - x2) < 2 * lam ∧ (x4 - x3) < 2 * lam ∧ (x5 - x4) < 2 * lam ∧ 2 * lam <= (x6 - x5) ∧ (x6 - x5) < 3 * lam ∧ 2 * lam <= (tl + p - x6) ∧ (tl + p - x6) < 3 * lam)

abbrev CMSig2_9_H_L (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 3 * lam ≤ z - tl) ∧
    (c0 - tl < 4 * lam ∨ c1 - tl < 4 * lam ∨ c2 - tl < 4 * lam ∨ c3 - tl < 4 * lam ∨ c4 - tl < 4 * lam ∨ c5 - tl < 4 * lam ∨ c6 - tl < 4 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam ∨ tl + p - c6 < 2 * lam)

abbrev CMSig2_9_H_I (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    ((c0 < c0 ∧ 3 * lam ≤ c0 - c0 ∧ c0 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 3 * lam ≤ c1 - c0 ∧ c1 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 3 * lam ≤ c2 - c0 ∧ c2 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 3 * lam ≤ c3 - c0 ∧ c3 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 3 * lam ≤ c4 - c0 ∧ c4 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 3 * lam ≤ c5 - c0 ∧ c5 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c0 < c6 ∧ 3 * lam ≤ c6 - c0 ∧ c6 - c0 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c6 ≤ z)) ∨
        (c1 < c0 ∧ 3 * lam ≤ c0 - c1 ∧ c0 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 3 * lam ≤ c1 - c1 ∧ c1 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 3 * lam ≤ c2 - c1 ∧ c2 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 3 * lam ≤ c3 - c1 ∧ c3 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 3 * lam ≤ c4 - c1 ∧ c4 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 3 * lam ≤ c5 - c1 ∧ c5 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c1 < c6 ∧ 3 * lam ≤ c6 - c1 ∧ c6 - c1 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c6 ≤ z)) ∨
        (c2 < c0 ∧ 3 * lam ≤ c0 - c2 ∧ c0 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 3 * lam ≤ c1 - c2 ∧ c1 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 3 * lam ≤ c2 - c2 ∧ c2 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 3 * lam ≤ c3 - c2 ∧ c3 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 3 * lam ≤ c4 - c2 ∧ c4 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 3 * lam ≤ c5 - c2 ∧ c5 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c2 < c6 ∧ 3 * lam ≤ c6 - c2 ∧ c6 - c2 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c6 ≤ z)) ∨
        (c3 < c0 ∧ 3 * lam ≤ c0 - c3 ∧ c0 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 3 * lam ≤ c1 - c3 ∧ c1 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 3 * lam ≤ c2 - c3 ∧ c2 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 3 * lam ≤ c3 - c3 ∧ c3 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 3 * lam ≤ c4 - c3 ∧ c4 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 3 * lam ≤ c5 - c3 ∧ c5 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c3 < c6 ∧ 3 * lam ≤ c6 - c3 ∧ c6 - c3 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c6 ≤ z)) ∨
        (c4 < c0 ∧ 3 * lam ≤ c0 - c4 ∧ c0 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 3 * lam ≤ c1 - c4 ∧ c1 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 3 * lam ≤ c2 - c4 ∧ c2 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 3 * lam ≤ c3 - c4 ∧ c3 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 3 * lam ≤ c4 - c4 ∧ c4 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 3 * lam ≤ c5 - c4 ∧ c5 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c4 < c6 ∧ 3 * lam ≤ c6 - c4 ∧ c6 - c4 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c6 ≤ z)) ∨
        (c5 < c0 ∧ 3 * lam ≤ c0 - c5 ∧ c0 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 3 * lam ≤ c1 - c5 ∧ c1 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 3 * lam ≤ c2 - c5 ∧ c2 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 3 * lam ≤ c3 - c5 ∧ c3 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 3 * lam ≤ c4 - c5 ∧ c4 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 3 * lam ≤ c5 - c5 ∧ c5 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c5 ≤ z)) ∨
        (c5 < c6 ∧ 3 * lam ≤ c6 - c5 ∧ c6 - c5 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c6 ≤ z)) ∨
        (c6 < c0 ∧ 3 * lam ≤ c0 - c6 ∧ c0 - c6 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c0 ≤ z)) ∨
        (c6 < c1 ∧ 3 * lam ≤ c1 - c6 ∧ c1 - c6 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c1 ≤ z)) ∨
        (c6 < c2 ∧ 3 * lam ≤ c2 - c6 ∧ c2 - c6 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c2 ≤ z)) ∨
        (c6 < c3 ∧ 3 * lam ≤ c3 - c6 ∧ c3 - c6 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c3 ≤ z)) ∨
        (c6 < c4 ∧ 3 * lam ≤ c4 - c6 ∧ c4 - c6 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c4 ≤ z)) ∨
        (c6 < c5 ∧ 3 * lam ≤ c5 - c6 ∧ c5 - c6 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c5 ≤ z)) ∨
        (c6 < c6 ∧ 3 * lam ≤ c6 - c6 ∧ c6 - c6 < 4 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c6 ≤ z))) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam ∨ c6 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam ∨ tl + p - c6 < 2 * lam)

abbrev CMSig2_9_H_R (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 3 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 4 * lam ∨ tl + p - c1 < 4 * lam ∨ tl + p - c2 < 4 * lam ∨ tl + p - c3 < 4 * lam ∨ tl + p - c4 < 4 * lam ∨ tl + p - c5 < 4 * lam ∨ tl + p - c6 < 4 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam ∨ c6 - tl < 2 * lam)

abbrev CMSig2_9_M_LI (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam ∨ c4 - tl < 3 * lam ∨ c5 - tl < 3 * lam ∨ c6 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam ∨ tl + p - c6 < 2 * lam) ∧
    ((c0 < c0 ∧ 2 * lam ≤ c0 - c0 ∧ c0 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 2 * lam ≤ c4 - c0 ∧ c4 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 2 * lam ≤ c5 - c0 ∧ c5 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c0 < c6 ∧ 2 * lam ≤ c6 - c0 ∧ c6 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c6 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 2 * lam ≤ c1 - c1 ∧ c1 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 2 * lam ≤ c4 - c1 ∧ c4 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 2 * lam ≤ c5 - c1 ∧ c5 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c1 < c6 ∧ 2 * lam ≤ c6 - c1 ∧ c6 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c6 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 2 * lam ≤ c2 - c2 ∧ c2 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 2 * lam ≤ c4 - c2 ∧ c4 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 2 * lam ≤ c5 - c2 ∧ c5 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c2 < c6 ∧ 2 * lam ≤ c6 - c2 ∧ c6 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c6 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 2 * lam ≤ c3 - c3 ∧ c3 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 2 * lam ≤ c4 - c3 ∧ c4 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 2 * lam ≤ c5 - c3 ∧ c5 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c3 < c6 ∧ 2 * lam ≤ c6 - c3 ∧ c6 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c6 ≤ z)) ∨
        (c4 < c0 ∧ 2 * lam ≤ c0 - c4 ∧ c0 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 2 * lam ≤ c1 - c4 ∧ c1 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 2 * lam ≤ c2 - c4 ∧ c2 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 2 * lam ≤ c3 - c4 ∧ c3 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 2 * lam ≤ c4 - c4 ∧ c4 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 2 * lam ≤ c5 - c4 ∧ c5 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c4 < c6 ∧ 2 * lam ≤ c6 - c4 ∧ c6 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c6 ≤ z)) ∨
        (c5 < c0 ∧ 2 * lam ≤ c0 - c5 ∧ c0 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 2 * lam ≤ c1 - c5 ∧ c1 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 2 * lam ≤ c2 - c5 ∧ c2 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 2 * lam ≤ c3 - c5 ∧ c3 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 2 * lam ≤ c4 - c5 ∧ c4 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 2 * lam ≤ c5 - c5 ∧ c5 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c5 ≤ z)) ∨
        (c5 < c6 ∧ 2 * lam ≤ c6 - c5 ∧ c6 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c6 ≤ z)) ∨
        (c6 < c0 ∧ 2 * lam ≤ c0 - c6 ∧ c0 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c0 ≤ z)) ∨
        (c6 < c1 ∧ 2 * lam ≤ c1 - c6 ∧ c1 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c1 ≤ z)) ∨
        (c6 < c2 ∧ 2 * lam ≤ c2 - c6 ∧ c2 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c2 ≤ z)) ∨
        (c6 < c3 ∧ 2 * lam ≤ c3 - c6 ∧ c3 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c3 ≤ z)) ∨
        (c6 < c4 ∧ 2 * lam ≤ c4 - c6 ∧ c4 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c4 ≤ z)) ∨
        (c6 < c5 ∧ 2 * lam ≤ c5 - c6 ∧ c5 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c5 ≤ z)) ∨
        (c6 < c6 ∧ 2 * lam ≤ c6 - c6 ∧ c6 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c6 ≤ z)))

abbrev CMSig2_9_M_LR (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam ∨ c4 - tl < 3 * lam ∨ c5 - tl < 3 * lam ∨ c6 - tl < 3 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam ∨ tl + p - c4 < 3 * lam ∨ tl + p - c5 < 3 * lam ∨ tl + p - c6 < 3 * lam)

abbrev CMSig2_9_M_IR (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam ∨ c6 - tl < 2 * lam) ∧
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam ∨ tl + p - c4 < 3 * lam ∨ tl + p - c5 < 3 * lam ∨ tl + p - c6 < 3 * lam) ∧
    ((c0 < c0 ∧ 2 * lam ≤ c0 - c0 ∧ c0 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 2 * lam ≤ c4 - c0 ∧ c4 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 2 * lam ≤ c5 - c0 ∧ c5 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c0 < c6 ∧ 2 * lam ≤ c6 - c0 ∧ c6 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c6 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 2 * lam ≤ c1 - c1 ∧ c1 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 2 * lam ≤ c4 - c1 ∧ c4 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 2 * lam ≤ c5 - c1 ∧ c5 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c1 < c6 ∧ 2 * lam ≤ c6 - c1 ∧ c6 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c6 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 2 * lam ≤ c2 - c2 ∧ c2 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 2 * lam ≤ c4 - c2 ∧ c4 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 2 * lam ≤ c5 - c2 ∧ c5 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c2 < c6 ∧ 2 * lam ≤ c6 - c2 ∧ c6 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c6 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 2 * lam ≤ c3 - c3 ∧ c3 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 2 * lam ≤ c4 - c3 ∧ c4 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 2 * lam ≤ c5 - c3 ∧ c5 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c3 < c6 ∧ 2 * lam ≤ c6 - c3 ∧ c6 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c6 ≤ z)) ∨
        (c4 < c0 ∧ 2 * lam ≤ c0 - c4 ∧ c0 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 2 * lam ≤ c1 - c4 ∧ c1 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 2 * lam ≤ c2 - c4 ∧ c2 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 2 * lam ≤ c3 - c4 ∧ c3 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 2 * lam ≤ c4 - c4 ∧ c4 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 2 * lam ≤ c5 - c4 ∧ c5 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c4 < c6 ∧ 2 * lam ≤ c6 - c4 ∧ c6 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c6 ≤ z)) ∨
        (c5 < c0 ∧ 2 * lam ≤ c0 - c5 ∧ c0 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 2 * lam ≤ c1 - c5 ∧ c1 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 2 * lam ≤ c2 - c5 ∧ c2 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 2 * lam ≤ c3 - c5 ∧ c3 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 2 * lam ≤ c4 - c5 ∧ c4 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 2 * lam ≤ c5 - c5 ∧ c5 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c5 ≤ z)) ∨
        (c5 < c6 ∧ 2 * lam ≤ c6 - c5 ∧ c6 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c6 ≤ z)) ∨
        (c6 < c0 ∧ 2 * lam ≤ c0 - c6 ∧ c0 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c0 ≤ z)) ∨
        (c6 < c1 ∧ 2 * lam ≤ c1 - c6 ∧ c1 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c1 ≤ z)) ∨
        (c6 < c2 ∧ 2 * lam ≤ c2 - c6 ∧ c2 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c2 ≤ z)) ∨
        (c6 < c3 ∧ 2 * lam ≤ c3 - c6 ∧ c3 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c3 ≤ z)) ∨
        (c6 < c4 ∧ 2 * lam ≤ c4 - c6 ∧ c4 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c4 ≤ z)) ∨
        (c6 < c5 ∧ 2 * lam ≤ c5 - c6 ∧ c5 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c5 ≤ z)) ∨
        (c6 < c6 ∧ 2 * lam ≤ c6 - c6 ∧ c6 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c6 ≤ z)))

abbrev CMSig1_9_L_0 (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 2 * lam ≤ z - tl) ∧
    (c0 - tl < 3 * lam ∨ c1 - tl < 3 * lam ∨ c2 - tl < 3 * lam ∨ c3 - tl < 3 * lam ∨ c4 - tl < 3 * lam ∨ c5 - tl < 3 * lam ∨ c6 - tl < 3 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam ∨ tl + p - c6 < 2 * lam)

abbrev CMSig1_9_L_I (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    ((c0 < c0 ∧ 2 * lam ≤ c0 - c0 ∧ c0 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c0 ≤ z)) ∨
        (c0 < c1 ∧ 2 * lam ≤ c1 - c0 ∧ c1 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c1 ≤ z)) ∨
        (c0 < c2 ∧ 2 * lam ≤ c2 - c0 ∧ c2 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c2 ≤ z)) ∨
        (c0 < c3 ∧ 2 * lam ≤ c3 - c0 ∧ c3 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c3 ≤ z)) ∨
        (c0 < c4 ∧ 2 * lam ≤ c4 - c0 ∧ c4 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c4 ≤ z)) ∨
        (c0 < c5 ∧ 2 * lam ≤ c5 - c0 ∧ c5 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c5 ≤ z)) ∨
        (c0 < c6 ∧ 2 * lam ≤ c6 - c0 ∧ c6 - c0 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c0 ∨ c6 ≤ z)) ∨
        (c1 < c0 ∧ 2 * lam ≤ c0 - c1 ∧ c0 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c0 ≤ z)) ∨
        (c1 < c1 ∧ 2 * lam ≤ c1 - c1 ∧ c1 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c1 ≤ z)) ∨
        (c1 < c2 ∧ 2 * lam ≤ c2 - c1 ∧ c2 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c2 ≤ z)) ∨
        (c1 < c3 ∧ 2 * lam ≤ c3 - c1 ∧ c3 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c3 ≤ z)) ∨
        (c1 < c4 ∧ 2 * lam ≤ c4 - c1 ∧ c4 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c4 ≤ z)) ∨
        (c1 < c5 ∧ 2 * lam ≤ c5 - c1 ∧ c5 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c5 ≤ z)) ∨
        (c1 < c6 ∧ 2 * lam ≤ c6 - c1 ∧ c6 - c1 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c1 ∨ c6 ≤ z)) ∨
        (c2 < c0 ∧ 2 * lam ≤ c0 - c2 ∧ c0 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c0 ≤ z)) ∨
        (c2 < c1 ∧ 2 * lam ≤ c1 - c2 ∧ c1 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c1 ≤ z)) ∨
        (c2 < c2 ∧ 2 * lam ≤ c2 - c2 ∧ c2 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c2 ≤ z)) ∨
        (c2 < c3 ∧ 2 * lam ≤ c3 - c2 ∧ c3 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c3 ≤ z)) ∨
        (c2 < c4 ∧ 2 * lam ≤ c4 - c2 ∧ c4 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c4 ≤ z)) ∨
        (c2 < c5 ∧ 2 * lam ≤ c5 - c2 ∧ c5 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c5 ≤ z)) ∨
        (c2 < c6 ∧ 2 * lam ≤ c6 - c2 ∧ c6 - c2 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c2 ∨ c6 ≤ z)) ∨
        (c3 < c0 ∧ 2 * lam ≤ c0 - c3 ∧ c0 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c0 ≤ z)) ∨
        (c3 < c1 ∧ 2 * lam ≤ c1 - c3 ∧ c1 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c1 ≤ z)) ∨
        (c3 < c2 ∧ 2 * lam ≤ c2 - c3 ∧ c2 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c2 ≤ z)) ∨
        (c3 < c3 ∧ 2 * lam ≤ c3 - c3 ∧ c3 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c3 ≤ z)) ∨
        (c3 < c4 ∧ 2 * lam ≤ c4 - c3 ∧ c4 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c4 ≤ z)) ∨
        (c3 < c5 ∧ 2 * lam ≤ c5 - c3 ∧ c5 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c5 ≤ z)) ∨
        (c3 < c6 ∧ 2 * lam ≤ c6 - c3 ∧ c6 - c3 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c3 ∨ c6 ≤ z)) ∨
        (c4 < c0 ∧ 2 * lam ≤ c0 - c4 ∧ c0 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c0 ≤ z)) ∨
        (c4 < c1 ∧ 2 * lam ≤ c1 - c4 ∧ c1 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c1 ≤ z)) ∨
        (c4 < c2 ∧ 2 * lam ≤ c2 - c4 ∧ c2 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c2 ≤ z)) ∨
        (c4 < c3 ∧ 2 * lam ≤ c3 - c4 ∧ c3 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c3 ≤ z)) ∨
        (c4 < c4 ∧ 2 * lam ≤ c4 - c4 ∧ c4 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c4 ≤ z)) ∨
        (c4 < c5 ∧ 2 * lam ≤ c5 - c4 ∧ c5 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c5 ≤ z)) ∨
        (c4 < c6 ∧ 2 * lam ≤ c6 - c4 ∧ c6 - c4 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c4 ∨ c6 ≤ z)) ∨
        (c5 < c0 ∧ 2 * lam ≤ c0 - c5 ∧ c0 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c0 ≤ z)) ∨
        (c5 < c1 ∧ 2 * lam ≤ c1 - c5 ∧ c1 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c1 ≤ z)) ∨
        (c5 < c2 ∧ 2 * lam ≤ c2 - c5 ∧ c2 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c2 ≤ z)) ∨
        (c5 < c3 ∧ 2 * lam ≤ c3 - c5 ∧ c3 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c3 ≤ z)) ∨
        (c5 < c4 ∧ 2 * lam ≤ c4 - c5 ∧ c4 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c4 ≤ z)) ∨
        (c5 < c5 ∧ 2 * lam ≤ c5 - c5 ∧ c5 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c5 ≤ z)) ∨
        (c5 < c6 ∧ 2 * lam ≤ c6 - c5 ∧ c6 - c5 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c5 ∨ c6 ≤ z)) ∨
        (c6 < c0 ∧ 2 * lam ≤ c0 - c6 ∧ c0 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c0 ≤ z)) ∨
        (c6 < c1 ∧ 2 * lam ≤ c1 - c6 ∧ c1 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c1 ≤ z)) ∨
        (c6 < c2 ∧ 2 * lam ≤ c2 - c6 ∧ c2 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c2 ≤ z)) ∨
        (c6 < c3 ∧ 2 * lam ≤ c3 - c6 ∧ c3 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c3 ≤ z)) ∨
        (c6 < c4 ∧ 2 * lam ≤ c4 - c6 ∧ c4 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c4 ≤ z)) ∨
        (c6 < c5 ∧ 2 * lam ≤ c5 - c6 ∧ c5 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c5 ≤ z)) ∨
        (c6 < c6 ∧ 2 * lam ≤ c6 - c6 ∧ c6 - c6 < 3 * lam ∧ (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], z ≤ c6 ∨ c6 ≤ z))) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam ∨ c6 - tl < 2 * lam) ∧
    (tl + p - c0 < 2 * lam ∨ tl + p - c1 < 2 * lam ∨ tl + p - c2 < 2 * lam ∨ tl + p - c3 < 2 * lam ∨ tl + p - c4 < 2 * lam ∨ tl + p - c5 < 2 * lam ∨ tl + p - c6 < 2 * lam)

abbrev CMSig1_9_L_R (lam p tl c0 c1 c2 c3 c4 c5 c6 : ℝ) : Prop :=
    (∀ z ∈ [c0, c1, c2, c3, c4, c5, c6], 2 * lam ≤ tl + p - z) ∧
    (tl + p - c0 < 3 * lam ∨ tl + p - c1 < 3 * lam ∨ tl + p - c2 < 3 * lam ∨ tl + p - c3 < 3 * lam ∨ tl + p - c4 < 3 * lam ∨ tl + p - c5 < 3 * lam ∨ tl + p - c6 < 3 * lam) ∧
    (c0 - tl < 2 * lam ∨ c1 - tl < 2 * lam ∨ c2 - tl < 2 * lam ∨ c3 - tl < 2 * lam ∨ c4 - tl < 2 * lam ∨ c5 - tl < 2 * lam ∨ c6 - tl < 2 * lam)

end R2N4
