import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Necessary bare LOW triangle model.  Period and both endpoint angle
caps are retained.  No positive row, floor, deletion or saturation premise. -/
namespace Jsp404.NoSatNineDBMTerminal

structure NineModel (lam p : ℝ) where
  hlam : 0 < lam
  hp : 2*p < 7*lam
  d : Fin 9 → Fin 9 → ℝ
  hrange : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < p
  htr : ∀ i j k : Fin 9, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ p-lam ∧ d j k-d i k ≤ p-lam) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ p-lam ∧ d i j-d i k ≤ p-lam)

theorem endpoint_caps {lam p : ℝ} (m : NineModel lam p)
    (i j k : Fin 9) (hij : i < j) (hjk : j < k) :
    m.d i k-m.d i j < (5/2 : ℝ)*lam ∧
    m.d i j-m.d i k < (5/2 : ℝ)*lam ∧
    m.d j k-m.d i k < (5/2 : ℝ)*lam ∧
    m.d i k-m.d j k < (5/2 : ℝ)*lam := by
  have hp := m.hp
  have hlam := m.hlam
  rcases m.htr i j k hij hjk with h | h
  all_goals rcases h with ⟨ha, hb, hc, hd, he⟩
  all_goals repeat' apply And.intro
  all_goals linarith

#print axioms endpoint_caps
end Jsp404.NoSatNineDBMTerminal
