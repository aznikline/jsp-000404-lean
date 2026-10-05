import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Original necessary eleven-point angle model.  Every triangle retains
its separation, strict betweenness, and both endpoint caps. -/
namespace Jsp404.NoSatElevenDBMTerminal

structure ElevenModel (lam p : ℝ) where
  hlam : 0 < lam
  hp : p < 4*lam
  d : Fin 11 → Fin 11 → ℝ
  hrange : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < p
  htr : ∀ i j k : Fin 11, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ p-lam ∧ d j k-d i k ≤ p-lam) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ p-lam ∧ d i j-d i k ≤ p-lam)

theorem endpoint_caps {lam p : ℝ} (m : ElevenModel lam p)
    (i j k : Fin 11) (hij : i < j) (hjk : j < k) :
    m.d i k-m.d i j < 3*lam ∧
    m.d i j-m.d i k < 3*lam ∧
    m.d j k-m.d i k < 3*lam ∧
    m.d i k-m.d j k < 3*lam := by
  have hp := m.hp
  have hlam := m.hlam
  rcases m.htr i j k hij hjk with h | h
  all_goals rcases h with ⟨ha, hb, hc, hd, he⟩
  all_goals repeat' apply And.intro
  all_goals linarith

#print axioms endpoint_caps
end Jsp404.NoSatElevenDBMTerminal
