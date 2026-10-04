import Jsp000404.GapDefectStructure

namespace Jsp404.GlobalFiveLowTerminal

def GapBudget (n p a b c d : ℝ) : Prop :=
  n-1 ≤ b-a ∨ n-1 ≤ c-b ∨ n-1 ≤ d-c ∨ n-1 ≤ p+a-d ∨
  (2 ≤ b-a ∧ 2 ≤ c-b ∧ n ≤ (b-a)+(c-b)) ∨
  (2 ≤ b-a ∧ 2 ≤ d-c ∧ n ≤ (b-a)+(d-c)) ∨
  (2 ≤ b-a ∧ 2 ≤ p+a-d ∧ n ≤ (b-a)+(p+a-d)) ∨
  (2 ≤ c-b ∧ 2 ≤ d-c ∧ n ≤ (c-b)+(d-c)) ∨
  (2 ≤ c-b ∧ 2 ≤ p+a-d ∧ n ≤ (c-b)+(p+a-d)) ∨
  (2 ≤ d-c ∧ 2 ≤ p+a-d ∧ n ≤ (d-c)+(p+a-d))

structure FiveModel (n delta : ℝ) (q : Fin 5) where
  hn : 3 ≤ n
  hdelta : 0 ≤ delta ∧ delta < 1/2
  d : Fin 5 → Fin 5 → ℝ
  symm : ∀ i j, d i j = d j i
  range : ∀ i j, i ≠ j → 0 ≤ d i j ∧ d i j < n+delta
  triangle : ∀ i j k : Fin 5, i < j → j < k →
    (d i j+1 ≤ d j k ∧ d i j < d i k ∧ d i k < d j k ∧
      d i k-d i j ≤ n+delta-1 ∧ d j k-d i k ≤ n+delta-1) ∨
    (d j k+1 ≤ d i j ∧ d j k < d i k ∧ d i k < d i j ∧
      d i k-d j k ≤ n+delta-1 ∧ d i j-d i k ≤ n+delta-1)
  budget : ∀ i : Fin 5, i ≠ q → ∀ a b c e : Fin 5,
    [a,b,c,e].Perm ((List.finRange 5).erase i) →
    d i a ≤ d i b → d i b ≤ d i c → d i c ≤ d i e →
    GapBudget n (n+delta) (d i a) (d i b) (d i c) (d i e)
end Jsp404.GlobalFiveLowTerminal
