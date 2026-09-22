import Jsp000404.ProperGaps
import Mathlib.Data.Rat.BigOperators

/-!
# A strict five-center counterexample to the no-saturation shortcut

The old research conjecture "no saturated vertices implies W <= 2 in
both regimes" is false. The regular pentagon's direction data, at
T = 11/4, gives a proper, nonnegative, strictly feasible model with
all exponents zero and W = 5/2. This file checks the exact rational
model, not an unformalized claim that the model embeds in the plane.
The geometric origin is documented separately in the research note.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Jsp404

def pentagonSk : Skeleton 5 where
  vtx := ![
    ⟨![0, 2, 3, 0, 1], ![true, false, false, true, true], ![0, 1, 0, 0]⟩,
    ⟨![3, 0, 0, 1, 2], ![true, true, true, true, true], ![0, 0, 0, 1]⟩,
    ⟨![3, 0, 0, 1, 2], ![true, false, false, true, true], ![1, 0, 0, 0]⟩,
    ⟨![0, 1, 2, 0, 3], ![false, false, false, false, true], ![0, 0, 1, 0]⟩,
    ⟨![0, 1, 2, 3, 0], ![false, false, false, false, false], ![0, 0, 0, 1]⟩]

def pentagonRatR : Fin 5 → Fin 4 → ℚ := ![
  ![11/20, 1/10, 11/20, 11/20],
  ![11/20, 11/20, 11/20, 1/10],
  ![1/10, 11/20, 11/20, 11/20],
  ![11/20, 11/20, 1/10, 11/20],
  ![11/20, 11/20, 11/20, 1/10]]

noncomputable def pentagonR : Fin 5 → Fin 4 → ℝ := fun v g => pentagonRatR v g

def pentagonRatAngle (x a b : Fin 5) : ℚ :=
  if (pentagonSk.vtx x).bits a = (pentagonSk.vtx x).bits b then
    ∑ g ∈ (pentagonSk.vtx x).arc a b,
      (((pentagonSk.vtx x).q g : ℚ) + pentagonRatR x g)
  else 2 + 3/4 - ∑ g ∈ (pentagonSk.vtx x).arc a b,
      (((pentagonSk.vtx x).q g : ℚ) + pentagonRatR x g)

lemma pentagon_angle (x a b : Fin 5) :
    angleExpr 2 pentagonSk pentagonR (3/4) x a b = (pentagonRatAngle x a b : ℝ) := by
  unfold angleExpr pentagonRatAngle
  split_ifs <;> simp [Rat.cast_sum, pentagonR]

theorem pentagonSk_proper : pentagonSk.Proper := by unfold Skeleton.Proper; decide +kernel

theorem pentagonSk_q_nonnegative : ∀ x g, 0 ≤ (pentagonSk.vtx x).q g := by decide +kernel

theorem pentagonR_strict : ∀ x g, 0 ≤ pentagonR x g ∧ pentagonR x g < 1 := by
  have h : ∀ x g, 0 ≤ pentagonRatR x g ∧ pentagonRatR x g < 1 := by decide +kernel
  intro x g
  change 0 ≤ (pentagonRatR x g : ℝ) ∧ (pentagonRatR x g : ℝ) < 1
  exact_mod_cast h x g

theorem pentagonSk_modeA : ModeA 2 pentagonSk pentagonR (3/4) where
  r_nn := fun x g => (pentagonR_strict x g).1
  r_le := fun x g => (pentagonR_strict x g).2.le
  fan := by
    have h : ∀ x, (∑ g, pentagonRatR x g) - 3/4 =
        (2 : ℚ) - ∑ g, ((pentagonSk.vtx x).q g : ℚ) := by decide +kernel
    intro x
    change (∑ g, (pentagonRatR x g : ℝ)) - 3/4 =
      (2 : ℝ) - ↑(∑ g, (pentagonSk.vtx x).q g)
    have hR := congrArg (fun q : ℚ => (q : ℝ)) (h x)
    push_cast at hR ⊢
    exact hR
  tri := by
    have h : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
        pentagonRatAngle a b c + pentagonRatAngle b a c +
          pentagonRatAngle c a b = 2 + 3/4 := by decide +kernel
    intro a b c hab hac hbc
    simp only [pentagon_angle]
    have hR := congrArg (fun q : ℚ => (q : ℝ)) (h a b c hab hac hbc)
    push_cast at hR
    exact hR
  ang_le := by
    have h : ∀ x a b, pentagonRatAngle x a b ≤ 2 - 1 + 3/4 := by decide +kernel
    intro x a b _
    rw [pentagon_angle]
    have hR : (pentagonRatAngle x a b : ℝ) ≤ ((2 - 1 + 3/4 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (h x a b)
    norm_num at hR ⊢
    exact hR
  ang_nn := by
    have h : ∀ x a b, 0 ≤ pentagonRatAngle x a b := by decide +kernel
    intro x a b _
    rw [pentagon_angle]
    exact_mod_cast h x a b

theorem pentagonSk_consistent : pentagonSk.Consistent 2 :=
  ⟨pentagonR, 3/4, by norm_num, by norm_num, pentagonSk_modeA⟩

theorem pentagonSk_no_saturation : ∀ x, (pentagonSk.vtx x).kexp = 0 := by decide +kernel

theorem pentagonSk_weight : pentagonSk.W 2 = 5/2 := by decide +kernel

/-- An explicit strict witness: no negative-cell, duplicate-position, or
closed-remainder loophole is involved. -/
theorem strict_no_saturation_counterexample :
    ∃ sk : Skeleton 5, sk.Proper ∧ (∀ x g, 0 ≤ (sk.vtx x).q g) ∧
      (∀ x, (sk.vtx x).kexp = 0) ∧ sk.W 2 = 5/2 ∧
      ∃ r, ModeA 2 sk r (3/4) ∧ ∀ x g, 0 ≤ r x g ∧ r x g < 1 :=
  ⟨pentagonSk, pentagonSk_proper, pentagonSk_q_nonnegative,
    pentagonSk_no_saturation, pentagonSk_weight,
    pentagonR, pentagonSk_modeA, pentagonR_strict⟩

/-- Even proper nonnegative strict models can reach the high cap with no
saturated vertex. A proof of the high theorem must handle this case. -/
theorem not_no_saturation_low_capacity :
    ¬ (∀ sk : Skeleton 5, sk.Proper → sk.Consistent 2 →
      (∀ x g, 0 ≤ (sk.vtx x).q g) →
      (∀ x, (sk.vtx x).kexp = 0) → sk.W 2 ≤ 2) := by
  intro h
  have hw := h pentagonSk pentagonSk_proper pentagonSk_consistent
    pentagonSk_q_nonnegative pentagonSk_no_saturation
  rw [pentagonSk_weight] at hw
  norm_num at hw

#print axioms pentagonSk_modeA
#print axioms strict_no_saturation_counterexample
#print axioms not_no_saturation_low_capacity

end Jsp404
