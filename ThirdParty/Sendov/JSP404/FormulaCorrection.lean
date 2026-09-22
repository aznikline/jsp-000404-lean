import JSP404.Counterexample

/-!
# A kernel-checked refutation of the transcribed lower-interval formula

The Erdős Problems page, as checked on 2026-09-16, used numerator 1 in the
lower-interval branch. Sendov's English final Theorem 4.1 (1995, p.42) and
Russian Theorems 4.1 and 4.4 use numerator 2 after the same re-indexing.
The English introduction (1.1) also prints numerator 1, so we do not attribute
the discrepancy specifically to the website. The definitions record both expressions;
they do not assume Sendov's theorem or claim to prove his full classification.
-/

noncomputable section

namespace JSP404

/-- The lower-interval expression transcribed on the problem page. -/
def transcribedLowerBranch (n : ℕ) : ℝ :=
  (1 - 1 / (2 * (n : ℝ) - 1)) * Real.pi

/-- The lower-interval expression in Sendov's original formula, re-indexed. -/
def sourceLowerBranch (n : ℕ) : ℝ :=
  (1 - 2 / (2 * (n : ℝ) - 1)) * Real.pi

/-- The interval paired with the transcribed expression, in a range where every
natural exponent agrees with its ordinary integer interpretation. -/
def InLowerInterval (n N : ℕ) : Prop :=
  3 ≤ n ∧ 2 ^ (n - 1) < N ∧ N ≤ 2 ^ (n - 1) + 2 ^ (n - 3)

/-- The literal lower-interval assertion; the next theorem disproves it using
actual planar points, without assuming an alternative formula for alpha. -/
def TranscribedLowerFormula : Prop :=
  ∀ n N : ℕ, InLowerInterval n N → alpha N = transcribedLowerBranch n

theorem five_in_lower_interval : InLowerInterval 3 5 := by
  norm_num [InLowerInterval]

theorem transcribed_branch_at_three : transcribedLowerBranch 3 = 4 * Real.pi / 5 := by
  norm_num [transcribedLowerBranch]
  ring

theorem source_branch_at_three : sourceLowerBranch 3 = 3 * Real.pi / 5 := by
  norm_num [sourceLowerBranch]
  ring

/-- The faulty entire formula is false, since its n=3,N=5 specialization fails. -/
theorem not_transcribed_lower_formula : ¬ TranscribedLowerFormula := by
  intro h
  have hfive := h 3 5 five_in_lower_interval
  rw [transcribed_branch_at_three] at hfive
  exact alpha_five_ne_four_pi_div_five hfive

/-- The two printed expressions really differ throughout the meaningful range. -/
theorem source_branch_lt_transcribed {n : ℕ} (hn : 3 ≤ n) :
    sourceLowerBranch n < transcribedLowerBranch n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hdiv : 1 / (2 * (n : ℝ) - 1) < 2 / (2 * (n : ℝ) - 1) :=
    div_lt_div_of_pos_right (by norm_num) hd
  unfold sourceLowerBranch transcribedLowerBranch
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos

end JSP404
