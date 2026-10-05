import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Arithmetic foundations for genuine finite score-preserving splitting.
No geometric continuity or recursive inflation theorem is assumed here.
-/

namespace Jsp404.GapSplitFloorStability

/-- Cutting a genuine positive-score gap one lambda from its end spends
exactly one score unit. -/
theorem floor_score_end_split {lam G : ℝ} (hlam : 0 < lam) (hG : 2 * lam ≤ G) :
    (⌊lam / lam⌋₊ - 1) + (⌊(G - lam) / lam⌋₊ - 1) + 1 =
      ⌊G / lam⌋₊ - 1 := by
  have hq : (2 : ℝ) ≤ G / lam := (le_div_iff₀ hlam).mpr hG
  have hq2 : 2 ≤ ⌊G / lam⌋₊ := Nat.le_floor hq
  have hdiv : (G - lam) / lam = G / lam - 1 := by
    rw [sub_div, div_self (ne_of_gt hlam)]
  have hunit : ⌊lam / lam⌋₊ - 1 = 0 := by
    simp [ne_of_gt hlam]
  rw [hunit, zero_add]
  rw [hdiv, Nat.floor_sub_one]
  omega

/-- A finite list of nonnegative gaps admits a strictly smaller scale,
arbitrarily close from below, preserving every natural floor. Positive
floors have strict lower margins and every floor has a strict upper margin.
Zero gaps and zero floors are retained. -/
theorem exists_floor_stable_scale_with_margins (gs : List ℝ)
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ {tau : ℝ}, (∀ g ∈ gs, 0 ≤ g) → 0 < tau → tau < lam →
      ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
        ∀ g ∈ gs,
          ⌊g / lam'⌋₊ = ⌊g / lam⌋₊ ∧
          g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam' ∧
          (0 < ⌊g / lam⌋₊ → (⌊g / lam⌋₊ : ℝ) * lam' < g) := by
  induction gs with
  | nil =>
      intro tau _ htau0 htau
      refine ⟨(tau + lam) / 2, by linarith, by linarith, ?_⟩
      simp
  | cons g gs ih =>
      intro tau hnonneg htau0 htau
      have hg0 : 0 ≤ g := hnonneg g (by simp)
      have hden : 0 < (⌊g / lam⌋₊ : ℝ) + 1 := by
        exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
      have hupper : g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam :=
        (div_lt_iff₀ hlam).mp (Nat.lt_floor_add_one (g / lam))
      let cutoff : ℝ := g / ((⌊g / lam⌋₊ : ℝ) + 1)
      have hcutoff : cutoff < lam := by
        dsimp [cutoff]
        apply (div_lt_iff₀ hden).mpr
        simpa only [mul_comm] using hupper
      have hmax0 : 0 < max tau cutoff :=
        lt_of_lt_of_le htau0 (le_max_left _ _)
      have hmaxlam : max tau cutoff < lam := max_lt htau hcutoff
      obtain ⟨lam', hmax, hsmall, hrest⟩ :=
        ih (fun x hx => hnonneg x (by simp [hx])) hmax0 hmaxlam
      have htau' : tau < lam' := (le_max_left _ _).trans_lt hmax
      have hlam' : 0 < lam' := htau0.trans htau'
      have hcutoff' : cutoff < lam' := (le_max_right _ _).trans_lt hmax
      have hupper' : g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam' := by
        have h := (div_lt_iff₀ hden).mp hcutoff'
        simpa only [mul_comm] using h
      have hfloorle : (⌊g / lam⌋₊ : ℝ) * lam ≤ g :=
        (le_div_iff₀ hlam).mp (Nat.floor_le (div_nonneg hg0 hlam.le))
      have hlower : (⌊g / lam⌋₊ : ℝ) * lam' ≤ g :=
        (mul_le_mul_of_nonneg_left hsmall.le (Nat.cast_nonneg _)).trans hfloorle
      have heq : ⌊g / lam'⌋₊ = ⌊g / lam⌋₊ := by
        apply (Nat.floor_eq_iff (div_nonneg hg0 hlam'.le)).mpr
        exact ⟨(le_div_iff₀ hlam').mpr hlower,
          (div_lt_iff₀ hlam').mpr hupper'⟩
      have hstrict : 0 < ⌊g / lam⌋₊ → (⌊g / lam⌋₊ : ℝ) * lam' < g := by
        intro hq
        have hqR : (0 : ℝ) < (⌊g / lam⌋₊ : ℝ) := Nat.cast_pos.mpr hq
        exact (mul_lt_mul_of_pos_left hsmall hqR).trans_le hfloorle
      refine ⟨lam', htau', hsmall, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨heq, hupper', hstrict⟩
      · exact hrest x hx

/-- The floor equality projection of the finite-margin statement. -/
theorem exists_floor_stable_scale (gs : List ℝ) {lam tau : ℝ}
    (hlam : 0 < lam) (hnonneg : ∀ g ∈ gs, 0 ≤ g)
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ g ∈ gs, ⌊g / lam'⌋₊ = ⌊g / lam⌋₊ := by
  obtain ⟨lam', h1, h2, h3⟩ :=
    exists_floor_stable_scale_with_margins gs hlam hnonneg htau0 htau
  exact ⟨lam', h1, h2, fun g hg => (h3 g hg).1⟩

#print axioms floor_score_end_split
#print axioms exists_floor_stable_scale_with_margins
#print axioms exists_floor_stable_scale

end Jsp404.GapSplitFloorStability
