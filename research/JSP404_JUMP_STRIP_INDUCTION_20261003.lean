import research.JSP404_JUMP_FAMILY_CLOSURE_20261003

/-!
# Conditional jump induction from ordinary-point strip cardinal bounds

The hypotheses below bound the number of actual distinct planar points,
not weighted skeleton capacities. Neither strip bound is proved here.
The high hypothesis covers the full strip `δ < 1`, including `δ = 1/2`.
-/

open scoped EuclideanGeometry

namespace Jsp404.JumpStripInduction20261003

/-- Explicit ordinary-point cardinal hypotheses for every strip from three
onwards. Injectivity is stated separately as well as in legality. -/
structure ActualPointStripBounds : Prop where
  low : ∀ (n : ℕ), 3 ≤ n → ∀ (s : ℕ) (c : Fin s → Plane₂) (lam : ℝ),
    Function.Injective c → Section4Legality c lam →
    Nat.floor (Real.pi / lam) = n →
    Real.pi / lam - (n : ℝ) < 1 / 2 → s ≤ 2 ^ n
  high : ∀ (n : ℕ), 3 ≤ n → ∀ (s : ℕ) (c : Fin s → Plane₂) (lam : ℝ),
    Function.Injective c → Section4Legality c lam →
    Nat.floor (Real.pi / lam) = n →
    Real.pi / lam - (n : ℝ) < 1 → s ≤ 2 ^ n + 2 ^ (n - 2)

/-- Exact strip normalization from a previous high-angle baseline and a
strict failure of the next target. The left endpoint `δ = 0` is included.
The parameter `t = 1/2` gives LOW; `t = 1` gives the full HIGH strip. -/
theorem strip_normalization_of_angle_bounds {n : ℕ} (hn : 3 ≤ n)
    {M t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hbase : Real.pi - Real.pi / (n : ℝ) ≤ M)
    (hbad : M < Real.pi - Real.pi / ((n : ℝ) + t)) :
    0 < Real.pi - M ∧ Real.pi - M ≤ Real.pi / (n : ℝ) ∧
      Nat.floor (Real.pi / (Real.pi - M)) = n ∧
      Real.pi / (Real.pi - M) - (n : ℝ) < t := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnt : 0 < (n : ℝ) + t := by positivity
  have hlo : Real.pi / ((n : ℝ) + t) < Real.pi - M := by linarith
  have hlam : 0 < Real.pi - M := (div_pos Real.pi_pos hnt).trans hlo
  have hhi : Real.pi - M ≤ Real.pi / (n : ℝ) := by linarith
  have hfraclo : (n : ℝ) ≤ Real.pi / (Real.pi - M) := by
    rw [le_div_iff₀ hlam]
    calc (n : ℝ) * (Real.pi - M) ≤ (n : ℝ) * (Real.pi / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hhi hnpos.le
      _ = Real.pi := by field_simp
  have hfrachigh : Real.pi / (Real.pi - M) < (n : ℝ) + t := by
    rw [div_lt_iff₀ hlam]
    calc Real.pi = ((n : ℝ) + t) * (Real.pi / ((n : ℝ) + t)) := by field_simp
      _ < ((n : ℝ) + t) * (Real.pi - M) := mul_lt_mul_of_pos_left hlo hnt
  refine ⟨hlam, hhi, ?_, by linarith⟩
  apply (Nat.floor_eq_iff (by positivity : 0 ≤ Real.pi / (Real.pi - M))).mpr
  exact ⟨hfraclo, by linarith⟩

/-- Enumerate the actual point set at its finite maximum angle. -/
theorem legal_enumeration_at_maxAngle (s : Finset JSP404.Point)
    (hlam : 0 < Real.pi - JSP404.maxAngle s) :
    ∃ c : Fin s.card → Plane₂, Function.Injective c ∧
      Section4Legality c (Real.pi - JSP404.maxAngle s) := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  let c : Fin s.card → Plane₂ := fun i => (e.symm i).val
  have hinj : Function.Injective c := Subtype.val_injective.comp e.symm.injective
  refine ⟨c, hinj, ⟨hlam, hinj, ?_⟩⟩
  intro i j k hij hjk hik
  have hm := JSP404.angle_le_maxAngle
    (e.symm i).property (e.symm j).property (e.symm k).property
    (hinj.ne hij) (hinj.ne hik) (hinj.ne hjk)
  dsimp [c] at hm ⊢
  linarith

/-- A strip cardinal bound yields a target guarantee once the previous
high angle has been transferred to this cardinality. -/
theorem guaranteed_of_strip_count (n N : ℕ) (hn : 3 ≤ n) (hN : 3 ≤ N)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hbase : JSP404.Guaranteed N (Real.pi - Real.pi / (n : ℝ)))
    (hcard : ∀ (s : ℕ) (c : Fin s → Plane₂) (lam : ℝ),
      Function.Injective c → Section4Legality c lam →
      Nat.floor (Real.pi / lam) = n →
      Real.pi / lam - (n : ℝ) < t → s < N) :
    JSP404.Guaranteed N (Real.pi - Real.pi / ((n : ℝ) + t)) := by
  intro s hs
  have hs3 : 3 ≤ s.card := hs ▸ hN
  apply (JSP404.hasLargeAngle_iff_le_maxAngle hs3).mpr
  by_contra hbad
  have hm : JSP404.maxAngle s < Real.pi - Real.pi / ((n : ℝ) + t) :=
    lt_of_not_ge hbad
  have hb := (JSP404.hasLargeAngle_iff_le_maxAngle hs3).mp (hbase s hs)
  obtain ⟨hlam, _, hfloor, hdelta⟩ :=
    strip_normalization_of_angle_bounds hn ht ht1 hb hm
  obtain ⟨c, hinj, hlegal⟩ := legal_enumeration_at_maxAngle s hlam
  have hlt := hcard s.card c (Real.pi - JSP404.maxAngle s) hinj hlegal hfloor hdelta
  omega

private theorem jump_pair_from_baseline (bounds : ActualPointStripBounds)
    (n : ℕ) (hn : 3 ≤ n)
    (hbase : JSP404.Guaranteed (2 ^ n + 1) (Real.pi - Real.pi / (n : ℝ))) :
    JSP404.Guaranteed (2 ^ n + 1)
        ((1 - 2 / (2 * n + 1 : ℝ)) * Real.pi) ∧
      JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
        ((1 - 1 / (n + 1 : ℝ)) * Real.pi) := by
  have hsize : 3 ≤ 2 ^ n + 1 := by
    have hp : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hp
    omega
  have hlow := guaranteed_of_strip_count n (2 ^ n + 1) hn hsize (1 / 2)
    (by norm_num) (by norm_num) hbase (by
      intro s c lam hinj hlegal hfloor hdelta
      have hc := bounds.low n hn s c lam hinj hlegal hfloor hdelta
      omega)
  have hpowNonneg : 0 ≤ (2 : ℕ) ^ (n - 2) := Nat.zero_le _
  have hcounts : (2 : ℕ) ^ n + 1 ≤ 2 ^ n + 2 ^ (n - 2) + 1 := by omega
  have hbaseHigh : JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
      (Real.pi - Real.pi / (n : ℝ)) :=
    JSP404.guaranteed_mono hcounts hbase
  have hhigh := guaranteed_of_strip_count n (2 ^ n + 2 ^ (n - 2) + 1)
    hn (hsize.trans hcounts) 1 (by norm_num) (by norm_num) hbaseHigh (by
      intro s c lam hinj hlegal hfloor hdelta
      have hc := bounds.high n hn s c lam hinj hlegal hfloor hdelta
      omega)
  constructor
  · convert hlow using 1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    field_simp
  · convert hhigh using 1 <;> ring

/-- Simultaneous strong induction: the previous HIGH jump supplies the
baseline for both current jumps. At `n = 3`, six points supply `2π/3`
from the existing unconditional initial range. -/
theorem jump_families_of_actual_point_strip_bounds (bounds : ActualPointStripBounds) :
    (∀ n : ℕ, 3 ≤ n → JSP404.Guaranteed (2 ^ n + 1)
      ((1 - 2 / (2 * n + 1 : ℝ)) * Real.pi)) ∧
    (∀ n : ℕ, 3 ≤ n → JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
      ((1 - 1 / (n + 1 : ℝ)) * Real.pi)) := by
  have hpairs : ∀ n : ℕ, 3 ≤ n →
      JSP404.Guaranteed (2 ^ n + 1)
        ((1 - 2 / (2 * n + 1 : ℝ)) * Real.pi) ∧
      JSP404.Guaranteed (2 ^ n + 2 ^ (n - 2) + 1)
        ((1 - 1 / (n + 1 : ℝ)) * Real.pi) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      apply jump_pair_from_baseline bounds n hn
      by_cases hn3 : n = 3
      · subst n
        have h6 : JSP404.Guaranteed 6 (alphaN 6) := by
          rw [← sendov_alpha_eq_le_eight 6 (by norm_num) (by norm_num)]
          exact JSP404.guaranteed_alpha (by norm_num)
        have h6' : JSP404.Guaranteed 6 (Real.pi - Real.pi / 3) := by
          convert h6 using 1 <;> norm_num [alphaN, Nat.clog] <;> ring
        exact JSP404.guaranteed_mono (by norm_num) h6'
      · have hn4 : 4 ≤ n := by omega
        have hprev := (ih (n - 1) (by omega) (by omega)).2
        have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
          exact_mod_cast (show n - 1 + 1 = n by omega)
        have hprev' : JSP404.Guaranteed (2 ^ (n - 1) + 2 ^ ((n - 1) - 2) + 1)
            (Real.pi - Real.pi / (n : ℝ)) := by
          convert hprev using 1
          rw [hcast]
          ring
        have hpow : (2 : ℕ) ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
          have he : n = (n - 1) + 1 := by omega
          conv_lhs => rw [he]
          rw [pow_succ]
          ring
        have hexp : (n - 1) - 2 ≤ n - 1 := by omega
        have hsmall := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hexp
        exact JSP404.guaranteed_mono (by omega) hprev'
  exact ⟨fun n hn => (hpairs n hn).1, fun n hn => (hpairs n hn).2⟩

/-- Conditional equality for the original geometric extremal quantity,
using the separately checked jump-family closure consumer. -/
theorem sendov_alpha_eq_of_actual_point_strip_bounds (bounds : ActualPointStripBounds)
    (N : ℕ) (hN : 3 ≤ N) : JSP404.alpha N = alphaN N := by
  obtain ⟨hLow, hHigh⟩ := jump_families_of_actual_point_strip_bounds bounds
  exact sendov_alpha_eq_of_jump_families hLow hHigh N hN

/-- Conditional full original lower-and-sharpness statement. -/
theorem sendov_of_actual_point_strip_bounds (bounds : ActualPointStripBounds)
    (N : ℕ) (hN : 3 ≤ N) :
    (∀ C : PtCfg, C.pts.length = N →
      ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : PtCfg, C.pts.length = N ∧
      ∀ p q r : Plane₂, p ∈ C.pts → q ∈ C.pts → r ∈ C.pts →
        p ≠ q → r ≠ q → p ≠ r → ∠ p q r < alphaN N + ε) := by
  obtain ⟨hLow, hHigh⟩ := jump_families_of_actual_point_strip_bounds bounds
  exact sendov_of_jump_families hLow hHigh N hN

#print axioms strip_normalization_of_angle_bounds
#print axioms legal_enumeration_at_maxAngle
#print axioms guaranteed_of_strip_count
#print axioms jump_families_of_actual_point_strip_bounds
#print axioms sendov_alpha_eq_of_actual_point_strip_bounds
#print axioms sendov_of_actual_point_strip_bounds

end Jsp404.JumpStripInduction20261003
