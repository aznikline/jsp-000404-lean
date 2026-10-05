import Jsp000404.SixModelCompression
import Jsp000404.R2SixCentreN3

/-! Scalar-only adapter for the compressed strip n = 3.  Signatures are
extracted from the original natural-floor row score and sorted row permutation.
This module does not assert planar realizability of compressed scalar data. -/

namespace Jsp404.N3SixModelTerminal

open SixModelCompression

abbrev ModelSix3 := ModelSix 3

/-- The unchanged scalar terminal model at normalized unit scale. -/
noncomputable def model (M : ModelSix3) : N3Model where
  lam := 1
  p := 3 + M.delta
  hlam := by norm_num
  hp := by
    have h0 := M.hdelta.1
    have h1 := M.hdelta.2
    constructor <;> linarith
  t := M.theta
  ht := M.htheta
  ht0 := (M.theta_bounds 0).1
  ht4 := by
    have h := (M.theta_bounds 4).2
    linarith
  d := M.d
  hcor := by
    intro i j hij
    simpa using M.corridor i j hij
  htr := M.triangle

/-- `⌊g/λ⌋₊ = 2` means `g ∈ [2λ, 3λ)` and `⌊g/λ⌋₊ ≤ 1` means `g < 2λ`
(for `g ≥ 0`). -/
private theorem floor_two_iff {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 2 ↔ 2 * lam ≤ g ∧ g < 3 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (2:ℝ) ≤ g / lam := by exact_mod_cast h1
    have h2' : g / lam < (3:ℝ) := by
      have := h2
      push_cast at this ⊢; linarith
    rw [le_div_iff₀ hlam] at h1'
    rw [div_lt_iff₀ hlam] at h2'
    exact ⟨h1', h2'⟩
  · rintro ⟨h1, h2⟩
    have h1' : (2:ℝ) ≤ g / lam := by
      rw [le_div_iff₀ hlam]; exact h1
    have h2' : g / lam < (3:ℝ) := by
      rw [div_lt_iff₀ hlam]; exact h2
    exact ⟨by exact_mod_cast h1', by push_cast; linarith⟩

private theorem floor_le_one_iff {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ ≤ 1 ↔ g < 2 * lam := by
  rw [show ⌊g / lam⌋₊ ≤ 1 ↔ ⌊g / lam⌋₊ < 2 from (Nat.lt_add_one_iff).symm]
  rw [Nat.floor_lt (div_nonneg hg hlam.le)]
  constructor
  · intro h; rw [div_lt_iff₀ hlam] at h; exact_mod_cast h
  · intro h; rw [div_lt_iff₀ hlam]; exact_mod_cast h

set_option maxHeartbeats 800000 in
/-- Score `1` on a sorted four-chord anchored row is the `RowSig`
signature: exactly one of the five primitive gaps lies in `[2λ, 3λ)`
and the others are `< 2λ`. -/
theorem rowSig_of_linearScore_one {lam θ p : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ θ + p)
    (hsc : linearGapScore lam θ (θ + p) [x0, x1, x2, x3] = 1) :
    RowSig lam p θ x0 x1 x2 x3 := by
  have hg0 : 0 ≤ x0 - θ := by linarith [hord.1]
  have hg1 : 0 ≤ x1 - x0 := by linarith [hord.2.1]
  have hg2 : 0 ≤ x2 - x1 := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ x3 - x2 := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ θ + p - x3 := by linarith [hord.2.2.2.2]
  have hsum : (⌊(x0 - θ) / lam⌋₊ - 1) + ((⌊(x1 - x0) / lam⌋₊ - 1) +
      ((⌊(x2 - x1) / lam⌋₊ - 1) + ((⌊(x3 - x2) / lam⌋₊ - 1) +
        (⌊(θ + p - x3) / lam⌋₊ - 1)))) = 1 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 2 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 2 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 2 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 2 := by omega
  have b4 : ⌊(θ + p - x3) / lam⌋₊ ≤ 2 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + p - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + p - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + p - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + p - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + p - x3) / lam⌋₊ = 2) := by
    by_cases k0 : ⌊(x0 - θ) / lam⌋₊ = 2
    · exact Or.inl ⟨k0, by omega, by omega, by omega, by omega⟩
    · by_cases k1 : ⌊(x1 - x0) / lam⌋₊ = 2
      · exact Or.inr (Or.inl ⟨by omega, k1, by omega, by omega, by omega⟩)
      · by_cases k2 : ⌊(x2 - x1) / lam⌋₊ = 2
        · exact Or.inr (Or.inr (Or.inl
            ⟨by omega, by omega, k2, by omega, by omega⟩))
        · by_cases k3 : ⌊(x3 - x2) / lam⌋₊ = 2
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨by omega, by omega, by omega, k3, by omega⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨by omega, by omega, by omega, by omega, by omega⟩)))
  refine ⟨hord.1, hord.2.1, hord.2.2.1, hord.2.2.2.1, hord.2.2.2.2, ?_⟩
  rw [floor_two_iff hlam hg0, floor_two_iff hlam hg1, floor_two_iff hlam hg2,
    floor_two_iff hlam hg3, floor_two_iff hlam hg4] at key
  rw [floor_le_one_iff hlam hg0, floor_le_one_iff hlam hg1,
    floor_le_one_iff hlam hg2, floor_le_one_iff hlam hg3,
    floor_le_one_iff hlam hg4] at key
  obtain ⟨⟨p0, q0⟩, b1, b2, b3, b4⟩ | ⟨a1, ⟨p1, q1⟩, b2, b3, b4⟩ |
      ⟨a1, a2, ⟨p2, q2⟩, b3, b4⟩ | ⟨a1, a2, b1, ⟨p3, q3⟩, b4⟩ |
      ⟨a1, a2, b1, b2, ⟨p4, q4⟩⟩ := key
  · exact Or.inl ⟨p0, q0, b1, b2, b3, b4⟩
  · exact Or.inr (Or.inl ⟨a1, p1, q1, b2, b3, b4⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, p2, q2, b3, b4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, b1, p3, q3, b4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, b1, b2, p4, q4⟩)))

/-- A nonzero complement defect fixes the natural-number score exactly. -/
theorem linearScore_eq_one_of_rowDefect_eq_two (M : ModelSix3) (i : Fin 5)
    (hd : SixModelCompression.rowDefect M i = 2) :
    linearGapScore 1 (M.theta i) (M.theta i + (3 + M.delta)) (M.rowxs i) = 1 := by
  unfold SixModelCompression.rowDefect at hd
  norm_num only [Nat.cast_ofNat] at hd
  omega

/-- The actual sorted scalar row gives the signature; no signature is assumed. -/
theorem rowSig_of_rowDefect_eq_two (M : ModelSix3) (i : Fin 5)
    (hd : SixModelCompression.rowDefect M i = 2) :
    ∃ x0 x1 x2 x3 : ℝ,
      List.Perm [x0, x1, x2, x3]
        (((List.finRange 5).erase i).map (M.d i)) ∧
      RowSig 1 (3 + M.delta) (M.theta i) x0 x1 x2 x3 := by
  classical
  have hlength : (M.rowxs i).length = 4 := by
    have hp := (M.row_perm i).length_eq
    have htarget : (((List.finRange 5).erase i).map (M.d i)).length = 4 := by
      rw [List.length_map]
      fin_cases i <;> rfl
    exact hp.trans htarget
  obtain ⟨x0, x1, x2, x3, hrest⟩ := List.length_eq_four.mp hlength
  have hsort := M.row_sorted i
  rw [hrest] at hsort
  obtain ⟨h01, hs1⟩ := List.pairwise_cons.mp hsort
  obtain ⟨h12, hs2⟩ := List.pairwise_cons.mp hs1
  obtain ⟨h23, _⟩ := List.pairwise_cons.mp hs2
  have e01 : x0 ≤ x1 := h01 x1 (by simp)
  have e12 : x1 ≤ x2 := h12 x2 (by simp)
  have e23 : x2 ≤ x3 := h23 x3 (by simp)
  have hmem := row_mem_bounds M i
  have hx0 := hmem x0 (by rw [hrest]; simp)
  have hx3 := hmem x3 (by rw [hrest]; simp)
  norm_num only [Nat.cast_ofNat] at hx0 hx3
  have ht := M.theta_bounds i
  have hdelta := M.hdelta.2
  have hord : M.theta i ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧
      x3 ≤ M.theta i + (3 + M.delta) := by
    refine ⟨?_, e01, e12, e23, ?_⟩ <;> linarith
  have hscore := linearScore_eq_one_of_rowDefect_eq_two M i hd
  rw [hrest] at hscore
  refine ⟨x0, x1, x2, x3, ?_, rowSig_of_linearScore_one (by norm_num) hord hscore⟩
  rw [← hrest]
  exact M.row_perm i

/-- Rank one cannot have defect two in a normalized n = 3 scalar model. -/
theorem row_one_defect_two_impossible (M : ModelSix3)
    (h1 : SixModelCompression.rowDefect M 1 = 2) : False := by
  obtain ⟨x0, x1, x2, x3, hp, hs⟩ := rowSig_of_rowDefect_eq_two M 1 h1
  change List.Perm [x0, x1, x2, x3]
    [M.d 1 0, M.d 1 2, M.d 1 3, M.d 1 4] at hp
  rw [M.symm 1 0 (by decide)] at hp
  exact n3_row1 (model M) (by simpa [model] using hp) (by simpa [model] using hs)

/-- Rank three has the corresponding scalar exclusion. -/
theorem row_three_defect_two_impossible (M : ModelSix3)
    (h3 : SixModelCompression.rowDefect M 3 = 2) : False := by
  obtain ⟨x0, x1, x2, x3, hp, hs⟩ := rowSig_of_rowDefect_eq_two M 3 h3
  change List.Perm [x0, x1, x2, x3]
    [M.d 3 0, M.d 3 1, M.d 3 2, M.d 3 4] at hp
  rw [M.symm 3 0 (by decide), M.symm 3 1 (by decide), M.symm 3 2 (by decide)] at hp
  exact n3_row3 (model M) (by simpa [model] using hp) (by simpa [model] using hs)

/-- The two endpoint ranks cannot simultaneously have defect two. -/
theorem endpoint_defects_two_impossible (M : ModelSix3)
    (h0 : SixModelCompression.rowDefect M 0 = 2)
    (h4 : SixModelCompression.rowDefect M 4 = 2) : False := by
  obtain ⟨x0, x1, x2, x3, hp0, hs0⟩ := rowSig_of_rowDefect_eq_two M 0 h0
  obtain ⟨y0, y1, y2, y3, hp4, hs4⟩ := rowSig_of_rowDefect_eq_two M 4 h4
  change List.Perm [x0, x1, x2, x3]
    [M.d 0 1, M.d 0 2, M.d 0 3, M.d 0 4] at hp0
  change List.Perm [y0, y1, y2, y3]
    [M.d 4 0, M.d 4 1, M.d 4 2, M.d 4 3] at hp4
  rw [M.symm 4 0 (by decide), M.symm 4 1 (by decide),
    M.symm 4 2 (by decide), M.symm 4 3 (by decide)] at hp4
  exact n3_between (model M) (by simpa [model] using hp0) (by simpa [model] using hs0)
    (by simpa [model] using hp4) (by simpa [model] using hs4)

#print axioms rowSig_of_linearScore_one
#print axioms rowSig_of_rowDefect_eq_two
#print axioms row_one_defect_two_impossible
#print axioms row_three_defect_two_impossible
#print axioms endpoint_defects_two_impossible

end Jsp404.N3SixModelTerminal
