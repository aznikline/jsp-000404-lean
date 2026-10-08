import Jsp000404.R2SixCentreN4
import Jsp000404.N3Extraction
import Jsp000404.FivePointCapacity
import Jsp000404.ChartInvariance

/-!
# Extraction: six-centre `SatChart` → `N4Model`

Instantiates the scalar `n = 4` terminal model `R2N4.N4Model` from a
real six-centre `SatChart`, parallel to `N3Extraction`:

* `n4T` / `n4σ` are the sorted non-anchor `theta` values and the
  rank-to-index bijection, identical to the `n = 3` machinery.
* `d i j` is the shared chord `dirRep (σ i) (σ j)`; `n4corridor` and
  `n4triple` replay `up_corridor`, `up_trans` and `up_cap`.
* `n4_row2_exists` / `n4_row1_exists` extract the sorted four-chord row
  at a chart index together with its `RowSig2` (defect `2`, score `2`)
  or `RowSig1` (defect `3`, score `1`) signature and the `List.Perm`
  onto the model chords.
* `six_centre_n4_overcap` is the terminal: a six-centre configuration
  at `n = 4` with a saturated anchor, two defect-`2` rows and all other
  rows of defect `≥ 3` has `potential ≤ 2^4 + 2^2`.  Over-capacity
  forces two defect-`3` rows among the three tail rows; each θ-class is
  then closed by the generated leaf certificates `n4cert_*`, with the
  between class additionally using the residual emission chord
  `r2_residual_tail_emission`.
-/

namespace Jsp404

open Classical
open scoped EuclideanSpace

/-- `⌊g/λ⌋₊ = 3` means `g ∈ [3λ, 4λ)` (for `g ≥ 0`). -/
theorem floor_three_iff {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    ⌊g / lam⌋₊ = 3 ↔ 3 * lam ≤ g ∧ g < 4 * lam := by
  rw [Nat.floor_eq_iff (div_nonneg hg hlam.le)]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (3:ℝ) ≤ g / lam := by exact_mod_cast h1
    have h2' : g / lam < (4:ℝ) := by
      have := h2
      push_cast at this ⊢; linarith
    rw [le_div_iff₀ hlam] at h1'
    rw [div_lt_iff₀ hlam] at h2'
    exact ⟨h1', h2'⟩
  · rintro ⟨h1, h2⟩
    have h1' : (3:ℝ) ≤ g / lam := by
      rw [le_div_iff₀ hlam]; exact h1
    have h2' : g / lam < (4:ℝ) := by
      rw [div_lt_iff₀ hlam]; exact h2
    exact ⟨by exact_mod_cast h1', by push_cast; linarith⟩

set_option maxHeartbeats 800000 in
/-- Score `2` on a sorted four-chord anchored row is the `RowSig2`
signature: either one primitive gap lies in `[3λ, 4λ)` and the rest are
`< 2λ`, or two gaps lie in `[2λ, 3λ)` and the rest are `< 2λ`. -/
theorem rowSig2_of_linearScore_two {lam θ : ℝ} (hlam : 0 < lam)
    {x0 x1 x2 x3 : ℝ}
    (hord : θ ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧ x3 ≤ θ + Real.pi)
    (hsc : linearGapScore lam θ (θ + Real.pi) [x0, x1, x2, x3] = 2) :
    R2N4.RowSig2 lam Real.pi θ x0 x1 x2 x3 := by
  have hg0 : 0 ≤ x0 - θ := by linarith [hord.1]
  have hg1 : 0 ≤ x1 - x0 := by linarith [hord.2.1]
  have hg2 : 0 ≤ x2 - x1 := by linarith [hord.2.2.1]
  have hg3 : 0 ≤ x3 - x2 := by linarith [hord.2.2.2.1]
  have hg4 : 0 ≤ θ + Real.pi - x3 := by linarith [hord.2.2.2.2]
  have hsum : (⌊(x0 - θ) / lam⌋₊ - 1) + ((⌊(x1 - x0) / lam⌋₊ - 1) +
      ((⌊(x2 - x1) / lam⌋₊ - 1) + ((⌊(x3 - x2) / lam⌋₊ - 1) +
        (⌊(θ + Real.pi - x3) / lam⌋₊ - 1)))) = 2 := by
    have h := hsc
    simp only [linearGapScore, gapScore] at h
    omega
  have b0 : ⌊(x0 - θ) / lam⌋₊ ≤ 3 := by omega
  have b1 : ⌊(x1 - x0) / lam⌋₊ ≤ 3 := by omega
  have b2 : ⌊(x2 - x1) / lam⌋₊ ≤ 3 := by omega
  have b3 : ⌊(x3 - x2) / lam⌋₊ ≤ 3 := by omega
  have b4 : ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 3 := by omega
  have key :
      (⌊(x0 - θ) / lam⌋₊ = 3 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 3 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 3 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 3 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 3) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ = 2 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ = 2 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ ≤ 1) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ = 2 ∧ ⌊(x3 - x2) / lam⌋₊ ≤ 1 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) ∨
      (⌊(x0 - θ) / lam⌋₊ ≤ 1 ∧ ⌊(x1 - x0) / lam⌋₊ ≤ 1 ∧
          ⌊(x2 - x1) / lam⌋₊ ≤ 1 ∧ ⌊(x3 - x2) / lam⌋₊ = 2 ∧
          ⌊(θ + Real.pi - x3) / lam⌋₊ = 2) := by
    by_cases q0 : ⌊(x0 - θ) / lam⌋₊ = 3
    · exact Or.inl ⟨q0, by omega, by omega, by omega, by omega⟩
    · by_cases q1 : ⌊(x1 - x0) / lam⌋₊ = 3
      · exact Or.inr (Or.inl ⟨by omega, q1, by omega, by omega, by omega⟩)
      · by_cases q2 : ⌊(x2 - x1) / lam⌋₊ = 3
        · exact Or.inr (Or.inr (Or.inl
            ⟨by omega, by omega, q2, by omega, by omega⟩))
        · by_cases q3 : ⌊(x3 - x2) / lam⌋₊ = 3
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨by omega, by omega, by omega, q3, by omega⟩)))
          · by_cases q4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 3
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨by omega, by omega, by omega, by omega, q4⟩))))
            · -- no gap has floor `3`: exactly two floors equal `2`.
              by_cases r0 : ⌊(x0 - θ) / lam⌋₊ = 2
              · by_cases r1 : ⌊(x1 - x0) / lam⌋₊ = 2
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨r0, r1, by omega, by omega, by omega⟩)))))
                · by_cases r2 : ⌊(x2 - x1) / lam⌋₊ = 2
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inl ⟨r0, by omega, r2, by omega, by omega⟩))))))
                  · by_cases r3 : ⌊(x3 - x2) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inl
                          ⟨r0, by omega, by omega, r3, by omega⟩)))))))
                    · have r4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inl
                          ⟨r0, by omega, by omega, by omega, r4⟩))))))))
              · by_cases s1 : ⌊(x1 - x0) / lam⌋₊ = 2
                · by_cases s2 : ⌊(x2 - x1) / lam⌋₊ = 2
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl
                        ⟨by omega, s1, s2, by omega, by omega⟩)))))))))
                  · by_cases s3 : ⌊(x3 - x2) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨by omega, s1, by omega, s3, by omega⟩))))))))))
                    · have s4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨by omega, s1, by omega, by omega, s4⟩)))))))))))
                · by_cases t2 : ⌊(x2 - x1) / lam⌋₊ = 2
                  · by_cases t3 : ⌊(x3 - x2) / lam⌋₊ = 2
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inl
                            ⟨by omega, by omega, t2, t3, by omega⟩))))))))))))
                    · have t4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inr (Or.inl
                            ⟨by omega, by omega, t2, by omega, t4⟩)))))))))))))
                  · have u3 : ⌊(x3 - x2) / lam⌋₊ = 2 := by omega
                    have u4 : ⌊(θ + Real.pi - x3) / lam⌋₊ = 2 := by omega
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr
                          ⟨by omega, by omega, by omega, u3, u4⟩)))))))))))))
  rw [floor_three_iff hlam hg0, floor_three_iff hlam hg1,
    floor_three_iff hlam hg2, floor_three_iff hlam hg3,
    floor_three_iff hlam hg4, floor_two_iff hlam hg0,
    floor_two_iff hlam hg1, floor_two_iff hlam hg2,
    floor_two_iff hlam hg3, floor_two_iff hlam hg4,
    floor_le_one_iff hlam hg0, floor_le_one_iff hlam hg1,
    floor_le_one_iff hlam hg2, floor_le_one_iff hlam hg3,
    floor_le_one_iff hlam hg4] at key
  rcases key with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    tauto

section SixCentreN4

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 6 → Plane₂} {v : Fin 6} {theta : Fin 5 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- Distinct non-anchor centres have distinct anchor directions. -/
theorem n4theta_injective : Function.Injective theta := by
  intro i j hij
  by_contra hne
  rcases up_or_up C hne with h | h
  · exact absurd hij (ne_of_lt (up_theta_lt C hne h))
  · exact absurd hij.symm (ne_of_lt (up_theta_lt C (Ne.symm hne) h))

/-- The five non-anchor `theta`s are distinct. -/
theorem n4Tcard : (Finset.image theta Finset.univ).card = 5 := by
  classical
  rw [Finset.card_image_of_injective _ (n4theta_injective C),
    Finset.card_univ, Fintype.card_fin]

/-- Sorted `theta` values as a strict-mono enumeration. -/
noncomputable def n4T : Fin 5 → ℝ :=
  (Finset.image theta Finset.univ).orderEmbOfFin (n4Tcard C)

theorem n4T_strictMono : StrictMono (n4T C) := fun _ _ h =>
  ((Finset.image theta Finset.univ).orderEmbOfFin _).strictMono h

/-- Rank-to-index bijection: `n4σ C i` is the centre whose `theta` is
the `i`-th smallest. -/
noncomputable def n4σ : Fin 5 → Fin 5 := fun i =>
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n4Tcard C) i)).choose

theorem n4σ_spec (i : Fin 5) : theta (n4σ C i) = n4T C i :=
  (Finset.mem_image.mp
    (Finset.orderEmbOfFin_mem _ (n4Tcard C) i)).choose_spec.2

theorem n4σ_injective : Function.Injective (n4σ C) := by
  intro i j hij
  apply (n4T_strictMono C).injective
  rw [← n4σ_spec C i, ← n4σ_spec C j, hij]

theorem n4σ_bijective : Function.Bijective (n4σ C) :=
  Finite.injective_iff_bijective.mp (n4σ_injective C)

theorem n4σ_ne {i j : Fin 5} (h : i ≠ j) : n4σ C i ≠ n4σ C j :=
  fun hh => h (n4σ_injective C hh)

/-- A lower-`theta` centre is always `Up` of a higher one, at
`n4σ`-ranks. -/
theorem n4σ_up {i j : Fin 5} (hij : i < j) :
    Up o e c v (n4σ C i) (n4σ C j) := by
  have hlt : theta (n4σ C i) < theta (n4σ C j) := by
    rw [n4σ_spec C i, n4σ_spec C j]
    exact n4T_strictMono C hij
  exact up_of_theta_lt' C (n4σ_ne C hij.ne) hlt

/-- Corridor bounds in model coordinates. -/
theorem n4corridor {i j : Fin 5} (hij : i < j) :
    n4T C i + lam ≤
        dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j) ∧
      dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j) ≤
        Real.pi - lam + n4T C j := by
  have hcor := up_corridor C (n4σ_ne C hij.ne) (n4σ_up C hij)
  rwa [n4σ_spec C i, n4σ_spec C j] at hcor

/-- Triple `Up`-constraints in model coordinates. -/
theorem n4triple {i j k : Fin 5} (hij : i < j) (hjk : j < k) :
    (dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n4σ C j) (n4σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j) <
          dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C k) <
          dirRep o e (c ∘ v.succAbove) (n4σ C j) (n4σ C k)) ∨
      (dirRep o e (c ∘ v.succAbove) (n4σ C j) (n4σ C k) + lam ≤
          dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j) ∧
        dirRep o e (c ∘ v.succAbove) (n4σ C j) (n4σ C k) <
          dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C k) ∧
        dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C k) <
          dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j)) := by
  have hl0 : 0 < lam := C.hlam
  have hneij : n4σ C i ≠ n4σ C j := n4σ_ne C hij.ne
  have hnejk : n4σ C j ≠ n4σ C k := n4σ_ne C hjk.ne
  have hneik : n4σ C i ≠ n4σ C k := n4σ_ne C (hij.trans hjk).ne
  have hupij := n4σ_up C hij
  have hupjk := n4σ_up C hjk
  obtain ⟨-, hbetween⟩ := up_trans C hneij hnejk hneik hupij hupjk
  have hcap := up_cap C hneij hnejk hneik hupij hupjk
  rcases le_or_gt 0 (dirRep o e (c ∘ v.succAbove) (n4σ C j) (n4σ C k) -
    dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j)) with hs | hs
  · rw [abs_of_nonneg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, h1, h2⟩
    · exfalso; linarith
  · rw [abs_of_neg hs] at hcap
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact Or.inr ⟨by linarith, h1, h2⟩

/-- The scalar `n = 4` model of the six-centre configuration. -/
noncomputable def n4model : R2N4.N4Model where
  lam := lam
  p := Real.pi
  hlam := C.hlam
  hp := by
    have h1 := C.hnl
    have h2 := C.hπ
    push_cast at h1 h2
    constructor <;> linarith
  t := n4T C
  ht := n4T_strictMono C
  ht0 := by
    have h := (C.htheta (n4σ C 0)).1.1
    rwa [n4σ_spec C 0] at h
  ht4 := by
    have h := (C.htheta (n4σ C 4)).1.2
    rw [n4σ_spec C 4] at h
    push_cast at h ⊢
    linarith
  d := fun i j => dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j)
  hcor := fun _ _ h => n4corridor C h
  htr := fun _ _ _ h1 h2 => n4triple C h1 h2

theorem n4model_lam : (n4model C).lam = lam := rfl
theorem n4model_p : (n4model C).p = Real.pi := rfl
theorem n4model_t (i : Fin 5) : (n4model C).t i = n4T C i := rfl
theorem n4model_d (i j : Fin 5) :
    (n4model C).d i j =
      dirRep o e (c ∘ v.succAbove) (n4σ C i) (n4σ C j) := rfl

/-- Rank identification: `n4σ C r = u` iff the `r`-th sorted `theta`
value is `theta u`. -/
theorem n4σ_eq_iff (u r : Fin 5) :
    n4σ C r = u ↔ n4T C r = theta u := by
  constructor
  · intro h; rw [← n4σ_spec C r, h]
  · intro h
    exact n4theta_injective C ((n4σ_spec C r).trans h)

/-- Rank via bisection: if every smaller rank lies strictly below
`theta u` and `n4T C r` does not, then `n4T C r = theta u`. -/
theorem n4T_eq_of_bounds (u : Fin 5) (r : Fin 5)
    (hlo : ∀ s : Fin 5, s < r → n4T C s < theta u)
    (hhi : theta u ≤ n4T C r) :
    n4T C r = theta u := by
  obtain ⟨r', hr'⟩ : ∃ r' : Fin 5, n4T C r' = theta u := by
    have hmem : theta u ∈ Set.range
        ⇑((Finset.image theta Finset.univ).orderEmbOfFin (n4Tcard C)) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    exact hmem
  rcases lt_trichotomy r' r with hlt | heq | hgt
  · exact absurd (hlo r' hlt) (by rw [hr']; exact lt_irrefl _)
  · exact heq ▸ hr'
  · have h2 := n4T_strictMono C hgt
    rw [hr'] at h2
    linarith

/-- Chord symmetry in the model. -/
theorem n4d_comm (i j : Fin 5) (h : i ≠ j) :
    (n4model C).d i j = (n4model C).d j i := by
  have h' : n4σ C i ≠ n4σ C j := n4σ_ne C h
  exact phi_comm C h'

/-- Common core of `n4_row_exists`: the sorted four-chord list of the
row at chart index `u = n4σ C r`, with ordering and `List.Perm` onto
the model chords.  The score is returned for signature dispatch. -/
theorem n4_row_core {r u : Fin 5} (hu : n4σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2 ∨
      rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 : ℝ,
      (n4T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧
        x3 ≤ n4T C r + Real.pi) ∧
      linearGapScore lam (n4T C r) (n4T C r + Real.pi)
          [x0, x1, x2, x3] = 4 - rowDefect 4 lam
            (directionRow o e c (v.succAbove u)) ∧
      List.Perm [x0, x1, x2, x3]
        (((List.finRange 5).erase r).map fun j => (n4model C).d r j) := by
  classical
  have hTu : n4T C r = theta u := (n4σ_eq_iff C u r).mp hu
  have hlen : (directionRow o e (c ∘ v.succAbove) u).length = 4 := by
    have h := directionRow_length o e (c ∘ v.succAbove) u
    omega
  obtain ⟨x0, x1, x2, x3, hrest⟩ := List.length_eq_four.mp hlen
  have hsort := directionRow_sorted o e (c ∘ v.succAbove) u
  rw [hrest] at hsort
  obtain ⟨h01', hs1⟩ := List.sortedLE_cons.mp hsort
  obtain ⟨h12', hs2⟩ := List.sortedLE_cons.mp hs1
  obtain ⟨h23', -⟩ := List.sortedLE_cons.mp hs2
  have e01 : x0 ≤ x1 := h01' x1 (by simp)
  have e12 : x1 ≤ x2 := h12' x2 (by simp)
  have e23 : x2 ≤ x3 := h23' x3 (by simp)
  have hmem : ∀ x ∈ directionRow o e (c ∘ v.succAbove) u,
      lam ≤ x ∧ x < Real.pi := by
    intro x hx
    obtain ⟨j, hju, rfl⟩ := (mem_directionRow o e (c ∘ v.succAbove)).mp hx
    exact ⟨phi_ge_lam C (Ne.symm hju), (linRep_mem_Ico _).2⟩
  have hβ : Real.pi - 4 * lam < lam := by exact_mod_cast C.hβ
  have hx0ge : theta u ≤ x0 := by
    have hx := (hmem x0 (by rw [hrest]; simp)).1
    have hθ : theta u ≤ Real.pi - 4 * lam := by
      exact_mod_cast (C.htheta u).1.2
    linarith
  have hx3le : x3 ≤ theta u + Real.pi := by
    have hx := (hmem x3 (by rw [hrest]; simp)).2
    have hθ0 := (C.htheta u).1.1
    linarith
  have hlampi : lam < Real.pi := by
    have h1 := C.hnl; have h2 := C.hn3'; have h3 := C.hlam; nlinarith
  have htheta' : ∀ i, theta i ∈ Set.Icc 0 lam ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle) := by
    intro i
    refine ⟨?_, (C.htheta i).2⟩
    have h := (C.htheta i).1
    rw [Set.mem_Icc] at h ⊢
    have h2 : theta i ≤ Real.pi - 4 * lam := by exact_mod_cast h.2
    exact ⟨h.1, by linarith⟩
  have hscore := anchored_rowScore_eq_linear o e C.he c C.hleg.inj v C.hlam
    hlampi theta htheta' (fun a b hab => phi_ge_lam C hab) u
  have hcells := rowCells_directionRow_le_of_floor_eq o e c C.hlam
    (v.succAbove u) (by omega) C.hn
  have hsub := rowScore_eq_sub_defect lam C.hlam 4 _ hcells
  rw [hscore, hrest, ← hTu] at hsub
  refine ⟨⟨hx0ge, e01, e12, e23, hx3le⟩, hsub, ?_⟩
  have hp1 : List.Perm (directionRow o e (c ∘ v.succAbove) u)
      (((List.finRange 5).erase u).map
        (dirRep o e (c ∘ v.succAbove) u)) :=
    List.perm_insertionSort _ _
  rw [hrest] at hp1
  have hmap : List.Perm ((List.finRange 5).erase u)
      (((List.finRange 5).erase r).map (n4σ C)) := by
    apply List.Subperm.antisymm
    · apply List.Nodup.subperm ((List.nodup_finRange 5).erase u)
      intro x hx
      rw [(List.nodup_finRange 5).mem_erase_iff] at hx
      obtain ⟨j, hj⟩ := (n4σ_bijective C).surjective x
      refine List.mem_map.mpr ⟨j, ?_, hj⟩
      rw [(List.nodup_finRange 5).mem_erase_iff]
      exact ⟨fun hjr => hx.1 (by rw [← hj, hjr, hu]), List.mem_finRange _⟩
    · apply List.Nodup.subperm
        (((List.nodup_finRange 5).erase r).map (n4σ_injective C))
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨j, hje, rfl⟩ := hx
      rw [(List.nodup_finRange 5).mem_erase_iff] at hje ⊢
      exact ⟨fun hxu => hje.1 (n4σ_injective C (hxu.trans hu.symm)),
        List.mem_finRange _⟩
  have hp2 := hmap.map (dirRep o e (c ∘ v.succAbove) u)
  rw [List.map_map] at hp2
  refine hp1.trans (hp2.trans ?_)
  have hfeq : (dirRep o e (c ∘ v.succAbove) u ∘ n4σ C) =
      fun j => (n4model C).d r j := by
    funext j
    show dirRep o e (c ∘ v.succAbove) u (n4σ C j) = (n4model C).d r j
    rw [n4model_d C r j, hu]
  rw [hfeq]

/-- A defect-`2` row at `n = 4` yields a `RowSig2` witness list. -/
theorem n4_row2_exists {r u : Fin 5} (hu : n4σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 2) :
    ∃ x0 x1 x2 x3 : ℝ,
      (n4T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧
        x3 ≤ n4T C r + Real.pi) ∧
      R2N4.RowSig2 lam Real.pi (n4T C r) x0 x1 x2 x3 ∧
      List.Perm [x0, x1, x2, x3]
        (((List.finRange 5).erase r).map fun j => (n4model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, hord, hlin, hperm⟩ :=
    n4_row_core C hu (Or.inl hd)
  refine ⟨x0, x1, x2, x3, hord, ?_, hperm⟩
  rw [hd] at hlin
  exact rowSig2_of_linearScore_two C.hlam hord (by omega)
/-- A defect-`3` row at `n = 4` yields a `RowSig1` witness list. -/
theorem n4_row1_exists {r u : Fin 5} (hu : n4σ C r = u)
    (hd : rowDefect 4 lam (directionRow o e c (v.succAbove u)) = 3) :
    ∃ x0 x1 x2 x3 : ℝ,
      (n4T C r ≤ x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧ x2 ≤ x3 ∧
        x3 ≤ n4T C r + Real.pi) ∧
      R2N4.RowSig1 lam Real.pi (n4T C r) x0 x1 x2 x3 ∧
      List.Perm [x0, x1, x2, x3]
        (((List.finRange 5).erase r).map fun j => (n4model C).d r j) := by
  obtain ⟨x0, x1, x2, x3, hord, hlin, hperm⟩ :=
    n4_row_core C hu (Or.inr hd)
  refine ⟨x0, x1, x2, x3, hord, ?_, hperm⟩
  rw [hd] at hlin
  have hS := rowSig_of_linearScore_one C.hlam hord (by omega)
  rcases hS with ⟨-, -, -, -, -, hS'⟩
  exact hS'

/-- All-above class: the two defect-`2` rows occupy ranks `0` and `1`. -/
theorem n4σ_zero_one_of_all_above {lo hi : Fin 5} (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 5, z ≠ lo → z ≠ hi → theta hi < theta z) :
    n4σ C 0 = lo ∧ n4σ C 1 = hi := by
  have hge : ∀ z : Fin 5, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hθ.trans (hcl z h1 h2)).le
  have hT0 : n4T C 0 = theta lo := by
    apply n4T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n4σ_spec C 0]; exact hge _
  have hσ0 : n4σ C 0 = lo := (n4σ_eq_iff C lo 0).mpr hT0
  have hT1 : n4T C 1 = theta hi := by
    apply n4T_eq_of_bounds C hi 1
    · intro s hs
      have hs0 : s = 0 := Fin.ext (Nat.lt_one_iff.mp hs)
      rw [hs0, hT0]; exact hθ
    · rw [← n4σ_spec C 1]
      rcases eq_or_ne (n4σ C 1) lo with h1 | h1
      · exact absurd (n4σ_injective C (h1.trans hσ0.symm)) (by decide)
      · rcases eq_or_ne (n4σ C 1) hi with rfl | h2
        · exact le_refl _
        · exact (hcl _ h1 h2).le
  exact ⟨hσ0, (n4σ_eq_iff C hi 1).mpr hT1⟩

/-- All-below class: the two defect-`2` rows occupy ranks `3` and `4`. -/
theorem n4σ_three_four_of_all_below {lo hi : Fin 5} (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 5, z ≠ lo → z ≠ hi → theta z < theta lo) :
    n4σ C 3 = lo ∧ n4σ C 4 = hi := by
  have hle : ∀ z : Fin 5, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact ((hcl z h2 h1).trans hθ).le
  have hT4 : n4T C 4 = theta hi := by
    apply n4T_eq_of_bounds C hi 4
    · intro s hs
      rw [← n4σ_spec C s]
      rcases eq_or_ne (n4σ C s) hi with h1 | h1
      · exfalso
        have hmax : n4T C 4 ≤ theta hi := by
          rw [← n4σ_spec C 4]; exact hle _
        have hlt : n4T C s < n4T C 4 := n4T_strictMono C hs
        rw [← n4σ_spec C s, h1] at hlt
        linarith
      · rcases eq_or_ne (n4σ C s) lo with rfl | h2
        · exact hθ
        · exact (hcl _ h2 h1).trans hθ
    · obtain ⟨r', hr'⟩ := (n4σ_bijective C).surjective hi
      have hle4 : r' ≤ (4 : Fin 5) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n4T_strictMono C).monotone hle4
      rw [← n4σ_spec C r', hr'] at hm
      exact hm
  have hσ4 : n4σ C 4 = hi := (n4σ_eq_iff C hi 4).mpr hT4
  have hT3 : n4T C 3 = theta lo := by
    apply n4T_eq_of_bounds C lo 3
    · intro s hs
      rw [← n4σ_spec C s]
      by_contra hnn
      replace hnn := not_lt.mp hnn
      have h1 : n4σ C s = lo ∨ n4σ C s = hi := by
        rcases eq_or_ne (n4σ C s) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n4σ C s) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hnn)
      have h3 : n4σ C 3 = lo ∨ n4σ C 3 = hi := by
        have hge3 : theta lo ≤ n4T C 3 := by
          have hlt := n4T_strictMono C hs
          rw [← n4σ_spec C s] at hlt
          linarith
        rw [← n4σ_spec C 3] at hge3
        rcases eq_or_ne (n4σ C 3) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n4σ C 3) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge3)
      have h4 : n4σ C 4 = lo ∨ n4σ C 4 = hi := by
        have hge4 : theta lo ≤ n4T C 4 := by
          have hlt := n4T_strictMono C
            (hs.trans (by decide : (3 : Fin 5) < 4))
          rw [← n4σ_spec C s] at hlt
          linarith
        rw [← n4σ_spec C 4] at hge4
        rcases eq_or_ne (n4σ C 4) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n4σ C 4) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge4)
      exact n3_pigeon
        (fun h => (ne_of_lt hs) (n4σ_injective C h))
        (fun h => (ne_of_lt (hs.trans (by decide : (3 : Fin 5) < 4)))
          (n4σ_injective C h))
        (fun h => absurd (n4σ_injective C h) (by decide))
        h1 h3 h4
    · rw [← n4σ_spec C 3]
      rcases eq_or_ne (n4σ C 3) hi with h3hi | h3hi
      · exact absurd (n4σ_injective C (h3hi.trans hσ4.symm)) (by decide)
      · rcases eq_or_ne (n4σ C 3) lo with rfl | h3lo
        · exact le_refl _
        · exfalso
          obtain ⟨r_l, hr_l⟩ := (n4σ_bijective C).surjective lo
          have hrl3 : r_l ≠ 3 := fun h => h3lo (h ▸ hr_l)
          have hrl4 : r_l ≠ 4 := fun h =>
            hθ.ne (by rw [← hr_l, ← hσ4, h])
          have hrl2 : r_l.val ≤ 2 := by
            have hlt5 := r_l.isLt
            have h3v : r_l.val ≠ 3 := fun hv => hrl3 (Fin.ext hv)
            have h4v : r_l.val ≠ 4 := fun hv => hrl4 (Fin.ext hv)
            omega
          have hlt : n4T C r_l < n4T C 3 := by
            apply n4T_strictMono C
            rw [Fin.lt_def]
            omega
          rw [← n4σ_spec C r_l, hr_l] at hlt
          have hcl3 : n4T C 3 < theta lo := by
            have h := hcl _ h3lo h3hi
            rwa [n4σ_spec C 3] at h
          linarith
  exact ⟨(n4σ_eq_iff C lo 3).mpr hT3, hσ4⟩

/-- Between class: the two defect-`2` rows occupy ranks `0` and `4`. -/
theorem n4σ_zero_four_of_between {lo hi : Fin 5} (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi) :
    n4σ C 0 = lo ∧ n4σ C 4 = hi := by
  have hge : ∀ z : Fin 5, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hcl z h1 h2).1.le
  have hle : ∀ z : Fin 5, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact (hcl z h2 h1).2.le
  have hT0 : n4T C 0 = theta lo := by
    apply n4T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n4σ_spec C 0]; exact hge _
  have hT4 : n4T C 4 = theta hi := by
    apply n4T_eq_of_bounds C hi 4
    · intro s hs
      rw [← n4σ_spec C s]
      rcases eq_or_ne (n4σ C s) hi with h1 | h1
      · exfalso
        have hmax : theta (n4σ C 4) ≤ theta hi := by
          rw [n4σ_spec C 4]; exact hle _
        have hlt : n4T C s < n4T C 4 := n4T_strictMono C hs
        rw [← n4σ_spec C s, ← n4σ_spec C 4, h1] at hlt
        linarith
      · rcases eq_or_ne (n4σ C s) lo with h2 | h2
        · rw [h2]; exact hθ
        · exact (hcl _ h2 h1).2
    · obtain ⟨r', hr'⟩ := (n4σ_bijective C).surjective hi
      have hle4 : r' ≤ (4 : Fin 5) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n4T_strictMono C).monotone hle4
      rw [← n4σ_spec C r', hr'] at hm
      exact hm
  exact ⟨(n4σ_eq_iff C lo 0).mpr hT0, (n4σ_eq_iff C hi 4).mpr hT4⟩

/-- Rewrites the erased-index chord list of row `r` into min/max order
so it matches the certificate's literal chord lists. -/
theorem n4_row_perm {r : Fin 5} {x0 x1 x2 x3 : ℝ}
    (h : List.Perm [x0, x1, x2, x3]
      (((List.finRange 5).erase r).map fun j => (n4model C).d r j)) :
    List.Perm [x0, x1, x2, x3]
      (((List.finRange 5).erase r).map fun j =>
        (n4model C).d (min r j) (max r j)) := by
  have hmap : ((List.finRange 5).erase r).map
        (fun j => (n4model C).d r j) =
      ((List.finRange 5).erase r).map
        (fun j => (n4model C).d (min r j) (max r j)) := by
    apply List.map_congr_left
    intro j hj
    have hjr : j ≠ r := by
      rw [(List.nodup_finRange 5).mem_erase_iff] at hj
      exact hj.1
    rcases lt_or_ge r j with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le]
    · rw [min_eq_right hge, max_eq_left hge]
      exact n4d_comm C r j hjr.symm
  rwa [hmap] at h

end SixCentreN4

section N4Terminal

/-- `2 ^ k = 2` forces `k = 1`. -/
private theorem pow_two_eq_one {k : ℕ} (h : (2 : ℕ) ^ k = 2) :
    k = 1 := by
  rcases k with _ | _ | k
  · simp at h
  · rfl
  · exfalso
    have hge : (4 : ℕ) ≤ 2 ^ (k + 2) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- The five-term `Fin 5` sum expansion used in the potential split. -/
private theorem sum_five (g : Fin 5 → ℕ) :
    (∑ ρ : Fin 5, g ρ) = g 0 + (g 1 + (g 2 + (g 3 + g 4))) := by
  have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by
    ext x
    fin_cases x <;> simp
  rw [huniv]
  rw [Finset.sum_insert (by decide : (0 : Fin 5) ∉
      ({1, 2, 3, 4} : Finset (Fin 5))),
    Finset.sum_insert (by decide : (1 : Fin 5) ∉
      ({2, 3, 4} : Finset (Fin 5))),
    Finset.sum_insert (by decide : (2 : Fin 5) ∉
      ({3, 4} : Finset (Fin 5))),
    Finset.sum_insert (by decide : (3 : Fin 5) ∉
      ({4} : Finset (Fin 5))),
    Finset.sum_singleton]

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {theta : Fin 5 → ℝ} {c : Fin 6 → Plane₂} {v : Fin 6}

/-- Tail-term bound: a defect-`≥ 3` tail row contributes `≤ 2`. -/
private theorem tail_term_le_two {C : SatChart o e 4 lam c v theta}
    {ρ : Fin 5}
    (hd : 3 ≤ rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ)))) :
    2 ^ (4 - rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ)))) ≤ 2 := by
  calc 2 ^ (4 - rowDefect 4 lam
          (directionRow o e c (v.succAbove (n4σ C ρ))))
      ≤ 2 ^ (1 : ℕ) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 := by norm_num

/-- If a tail row is not defect `3` it is defect `≥ 4` and contributes
`≤ 1`. -/
private theorem tail_term_le_one_of_ne_three {C : SatChart o e 4 lam c v theta}
    {ρ : Fin 5}
    (hd : 3 ≤ rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))))
    (hne : rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))) ≠ 3) :
    2 ^ (4 - rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ)))) ≤ 1 := by
  have hge : 4 ≤ rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))) := by omega
  have h0 : (4 : ℕ) - rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))) = 0 := by omega
  rw [h0]; norm_num

/-- Equality with `2` for a tail term forces defect `3`. -/
private theorem tail_term_eq_three {C : SatChart o e 4 lam c v theta}
    {ρ : Fin 5}
    (hd : 3 ≤ rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))))
    (h2 : 2 ≤ 2 ^ (4 - rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))))) :
    rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))) = 3 := by
  have hk : 4 - rowDefect 4 lam
      (directionRow o e c (v.succAbove (n4σ C ρ))) = 1 := by
    apply pow_two_eq_one
    exact (tail_term_le_two (C := C) hd).antisymm h2
  omega

/-- **Six-centre `n = 4` over-capacity exclusion.**  A six-centre
configuration at `n = 4` with a saturated anchor, two defect-`2` rows
and all remaining rows of defect `≥ 3` cannot have potential above
`2^4 + 2^2`: the bound forces at least two of the three tail rows to
have defect exactly `3`, and the `n4cert_*` certificates contradict
every θ-class placement (the between class additionally via the
residual emission chord). -/
theorem six_centre_n4_overcap
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    {v A B : Fin 6} (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hdA : rowDefect 4 lam (directionRow o e c A) = 2)
    (hdB : rowDefect 4 lam (directionRow o e c B) = 2)
    (htail3 : ∀ w : Fin 6, w ≠ v → w ≠ A → w ≠ B →
      3 ≤ rowDefect 4 lam (directionRow o e c w))
    (hover : 2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c)) :
    False := by
  classical
  have hover0 := hover
  obtain ⟨e', he', theta, C, lo, hi, hswap, hθlt, hclass⟩ :=
    six_centre_theta_class o e he (by decide : (3 : ℕ) ≤ 4) hlam hn
      hleg hvA hvB hAB hsat hdA hdB
  have href : ∀ x : Fin 6,
      rowDefect 4 lam (directionRow o e' c x) =
        rowDefect 4 lam (directionRow o e c x) :=
    fun x => rowDefect_directionRow_reference_eq o e' e he' he c
      hleg.inj x hlam (by omega) hn
  have hdlo : rowDefect 4 lam (directionRow o e' c (v.succAbove lo)) =
      2 := by
    rcases hswap with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1, href] <;> assumption
  have hdhi : rowDefect 4 lam (directionRow o e' c (v.succAbove hi)) =
      2 := by
    rcases hswap with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2, href] <;> assumption
  have hdv' : rowDefect 4 lam (directionRow o e' c v) = 1 := by
    rw [href]; exact hsat
  have htail : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      3 ≤ rowDefect 4 lam
        (directionRow o e' c (v.succAbove z)) := by
    intro z hzlo hzhi
    rw [href]
    apply htail3 _ (Fin.succAbove_ne v z)
    · rcases hswap with ⟨hA, -⟩ | ⟨-, hA⟩
      · rw [← hA]
        exact fun h => hzlo (Fin.succAbove_right_injective h)
      · rw [← hA]
        exact fun h => hzhi (Fin.succAbove_right_injective h)
    · rcases hswap with ⟨-, hB⟩ | ⟨hB, -⟩
      · rw [← hB]
        exact fun h => hzhi (Fin.succAbove_right_injective h)
      · rw [← hB]
        exact fun h => hzlo (Fin.succAbove_right_injective h)
  have hcell : ∀ x : Fin 6, rowCells lam (directionRow o e' c x) ≤ 4 :=
    fun x => rowCells_directionRow_le_of_floor_eq o e' c C.hlam x
      (by omega) C.hn
  have hsc : ∀ x : Fin 6, exponentAt lam (directionRows o e' c) x =
      4 - rowDefect 4 lam (directionRow o e' c x) :=
    fun x => rowScore_eq_sub_defect lam C.hlam 4 _ (hcell x)
  have hpot : potential lam (directionRows o e' c) =
      2 ^ (4 - rowDefect 4 lam (directionRow o e' c v)) +
        ∑ ρ : Fin 5, 2 ^ (4 - rowDefect 4 lam
          (directionRow o e' c (v.succAbove (n4σ C ρ)))) := by
    rw [potential_eq_exponent_sum, Fin.sum_univ_succAbove _ v]
    congr 1
    · exact congrArg (2 ^ ·) (hsc v)
    · have hF : ∀ i : Fin 5,
          2 ^ exponentAt lam (directionRows o e' c) (v.succAbove i) =
            2 ^ (4 - rowDefect 4 lam
              (directionRow o e' c (v.succAbove i))) :=
        fun i => congrArg (2 ^ ·) (hsc _)
      rw [Finset.sum_congr rfl (fun i _ => hF i)]
      exact (Equiv.sum_comp
        (Equiv.ofBijective (n4σ C) (n4σ_bijective C))
        (fun i : Fin 5 => 2 ^ (4 - rowDefect 4 lam
          (directionRow o e' c (v.succAbove i))))).symm
  have hpoteq : potential lam (directionRows o e' c) =
      potential lam (directionRows o e c) :=
    potential_directionRows_reference_eq o e' e he' he c hleg.inj lam
  rw [← hpoteq, hpot, hdv'] at hover
  rw [sum_five] at hover
  norm_num at hover
  rcases hclass with hbelow | hbetween | habove
  · -- all-below: `lo`, `hi` occupy ranks `3`, `4`; tails at `0, 1, 2`.
    obtain ⟨hσ3, hσ4⟩ := n4σ_three_four_of_all_below C hθlt hbelow
    have hdT : ∀ ρ : Fin 5, ρ ≠ 3 → ρ ≠ 4 →
        3 ≤ rowDefect 4 lam
          (directionRow o e' c (v.succAbove (n4σ C ρ))) := by
      intro ρ h3 h4
      exact htail _ (fun h => h3 (n4σ_injective C (h.trans hσ3.symm)))
        (fun h => h4 (n4σ_injective C (h.trans hσ4.symm)))
    have hd3' : rowDefect 4 lam (directionRow o e' c
        (v.succAbove (n4σ C 3))) = 2 := by rw [hσ3]; exact hdlo
    have hd4' : rowDefect 4 lam (directionRow o e' c
        (v.succAbove (n4σ C 4))) = 2 := by rw [hσ4]; exact hdhi
    rw [hd3', hd4'] at hover
    norm_num at hover
    by_cases h1d3 : rowDefect 4 lam (directionRow o e' c
        (v.succAbove (n4σ C 1))) = 3
    · -- rank `1` is defect-`3`: `pair_B` on rows `1, 3`.
      obtain ⟨x10, x11, x12, x13, ho1, hs1, hp1⟩ :=
        n4_row1_exists C rfl h1d3
      obtain ⟨x30, x31, x32, x33, ho3, hs3, hp3⟩ :=
        n4_row2_exists C hσ3 hdlo
      have hp1' : List.Perm [x10, x11, x12, x13]
          [(n4model C).d 0 1, (n4model C).d 1 2, (n4model C).d 1 3,
           (n4model C).d 1 4] := n4_row_perm C hp1
      have hp3' : List.Perm [x30, x31, x32, x33]
          [(n4model C).d 0 3, (n4model C).d 1 3, (n4model C).d 2 3,
           (n4model C).d 3 4] := n4_row_perm C hp3
      exact R2N4.n4cert_pair_B (n4model C) ho1 hs1 hp1' ho3 hs3 hp3'
    · -- rank `1` is defect-`≥ 4`: over-capacity then forces ranks
      -- `0, 2` defect-`3`; `triple_B` on rows `0, 2, 3`.
      have hle1 := tail_term_le_one_of_ne_three (C := C)
        (hdT 1 (by decide) (by decide)) h1d3
      have hle0 := tail_term_le_two (C := C)
        (hdT 0 (by decide) (by decide))
      have hle2 := tail_term_le_two (C := C)
        (hdT 2 (by decide) (by decide))
      have hge0 : 2 ≤ 2 ^ (4 - rowDefect 4 lam
          (directionRow o e' c (v.succAbove (n4σ C 0)))) := by omega
      have hge2 : 2 ≤ 2 ^ (4 - rowDefect 4 lam
          (directionRow o e' c (v.succAbove (n4σ C 2)))) := by omega
      have hd0 := tail_term_eq_three (C := C)
        (hdT 0 (by decide) (by decide)) hge0
      have hd2 := tail_term_eq_three (C := C)
        (hdT 2 (by decide) (by decide)) hge2
      obtain ⟨x00, x01, x02, x03, ho0, hs0, hp0⟩ :=
        n4_row1_exists C rfl hd0
      obtain ⟨x20, x21, x22, x23, ho2, hs2, hp2⟩ :=
        n4_row1_exists C rfl hd2
      obtain ⟨x30, x31, x32, x33, ho3, hs3, hp3⟩ :=
        n4_row2_exists C hσ3 hdlo
      have hp0' : List.Perm [x00, x01, x02, x03]
          [(n4model C).d 0 1, (n4model C).d 0 2, (n4model C).d 0 3,
           (n4model C).d 0 4] := n4_row_perm C hp0
      have hp2' : List.Perm [x20, x21, x22, x23]
          [(n4model C).d 0 2, (n4model C).d 1 2, (n4model C).d 2 3,
           (n4model C).d 2 4] := n4_row_perm C hp2
      have hp3' : List.Perm [x30, x31, x32, x33]
          [(n4model C).d 0 3, (n4model C).d 1 3, (n4model C).d 2 3,
           (n4model C).d 3 4] := n4_row_perm C hp3
      exact R2N4.n4cert_triple_B (n4model C) ho0 hs0 hp0' ho2 hs2 hp2'
        ho3 hs3 hp3'
  · -- between: `lo`, `hi` occupy ranks `0`, `4`; `pair04_em`.
    obtain ⟨hσ0, hσ4⟩ := n4σ_zero_four_of_between C hθlt hbetween
    have hge2' : ∀ r : Fin 5, 2 ≤ rowDefect 4 lam
        (directionRow o e' c (v.succAbove r)) := by
      intro r
      rcases eq_or_ne r lo with rfl | h1
      · omega
      · rcases eq_or_ne r hi with rfl | h2
        · omega
        · have := htail r h1 h2; omega
    have honly' : ∀ r : Fin 5, rowDefect 4 lam
        (directionRow o e' c (v.succAbove r)) = 2 →
        r = lo ∨ r = hi := by
      intro r hr
      rcases eq_or_ne r lo with rfl | h1
      · exact Or.inl rfl
      · rcases eq_or_ne r hi with rfl | h2
        · exact Or.inr rfl
        · exfalso; have := htail r h1 h2; omega
    have hover' : 2 ^ 4 + 2 ^ 2 <
        potential lam (directionRows o e' c) := by
      rw [hpoteq]; exact hover0
    obtain ⟨r, w, hrab, hwa, hwb, hwr, hdw3, hemi⟩ :=
      r2_residual_tail_emission o e' he' (by decide : (3 : ℕ) ≤ 5)
        (by decide : (3 : ℕ) ≤ 4) C.hlam
        C.hn C.hleg v C.htheta hdv' hge2' hθlt hdlo hdhi honly' hover'
    obtain ⟨ρw, hρw⟩ := (n4σ_bijective C).surjective w
    have hρ0 : ρw ≠ 0 := by
      intro h
      apply hwa
      calc w = n4σ C ρw := hρw.symm
        _ = n4σ C 0 := by rw [h]
        _ = lo := hσ0
    have hρ4 : ρw ≠ 4 := by
      intro h
      apply hwb
      calc w = n4σ C ρw := hρw.symm
        _ = n4σ C 4 := by rw [h]
        _ = hi := hσ4
    have hρ : ρw = 1 ∨ ρw = 2 ∨ ρw = 3 := by
      fin_cases ρw
      · exact absurd rfl hρ0
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd rfl hρ4
    have h0lt : (0 : Fin 5) < ρw := by
      rw [Fin.lt_def]
      exact Nat.pos_of_ne_zero
        (fun h => hρ0 (Fin.ext (b := (0 : Fin 5)) h))
    have hρlt4 : ρw < 4 := by
      rw [Fin.lt_def]
      have h5 := ρw.isLt
      have hv : ρw.val ≠ 4 := fun h => hρ4 (Fin.ext (b := (4 : Fin 5)) h)
      omega
    have hem :
        ((n4model C).t 0 + (n4model C).p - (n4model C).lam <
          (n4model C).d 0 1) ∨
        ((n4model C).t 0 + (n4model C).p - (n4model C).lam <
          (n4model C).d 0 2) ∨
        ((n4model C).t 0 + (n4model C).p - (n4model C).lam <
          (n4model C).d 0 3) ∨
        ((n4model C).d 1 4 < (n4model C).t 4 + (n4model C).lam) ∨
        ((n4model C).d 2 4 < (n4model C).t 4 + (n4model C).lam) ∨
        ((n4model C).d 3 4 < (n4model C).t 4 + (n4model C).lam) := by
      rcases hrab with rfl | rfl
      · -- emitter `r = lo` (rank `0`): only the upper-end strip is
        -- geometrically possible.
        have hdir : dirRep o e' (c ∘ v.succAbove) lo w =
            (n4model C).d 0 ρw := by
          rw [← hσ0, ← hρw]
          exact (n4model_d C 0 ρw).symm
        have htl : theta lo = (n4model C).t 0 := by
          rw [← hσ0]; exact n4σ_spec C 0
        rw [hdir, htl] at hemi
        rcases hemi with hlow | hhigh
        · exfalso
          obtain ⟨hc1, -⟩ := (n4model C).hcor 0 ρw h0lt
          rw [n4model_lam C] at hc1
          linarith
        · have hh : (n4model C).t 0 + (n4model C).p -
              (n4model C).lam < (n4model C).d 0 ρw := by
            rw [n4model_p C, n4model_lam C]; linarith
          rcases hρ with rfl | rfl | rfl
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
          · exact Or.inr (Or.inr (Or.inl hh))
      · -- emitter `r = hi` (rank `4`): only the lower-end strip.
        have hcomm : dirRep o e' (c ∘ v.succAbove) hi w =
            dirRep o e' (c ∘ v.succAbove) w hi :=
          phi_comm C hwb.symm
        have hdir : dirRep o e' (c ∘ v.succAbove) w hi =
            (n4model C).d ρw 4 := by
          rw [← hρw, ← hσ4]
          exact (n4model_d C ρw 4).symm
        have htl : theta hi = (n4model C).t 4 := by
          rw [← hσ4]; exact n4σ_spec C 4
        rw [hcomm, hdir, htl] at hemi
        rcases hemi with hlow | hhigh
        · have hll : (n4model C).d ρw 4 < (n4model C).t 4 +
              (n4model C).lam := by
            rw [n4model_lam C]; linarith
          rcases hρ with rfl | rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl hll)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hll))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hll))))
        · exfalso
          obtain ⟨-, hc2⟩ := (n4model C).hcor ρw 4 hρlt4
          rw [n4model_p C, n4model_lam C] at hc2
          linarith
    obtain ⟨x00, x01, x02, x03, ho0, hs0, hp0⟩ :=
      n4_row2_exists C hσ0 hdlo
    obtain ⟨x40, x41, x42, x43, ho4, hs4, hp4⟩ :=
      n4_row2_exists C hσ4 hdhi
    have hp0' : List.Perm [x00, x01, x02, x03]
        [(n4model C).d 0 1, (n4model C).d 0 2, (n4model C).d 0 3,
         (n4model C).d 0 4] := n4_row_perm C hp0
    have hp4' : List.Perm [x40, x41, x42, x43]
        [(n4model C).d 0 4, (n4model C).d 1 4, (n4model C).d 2 4,
         (n4model C).d 3 4] := n4_row_perm C hp4
    exact R2N4.n4cert_pair04_em (n4model C) ho0 hs0 hp0' ho4 hs4 hp4'
      hem
  · -- all-above: `lo`, `hi` occupy ranks `0`, `1`; tails at `2, 3, 4`.
    obtain ⟨hσ0, hσ1⟩ := n4σ_zero_one_of_all_above C hθlt habove
    have hdT : ∀ ρ : Fin 5, ρ ≠ 0 → ρ ≠ 1 →
        3 ≤ rowDefect 4 lam
          (directionRow o e' c (v.succAbove (n4σ C ρ))) := by
      intro ρ h0 h1
      exact htail _ (fun h => h0 (n4σ_injective C (h.trans hσ0.symm)))
        (fun h => h1 (n4σ_injective C (h.trans hσ1.symm)))
    have hd0' : rowDefect 4 lam (directionRow o e' c
        (v.succAbove (n4σ C 0))) = 2 := by rw [hσ0]; exact hdlo
    have hd1' : rowDefect 4 lam (directionRow o e' c
        (v.succAbove (n4σ C 1))) = 2 := by rw [hσ1]; exact hdhi
    rw [hd0', hd1'] at hover
    norm_num at hover
    by_cases h3d3 : rowDefect 4 lam (directionRow o e' c
        (v.succAbove (n4σ C 3))) = 3
    · -- rank `3` is defect-`3`: `pair_A` on rows `1, 3`.
      obtain ⟨x10, x11, x12, x13, ho1, hs1, hp1⟩ :=
        n4_row2_exists C hσ1 hdhi
      obtain ⟨x30, x31, x32, x33, ho3, hs3, hp3⟩ :=
        n4_row1_exists C rfl h3d3
      have hp1' : List.Perm [x10, x11, x12, x13]
          [(n4model C).d 0 1, (n4model C).d 1 2, (n4model C).d 1 3,
           (n4model C).d 1 4] := n4_row_perm C hp1
      have hp3' : List.Perm [x30, x31, x32, x33]
          [(n4model C).d 0 3, (n4model C).d 1 3, (n4model C).d 2 3,
           (n4model C).d 3 4] := n4_row_perm C hp3
      exact R2N4.n4cert_pair_A (n4model C) ho1 hs1 hp1' ho3 hs3 hp3'
    · -- rank `3` is defect-`≥ 4`: over-capacity then forces ranks
      -- `2, 4` defect-`3`; `triple_A` on rows `1, 2, 4`.
      have hle3 := tail_term_le_one_of_ne_three (C := C)
        (hdT 3 (by decide) (by decide)) h3d3
      have hle2 := tail_term_le_two (C := C)
        (hdT 2 (by decide) (by decide))
      have hle4 := tail_term_le_two (C := C)
        (hdT 4 (by decide) (by decide))
      have hge2 : 2 ≤ 2 ^ (4 - rowDefect 4 lam
          (directionRow o e' c (v.succAbove (n4σ C 2)))) := by omega
      have hge4 : 2 ≤ 2 ^ (4 - rowDefect 4 lam
          (directionRow o e' c (v.succAbove (n4σ C 4)))) := by omega
      have hd2 := tail_term_eq_three (C := C)
        (hdT 2 (by decide) (by decide)) hge2
      have hd4 := tail_term_eq_three (C := C)
        (hdT 4 (by decide) (by decide)) hge4
      obtain ⟨x10, x11, x12, x13, ho1, hs1, hp1⟩ :=
        n4_row2_exists C hσ1 hdhi
      obtain ⟨x20, x21, x22, x23, ho2, hs2, hp2⟩ :=
        n4_row1_exists C rfl hd2
      obtain ⟨x40, x41, x42, x43, ho4, hs4, hp4⟩ :=
        n4_row1_exists C rfl hd4
      have hp1' : List.Perm [x10, x11, x12, x13]
          [(n4model C).d 0 1, (n4model C).d 1 2, (n4model C).d 1 3,
           (n4model C).d 1 4] := n4_row_perm C hp1
      have hp2' : List.Perm [x20, x21, x22, x23]
          [(n4model C).d 0 2, (n4model C).d 1 2, (n4model C).d 2 3,
           (n4model C).d 2 4] := n4_row_perm C hp2
      have hp4' : List.Perm [x40, x41, x42, x43]
          [(n4model C).d 0 4, (n4model C).d 1 4, (n4model C).d 2 4,
           (n4model C).d 3 4] := n4_row_perm C hp4
      exact R2N4.n4cert_triple_A (n4model C) ho1 hs1 hp1' ho2 hs2 hp2'
        ho4 hs4 hp4'

end N4Terminal

#print axioms six_centre_n4_overcap

end Jsp404
