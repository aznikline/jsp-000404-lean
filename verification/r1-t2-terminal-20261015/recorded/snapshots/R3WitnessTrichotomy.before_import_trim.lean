import Jsp000404.R3WitnessBounds

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section R3Dag

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}
  (C : SatChart o e n lam c v theta)
include C

/-- **Defect-2 fan trichotomy — forced first inner gap.**  For a sorted
row `A < B < D` with fan cut `theta a`, if the first inner gap is big
(`lam ≤ B − A`, supplied as `1 ≤ ⌊(B−A)/λ⌋₊`), the row's big-gap pattern
is one of `{0,1}`, `{1}`, `{1,3}`: every pattern containing `2`, the
triple `{0,1,3}`, or all four gaps overflows the defect equation
against the corridors (`A ≥ tl + lam`, `D ≤ π − lam + th`,
`tl < theta a < th ≤ β`). -/
theorem r3_fan_trich_lo {a p q r : Fin 4} {A B D tl th : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk1 : 1 ≤ ⌊(B - A) / lam⌋₊)
    (hAlo : tl + lam ≤ A) (hDhi : D ≤ Real.pi - lam + th)
    (htlt : tl < theta a) (htt : theta a < th)
    (htl0 : 0 ≤ tl) (htaβ : theta a ≤ Real.pi - n * lam)
    (hthβ : th ≤ Real.pi - n * lam) :
    (⌊(A - theta a) / lam⌋₊ + ⌊(B - A) / lam⌋₊ = n ∧ 1 ≤ ⌊(A - theta a) / lam⌋₊ ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(B - A) / lam⌋₊ = n - 1 ∧ ⌊(A - theta a) / lam⌋₊ = 0 ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(B - A) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  by_cases h2 : 1 ≤ f2
  · -- `f2` big: every pattern containing index `2` dies.
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,2,3}: Σf = n+2 → π ≥ (n+2)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {0,1,2}: D − ta ≥ (n+1)·lam but D < π < (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (D - B) := by
          have h : (f0:ℝ) + f1 + f2 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2]
        have hDlt : D < Real.pi := by linarith [hthβ, hβ]
        linarith [hFl, hDlt, hta0, hπ]
    · by_cases h3 : 1 ≤ f3
      · -- {1,2,3}: ta + π − A ≥ (n+1)·lam → A ≤ ta + β − λ < tl + λ
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f1:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2, e3]
        linarith [hFl, hAlo, htlt, htaβ, hβ]
      · -- {1,2}: D − A ≥ n·lam vs corridor bound (n−2)·lam + 2β
        exfalso
        have hFl : (n:ℝ) * lam ≤ (B - A) + (D - B) := by
          have h : (f1:ℝ) + f2 = n := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2]
        linarith [hFl, hAlo, hDhi, hthβ, htl0, hβ]
  · push_neg at h2
    have hf2z : f2 = 0 := Nat.lt_one_iff.mp h2
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,3}: π + B − D ≥ (n+1)·lam → B > D, contradicting sort
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e3]
        linarith [hFl, hord.2, hπ]
      · -- {0,1}: surviving family
        exact Or.inl ⟨by omega, h0, hf2z, by omega⟩
    · by_cases h3 : 1 ≤ f3
      · -- {1,3}: surviving family
        refine Or.inr (Or.inr ⟨by omega, by omega, hf2z, h3⟩)
      · -- {1}: f1 = n − 1
        exact Or.inr (Or.inl ⟨by omega, by omega, hf2z, by omega⟩)

/-- **Defect-2 fan trichotomy — forced last inner gap (mirror of
`r3_fan_trich_lo`).**  With `lam ≤ D − B` the big-gap pattern is one of
`{2}`, `{0,2}`, `{2,3}`. -/
theorem r3_fan_trich_hi {a p q r : Fin 4} {A B D tl th : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk2 : 1 ≤ ⌊(D - B) / lam⌋₊)
    (hAlo : tl + lam ≤ A) (hDhi : D ≤ Real.pi - lam + th)
    (htlt : tl < theta a) (htt : theta a < th)
    (htl0 : 0 ≤ tl) (htaβ : theta a ≤ Real.pi - n * lam)
    (hthβ : th ≤ Real.pi - n * lam) :
    (⌊(D - B) / lam⌋₊ = n - 1 ∧ ⌊(A - theta a) / lam⌋₊ = 0 ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(D - B) / lam⌋₊ = n ∧
        1 ≤ ⌊(A - theta a) / lam⌋₊ ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(D - B) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  by_cases h1 : 1 ≤ f1
  · -- `f1` big: every pattern containing index `1` dies.
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,2,3}: π ≥ (n+2)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {0,1,2}: D − ta ≥ (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (D - B) := by
          have h : (f0:ℝ) + f1 + f2 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2]
        have hDlt : D < Real.pi := by linarith [hthβ, hβ]
        linarith [hFl, hDlt, hta0, hπ]
    · by_cases h3 : 1 ≤ f3
      · -- {1,2,3}: ta + π − A ≥ (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f1:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2, e3]
        linarith [hFl, hAlo, htlt, htaβ, hβ]
      · -- {1,2}: D − A ≥ n·lam
        exfalso
        have hFl : (n:ℝ) * lam ≤ (B - A) + (D - B) := by
          have h : (f1:ℝ) + f2 = n := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2]
        linarith [hFl, hAlo, hDhi, hthβ, htl0, hβ]
  · push_neg at h1
    have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,2,3}: π + A − B ≥ (n+1)·lam → A > B
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e2, e3]
        linarith [hFl, hord.1, hπ]
      · -- {0,2}: surviving family
        exact Or.inr (Or.inl ⟨by omega, h0, hf1z, by omega⟩)
    · by_cases h3 : 1 ≤ f3
      · -- {2,3}: surviving family
        exact Or.inr (Or.inr ⟨by omega, by omega, hf1z, h3⟩)
      · -- {2}: f2 = n − 1
        exact Or.inl ⟨by omega, by omega, hf1z, by omega⟩

/-- **Defect-2 fan tetratomy — all-up row (forced first gap).**  When
every target lies above `theta a`, the first gap is always big
(`A ≥ theta a + lam`).  The big-gap pattern is one of `{0}`, `{0,1}`,
`{0,2}`, `{0,3}`; every pattern with three or more big gaps overflows.
Only ordering facts and `lam ≤ A`, `D < π`, `theta a ≤ β` are needed. -/
theorem r3_fan_trich_t3 {a p q r : Fin 4} {A B D : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk0 : 1 ≤ ⌊(A - theta a) / lam⌋₊)
    (hAl : lam ≤ A) (hDl : D < Real.pi)
    (htaβ : theta a ≤ Real.pi - n * lam) :
    (⌊(A - theta a) / lam⌋₊ = n - 1 ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(B - A) / lam⌋₊ = n ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(B - A) / lam⌋₊) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(D - B) / lam⌋₊ = n ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(D - B) / lam⌋₊) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  -- every pattern with ≥3 big gaps dies; `f0` is always big.
  by_cases h1 : 1 ≤ f1
  · by_cases h2 : 1 ≤ f2
    · by_cases h3 : 1 ≤ f3
      · exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {0,1,2}: D − ta ≥ (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (D - B) := by
          have h : (f0:ℝ) + f1 + f2 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2]
        linarith [hFl, hDl, hta0, hπ]
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,3}: B + π − D ≥ (n+1)·lam → B > D
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e3]
        linarith [hFl, hord.2, hπ]
      · -- {0,1}
        exact Or.inr (Or.inl ⟨by omega, by omega, by omega, h1⟩)
  · push_neg at h1
    have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
    by_cases h2 : 1 ≤ f2
    · by_cases h3 : 1 ≤ f3
      · -- {0,2,3}: A + π − B ≥ (n+1)·lam → A > B
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e2, e3]
        linarith [hFl, hord.1, hπ]
      · -- {0,2}
        exact Or.inr (Or.inr (Or.inl ⟨by omega, hf1z, by omega, h2⟩))
    · push_neg at h2
      have hf2z : f2 = 0 := Nat.lt_one_iff.mp h2
      by_cases h3 : 1 ≤ f3
      · -- {0,3}
        exact Or.inr (Or.inr (Or.inr ⟨by omega, hf1z, hf2z, h3⟩))
      · -- {0}: f0 = n − 1
        exact Or.inl ⟨by omega, hf1z, hf2z, by omega⟩

/-- **Defect-2 fan tetratomy — all-down row (forced last gap).**  Mirror
of `r3_fan_trich_t3`: the last gap is always big; the big-gap pattern is
one of `{3}`, `{0,3}`, `{1,3}`, `{2,3}`. -/
theorem r3_fan_trich_t4 {a p q r : Fin 4} {A B D : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk3 : 1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊)
    (hAl : lam ≤ A) (hDl : D < Real.pi)
    (htaβ : theta a ≤ Real.pi - n * lam) :
    (⌊(theta a + Real.pi - D) / lam⌋₊ = n - 1 ∧ ⌊(A - theta a) / lam⌋₊ = 0 ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(A - theta a) / lam⌋₊) ∨
      (⌊(B - A) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(B - A) / lam⌋₊) ∨
      (⌊(D - B) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(D - B) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  by_cases h2 : 1 ≤ f2
  · by_cases h1 : 1 ≤ f1
    · by_cases h0 : 1 ≤ f0
      · -- {0,1,2,3}
        exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {1,2,3}: ta + π − A ≥ (n+1)·lam → A < lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f1:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2, e3]
        linarith [hFl, hAl, htaβ, hβ]
    · push_neg at h1
      have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
      by_cases h0 : 1 ≤ f0
      · -- {0,2,3}: A + π − B ≥ (n+1)·lam → A > B
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e2, e3]
        linarith [hFl, hord.1, hπ]
      · -- {2,3}
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hf1z, h2⟩))
  · push_neg at h2
    have hf2z : f2 = 0 := Nat.lt_one_iff.mp h2
    by_cases h1 : 1 ≤ f1
    · by_cases h0 : 1 ≤ f0
      · -- {0,1,3}: B + π − D ≥ (n+1)·lam → B > D
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e3]
        linarith [hFl, hord.2, hπ]
      · -- {1,3}
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, hf2z, h1⟩))
    · push_neg at h1
      have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
      by_cases h0 : 1 ≤ f0
      · -- {0,3}
        exact Or.inr (Or.inl ⟨by omega, hf1z, hf2z, h0⟩)
      · -- {3}: f3 = n − 1
        exact Or.inl ⟨by omega, by omega, hf1z, hf2z⟩

end R3Dag

end Jsp404
