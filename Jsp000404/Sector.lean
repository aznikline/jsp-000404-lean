import Jsp000404.GC
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Double sectors and directions (Sendov §3, Lemma 3.2)

Directions are `Real.Angle`s (`ℝ/2Real.piℤ`). The direction of a segment `pq` is
`o.oangle e (q - p)` for a fixed reference vector `e`. A *double sector*
`T(θ, lam)` is the union of the two opposite arcs of radius `lam/2` about `θ`
and `θ + Real.pi`.

**Lemma 3.2**: if `D(pq)` and `D(qr)` lie in the same part of `T(θ, lam)`,
then `∠ p q r > Real.pi - lam`.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- Circular distance between two angles, in `[0, Real.pi]`. -/
noncomputable def angDist (φ ψ : Real.Angle) : ℝ := |(φ - ψ).toReal|

/-- The oriented direction of the vector `p → q`, measured from `e`. -/
noncomputable def dirV (o : Orientation ℝ Plane₂ (Fin 2)) (e p q : Plane₂) :
    Real.Angle :=
  o.oangle e (q - p)

/-- `φ` lies in the double sector `T(θ, lam)`: within `lam/2` of `θ` or `θ + Real.pi`. -/
def inDoubleSector (θ : Real.Angle) (lam : ℝ) (φ : Real.Angle) : Prop :=
  angDist φ θ < lam / 2 ∨ angDist φ (θ + Real.pi) < lam / 2

/-- `Real.pi = -Real.pi` as a real angle, since `2Real.pi = 0` in `ℝ/2Real.piℤ`. -/
lemma pi_eq_neg_pi : (Real.pi : Real.Angle) = -Real.pi :=
  eq_neg_of_add_eq_zero_left Real.Angle.coe_pi_add_coe_pi

/-- The angle-difference core of Lemma 3.2: two directions within `lam/2` of
two antipodal centers differ by more than `Real.pi - lam` (as an unoriented angle). -/
lemma angDist_antipodal {φ₁ φ₂ θ : Real.Angle} {lam : ℝ} (hlam : lam < Real.pi)
    (h1 : angDist φ₁ (θ + Real.pi) < lam / 2) (h2 : angDist φ₂ θ < lam / 2) :
    |(φ₂ - φ₁).toReal| > Real.pi - lam := by
  set ε₁ := (φ₁ - (θ + Real.pi)).toReal with hε₁def
  set ε₂ := (φ₂ - θ).toReal with hε₂def
  have hε1 : |ε₁| < lam / 2 := h1
  have hε2 : |ε₂| < lam / 2 := h2
  have hε : |ε₂ - ε₁| < lam := by
    have := abs_sub ε₂ ε₁
    have h1' := abs_lt.1 hε1
    have h2' := abs_lt.1 hε2
    exact lt_of_le_of_lt this (by linarith)
  -- φ₂ - φ₁ = ↑(ε₂ - ε₁ - Real.pi) as real angles
  have hdiff : φ₂ - φ₁ = ((ε₂ - ε₁ - Real.pi : ℝ) : Real.Angle) := by
    have e1 : φ₂ - θ = ((ε₂ : ℝ) : Real.Angle) := by
      rw [hε₂def, Real.Angle.coe_toReal]
    have e2 : φ₁ - (θ + Real.pi) = ((ε₁ : ℝ) : Real.Angle) := by
      rw [hε₁def, Real.Angle.coe_toReal]
    have hsub : φ₂ - φ₁ = (φ₂ - θ) - (φ₁ - (θ + Real.pi)) - Real.pi := by abel
    rw [hsub, e1, e2, ← Real.Angle.coe_sub, ← Real.Angle.coe_sub]
  rw [hdiff, Real.Angle.toReal_coe]
  by_cases hv : ε₂ - ε₁ ≤ 0
  · -- ε₂-ε₁-Real.pi ≤ -Real.pi: shift up by one period 2Real.pi
    have hmem : ε₂ - ε₁ + Real.pi ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      have h' := abs_lt.1 hε
      refine ⟨by linarith, by linarith⟩
    have hto : toIocMod Real.two_pi_pos (-Real.pi) (ε₂ - ε₁ - Real.pi) = ε₂ - ε₁ + Real.pi := by
      have hshift : toIocMod Real.two_pi_pos (-Real.pi) (ε₂ - ε₁ - Real.pi) =
          toIocMod Real.two_pi_pos (-Real.pi) (ε₂ - ε₁ - Real.pi + (1 : ℤ) • (2 * Real.pi)) := by
        rw [toIocMod_add_zsmul]
      rw [hshift]
      rw [show ε₂ - ε₁ - Real.pi + (1 : ℤ) • (2 * Real.pi) = ε₂ - ε₁ + Real.pi by simp; ring]
      exact (toIocMod_eq_self Real.two_pi_pos).mpr hmem
    rw [hto, abs_of_pos (by have := abs_lt.1 hε; linarith)]
    have := abs_lt.1 hε
    linarith
  · -- -Real.pi < ε₂-ε₁-Real.pi < 0: toIocMod fixes it
    have hv := lt_of_not_ge hv
    have hmem : ε₂ - ε₁ - Real.pi ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      have h' := abs_lt.1 hε
      refine ⟨by linarith, by linarith⟩
    rw [(toIocMod_eq_self Real.two_pi_pos).mpr hmem,
      abs_of_neg (by have := abs_lt.1 hε; linarith)]
    have := abs_lt.1 hε
    linarith

/-- **Lemma 3.2** (Sendov). If `D(pq)` and `D(qr)` lie in the same part of
the double sector `T(θ, lam)`, then `∠ p q r > Real.pi - lam`. -/
theorem lemma_3_2 {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    (he : e ≠ 0) (θ : Real.Angle) {lam : ℝ} (hlpi : lam < Real.pi)
    {p q r : Plane₂} (hpq : p ≠ q) (hrq : r ≠ q)
    (hsame : (angDist (dirV o e p q) θ < lam / 2 ∧ angDist (dirV o e q r) θ < lam / 2) ∨
             (angDist (dirV o e p q) (θ + Real.pi) < lam / 2 ∧
              angDist (dirV o e q r) (θ + Real.pi) < lam / 2)) :
    ∠ p q r > Real.pi - lam := by
  have hpq' : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hrq' : r - q ≠ 0 := sub_ne_zero.mpr hrq
  -- ∠ p q r = |oangle (p-q) (r-q)|.toReal
  have hangle : ∠ p q r = |(o.oangle (p - q) (r - q)).toReal| := by
    show InnerProductGeometry.angle (p -ᵥ q) (r -ᵥ q) = _
    rw [vsub_eq_sub, vsub_eq_sub]
    exact o.angle_eq_abs_oangle_toReal hpq' hrq'
  -- oangle (p-q)(r-q) = oangle e (r-q) - oangle e (p-q)
  have hsub : o.oangle (p - q) (r - q) =
      o.oangle e (r - q) - o.oangle e (p - q) := by
    rw [o.oangle_sub_left he hpq' hrq']
  -- oangle e (p - q) = dirV p q + Real.pi
  have hflipp : o.oangle e (p - q) = dirV o e p q + Real.pi := by
    have : p - q = -(q - p) := by abel
    rw [this, o.oangle_neg_right he (sub_ne_zero.mpr (Ne.symm hpq))]
    rfl
  -- oangle e (r - q) = dirV q r
  have hdirr : o.oangle e (r - q) = dirV o e q r := rfl
  rw [hangle, hsub, hdirr, hflipp]
  rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- both directions near θ: dirV p q + Real.pi is near θ + Real.pi, dirV q r near θ
    have hdist : angDist (dirV o e p q + Real.pi) (θ + Real.pi) < lam / 2 := by
      show |(dirV o e p q + Real.pi - (θ + Real.pi)).toReal| < lam / 2
      have : dirV o e p q + Real.pi - (θ + Real.pi) = dirV o e p q - θ := by abel
      rw [this]; exact h1
    exact angDist_antipodal hlpi hdist h2
  · -- both directions near θ + Real.pi: dirV p q + Real.pi is near θ, dirV q r near θ + Real.pi
    have hflip : dirV o e p q + Real.pi - θ = dirV o e p q - (θ + Real.pi) := by
      calc dirV o e p q + Real.pi - θ = dirV o e p q - θ + Real.pi := by abel
        _ = dirV o e p q - θ + -Real.pi := by nth_rw 1 [pi_eq_neg_pi]
        _ = dirV o e p q - θ - Real.pi := by rw [← sub_eq_add_neg]
        _ = dirV o e p q - (θ + Real.pi) := by rw [sub_add_eq_sub_sub]
    have hdist : angDist (dirV o e p q + Real.pi) θ < lam / 2 := by
      show |(dirV o e p q + Real.pi - θ).toReal| < lam / 2
      rw [hflip]; exact h1
    have := angDist_antipodal hlpi h2 hdist
    rw [show dirV o e q r - (dirV o e p q + Real.pi) = -((dirV o e p q + Real.pi) - dirV o e q r)
        by abel, Real.Angle.abs_toReal_neg]
    exact this

end Jsp404
