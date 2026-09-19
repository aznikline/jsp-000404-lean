import Jsp000404.Sector

/-!
# One-sided double sectors and the gap-covering core of Lemma 3.7

Sendov's `T(θ, λ)` is a *one-sided* double sector: directions in `[θ, θ+λ)`
plus the antipodal copy. This convention makes the sector-per-gap count
`⌊uψ/2⌋ - 1` of Lemma 3.7 exact.

The covering core: directions in a gap `(a, b)` of the projective circle
that keep a margin `2w` from both endpoints lie in
`[a + 2w, a + (2t+2)w)`, the union of `t` adjacent wings of width `2w`.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- Direction `φ` lies in the one-sided double sector `T(θ, lam)`:
`(φ - θ).toReal ∈ [0, lam)` or `(φ - θ - π).toReal ∈ [0, lam)`. -/
def inSectorOS (θ : Real.Angle) (lam : ℝ) (φ : Real.Angle) : Prop :=
  (φ - θ).toReal ∈ Set.Ico 0 lam ∨ (φ - θ - Real.pi).toReal ∈ Set.Ico 0 lam

/-- Which part of the double sector contains `φ` (`true` = base part). -/
noncomputable def partOS (θ : Real.Angle) (lam : ℝ) (φ : Real.Angle) : Bool :=
  decide ((φ - θ).toReal ∈ Set.Ico 0 lam)

/-- The angle core of Lemma 3.2 in one-sided form: two directions in the
same wing of width `lam < π` force an angle `> π - lam`. -/
lemma angle_gt_of_same_wing {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    (he : e ≠ 0) {θ : Real.Angle} {lam : ℝ} (hlam : lam < Real.pi)
    {u₁ u₂ : Plane₂} (hu1 : u₁ ≠ 0) (hu2 : u₂ ≠ 0)
    (h1 : (o.oangle e u₁ - θ).toReal ∈ Set.Ico 0 lam)
    (h2 : (o.oangle e u₂ - θ).toReal ∈ Set.Ico 0 lam) :
    InnerProductGeometry.angle (-u₁) u₂ > Real.pi - lam := by
  have hu1' : -u₁ ≠ 0 := neg_ne_zero.mpr hu1
  have hangle : InnerProductGeometry.angle (-u₁) u₂ =
      |(o.oangle (-u₁) u₂).toReal| :=
    o.angle_eq_abs_oangle_toReal hu1' hu2
  have hsub : o.oangle (-u₁) u₂ = o.oangle e u₂ - o.oangle e (-u₁) :=
    (o.oangle_sub_left he hu1' hu2).symm
  have hflip : o.oangle e (-u₁) = o.oangle e u₁ + Real.pi :=
    o.oangle_neg_right he hu1
  rw [hangle, hsub, hflip]
  set s₁ := (o.oangle e u₁ - θ).toReal with hs₁
  set s₂ := (o.oangle e u₂ - θ).toReal with hs₂
  obtain ⟨hs₁0, hs₁l⟩ := h1
  obtain ⟨hs₂0, hs₂l⟩ := h2
  have e1 : o.oangle e u₁ - θ = ((s₁ : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_toReal]
  have e2 : o.oangle e u₂ - θ = ((s₂ : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_toReal]
  have hdiff : o.oangle e u₂ - (o.oangle e u₁ + Real.pi) =
      ((s₂ - s₁ - Real.pi : ℝ) : Real.Angle) := by
    calc o.oangle e u₂ - (o.oangle e u₁ + Real.pi)
        = (o.oangle e u₂ - θ) - (o.oangle e u₁ - θ) - Real.pi := by abel
      _ = ((s₂ : ℝ) : Real.Angle) - ((s₁ : ℝ) : Real.Angle) - Real.pi := by
          rw [e2, e1]
      _ = ((s₂ - s₁ - Real.pi : ℝ) : Real.Angle) := by
          simp only [← Real.Angle.coe_sub]
  rw [hdiff, Real.Angle.toReal_coe]
  -- toReal of ↑(s₂ - s₁ - π): the representative in (-π, π]
  have hrep : toIocMod Real.two_pi_pos (-Real.pi) (s₂ - s₁ - Real.pi) =
      s₂ - s₁ + Real.pi ∨
      toIocMod Real.two_pi_pos (-Real.pi) (s₂ - s₁ - Real.pi) =
      s₂ - s₁ - Real.pi := by
    by_cases hle : s₂ - s₁ - Real.pi ≤ -Real.pi
    · left
      have hmem : s₂ - s₁ + Real.pi ∈
          Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        constructor <;> linarith [Real.pi_pos]
      have hto : toIocMod Real.two_pi_pos (-Real.pi) (s₂ - s₁ - Real.pi) =
          toIocMod Real.two_pi_pos (-Real.pi)
            (s₂ - s₁ - Real.pi + (1 : ℤ) • (2 * Real.pi)) := by
        rw [toIocMod_add_zsmul]
      rw [show s₂ - s₁ - Real.pi + (1 : ℤ) • (2 * Real.pi) =
          s₂ - s₁ + Real.pi by simp; ring] at hto
      rw [hto, (toIocMod_eq_self Real.two_pi_pos).mpr hmem]
    · right
      have hgt : -Real.pi < s₂ - s₁ - Real.pi := not_le.mp hle
      have hmem' : s₂ - s₁ - Real.pi ∈
          Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        constructor <;> linarith [Real.pi_pos]
      exact (toIocMod_eq_self Real.two_pi_pos).mpr hmem'
  rcases hrep with hrep | hrep
  · rw [hrep, abs_of_pos (by linarith [Real.pi_pos])]
    linarith [Real.pi_pos]
  · rw [hrep, abs_of_neg (by linarith [Real.pi_pos])]
    linarith [Real.pi_pos]

/-- A chain of adjacent half-open intervals covers their union. -/
lemma mem_Ico_chain {a w : ℝ} {t : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Ico (a + 2 * w) (a + (2 * t + 2) * w)) :
    ∃ l, 1 ≤ l ∧ l ≤ t ∧ ρ ∈ Set.Ico (a + 2 * l * w) (a + (2 * l + 2) * w) := by
  obtain ⟨hlo, hhi⟩ := hρ
  induction t with
  | zero =>
    simp at hlo hhi
    linarith
  | succ n ih =>
    by_cases h : ρ < a + (2 * n + 2) * w
    · obtain ⟨l, hl1, hlt, hlmem⟩ := ih h
      exact ⟨l, hl1, hlt.trans (Nat.le_succ n), hlmem⟩
    · push Not at h
      refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), le_rfl, ?_⟩
      have e1 : (a + 2 * ↑(n + 1) * w : ℝ) = a + (2 * ↑n + 2) * w := by
        push_cast; ring
      rw [e1]
      exact Set.mem_Ico.mpr ⟨h, hhi⟩

/-- The per-gap covering bound: a direction `ρ` at distance at least `2w`
from both ends of a gap `(a, b)` is covered by `t` consecutive wings
`[a + 2lw, a + (2l+2)w)`, provided `b - a < (2t + 4)w`. -/
lemma covered_of_gap {a b w : ℝ} {t : ℕ} {ρ : ℝ}
    (hlo : a + 2 * w ≤ ρ) (hhi : ρ ≤ b - 2 * w)
    (hspan : b - a < (2 * t + 4) * w) :
    ∃ l, 1 ≤ l ∧ l ≤ t ∧ ρ ∈ Set.Ico (a + 2 * l * w) (a + (2 * l + 2) * w) := by
  apply mem_Ico_chain
  constructor
  · exact hlo
  · calc ρ ≤ b - 2 * w := hhi
      _ < a + (2 * t + 4) * w - 2 * w := by linarith
      _ = a + (2 * t + 2) * w := by ring

end Jsp404
