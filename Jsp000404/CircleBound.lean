import Jsp000404.WingBound
import Jsp000404.CrossCircle

/-!
# Lemma 3.7 — the per-circle point bound

For a range-1 circle `C` of a GC `V` all of whose generalized angles are
at most `π - lam`, every generalized direction `GD p p'` of two points
inside `C` stays at line-distance `≥ lam` from every center line `o_i o_j`
(two orderings of `GA` give `angle(GD, o_j - o_i) ∈ [lam, π - lam]`).

Covering the gaps between consecutive center-line directions (mod `π`)
by consecutive wings of width `lam`, the wing-sector partition bound
gives `N_i ≤ 2^{k'(i)}` with `k'(i) = Σ_j (⌊g_j / lam⌋ - 1)₊`, the
`uψ/2`-formula of Sendov (3.10) in radians.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- Representative of the line class of a directed angle in `[0, π)`. -/
noncomputable def linRep (d : Real.Angle) : ℝ :=
  if d.toReal < 0 then d.toReal + Real.pi
  else if d.toReal = Real.pi then 0 else d.toReal

lemma linRep_mem_Ico (d : Real.Angle) : linRep d ∈ Set.Ico 0 Real.pi := by
  have h := d.toReal_mem_Ioc
  unfold linRep
  by_cases h1 : d.toReal < 0
  · rw [if_pos h1]
    constructor <;> linarith [Real.pi_pos, h.1, h.2]
  · rw [if_neg h1]
    by_cases h2 : d.toReal = Real.pi
    · rw [if_pos h2]
      exact ⟨le_refl _, Real.pi_pos⟩
    · rw [if_neg h2]
      exact ⟨by linarith, lt_of_le_of_ne h.2 h2⟩

/-- The representative lies in the same line class (mod `π`). -/
lemma linRep_class (d : Real.Angle) :
    ((linRep d : ℝ) : Real.Angle) = d ∨
    ((linRep d : ℝ) : Real.Angle) = d + Real.pi := by
  unfold linRep
  by_cases h1 : d.toReal < 0
  · right
    rw [if_pos h1, Real.Angle.coe_add, Real.Angle.coe_toReal]
  · rw [if_neg h1]
    by_cases h2 : d.toReal = Real.pi
    · right
      rw [if_pos h2]
      have hd : d = ((Real.pi : ℝ) : Real.Angle) := by
        rw [← Real.Angle.coe_toReal d, h2]
      rw [hd, ← Real.Angle.coe_add]
      rw [show (Real.pi + Real.pi : ℝ) = 2 * Real.pi from by ring]
      rw [Real.Angle.coe_two_pi]
      exact Real.Angle.coe_zero.symm
    · left
      rw [if_neg h2, Real.Angle.coe_toReal]

/-- `|toReal|` of `↑(x + kπ)` is either `|x|` or `π - |x|` for
`x ∈ (-π, π)`, `k ∈ {-1, 0, 1}`. -/
lemma abs_toReal_add_int_pi {x : ℝ} (hx : x ∈ Set.Ioo (-Real.pi) Real.pi)
    {k : ℤ} (hk : k = 0 ∨ k = 1 ∨ k = -1) :
    |(((x + k * Real.pi : ℝ) : Real.Angle)).toReal| = |x| ∨
    |(((x + k * Real.pi : ℝ) : Real.Angle)).toReal| = Real.pi - |x| := by
  obtain ⟨hx1, hx2⟩ := hx
  rcases hk with rfl | rfl | rfl
  · left
    rw [Int.cast_zero, zero_mul, add_zero, Real.Angle.toReal_coe,
      (toIocMod_eq_self Real.two_pi_pos).mpr (by
        constructor <;> linarith)]
  · right
    rw [Int.cast_one, one_mul, Real.Angle.toReal_coe]
    by_cases hle : x + Real.pi ≤ Real.pi
    · rw [(toIocMod_eq_self Real.two_pi_pos).mpr (by
          constructor <;> linarith)]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (show x ≤ 0 by linarith)]
      ring
    · push Not at hle
      have hto : toIocMod Real.two_pi_pos (-Real.pi) (x + Real.pi) =
          toIocMod Real.two_pi_pos (-Real.pi) (x - Real.pi) := by
        rw [show x + Real.pi = x - Real.pi + (1 : ℤ) • (2 * Real.pi) by
          simp; ring, toIocMod_add_zsmul]
      rw [hto, (toIocMod_eq_self Real.two_pi_pos).mpr (by
        constructor <;> linarith)]
      rw [abs_of_neg (by linarith),
        abs_of_nonneg (show 0 ≤ x by linarith)]
      ring
  · right
    rw [Int.cast_neg, Int.cast_one, neg_mul, one_mul, ← sub_eq_add_neg,
      Real.Angle.toReal_coe]
    by_cases hle : -Real.pi < x - Real.pi
    · rw [(toIocMod_eq_self Real.two_pi_pos).mpr (by
          constructor <;> linarith)]
      rw [abs_of_neg (by linarith),
        abs_of_nonneg (show 0 ≤ x by linarith)]
      ring
    · push Not at hle
      have hto : toIocMod Real.two_pi_pos (-Real.pi) (x - Real.pi) =
          toIocMod Real.two_pi_pos (-Real.pi) (x + Real.pi) := by
        rw [show x - Real.pi = x + Real.pi + (-1 : ℤ) • (2 * Real.pi) by
          simp; ring, toIocMod_add_zsmul]
      rw [hto, (toIocMod_eq_self Real.two_pi_pos).mpr (by
        constructor <;> linarith)]
      rw [abs_of_nonneg (by linarith),
        abs_of_nonpos (show x ≤ 0 by linarith)]
      ring

/-- If `↑ρ ≡ d`, `↑ρ' ≡ d'` (mod `π`) with `ρ, ρ' ∈ [0, π)`, then
`|(d' - d).toReal|` is `|ρ' - ρ|` or `π - |ρ' - ρ|`. -/
lemma toReal_diff_of_class {d d' : Real.Angle} {ρ ρ' : ℝ}
    (hρ : ρ ∈ Set.Ico 0 Real.pi) (hρ' : ρ' ∈ Set.Ico 0 Real.pi)
    (hc : ((ρ : ℝ) : Real.Angle) = d ∨ ((ρ : ℝ) : Real.Angle) = d + Real.pi)
    (hc' : ((ρ' : ℝ) : Real.Angle) = d' ∨
      ((ρ' : ℝ) : Real.Angle) = d' + Real.pi) :
    |(d' - d).toReal| = |ρ' - ρ| ∨ |(d' - d).toReal| = Real.pi - |ρ' - ρ| := by
  obtain ⟨hρ0, hρπ⟩ := hρ
  obtain ⟨hρ'0, hρ'π⟩ := hρ'
  have hx : ρ' - ρ ∈ Set.Ioo (-Real.pi) Real.pi :=
    ⟨by linarith, by linarith⟩
  -- normalize: `d = ↑(ρ - aπ)`, `d' = ↑(ρ' - bπ)` with `a, b ∈ {0, 1}`
  have hd : ∃ a : ℤ, (a = 0 ∨ a = 1) ∧
      d = ((ρ - a * Real.pi : ℝ) : Real.Angle) := by
    rcases hc with hc | hc
    · exact ⟨0, Or.inl rfl, by rw [Int.cast_zero, zero_mul, sub_zero, hc]⟩
    · refine ⟨1, Or.inr rfl, ?_⟩
      rw [Int.cast_one, one_mul, Real.Angle.coe_sub, eq_sub_iff_add_eq]
      exact hc.symm
  have hd' : ∃ b : ℤ, (b = 0 ∨ b = 1) ∧
      d' = ((ρ' - b * Real.pi : ℝ) : Real.Angle) := by
    rcases hc' with hc' | hc'
    · exact ⟨0, Or.inl rfl, by rw [Int.cast_zero, zero_mul, sub_zero, hc']⟩
    · refine ⟨1, Or.inr rfl, ?_⟩
      rw [Int.cast_one, one_mul, Real.Angle.coe_sub, eq_sub_iff_add_eq]
      exact hc'.symm
  obtain ⟨a, ha, hd⟩ := hd
  obtain ⟨b, hb, hd'⟩ := hd'
  have hk : a - b = 0 ∨ a - b = 1 ∨ a - b = -1 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp <;> omega
  have hdd : d' - d = ((ρ' - ρ + (a - b) * Real.pi : ℝ) : Real.Angle) := by
    rw [hd, hd', ← Real.Angle.coe_sub]
    congr 1
    push_cast
    ring
  rw [hdd]
  have hkey := abs_toReal_add_int_pi hx hk
  push_cast at hkey ⊢
  exact hkey

/-- Translating the `angle ∈ [lam, π - lam]` constraint into the
`[0, π)`-representatives: `|linRep d - linRep d'| ∈ [lam, π - lam]`. -/
lemma linRep_sub_mem_Icc {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
    (he : e ≠ 0) {u v : Plane₂} (hu : u ≠ 0) (hv : v ≠ 0) {lam : ℝ}
    (hangle : lam ≤ InnerProductGeometry.angle u v ∧
              InnerProductGeometry.angle u v ≤ Real.pi - lam) :
    lam ≤ |linRep (o.oangle e u) - linRep (o.oangle e v)| ∧
      |linRep (o.oangle e u) - linRep (o.oangle e v)| ≤ Real.pi - lam := by
  obtain ⟨ha1, ha2⟩ := hangle
  set d := o.oangle e u
  set d' := o.oangle e v
  have hov : InnerProductGeometry.angle u v = |(d' - d).toReal| := by
    rw [o.angle_eq_abs_oangle_toReal hu hv, o.oangle_sub_left he hu hv]
  have key := toReal_diff_of_class (linRep_mem_Ico d) (linRep_mem_Ico d')
    (linRep_class d) (linRep_class d')
  rcases key with hkey | hkey
  · rw [hov] at ha1 ha2
    rw [hkey] at ha1 ha2
    rw [show linRep d - linRep d' = -(linRep d' - linRep d) by ring, abs_neg]
    exact ⟨ha1, ha2⟩
  · rw [hov] at ha1 ha2
    rw [hkey] at ha1 ha2
    rw [show linRep d - linRep d' = -(linRep d' - linRep d) by ring, abs_neg]
    constructor <;> linarith

end Jsp404
