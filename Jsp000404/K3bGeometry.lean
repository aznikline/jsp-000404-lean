import Jsp000404.Induction
import Jsp000404.KraftResidual

/-!
# K3b — geometric instantiation of the residual-capacity layer

**Wiring convention (fixed once, deliberately explicit).**  The
`KraftResidual` defect function `d` is instantiated at the geometric
row defect

    d i := rowDefect n lam (directionRows o e c i)      -- = c_i

i.e. the Kraft coordinate `K = Σᵢ 2^{−cᵢ}` of
`potential_le_sendovCap_iff_kraft`.  It is NOT the ABCEDF skeleton
deficit `d_i = c_i − 1` (`W = 2K`); feeding `c − 1` here would compute
`W`, not `K`.

What is proved here:

* `geomDefectCount_one_le_two` — `a₁ ≤ 2` for `n ≥ 2`: three
  saturated rows are impossible (`not_three_saturated`).  This is the
  first place the residual layer consumes real geometry.
* `kraftResidual_one_eq` / `geom_kraftResidual_one_nonneg` —
  `R₁ = 2B − a₁ ≥ 0` for `B ≥ 1`: level 1 can never be the first
  overfull level.
* `exists_first_overfull_level_ge_two` — `K > B` (with `B ≥ 1`,
  covering `B = 1` low and `B = 5/4` high) yields a first overfull
  level `m ∈ [2, n]` with `R_{m−1} ≥ 0` and `a_m > 2·R_{m−1}`.
* `cycle_cert` / `cycle_cert_delta` — the polygon-shape certificate:
  `t ≥ 3` distinct centers whose cyclic interior angles
  `∠ vᵢ v_{i+1} v_{i+2}` sum to `(t−2)·π` (the triangulation identity)
  satisfy `t·λ ≤ 2π`, i.e. `δ ≥ t/2 − n`.  At `n = 2`: a 5-cycle gives
  `δ ≥ 1/2` (the `[2]⁵` tight profile), a 6-cycle `δ ≥ 1`.  The lemma
  consumes `Section4Legality.triAngle`; producing `hsum` from the fan
  order (angle additivity along a vertex fan) is the remaining
  geometric content of the certificate construction.
-/

namespace Jsp404

open Finset
open scoped EuclideanGeometry

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- `a₁` counts exactly the saturated rows (`rowDefect = 1`). -/
theorem geomDefectCount_one_le_two {s n : ℕ} (hn2 : 2 ≤ n)
    {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0) :
    defectCount
      (fun i => rowDefect n lam (directionRows o e c i)) 1 ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  rw [defectCount] at hcon
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcon
  obtain ⟨i, j, k, hij, hik, hjk, ht⟩ := Finset.card_eq_three.mp htc
  have mem := fun x (hx : x ∈ t) =>
    (Finset.mem_filter.mp (hts hx)).2
  have hi := mem i (by rw [ht]; simp)
  have hj := mem j (by rw [ht]; simp)
  have hk := mem k (by rw [ht]; simp)
  exact not_three_saturated o e hn2 hlam hn hleg he hij hik hjk hi hj hk

/-- `R₁ = 2B − a₁` whenever every defect is positive. -/
theorem kraftResidual_one_eq {s : ℕ} {B : ℚ} {d : Fin s → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) :
    kraftResidual B d 1 = 2 * B - defectCount d 1 := by
  simpa [kraftResidual_zero B d hd1] using kraftResidual_succ B d 0

/-- Level 1 can never be overfull for `n ≥ 2` and `B ≥ 1`:
`R₁ = 2B − a₁ ≥ 2 − 2 = 0` since at most two rows are saturated. -/
theorem geom_kraftResidual_one_nonneg {s n : ℕ} (hn2 : 2 ≤ n)
    {B : ℚ} (hB : 1 ≤ B)
    {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (hd1 : ∀ i, 1 ≤ rowDefect n lam (directionRows o e c i)) :
    0 ≤ kraftResidual B
      (fun i => rowDefect n lam (directionRows o e c i)) 1 := by
  rw [kraftResidual_one_eq hd1]
  have hle := geomDefectCount_one_le_two o e hn2 hlam hn hleg he
  have : (defectCount
      (fun i => rowDefect n lam (directionRows o e c i)) 1 : ℚ) ≤ 2 :=
    by exact_mod_cast hle
  linarith

/-- **The first overfull level is at least 2.**  Kraft failure
`K > B ≥ 1` on a legal configuration with `n ≥ 2` produces a minimal
`m ∈ [2, n]` where the prefix capacity first fails: `R_{m−1} ≥ 0` but
`a_m > 2·R_{m−1}`.  The `m ≥ 2` improvement over
`exists_min_overfull_level` is `geom_kraftResidual_one_nonneg`, i.e.
ultimately `not_three_saturated` — the residual layer and the
saturation geometry meet here for the first time. -/
theorem exists_first_overfull_level_ge_two {s n : ℕ} (hn2 : 2 ≤ n)
    (hs2 : 2 ≤ s) {B : ℚ} (hB : 1 ≤ B)
    {lam : ℝ} (hlam : 0 < lam) (hn : ⌊Real.pi / lam⌋₊ = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (h : B < kraftSum
      (fun i => rowDefect n lam (directionRows o e c i))) :
    ∃ m, 2 ≤ m ∧ m ≤ n ∧
      kraftResidual B
        (fun i => rowDefect n lam (directionRows o e c i)) m < 0 ∧
      0 ≤ kraftResidual B
        (fun i => rowDefect n lam (directionRows o e c i)) (m - 1) ∧
      2 * kraftResidual B
          (fun i => rowDefect n lam (directionRows o e c i)) (m - 1)
        < defectCount
            (fun i => rowDefect n lam (directionRows o e c i)) m := by
  classical
  set d := fun i => rowDefect n lam (directionRows o e c i) with hd
  have hcells : ∀ i, rowCells lam (directionRows o e c i) ≤ n :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i hs2 hn
  have hd1 : ∀ i, 1 ≤ d i :=
    fun i => one_le_rowDefect lam hlam n _ (by omega) (hcells i)
  have hM : ∀ i, d i ≤ n :=
    fun i => rowDefect_le lam hlam n _ (hcells i)
  obtain ⟨m, hm1, hmM, hneg, hprev, hover⟩ :=
    exists_min_overfull_level B d (by linarith) hM hd1 h
  have hR1 : 0 ≤ kraftResidual B d 1 :=
    geom_kraftResidual_one_nonneg o e hn2 hB hlam hn hleg he hd1
  refine ⟨m, ?_, hmM, hneg, hprev, hover⟩
  by_contra hm2
  push Not at hm2
  interval_cases m
  linarith

/-! ### The polygon (cycle) certificate -/

/-- `i + 1 ≠ i` in `Fin t` for `t ≥ 2` — cyclic successor is never
a fixed point. -/
theorem fin_add_one_ne_self {t : ℕ} [NeZero t] (ht : 2 ≤ t) (i : Fin t) :
    i + 1 ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one',
    Nat.mod_eq_of_lt (by omega : 1 < t)] at hv
  rcases Nat.lt_or_ge (i.val + 1) t with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have h1 : i.val + 1 = t := by omega
    rw [h1, Nat.mod_self] at hv
    omega

/-- `i ≠ i + 2` in `Fin t` for `t ≥ 3`. -/
theorem fin_ne_add_two {t : ℕ} [NeZero t] (ht : 3 ≤ t) (i : Fin t) :
    i ≠ i + 2 := by
  intro h
  have hv := congrArg Fin.val h
  have h2 : ((2 : Fin t) : ℕ) = 2 := by
    rw [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt ht]
  rw [Fin.val_add, h2] at hv
  rcases Nat.lt_or_ge (i.val + 2) t with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have hlt2 : i.val + 2 < 2 * t := by omega
    have hsub : (i.val + 2) % t = i.val + 2 - t := by
      conv_lhs => rw [show i.val + 2 = i.val + 2 - t + t by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hv
    omega

/-- **Cycle certificate.**  Let `v : Fin t → Fin s` select `t ≥ 3`
distinct centers and suppose the cyclic interior angles
`∠ vᵢ v_{i+1} v_{i+2}` sum to `(t−2)·π` — the polygon triangulation
identity.  Every interior angle is a triangle angle, hence `≤ π − λ`
by legality, so `(t−2)π ≤ t(π−λ)`, i.e. `t·λ ≤ 2π`.

The hypothesis `hsum` is the checkable side of the certificate: it is
produced by angle additivity along each vertex fan when the cyclic
order of the `v`-vertices is consistent with every vertex's direction
row — the remaining construction content of K3b. -/
theorem cycle_cert {s t : ℕ} [NeZero t] {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (ht : 3 ≤ t)
    (v : Fin t → Fin s) (hv : Function.Injective v)
    (hsum : ∑ i : Fin t,
      ∠ (c (v i)) (c (v (i + 1))) (c (v (i + 2))) =
        ((t : ℝ) - 2) * Real.pi) :
    (t : ℝ) * lam ≤ 2 * Real.pi := by
  have hb : ∀ i : Fin t,
      ∠ (c (v i)) (c (v (i + 1))) (c (v (i + 2)))
        ≤ Real.pi - lam := by
    intro i
    have h01 : v i ≠ v (i + 1) :=
      fun e' => (fin_add_one_ne_self (by omega) i).symm (hv e')
    have h12 : v (i + 1) ≠ v (i + 2) := by
      have h2 : (2 : Fin t) = 1 + 1 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one', Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (by omega : 2 < t),
          Nat.mod_eq_of_lt (by omega : 1 < t),
          Nat.mod_eq_of_lt (by omega : 2 < t)]
      rw [h2, ← add_assoc]
      exact fun e' => (fin_add_one_ne_self (by omega) (i + 1)).symm (hv e')
    have h02 : v i ≠ v (i + 2) := fun e' => fin_ne_add_two ht i (hv e')
    exact hleg.triAngle _ _ _ h01 h12 h02
  have hle := Finset.sum_le_sum (s := Finset.univ) fun i _ => hb i
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hle
  linarith

/-- In δ coordinates (`π = (n+δ)·λ`): a `t`-cycle certificate forces
`n + δ = π/λ ≥ t/2`, i.e. `δ ≥ t/2 − n`.  The `t = 5, n = 2` instance
is `δ ≥ 1/2`; `t = 6, n = 2` gives `δ ≥ 1`. -/
theorem cycle_cert_delta {s _n t : ℕ} [NeZero t] {c : Fin s → Plane₂}
    {lam : ℝ}
    (hleg : Section4Legality c lam) (ht : 3 ≤ t) (hlam : 0 < lam)
    (v : Fin t → Fin s) (hv : Function.Injective v)
    (hsum : ∑ i : Fin t,
      ∠ (c (v i)) (c (v (i + 1))) (c (v (i + 2))) =
        ((t : ℝ) - 2) * Real.pi) :
    (t : ℝ) / 2 ≤ Real.pi / lam := by
  have h := cycle_cert hleg ht v hv hsum
  rw [le_div_iff₀ hlam]
  linarith

end Jsp404
