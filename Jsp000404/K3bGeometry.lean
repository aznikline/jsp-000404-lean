import Jsp000404.Induction
import Jsp000404.KraftResidual
import Jsp000404.ChainWitness

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
* `arc_overflow_geometric_of_cells` — the fat-arc (non-polygon)
  certificate, fully wired to the real direction system: an arc
  `p ≤ q` of `directionRow i` between `dirRep u` and `dirRep v`
  carrying `≥ n` integer λ-cells, on the counterclockwise branch,
  forces `(n+1)·λ ≤ π`, i.e. `δ ≥ 1`.  Consumes `rnn` remainder
  bounds (`floor_mul_le_gap`), the fan-arc telescoping
  (`cyclicDiff_eq_Ico_sum_gapAfter`), the projective branch
  (`cyclicDiff_dirRep` + `linRep`), and `triAngle`.  No unproved
  angle-sum premise: the only certificate data are the checkable
  cell count, endpoint identifications, and orientation bit.
  `arc_overflow_geometric_absurd` is the `⌊π/λ⌋ = n` infeasibility
  corollary.  What remains open is the *selection* direction: why a
  first overfull level produces such an arc (or another certificate
  family) in the first place.
* `leaf_0001_cert` / `leaf_0001_absurd` — the concrete mixed-level
  signed residual `certs_n4_high/leaf_0001.json` wired end-to-end:
  two cyclic fan chains + two signed triangle identities + three
  `triAngle` remainder demands, recombined to `P = 1 + 2δ` with
  `P ≥ 3` and fed through `ResidualWitness.ge_of` at `τ = 1`,
  concluding `5·λ ≤ π` (`δ ≥ 1`), `False` under `⌊π/λ⌋ = 4`.
  The model's cyclic `order` enters as forward-arc comparisons on
  `dirRep`s (no `directionRow` position/rotation correspondence is
  needed in this form); the `bits` are `oangle.toReal` signs; the
  `qs` are cell lower bounds on arcs.  A wired instance, not yet a
  general construction.
-/

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

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

/-! ### The fat-arc certificate (non-polygon)

The second certificate family observed in the exact LP experiments:
a single angle `∠uiv` which equals a *forward fan arc*
`cyclicDiff a b` (the direct projective branch of
`linRep_oangle_eq_angle_or_pi_sub`) carrying at least `n` λ-cells.
Then `n·λ ≤ ∠uiv ≤ π − λ` forces `(n+1)·λ ≤ π`, i.e. `δ ≥ 1` — the
high-regime threshold.  Under `⌊π/λ⌋ = n` the hypotheses are outright
contradictory (`arc_overflow_absurd`): the skeleton is infeasible.

Constraint provenance: the arc is a consecutive sum of `gapAfter`
terms (`cyclicDiff_eq_Ico_sum_gapAfter`), each cell
`λ·⌊g/λ⌋ ≤ g` is the model's `rnn` remainder bound
(`floor_mul_le_gap`), the angle identity `∠ = cyclicDiff` is the
projective branch (`cyclicDiff_dirRep` + `linRep_oangle_eq_angle_or_pi_sub`),
and `∠uiv ≤ π − λ` is `Section4Legality.triAngle`.  No triangle sums
are used — this is genuinely not a polygon certificate. -/

/-- `λ·⌊g/λ⌋ ≤ g` for `0 ≤ g`: the per-gap remainder bound
(`r = g − λ⌊g/λ⌋ ≥ 0`). -/
theorem floor_mul_le_gap {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g) :
    (⌊g / lam⌋₊ : ℝ) * lam ≤ g := by
  have h1 : (⌊g / lam⌋₊ : ℝ) ≤ g / lam :=
    Nat.floor_le (div_nonneg hg hlam.le)
  rwa [le_div_iff₀ hlam] at h1

/-- Arc telescoping: the forward arc between sorted positions
`a ≤ b` of `l` is the consecutive-gap sum over `Finset.Ico a b`. -/
theorem cyclicDiff_eq_Ico_sum_gapAfter {l : List ℝ} (hs : l.SortedLE)
    {a b : Fin l.length} (hab : a ≤ b) :
    cyclicDiff (l.get a) (l.get b) =
      ∑ t ∈ Finset.Ico a b, gapAfter l t := by
  have hsmono := List.sortedLE_iff_monotone_get.mp hs
  -- transport the `Fin`-indexed `Ico` to an `ℕ`-indexed one
  have himg : Finset.Ico a.1 b.1 =
      (Finset.Ico a b).image (fun t : Fin l.length => t.1) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, by omega⟩, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by omega, by omega⟩
  set f : ℕ → ℝ :=
    fun x => if h : x < l.length then l.get ⟨x, h⟩ else 0 with hf
  have hfv : ∀ y : ℕ, (hy : y < l.length) → f y = l.get ⟨y, hy⟩ :=
    fun y hy => by rw [hf]; exact dif_pos hy
  have hsum : ∑ t ∈ Finset.Ico a b, gapAfter l t =
      ∑ x ∈ Finset.Ico a.1 b.1,
        (if h : x < l.length then gapAfter l ⟨x, h⟩ else 0) := by
    rw [himg, Finset.sum_image (fun x _ y _ h => Fin.ext h)]
    apply Finset.sum_congr rfl
    intro t _
    rw [dif_pos t.2]
  rw [hsum]
  have hterm : ∀ x ∈ Finset.Ico a.1 b.1,
      (if h : x < l.length then gapAfter l ⟨x, h⟩ else 0) =
        f (x + 1) - f x := by
    intro x hx
    have hxb : x < b.1 := (Finset.mem_Ico.mp hx).2
    rw [dif_pos (by omega : x < l.length)]
    unfold gapAfter
    rw [dif_pos (by omega : x + 1 < l.length),
      hfv _ (by omega : x + 1 < l.length),
      hfv _ (by omega : x < l.length)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range]
  simp only [add_assoc]
  rw [Finset.sum_range_sub (fun t => f (a.1 + t)) (b.1 - a.1),
    Nat.add_sub_cancel' (by omega : a.1 ≤ b.1), Nat.add_zero]
  rw [hfv _ b.2, hfv _ a.2]
  have hle : l.get a ≤ l.get b := hsmono hab
  unfold cyclicDiff
  by_cases heq : l.get a = l.get b
  · rw [if_pos heq]; linarith
  · rw [if_neg heq, if_pos (lt_of_le_of_ne hle heq)]

/-- Cells of a forward arc are bounded by its length: summing
`λ⌊g/λ⌋ ≤ g` over the arc's consecutive gaps.  This is the `rnn`
layer of the certificate. -/
theorem arc_cells_le_arc {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.SortedLE) (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    {a b : Fin l.length} (hab : a ≤ b) :
    (∑ t ∈ Finset.Ico a b, (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam ≤
      cyclicDiff (l.get a) (l.get b) := by
  have hne : l ≠ [] :=
    List.length_pos_iff.mp ((Nat.zero_le a.1).trans_lt a.2)
  have hnn : ∀ t : Fin l.length, 0 ≤ gapAfter l t :=
    fun t => gapAfter_nonneg hs hmem hne t
  rw [cyclicDiff_eq_Ico_sum_gapAfter hs hab, Finset.sum_mul]
  exact Finset.sum_le_sum fun t _ => floor_mul_le_gap hlam (hnn t)

/-- **Fat-arc certificate.**  If `∠uiv` equals a forward fan arc
`cyclicDiff a b` and that arc carries `≥ n` λ-cells, then
`(n+1)·λ ≤ π`, i.e. `δ = π/λ − n ≥ 1`. -/
theorem arc_overflow_cert {s n : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam)
    {i u v : Fin s} (hiu : u ≠ i) (hiv : i ≠ v) (huv : u ≠ v)
    {a b : ℝ}
    (harc : ∠ (c u) (c i) (c v) = cyclicDiff a b)
    (hfat : (n : ℝ) * lam ≤ cyclicDiff a b) :
    (n + 1 : ℝ) * lam ≤ Real.pi := by
  have hb := hleg.triAngle u i v hiu hiv huv
  linarith

/-- Cell-level form: the arc's `Σ⌊g/λ⌋ ≥ n` suffices — the remainder
bounds fill the gap between cells and arc length. -/
theorem arc_overflow_of_cells {s n : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam)
    {i u v : Fin s} (hiu : u ≠ i) (hiv : i ≠ v) (huv : u ≠ v)
    {a b : ℝ}
    (harc : ∠ (c u) (c i) (c v) = cyclicDiff a b)
    {l : List ℝ} (hs : l.SortedLE)
    (hmem : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    {p q : Fin l.length} (hpq : p ≤ q)
    (hpa : l.get p = a) (hqb : l.get q = b)
    (hcells : (n : ℕ) ≤
      ∑ t ∈ Finset.Ico p q, ⌊gapAfter l t / lam⌋₊) :
    (n + 1 : ℝ) * lam ≤ Real.pi := by
  have hfat : (n : ℝ) * lam ≤ cyclicDiff a b := by
    rw [← hpa, ← hqb]
    have h1 := arc_cells_le_arc hlam hs hmem hpq
    have h2 : (n : ℝ) * lam ≤
        (∑ t ∈ Finset.Ico p q, (⌊gapAfter l t / lam⌋₊ : ℝ)) * lam := by
      apply mul_le_mul_of_nonneg_right _ hlam.le
      exact_mod_cast hcells
    linarith
  exact arc_overflow_cert hleg hiu hiv huv harc hfat

/-- Under `⌊π/λ⌋ = n` a fat arc cannot exist: the certificate is an
infeasibility witness (`δ < 1` always holds by definition of `n`). -/
theorem arc_overflow_absurd {s n : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam)
    (hn : ⌊Real.pi / lam⌋₊ = n)
    {i u v : Fin s} (hiu : u ≠ i) (hiv : i ≠ v) (huv : u ≠ v)
    {a b : ℝ}
    (harc : ∠ (c u) (c i) (c v) = cyclicDiff a b)
    (hfat : (n : ℝ) * lam ≤ cyclicDiff a b) : False := by
  have h1 := arc_overflow_cert hleg hiu hiv huv harc hfat
  have h2 : Real.pi / lam < (n : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (Real.pi / lam)
    rwa [hn] at this
  rw [div_lt_iff₀ hlam] at h2
  linarith

/-! ### The fat-arc certificate, fully wired to the direction row

The `harc` hypothesis of `arc_overflow_cert` is discharged here by the
actual direction system: `cyclicDiff (dirRep i u) (dirRep i v)` equals
`linRep` of the oriented angle `i→u → i→v` (`cyclicDiff_dirRep`), and
`linRep` is `∠uiv` on the nonnegative-`toReal` branch — the model's
"same bit" skeleton selector.  The `toReal = π` edge would force
`∠uiv = π`, which `triAngle` + `λ > 0` already forbid, so the branch
condition `0 ≤ (oangle …).toReal` suffices; it is a locally checkable
fact of the configuration (one orientation sign), not a global
triangulation identity like `cycle_cert`'s `hsum`.

Hypotheses of `arc_overflow_geometric_of_cells` are exactly the
certificate data of a leaf: an arc `p ≤ q` of the sorted direction row
whose consecutive gaps carry `≥ n` integer cells, the endpoint
identifications `l[p] = dirRep u`, `l[q] = dirRep v`, and the
orientation bit.  Every constraint consumed is real geometry:
`rnn` (`floor_mul_le_gap`), the fan arc
(`cyclicDiff_eq_Ico_sum_gapAfter`), the projective branch
(`cyclicDiff_dirRep`, `linRep`), and `triAngle`. -/

/-- The forward arc between two direction representatives equals
`∠uiv` when the `i→u → i→v` sweep is counterclockwise
(`0 ≤ oangle.toReal`); the `toReal = π` case is excluded by legality
since `∠uiv = π` would violate `∠ ≤ π − λ`. -/
theorem dirRep_arc_eq_angle {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (he : e ≠ 0)
    {i u v : Fin s} (hiu : u ≠ i) (hiv : i ≠ v) (huv : u ≠ v)
    (hccw : 0 ≤ (o.oangle (c u - c i) (c v - c i)).toReal) :
    ∠ (c u) (c i) (c v) =
      cyclicDiff (dirRep o e c i u) (dirRep o e c i v) := by
  have hcu : c u ≠ c i := fun h => hiu (hleg.inj h)
  have hcv : c v ≠ c i := fun h => hiv (hleg.inj h.symm)
  have hangle : ∠ (c u) (c i) (c v) =
      |(o.oangle (c u - c i) (c v - c i)).toReal| := by
    show InnerProductGeometry.angle (c u -ᵥ c i) (c v -ᵥ c i) = _
    rw [vsub_eq_sub, vsub_eq_sub]
    exact o.angle_eq_abs_oangle_toReal
      (sub_ne_zero.mpr hcu) (sub_ne_zero.mpr hcv)
  have hb := hleg.triAngle u i v hiu hiv huv
  have hne : (o.oangle (c u - c i) (c v - c i)).toReal ≠ Real.pi := by
    intro h
    have hpi : ∠ (c u) (c i) (c v) = Real.pi := by
      rw [hangle, h, abs_of_pos Real.pi_pos]
    rw [hpi] at hb
    linarith [hleg.lam_pos]
  have hrep : linRep (o.oangle (c u - c i) (c v - c i)) =
      ∠ (c u) (c i) (c v) := by
    unfold linRep
    rw [if_neg (not_lt.mpr hccw), if_neg hne, hangle,
      abs_of_nonneg hccw]
  rw [cyclicDiff_dirRep o e c he hcu hcv, hrep]

/-- **Fat-arc certificate, direction-row form.**  If in `i`'s direction
row the forward arc from `dirRep u` to `dirRep v` has length `≥ n·λ`
and the sweep is counterclockwise, then `(n+1)·λ ≤ π`, i.e.
`δ = π/λ − n ≥ 1`. -/
theorem arc_overflow_geometric {s n : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hleg : Section4Legality c lam) (he : e ≠ 0)
    {i u v : Fin s} (hiu : u ≠ i) (hiv : i ≠ v) (huv : u ≠ v)
    (hccw : 0 ≤ (o.oangle (c u - c i) (c v - c i)).toReal)
    (hfat : (n : ℝ) * lam ≤
      cyclicDiff (dirRep o e c i u) (dirRep o e c i v)) :
    (n + 1 : ℝ) * lam ≤ Real.pi :=
  arc_overflow_cert hleg hiu hiv huv
    (dirRep_arc_eq_angle o e hleg he hiu hiv huv hccw) hfat

/-- **Fat-arc certificate, cell-level form on the actual row.**  The
`≥ n` bound is produced by summing `⌊g/λ⌋` over the consecutive gaps
of the arc `p ≤ q` in `directionRow i` — the `rnn` remainder layer of
the LP certificate. -/
theorem arc_overflow_geometric_of_cells {s n : ℕ}
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlam : 0 < lam) (he : e ≠ 0)
    {i u v : Fin s} (hiu : u ≠ i) (hiv : i ≠ v) (huv : u ≠ v)
    (hccw : 0 ≤ (o.oangle (c u - c i) (c v - c i)).toReal)
    {p q : Fin (directionRow o e c i).length} (hpq : p ≤ q)
    (hpa : (directionRow o e c i).get p = dirRep o e c i u)
    (hqb : (directionRow o e c i).get q = dirRep o e c i v)
    (hcells : n ≤ ∑ t ∈ Finset.Ico p q,
      ⌊gapAfter (directionRow o e c i) t / lam⌋₊) :
    (n + 1 : ℝ) * lam ≤ Real.pi := by
  have hfat : (n : ℝ) * lam ≤
      cyclicDiff (dirRep o e c i u) (dirRep o e c i v) := by
    rw [← hpa, ← hqb]
    have h1 := arc_cells_le_arc hlam (directionRow_sorted o e c i)
      (fun _ hx => directionRow_mem_Ico o e c hx) hpq
    have h2 : (n : ℝ) * lam ≤ (∑ t ∈ Finset.Ico p q,
        (⌊gapAfter (directionRow o e c i) t / lam⌋₊ : ℝ)) * lam :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcells) hlam.le
    linarith
  exact arc_overflow_geometric o e hleg he hiu hiv huv hccw hfat

/-- Under `⌊π/λ⌋ = n` the fat-arc certificate is an infeasibility
witness on the real direction system. -/
theorem arc_overflow_geometric_absurd {s n : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (hleg : Section4Legality c lam) (hlam : 0 < lam)
    (hn : ⌊Real.pi / lam⌋₊ = n) (he : e ≠ 0)
    {i u v : Fin s} (hiu : u ≠ i) (hiv : i ≠ v) (huv : u ≠ v)
    (hccw : 0 ≤ (o.oangle (c u - c i) (c v - c i)).toReal)
    (hfat : (n : ℝ) * lam ≤
      cyclicDiff (dirRep o e c i u) (dirRep o e c i v)) : False := by
  have h1 := arc_overflow_geometric o e hleg he hiu hiv huv hccw hfat
  have h2 : Real.pi / lam < (n : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (Real.pi / lam)
    rwa [hn] at this
  rw [div_lt_iff₀ hlam] at h2
  linarith

/-! ### The leaf-0001 signed residual, fully wired to real geometry

The mixed-level certificate `certs_n4_high/leaf_0001.json`
(`n = 4`, `s = 5`, defect profile `c = [1,2,2,2,3]`, `K = 11/8`,
first overfull level `m = 3`, target `τ = 1`) recombined by the lead
to a signed residual: two fan remainder budgets and two triangle
identities yield `P := r02+r03+r33+r10+r21+r32 = 1 + 2δ`, while
three angle upper bounds force `r10, r21, r32 ≥ 1` and the other
three remainders are nonnegative — hence `P ≥ 3` and `δ ≥ 1`.

Every piece below is sourced from real geometry:

* fan equations are cyclic `cyclicDiff` chains on the actual
  `dirRep` values (`cyclicDiff_chain4` — the model's `order` data,
  as forward-arc comparisons);
* triangle identities are `angle_add_angle_add_angle_eq_pi` with the
  arc/complement correspondence proved from the orientation bit
  (`dirRep_arc_eq_angle` / `dirRep_arc_eq_pi_sub_angle`);
* remainder demands `arc ≥ λ` come from `triAngle`;
* remainder nonnegativity `arc − q·λ ≥ 0` comes from the declared
  cell lower bound `q·λ ≤ arc`;
* the combination is instantiated through `ResidualWitness.ge_of`
  at `τ = 1`, with `w.δ` literally `π/λ − 4`.

The hypothesis bundle (declared cells as equalities plus the angle
demands) is what the LP's closed relaxation only meets at the
`δ = 1` boundary — the certificate is an infeasibility witness for
the `n = 4` regime (`leaf_0001_absurd`). -/

/-- The forward arc between two direction representatives in row `i`. -/
noncomputable def dirArc {s : ℕ} (c : Fin s → Plane₂)
    (i u v : Fin s) : ℝ :=
  cyclicDiff (dirRep o e c i u) (dirRep o e c i v)

/-- Complement branch of the projective correspondence: a clockwise
sweep (`oangle.toReal < 0`) means the forward arc is `π − ∠uiv`. -/
theorem dirRep_arc_eq_pi_sub_angle {s : ℕ} {c : Fin s → Plane₂}
    (he : e ≠ 0) {i u v : Fin s}
    (hcu : c u ≠ c i) (hcv : c v ≠ c i)
    (hcw : (o.oangle (c u - c i) (c v - c i)).toReal < 0) :
    ∠ (c u) (c i) (c v) =
      Real.pi - cyclicDiff (dirRep o e c i u) (dirRep o e c i v) := by
  have hangle : ∠ (c u) (c i) (c v) =
      |(o.oangle (c u - c i) (c v - c i)).toReal| := by
    show InnerProductGeometry.angle (c u -ᵥ c i) (c v -ᵥ c i) = _
    rw [vsub_eq_sub, vsub_eq_sub]
    exact o.angle_eq_abs_oangle_toReal
      (sub_ne_zero.mpr hcu) (sub_ne_zero.mpr hcv)
  have hrep : linRep (o.oangle (c u - c i) (c v - c i)) =
      Real.pi - ∠ (c u) (c i) (c v) := by
    unfold linRep
    rw [if_pos hcw, hangle, abs_of_neg hcw]
    ring
  rw [cyclicDiff_dirRep o e c he hcu hcv, hrep]
  ring

/-- On `[0, π)`, the forward arc is zero only for equal endpoints. -/
theorem cyclicDiff_eq_zero_of_Ico {a b : ℝ}
    (ha : a ∈ Set.Ico 0 Real.pi) (hb : b ∈ Set.Ico 0 Real.pi)
    (h : cyclicDiff a b = 0) : a = b := by
  by_contra hne
  obtain ⟨-, ha1⟩ := ha; obtain ⟨hb0, -⟩ := hb
  rw [cyclicDiff, if_neg hne] at h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos hlt] at h; linarith
  · rw [if_neg (not_lt.mpr hgt.le)] at h; linarith [Real.pi_pos]

/-- `b` on the forward arc `a → c` splits it. -/
theorem cyclicDiff_eq_add_of_le {a b c : ℝ}
    (ha : a ∈ Set.Ico 0 Real.pi) (hb : b ∈ Set.Ico 0 Real.pi)
    (hc : c ∈ Set.Ico 0 Real.pi)
    (h : cyclicDiff a b ≤ cyclicDiff a c) :
    cyclicDiff a c = cyclicDiff a b + cyclicDiff b c := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hc0, hc1⟩ := hc
  rcases eq_or_ne a c with rfl | hac
  · have haa : cyclicDiff a a = (0 : ℝ) := by simp [cyclicDiff]
    rw [haa] at h
    have hab0 : cyclicDiff a b = 0 :=
      le_antisymm h (cyclicDiff_nonneg ha1 hb0)
    have hab : a = b :=
      cyclicDiff_eq_zero_of_Ico ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hab0
    subst hab; simp [cyclicDiff]
  rcases eq_or_ne a b with rfl | hab
  · simp [cyclicDiff]
  rcases eq_or_ne b c with rfl | hbc
  · have hbb : cyclicDiff b b = (0 : ℝ) := by simp [cyclicDiff]
    rw [hbb]; simp
  rcases lt_or_gt_of_ne hab with h12 | h21 <;>
    rcases lt_or_gt_of_ne hac with h13 | h31 <;>
    rcases lt_or_gt_of_ne hbc with h23 | h32 <;>
    unfold cyclicDiff at h ⊢ <;>
    split_ifs at h ⊢ <;> (try contradiction) <;>
    linarith [Real.pi_pos]

/-- The two complementary arcs between distinct points sum to `π`. -/
theorem cyclicDiff_add_rev {a b : ℝ} (h : a ≠ b) :
    cyclicDiff a b + cyclicDiff b a = Real.pi := by
  unfold cyclicDiff
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [if_neg h, if_pos hlt, if_neg h.symm,
      if_neg (not_lt.mpr hlt.le)]
    linarith [Real.pi_pos]
  · rw [if_neg h, if_neg (not_lt.mpr hgt.le), if_neg h.symm,
      if_pos hgt]
    linarith [Real.pi_pos]

/-- Four-term cyclic chain: with `x2, x3, x4` in that order on the
forward arc from `x1`, the four consecutive arcs telescope to `π`.
This is the model's `order` datum for a 4-gap fan. -/
theorem cyclicDiff_chain4 {x1 x2 x3 x4 : ℝ}
    (h1 : x1 ∈ Set.Ico 0 Real.pi) (h2 : x2 ∈ Set.Ico 0 Real.pi)
    (h3 : x3 ∈ Set.Ico 0 Real.pi) (h4 : x4 ∈ Set.Ico 0 Real.pi)
    (h23 : cyclicDiff x1 x2 ≤ cyclicDiff x1 x3)
    (h34 : cyclicDiff x1 x3 ≤ cyclicDiff x1 x4)
    (h14 : 0 < cyclicDiff x1 x4) :
    cyclicDiff x1 x2 + cyclicDiff x2 x3 + cyclicDiff x3 x4 +
      cyclicDiff x4 x1 = Real.pi := by
  have e1 := cyclicDiff_eq_add_of_le h1 h2 h3 h23
  have e2 := cyclicDiff_eq_add_of_le h1 h3 h4 h34
  have hne : x1 ≠ x4 := by
    intro he
    rw [he, show cyclicDiff x4 x4 = 0 from if_pos rfl] at h14
    exact lt_irrefl _ h14
  have e3 := cyclicDiff_add_rev hne
  linarith

/-- **Leaf-0001 signed residual certificate.**  The geometric source
of `P = 1 + 2δ`, `P ≥ 3` for the `n = 4` mixed skeleton, instantiated
through `ResidualWitness.ge_of` at `τ = 1`.  Conclusion `5·λ ≤ π`,
i.e. `π/λ − 4 ≥ 1`: the system's `δ` is `≥ 1`.

Hypotheses (the certificate's `order`/`bits`/`qs` data, all on the
actual `dirRep` values of the configuration):
* `h012 h013 h014` — cyclic order of row 0 is `(1,2,3,4)`;
* `h301 h302 h304` — cyclic order of row 3 is `(0,1,2,4)`;
* `h203` — direction 1 lies on the `0 → 3` arc of row 2;
* `hb*` — the eight orientation bits (arc vs complement branch);
* `hq03 hq33` — the two nonzero declared cell counts
  (`q03 = 4`, `q33 = 3`), as lower bounds on the wrap gaps. -/
theorem leaf_0001_cert {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    (h012 : dirArc o e c 0 1 2 ≤ dirArc o e c 0 1 3)
    (h013 : dirArc o e c 0 1 3 ≤ dirArc o e c 0 1 4)
    (h014 : 0 < dirArc o e c 0 1 4)
    (h301 : dirArc o e c 3 0 1 ≤ dirArc o e c 3 0 2)
    (h302 : dirArc o e c 3 0 2 ≤ dirArc o e c 3 0 4)
    (h304 : 0 < dirArc o e c 3 0 4)
    (h203 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (hb102 : (o.oangle (c 0 - c 1) (c 2 - c 1)).toReal < 0)
    (hb012 : 0 ≤ (o.oangle (c 1 - c 0) (c 2 - c 0)).toReal)
    (hb021 : 0 ≤ (o.oangle (c 0 - c 2) (c 1 - c 2)).toReal)
    (hb203a : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb023 : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hb213 : (o.oangle (c 1 - c 2) (c 3 - c 2)).toReal < 0)
    (hb324 : (o.oangle (c 2 - c 3) (c 4 - c 3)).toReal < 0)
    (hq03 : (4 : ℝ) * lam ≤ dirArc o e c 0 4 1)
    (hq33 : (3 : ℝ) * lam ≤ dirArc o e c 3 4 0) :
    (5 : ℝ) * lam ≤ Real.pi := by
  have hinj := hleg.inj
  have hmem : ∀ i j : Fin 5,
      dirRep o e c i j ∈ Set.Ico 0 Real.pi :=
    fun _ _ => linRep_mem_Ico _
  -- fan equations: the two cyclic chains sum to π
  have F0 : dirArc o e c 0 1 2 + dirArc o e c 0 2 3 +
      dirArc o e c 0 3 4 + dirArc o e c 0 4 1 = Real.pi :=
    cyclicDiff_chain4 (hmem 0 1) (hmem 0 2) (hmem 0 3) (hmem 0 4)
      h012 h013 h014
  have F3 : dirArc o e c 3 0 1 + dirArc o e c 3 1 2 +
      dirArc o e c 3 2 4 + dirArc o e c 3 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 3 0) (hmem 3 1) (hmem 3 2) (hmem 3 4)
      h301 h302 h304
  -- two-gap arcs telescope
  have eV2 : dirArc o e c 2 0 3 =
      dirArc o e c 2 0 1 + dirArc o e c 2 1 3 :=
    cyclicDiff_eq_add_of_le (hmem 2 0) (hmem 2 1) (hmem 2 3) h203
  have eV3 : dirArc o e c 3 0 2 =
      dirArc o e c 3 0 1 + dirArc o e c 3 1 2 :=
    cyclicDiff_eq_add_of_le (hmem 3 0) (hmem 3 1) (hmem 3 2) h301
  -- angle ↔ arc correspondences from the orientation bits
  have A102 : ∠ (c 0) (c 1) (c 2) = Real.pi - dirArc o e c 1 0 2 :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hinj.ne (by decide)) (hinj.ne (by decide)) hb102
  have A012 : ∠ (c 1) (c 0) (c 2) = dirArc o e c 0 1 2 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb012
  have A021 : ∠ (c 0) (c 2) (c 1) = dirArc o e c 2 0 1 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb021
  have A203 : ∠ (c 2) (c 0) (c 3) = dirArc o e c 0 2 3 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb203a
  have A023 : ∠ (c 0) (c 2) (c 3) = Real.pi - dirArc o e c 2 0 3 :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hinj.ne (by decide)) (hinj.ne (by decide)) hb023
  have A032 : ∠ (c 0) (c 3) (c 2) = dirArc o e c 3 0 2 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb032
  have A213 : ∠ (c 1) (c 2) (c 3) = Real.pi - dirArc o e c 2 1 3 :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hinj.ne (by decide)) (hinj.ne (by decide)) hb213
  have A324 : ∠ (c 2) (c 3) (c 4) = Real.pi - dirArc o e c 3 2 4 :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hinj.ne (by decide)) (hinj.ne (by decide)) hb324
  -- triangle angle sums
  have T0 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c 0) (p₂ := c 1) (p₃ := c 2)
    (hinj.ne (by decide) : c 1 ≠ c 0)
  rw [EuclideanGeometry.angle_comm (c 1) (c 2) (c 0),
    EuclideanGeometry.angle_comm (c 2) (c 0) (c 1)] at T0
  -- T0 : ∠102 + ∠021 + ∠012 = π
  have T2 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c 0) (p₂ := c 2) (p₃ := c 3)
    (hinj.ne (by decide) : c 2 ≠ c 0)
  rw [EuclideanGeometry.angle_comm (c 2) (c 3) (c 0),
    EuclideanGeometry.angle_comm (c 3) (c 0) (c 2)] at T2
  -- T2 : ∠023 + ∠032 + ∠203 = π
  -- remainder demands from triAngle through the complement arcs
  have D10 : lam ≤ dirArc o e c 1 0 2 := by
    have h := hleg.triAngle 0 1 2 (by decide) (by decide) (by decide)
    linarith
  have D21 : lam ≤ dirArc o e c 2 1 3 := by
    have h := hleg.triAngle 1 2 3 (by decide) (by decide) (by decide)
    linarith
  have D32 : lam ≤ dirArc o e c 3 2 4 := by
    have h := hleg.triAngle 2 3 4 (by decide) (by decide) (by decide)
    linarith
  -- remainder nonnegativity: gap ≥ 0 / declared cells fit
  have N02 : 0 ≤ dirArc o e c 0 3 4 :=
    cyclicDiff_nonneg (hmem 0 3).2 (hmem 0 4).1
  -- the residual combination P and its two properties
  have hP_eq : dirArc o e c 0 3 4 + (dirArc o e c 0 4 1 - 4 * lam) +
      dirArc o e c 3 2 4 + (dirArc o e c 3 4 0 - 3 * lam) +
      dirArc o e c 1 0 2 + dirArc o e c 2 1 3 =
      2 * Real.pi - 7 * lam := by
    linarith
  have hP_ge : 3 * lam ≤ dirArc o e c 0 3 4 +
      (dirArc o e c 0 4 1 - 4 * lam) + dirArc o e c 3 2 4 +
      (dirArc o e c 3 4 0 - 3 * lam) + dirArc o e c 1 0 2 +
      dirArc o e c 2 1 3 := by
    linarith
  -- instantiate the parameterized residual backend at τ = 1,
  -- in real units (the λ-normalized record of the certificate):
  --   w.P = Σr·λ, w.U = 0, w.C = λ, w.K = 3λ, w.c = 2λ, w.u = 0,
  --   w.B = 0, w.δ = π/λ − 4  — the system's own δ.
  have hcancel : lam * (Real.pi / lam) = Real.pi :=
    mul_div_cancel₀ _ hlam.ne'
  have hδ : (1 : ℝ) ≤ Real.pi / lam - 4 :=
    ResidualWitness.ge_of
      ⟨dirArc o e c 0 3 4 + (dirArc o e c 0 4 1 - 4 * lam) +
        dirArc o e c 3 2 4 + (dirArc o e c 3 4 0 - 3 * lam) +
        dirArc o e c 1 0 2 + dirArc o e c 2 1 3,
       0, lam, 3 * lam, 2 * lam, 0, 0, Real.pi / lam - 4⟩
      (τ := 1)
      (by show _ - 0 - 2 * lam * (Real.pi / lam - 4) = lam
          linarith)
      (by show 3 * lam ≤ _; linarith)
      (by show (0:ℝ) ≤ 0 + 0 * (Real.pi / lam - 4); linarith)
      (by show (0:ℝ) < 2 * lam + 0; linarith)
      (by show (1:ℝ) * (2 * lam + 0) ≤ 3 * lam - 0 - lam; linarith)
  have hδ' : (5 : ℝ) ≤ Real.pi / lam := by linarith
  exact (le_div_iff₀ hlam).mp hδ'

/-- Under `⌊π/λ⌋ = 4` the leaf-0001 certificate data is outright
contradictory — the skeleton is infeasible in the `n = 4` regime. -/
theorem leaf_0001_absurd {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    (hn : ⌊Real.pi / lam⌋₊ = 4)
    (h012 : dirArc o e c 0 1 2 ≤ dirArc o e c 0 1 3)
    (h013 : dirArc o e c 0 1 3 ≤ dirArc o e c 0 1 4)
    (h014 : 0 < dirArc o e c 0 1 4)
    (h301 : dirArc o e c 3 0 1 ≤ dirArc o e c 3 0 2)
    (h302 : dirArc o e c 3 0 2 ≤ dirArc o e c 3 0 4)
    (h304 : 0 < dirArc o e c 3 0 4)
    (h203 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (hb102 : (o.oangle (c 0 - c 1) (c 2 - c 1)).toReal < 0)
    (hb012 : 0 ≤ (o.oangle (c 1 - c 0) (c 2 - c 0)).toReal)
    (hb021 : 0 ≤ (o.oangle (c 0 - c 2) (c 1 - c 2)).toReal)
    (hb203a : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb023 : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hb213 : (o.oangle (c 1 - c 2) (c 3 - c 2)).toReal < 0)
    (hb324 : (o.oangle (c 2 - c 3) (c 4 - c 3)).toReal < 0)
    (hq03 : (4 : ℝ) * lam ≤ dirArc o e c 0 4 1)
    (hq33 : (3 : ℝ) * lam ≤ dirArc o e c 3 4 0) : False := by
  have h1 := leaf_0001_cert o e hleg hlam he h012 h013 h014 h301 h302
    h304 h203 hb102 hb012 hb021 hb203a hb023 hb032 hb213 hb324
    hq03 hq33
  have hf' : Real.pi / lam < 5 := by
    have hf := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn] at hf
    exact_mod_cast hf
  rw [div_lt_iff₀ hlam] at hf'
  linarith

end Jsp404

