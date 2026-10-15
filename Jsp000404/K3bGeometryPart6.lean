import Jsp000404.K3bGeometryPart5

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- **Detour arc swap — the mixed-sign certificate core.**  Two rows
`u` and `a` each carry a fan (`Σ gaps = π`).  When the cyclic orders
place arcs `a → x` at `u` and `w → u` at `a`, and a third vertex `w`
sees `u` between `a` and `x` while `u` sees `a` and `x` on the
opposite side of `w` (the three decode equations below), the two fan
arcs can be *re-routed through `w`*:

    dirArc u a x + dirArc a w u = dirArc w a x + ∠wxu.

This is the geometric content of the mixed-sign LP supports (a
`+△(w,u,x) −△(w,u,a)` pair): the negative triangle term is not a
loose relaxation — it is exactly the fan arc `a → x` at `u` that gets
exchanged for the same arc measured at `w` plus the hinge angle at
`x`.  The three decode hypotheses are equations; callers discharge
them from `bits`/`order` data via `dirRep_arc_eq_angle`,
`dirRep_arc_eq_pi_sub_angle` and `cyclicDiff_eq_add_of_le`. -/
theorem detour_arc_swap {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam)
    {u a w x : Fin s} (huw : u ≠ w)
    (hW : ∠ (c u) (c w) (c a) + dirArc o e c w a x
        = ∠ (c u) (c w) (c x))
    (hU : ∠ (c w) (c u) (c a)
        = ∠ (c w) (c u) (c x) + dirArc o e c u a x)
    (hA : ∠ (c w) (c a) (c u) = dirArc o e c a w u) :
    dirArc o e c u a x + dirArc o e c a w u =
      dirArc o e c w a x + ∠ (c w) (c x) (c u) := by
  have hinj := hleg.inj
  have Twx : ∠ (c u) (c w) (c x) + ∠ (c w) (c x) (c u)
      + ∠ (c x) (c u) (c w) = Real.pi :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c x)
      (hinj.ne huw.symm)
  have Twa : ∠ (c u) (c w) (c a) + ∠ (c w) (c a) (c u)
      + ∠ (c a) (c u) (c w) = Real.pi :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c a)
      (hinj.ne huw.symm)
  rw [EuclideanGeometry.angle_comm (c x) (c u) (c w)] at Twx
  rw [EuclideanGeometry.angle_comm (c a) (c u) (c w)] at Twa
  linarith

/-- **Two-fan detour certificate.**  Fans at `u` and `a` split off the
detoured arcs `a → x` (at `u`) and `w → u` (at `a`); the detour swap
then rewrites

    2π = P_u + Q_u + R_a + S_a + dirArc w a x + ∠wxu.

Every term on the right is a nonnegative arc or angle carrying a cell
bound; if their total bound is `B·λ` then `δ = π/λ − n ≥ (B − 2n)/2`
through `ResidualWitness.ge_of`. -/
theorem two_fan_detour_cert {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    {n : ℕ} {u a w x : Fin s} (huw : u ≠ w)
    (Pu Qu Ra Sa : ℝ)
    (hfanU : Pu + dirArc o e c u a x + Qu = Real.pi)
    (hfanA : Ra + dirArc o e c a w u + Sa = Real.pi)
    (hW : ∠ (c u) (c w) (c a) + dirArc o e c w a x
        = ∠ (c u) (c w) (c x))
    (hU : ∠ (c w) (c u) (c a)
        = ∠ (c w) (c u) (c x) + dirArc o e c u a x)
    (hA : ∠ (c w) (c a) (c u) = dirArc o e c a w u)
    (B : ℝ)
    (hB : B * lam ≤ Pu + Qu + Ra + Sa
        + dirArc o e c w a x + ∠ (c w) (c x) (c u)) :
    (B - 2 * n) / 2 ≤ Real.pi / lam - n := by
  have hdet := detour_arc_swap o e hleg huw hW hU hA
  have hstar : 2 * Real.pi = Pu + Qu + Ra + Sa
      + dirArc o e c w a x + ∠ (c w) (c x) (c u) := by
    linarith
  have hcancel : lam * (Real.pi / lam) = Real.pi :=
    mul_div_cancel₀ _ hlam.ne'
  exact ResidualWitness.ge_of
    ⟨Pu + Qu + Ra + Sa + dirArc o e c w a x + ∠ (c w) (c x) (c u),
     0, 2 * n * lam, B * lam, 2 * lam, 0, 0, Real.pi / lam - n⟩
    (τ := (B - 2 * n) / 2)
    (by show _ - 0 - 2 * lam * (Real.pi / lam - n) = _; linarith)
    (by linarith)
    (by show (0 : ℝ) ≤ 0 + 0 * (Real.pi / lam - n); linarith)
    (by show (0 : ℝ) < 2 * lam + 0; linarith)
    (by ring_nf; linarith)

/-- **The `leaf_0177` detour certificate.**  The mixed-sign support
`fan1 + fan2 −△(0,1,2) +△(0,1,3) + caps` of the `s = 5`, `n = 4` leaf
is the detour identity at `u = 1`, `a = 2`, `w = 0`, `x = 3`: the
fan-1 arc `2 → 3` and the fan-2 arc `0 → 1` re-route through vertex
`0` as `dirArc 0 2 3 + ∠031`.  The eight resulting terms carry
`1+3+0+4+0+2 = 10` cells (`Pu` by the `∠012 ≤ π−λ` demand,
`Sa`'s first two arcs by `∠124 ≤ π−λ`, the wrap arcs by their
`q = 3` baselines, `∠031` by `q30 = 2`), so `2π ≥ 10λ`, i.e.
`δ = π/λ − 4 ≥ 1`. -/
theorem leaf_0177_detour_cert {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    (h012 : dirArc o e c 0 1 2 ≤ dirArc o e c 0 1 3)
    (h102 : dirArc o e c 1 0 2 ≤ dirArc o e c 1 0 3)
    (h103 : dirArc o e c 1 0 3 ≤ dirArc o e c 1 0 4)
    (h104 : 0 < dirArc o e c 1 0 4)
    (h201 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (h203 : dirArc o e c 2 0 3 ≤ dirArc o e c 2 0 4)
    (h204 : 0 < dirArc o e c 2 0 4)
    (h214 : dirArc o e c 2 1 3 ≤ dirArc o e c 2 1 4)
    (hb012 : 0 ≤ (o.oangle (c 1 - c 0) (c 2 - c 0)).toReal)
    (hb013 : 0 ≤ (o.oangle (c 1 - c 0) (c 3 - c 0)).toReal)
    (hb102 : (o.oangle (c 0 - c 1) (c 2 - c 1)).toReal < 0)
    (hb103 : (o.oangle (c 0 - c 1) (c 3 - c 1)).toReal < 0)
    (hb021 : 0 ≤ (o.oangle (c 0 - c 2) (c 1 - c 2)).toReal)
    (hb214 : (o.oangle (c 1 - c 2) (c 4 - c 2)).toReal < 0)
    (hb031 : 0 ≤ (o.oangle (c 0 - c 3) (c 1 - c 3)).toReal)
    (hq13 : (3 : ℝ) * lam ≤ dirArc o e c 1 4 0)
    (hq23 : (3 : ℝ) * lam ≤ dirArc o e c 2 4 0)
    (hq30 : (2 : ℝ) * lam ≤ dirArc o e c 3 0 1) :
    (5 : ℝ) * lam ≤ Real.pi := by
  classical
  have hmem : ∀ i j : Fin 5,
      dirRep o e c i j ∈ Set.Ico 0 Real.pi :=
    fun _ _ => linRep_mem_Ico _
  -- fan equations: rows 1 and 2 cyclic chains sum to π
  have F1 : dirArc o e c 1 0 2 + dirArc o e c 1 2 3 +
      dirArc o e c 1 3 4 + dirArc o e c 1 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 1 0) (hmem 1 2) (hmem 1 3) (hmem 1 4)
      h102 h103 h104
  have F2 : dirArc o e c 2 0 1 + dirArc o e c 2 1 3 +
      dirArc o e c 2 3 4 + dirArc o e c 2 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 2 0) (hmem 2 1) (hmem 2 3) (hmem 2 4)
      h201 h203 h204
  -- decode (w = 0): ∠102 + dirArc 0 2 3 = ∠103, both direct
  have A02 : ∠ (c 1) (c 0) (c 2) = dirArc o e c 0 1 2 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb012
  have A03 : ∠ (c 1) (c 0) (c 3) = dirArc o e c 0 1 3 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb013
  have e023 : dirArc o e c 0 1 3 =
      dirArc o e c 0 1 2 + dirArc o e c 0 2 3 :=
    cyclicDiff_eq_add_of_le (hmem 0 1) (hmem 0 2) (hmem 0 3) h012
  have hW : ∠ (c 1) (c 0) (c 2) + dirArc o e c 0 2 3
      = ∠ (c 1) (c 0) (c 3) := by linarith
  -- decode (u = 1): ∠012 = ∠013 + dirArc 1 2 3, both complement
  have B12 : ∠ (c 0) (c 1) (c 2) =
      Real.pi - dirArc o e c 1 0 2 :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hleg.inj.ne (by decide)) (hleg.inj.ne (by decide)) hb102
  have B13 : ∠ (c 0) (c 1) (c 3) =
      Real.pi - dirArc o e c 1 0 3 :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hleg.inj.ne (by decide)) (hleg.inj.ne (by decide)) hb103
  have e123 : dirArc o e c 1 0 3 =
      dirArc o e c 1 0 2 + dirArc o e c 1 2 3 :=
    cyclicDiff_eq_add_of_le (hmem 1 0) (hmem 1 2) (hmem 1 3) h102
  have hU : ∠ (c 0) (c 1) (c 2)
      = ∠ (c 0) (c 1) (c 3) + dirArc o e c 1 2 3 := by linarith
  -- decode (a = 2): ∠021 = dirArc 2 0 1, direct
  have hA : ∠ (c 0) (c 2) (c 1) = dirArc o e c 2 0 1 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb021
  -- cell bounds
  have bPu : lam ≤ dirArc o e c 1 0 2 := by
    have h := hleg.triAngle 0 1 2 (by decide) (by decide) (by decide)
    linarith
  have h134 : (0 : ℝ) ≤ dirArc o e c 1 3 4 :=
    cyclicDiff_nonneg (hmem 1 3).2 (hmem 1 4).1
  have bQu : (3 : ℝ) * lam ≤
      dirArc o e c 1 3 4 + dirArc o e c 1 4 0 := by
    linarith [hq13, h134]
  have e214 : dirArc o e c 2 1 4 =
      dirArc o e c 2 1 3 + dirArc o e c 2 3 4 :=
    cyclicDiff_eq_add_of_le (hmem 2 1) (hmem 2 3) (hmem 2 4) h214
  have B14 : ∠ (c 1) (c 2) (c 4) =
      Real.pi - dirArc o e c 2 1 4 :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hleg.inj.ne (by decide)) (hleg.inj.ne (by decide)) hb214
  have bSa : (4 : ℝ) * lam ≤ dirArc o e c 2 1 3
      + dirArc o e c 2 3 4 + dirArc o e c 2 4 0 := by
    have h := hleg.triAngle 1 2 4 (by decide) (by decide) (by decide)
    linarith
  have bX : (0 : ℝ) ≤ dirArc o e c 0 2 3 :=
    cyclicDiff_nonneg (hmem 0 2).2 (hmem 0 3).1
  have A31 : ∠ (c 0) (c 3) (c 1) = dirArc o e c 3 0 1 :=
    dirRep_arc_eq_angle o e hleg he (by decide) (by decide)
      (by decide) hb031
  have bE : (2 : ℝ) * lam ≤ ∠ (c 0) (c 3) (c 1) := by linarith
  -- the detour certificate: B = 10 cells over 2π
  have hδ := two_fan_detour_cert o e hleg hlam he (n := 4)
    (u := 1) (a := 2) (w := 0) (x := 3) (by decide)
    (dirArc o e c 1 0 2) (dirArc o e c 1 3 4 + dirArc o e c 1 4 0)
    (0 : ℝ) (dirArc o e c 2 1 3 + dirArc o e c 2 3 4
      + dirArc o e c 2 4 0)
    (by linarith) (by linarith) hW hU hA (10 : ℝ)
    (by have := bPu; have := bQu; have := bSa; have := bX
        have := bE; linarith)
  have hδ' : (1 : ℝ) ≤ Real.pi / lam - 4 := by linarith
  have hδ'' : (5 : ℝ) ≤ Real.pi / lam := by linarith
  exact (le_div_iff₀ hlam).mp hδ''

/-- **Single-triangle arc transfer.**  In a triangle `△vuw` whose apex
decodes follow the pattern (direct at `v`, complement at `u`, direct
at `w`), the arc `v → w` measured at `u` equals the sum of the arcs
`u → w` at `v` and `v → u` at `w`:

    dirArc u v w = dirArc v u w + dirArc w v u.

This is the elementary "slack transport" move: the same geometric arc
consumes a different number of `λ`-cells in different direction rows,
so re-measuring it at `v` and `w` can harvest the `q`-baseline
difference.  Iterating transfers (and the two-triangle `detour_arc_swap`)
generates the whole signed-triangle certificate space. -/
theorem dirArc_triangle_transfer {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (he : e ≠ 0)
    {v u w : Fin s} (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w)
    (hbV : 0 ≤ (o.oangle (c u - c v) (c w - c v)).toReal)
    (hbU : (o.oangle (c v - c u) (c w - c u)).toReal < 0)
    (hbW : 0 ≤ (o.oangle (c v - c w) (c u - c w)).toReal) :
    dirArc o e c u v w = dirArc o e c v u w + dirArc o e c w v u := by
  have hinj := hleg.inj
  have Av : ∠ (c u) (c v) (c w) = dirArc o e c v u w :=
    dirRep_arc_eq_angle o e hleg he hvu.symm hvw huw hbV
  have Au : ∠ (c v) (c u) (c w) =
      Real.pi - dirArc o e c u v w :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hinj.ne hvu) (hinj.ne huw.symm) hbU
  have Aw : ∠ (c v) (c w) (c u) = dirArc o e c w v u :=
    dirRep_arc_eq_angle o e hleg he hvw huw.symm hvu hbW
  have T : ∠ (c u) (c v) (c w) + ∠ (c v) (c w) (c u)
      + ∠ (c w) (c u) (c v) = Real.pi :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c w)
      (hinj.ne hvu)
  rw [EuclideanGeometry.angle_comm (c w) (c u) (c v)] at T
  linarith

/-- **The `leaf_0970` transfer certificate.**  Row `2`'s fan is tight
(`qs = [0,1,0,3]`, `Σq = 4 = n`, so `Σr = δ`): the block arc
`dirArc(2;0,3) = g20 + g21` transfers through `△(0,2,3)` to
`dirArc(0;2,3) + dirArc(3;0,2)`, whose `q`-baselines are `0` and
`2` — one cell more than the consumed `q20 + q21 = 1`.  With the wrap
`q23 = 3`: `π ≥ 5λ`, i.e. `δ ≥ 1`. -/
theorem leaf_0970_transfer_cert {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (_hlam : 0 < lam) (he : e ≠ 0)
    (h201 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (h203 : dirArc o e c 2 0 3 ≤ dirArc o e c 2 0 4)
    (h204 : 0 < dirArc o e c 2 0 4)
    (h301 : dirArc o e c 3 0 1 ≤ dirArc o e c 3 0 2)
    (hb023a : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb023c : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hq31 : (2 : ℝ) * lam ≤ dirArc o e c 3 1 2)
    (hq23 : (3 : ℝ) * lam ≤ dirArc o e c 2 4 0) :
    (5 : ℝ) * lam ≤ Real.pi := by
  classical
  have hmem : ∀ i j : Fin 5,
      dirRep o e c i j ∈ Set.Ico 0 Real.pi :=
    fun _ _ => linRep_mem_Ico _
  have F2 : dirArc o e c 2 0 1 + dirArc o e c 2 1 3 +
      dirArc o e c 2 3 4 + dirArc o e c 2 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 2 0) (hmem 2 1) (hmem 2 3) (hmem 2 4)
      h201 h203 h204
  -- the block 0 → 3 telescopes through 1, then transfers to rows 0,3
  have e203 : dirArc o e c 2 0 3 =
      dirArc o e c 2 0 1 + dirArc o e c 2 1 3 :=
    cyclicDiff_eq_add_of_le (hmem 2 0) (hmem 2 1) (hmem 2 3) h201
  have htr : dirArc o e c 2 0 3 =
      dirArc o e c 0 2 3 + dirArc o e c 3 0 2 :=
    dirArc_triangle_transfer o e hleg he (v := 0) (u := 2) (w := 3)
      (by decide) (by decide) (by decide) hb023a hb023c hb032
  have e302 : dirArc o e c 3 0 2 =
      dirArc o e c 3 0 1 + dirArc o e c 3 1 2 :=
    cyclicDiff_eq_add_of_le (hmem 3 0) (hmem 3 1) (hmem 3 2) h301
  have hnn01 : (0 : ℝ) ≤ dirArc o e c 0 2 3 :=
    cyclicDiff_nonneg (hmem 0 2).2 (hmem 0 3).1
  have hnn30 : (0 : ℝ) ≤ dirArc o e c 3 0 1 :=
    cyclicDiff_nonneg (hmem 3 0).2 (hmem 3 1).1
  have hnn22 : (0 : ℝ) ≤ dirArc o e c 2 3 4 :=
    cyclicDiff_nonneg (hmem 2 3).2 (hmem 2 4).1
  -- π = dirArc(0;2,3) + dirArc(3;0,1) + dirArc(3;1,2) + g22 + g23
  --   ≥ 0 + 0 + 2λ + 0 + 3λ = 5λ
  linarith

/-- **Composition of two detours through a shared anchor arc.**  If the
arc `a → x` at vertices `u₁` and `u₂` both detour through the same
witness `w` (the same `dirArc w a x` anchor), eliminating the anchor
gives a *row-to-row transfer with signed correction*:

    dirArc u₁ a x = dirArc u₂ a x
      + (dirArc a w u₂ − dirArc a w u₁)
      + (∠w x u₁ − ∠w x u₂).

The two difference terms are themselves telescoped arcs (with either
sign) whenever `u₁, u₂` are adjacent in `a`'s and `x`'s cyclic orders;
a negatively occurring arc is then absorbed by an upper (cell-`r < 1`)
bound.  This is the mechanism behind single-fan certificates such as
`leaf_0968`. -/
theorem detour_arc_compose {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam)
    {u₁ u₂ a w x : Fin s} (hu₁w : u₁ ≠ w) (hu₂w : u₂ ≠ w)
    (hW₁ : ∠ (c u₁) (c w) (c a) + dirArc o e c w a x
        = ∠ (c u₁) (c w) (c x))
    (hU₁ : ∠ (c w) (c u₁) (c a)
        = ∠ (c w) (c u₁) (c x) + dirArc o e c u₁ a x)
    (hA₁ : ∠ (c w) (c a) (c u₁) = dirArc o e c a w u₁)
    (hW₂ : ∠ (c u₂) (c w) (c a) + dirArc o e c w a x
        = ∠ (c u₂) (c w) (c x))
    (hU₂ : ∠ (c w) (c u₂) (c a)
        = ∠ (c w) (c u₂) (c x) + dirArc o e c u₂ a x)
    (hA₂ : ∠ (c w) (c a) (c u₂) = dirArc o e c a w u₂) :
    dirArc o e c u₁ a x = dirArc o e c u₂ a x
      + (dirArc o e c a w u₂ - dirArc o e c a w u₁)
      + (∠ (c w) (c x) (c u₁) - ∠ (c w) (c x) (c u₂)) := by
  have d₁ := detour_arc_swap o e hleg hu₁w hW₁ hU₁ hA₁
  have d₂ := detour_arc_swap o e hleg hu₂w hW₂ hU₂ hA₂
  linarith

/-- **The `leaf_0968` double-detour certificate.**  A single fan at
vertex `1` (`qs = [0,0,0,3]`) suffices once the arc `3 → 4` at `1`
hops to row `2` through the shared anchor `dirArc 0 3 4`:

    dirArc(1;3,4) = dirArc(2;3,4) + dirArc(3;1,2) − dirArc(4;1,2),

the two detours `△(0,1,4)−△(0,1,3)` and `△(0,2,3)−△(0,2,4)`
composed.  The negatively occurring arc `dirArc(4;1,2)` is absorbed
by its cell upper bound `≤ λ` (`r41 < 1`), while
`dirArc(1;0,3) ≥ λ` (the `∠013 ≤ π−λ` demand) and the baselines
`q31 = 2`, `q13 = 3` give `π ≥ 5λ`, i.e. `δ ≥ 1`. -/
theorem leaf_0968_transfer_cert {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (_hlam : 0 < lam) (he : e ≠ 0)
    (h102 : dirArc o e c 1 0 2 ≤ dirArc o e c 1 0 3)
    (h103 : dirArc o e c 1 0 3 ≤ dirArc o e c 1 0 4)
    (h104 : 0 < dirArc o e c 1 0 4)
    (h013 : dirArc o e c 0 1 3 ≤ dirArc o e c 0 1 4)
    (h023 : dirArc o e c 0 2 3 ≤ dirArc o e c 0 2 4)
    (h203 : dirArc o e c 2 0 3 ≤ dirArc o e c 2 0 4)
    (h301 : dirArc o e c 3 0 1 ≤ dirArc o e c 3 0 2)
    (h401 : dirArc o e c 4 0 1 ≤ dirArc o e c 4 0 2)
    (hb013 : 0 ≤ (o.oangle (c 1 - c 0) (c 3 - c 0)).toReal)
    (hb014 : 0 ≤ (o.oangle (c 1 - c 0) (c 4 - c 0)).toReal)
    (hb023 : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb024 : 0 ≤ (o.oangle (c 2 - c 0) (c 4 - c 0)).toReal)
    (hb103 : (o.oangle (c 0 - c 1) (c 3 - c 1)).toReal < 0)
    (hb104 : (o.oangle (c 0 - c 1) (c 4 - c 1)).toReal < 0)
    (hb203 : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb204 : (o.oangle (c 0 - c 2) (c 4 - c 2)).toReal < 0)
    (hb031 : 0 ≤ (o.oangle (c 0 - c 3) (c 1 - c 3)).toReal)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hb041 : 0 ≤ (o.oangle (c 0 - c 4) (c 1 - c 4)).toReal)
    (hb042 : 0 ≤ (o.oangle (c 0 - c 4) (c 2 - c 4)).toReal)
    (hD : lam ≤ dirArc o e c 1 0 3)
    (hC : dirArc o e c 4 1 2 ≤ lam)
    (hq31 : (2 : ℝ) * lam ≤ dirArc o e c 3 1 2)
    (hq13 : (3 : ℝ) * lam ≤ dirArc o e c 1 4 0) :
    (5 : ℝ) * lam ≤ Real.pi := by
  classical
  have hmem : ∀ i j : Fin 5,
      dirRep o e c i j ∈ Set.Ico 0 Real.pi :=
    fun _ _ => linRep_mem_Ico _
  have hinj := hleg.inj
  have ne : ∀ a b : Fin 5, a ≠ b → c a ≠ c b := fun _ _ h => hinj.ne h
  -- fan at 1, with the block arc 0 → 3 telescoped
  have F1 : dirArc o e c 1 0 2 + dirArc o e c 1 2 3 +
      dirArc o e c 1 3 4 + dirArc o e c 1 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 1 0) (hmem 1 2) (hmem 1 3) (hmem 1 4)
      h102 h103 h104
  have e103 : dirArc o e c 1 0 3 =
      dirArc o e c 1 0 2 + dirArc o e c 1 2 3 :=
    cyclicDiff_eq_add_of_le (hmem 1 0) (hmem 1 2) (hmem 1 3) h102
  -- detour 1: u=1, a=3, w=0, x=4
  have A013 : ∠ (c 1) (c 0) (c 3) = dirArc o e c 0 1 3 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb013
  have A014 : ∠ (c 1) (c 0) (c 4) = dirArc o e c 0 1 4 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb014
  have e014 : dirArc o e c 0 1 4 =
      dirArc o e c 0 1 3 + dirArc o e c 0 3 4 :=
    cyclicDiff_eq_add_of_le (hmem 0 1) (hmem 0 3) (hmem 0 4) h013
  have hW₁ : ∠ (c 1) (c 0) (c 3) + dirArc o e c 0 3 4
      = ∠ (c 1) (c 0) (c 4) := by linarith
  have A103c : ∠ (c 0) (c 1) (c 3) =
      Real.pi - dirArc o e c 1 0 3 :=
    dirRep_arc_eq_pi_sub_angle o e he (ne 0 1 (by decide))
      (ne 3 1 (by decide)) hb103
  have A104c : ∠ (c 0) (c 1) (c 4) =
      Real.pi - dirArc o e c 1 0 4 :=
    dirRep_arc_eq_pi_sub_angle o e he (ne 0 1 (by decide))
      (ne 4 1 (by decide)) hb104
  have e104 : dirArc o e c 1 0 4 =
      dirArc o e c 1 0 3 + dirArc o e c 1 3 4 :=
    cyclicDiff_eq_add_of_le (hmem 1 0) (hmem 1 3) (hmem 1 4) h103
  have hU₁ : ∠ (c 0) (c 1) (c 3)
      = ∠ (c 0) (c 1) (c 4) + dirArc o e c 1 3 4 := by linarith
  have hA₁ : ∠ (c 0) (c 3) (c 1) = dirArc o e c 3 0 1 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb031
  -- detour 2: u=2, a=3, w=0, x=4
  have A023 : ∠ (c 2) (c 0) (c 3) = dirArc o e c 0 2 3 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb023
  have A024 : ∠ (c 2) (c 0) (c 4) = dirArc o e c 0 2 4 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb024
  have e024 : dirArc o e c 0 2 4 =
      dirArc o e c 0 2 3 + dirArc o e c 0 3 4 :=
    cyclicDiff_eq_add_of_le (hmem 0 2) (hmem 0 3) (hmem 0 4) h023
  have hW₂ : ∠ (c 2) (c 0) (c 3) + dirArc o e c 0 3 4
      = ∠ (c 2) (c 0) (c 4) := by linarith
  have A203c : ∠ (c 0) (c 2) (c 3) =
      Real.pi - dirArc o e c 2 0 3 :=
    dirRep_arc_eq_pi_sub_angle o e he (ne 0 2 (by decide))
      (ne 3 2 (by decide)) hb203
  have A204c : ∠ (c 0) (c 2) (c 4) =
      Real.pi - dirArc o e c 2 0 4 :=
    dirRep_arc_eq_pi_sub_angle o e he (ne 0 2 (by decide))
      (ne 4 2 (by decide)) hb204
  have e204 : dirArc o e c 2 0 4 =
      dirArc o e c 2 0 3 + dirArc o e c 2 3 4 :=
    cyclicDiff_eq_add_of_le (hmem 2 0) (hmem 2 3) (hmem 2 4) h203
  have hU₂ : ∠ (c 0) (c 2) (c 3)
      = ∠ (c 0) (c 2) (c 4) + dirArc o e c 2 3 4 := by linarith
  have hA₂ : ∠ (c 0) (c 3) (c 2) = dirArc o e c 3 0 2 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb032
  -- composed transfer: dirArc(1;3,4) hops to row 2
  have htr : dirArc o e c 1 3 4 = dirArc o e c 2 3 4
      + (dirArc o e c 3 0 2 - dirArc o e c 3 0 1)
      + (∠ (c 0) (c 4) (c 1) - ∠ (c 0) (c 4) (c 2)) :=
    detour_arc_compose o e hleg (by decide) (by decide)
      hW₁ hU₁ hA₁ hW₂ hU₂ hA₂
  have E41 : ∠ (c 0) (c 4) (c 1) = dirArc o e c 4 0 1 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb041
  have E42 : ∠ (c 0) (c 4) (c 2) = dirArc o e c 4 0 2 :=
    dirRep_arc_eq_angle o e hleg he
      (by decide) (by decide) (by decide) hb042
  have e302 : dirArc o e c 3 0 2 =
      dirArc o e c 3 0 1 + dirArc o e c 3 1 2 :=
    cyclicDiff_eq_add_of_le (hmem 3 0) (hmem 3 1) (hmem 3 2) h301
  have e402 : dirArc o e c 4 0 2 =
      dirArc o e c 4 0 1 + dirArc o e c 4 1 2 :=
    cyclicDiff_eq_add_of_le (hmem 4 0) (hmem 4 1) (hmem 4 2) h401
  have hnn22 : (0 : ℝ) ≤ dirArc o e c 2 3 4 :=
    cyclicDiff_nonneg (hmem 2 3).2 (hmem 2 4).1
  -- π = dirArc(1;0,3) + dirArc(2;3,4) + dirArc(3;1,2)
  --     − dirArc(4;1,2) + dirArc(1;4,0)
  --   ≥ λ + 0 + 2λ − λ + 3λ = 5λ
  linarith

/-! ### Receiving-arc floor dichotomy — defect-`2` rows

The `rnn` layer pushed one level deeper.  A defect-`2` row has exactly
two arithmetic types — Type I (`rowBig = 1`, `rowCells = n − 1`) and
Type II (`rowBig = 2`, `rowCells = n`).  Any consecutive-index arc `T`
carrying at most one primitive λ-cell while its gap length reaches `λ`
forces a primitive gap of floor `≥ n − 1` into `univ \ T`.  Two such
gaps cannot coexist (`2(n−1) > n ≥ cells`), so the position is pinned. -/


end Jsp404
