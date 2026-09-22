import Jsp000404.Section4Legality
import Jsp000404.MainTheorem

/-!
# Integration layer — the conditional pipeline downstream of gadget selection

This file is the seam between the (still open) *gadget-selection* theorem and
the already-formalized `StaircaseBound → sendov_count_bound` pipeline of
`Staircase.lean` / `Section4Legality.lean`.

## The hypothesis bundle `GadgetSelection`

Sendov's omitted optimization step (`staircase_of_legality`, whose `tail` field
is still `sorry`) needs two weighted-capacity bounds on the skeleton exponents.
In skeleton language, with `dᵢ = (n-1) - kᵢ` and `W = Σᵢ 2^{-dᵢ}`:

* `low`  regime: `W ≤ 2`   forces `δ < 1/2`;
* `high` regime: `W ≤ 5/2` forces `δ < 1`.

Since `W = Σᵢ 2^{kᵢ} / 2^{n-1}`, these translate into bounds on `Σᵢ 2^{kᵢ}`
where `kᵢ` are the staircase exponents `exponents V o e lam`. The gadget-
selection theorem (being proved on another lane from `Gadget.lean`) supplies
precisely these bounds; we therefore record them as the *hypothesis bundle*
`GadgetSelection`, stated at the level the staircase machinery consumes:

* `low`  : `δ < 1/2 → Σᵢ 2^{kᵢ} ≤ 2ⁿ`
* `high` : `δ < 1   → Σᵢ 2^{kᵢ} ≤ 2ⁿ + 2^{n-2}`

When `Gadget.lean` lands, the adapter proving `GadgetSelection` extracts the
center skeleton from `Section4Legality`, runs `gadgetSelection_low` /
`gadgetSelection_high`, and converts the selected gadget's score bound into the
`Σ 2^{kᵢ}` bound via `Gadget.cap_total` and the `exponents`-vs-skeleton
correspondence. Nothing downstream changes.

## What is proved here

* `exponents_lt_of_floor` — the `top` field of `StaircaseBound`, unconditional
  (extracted from `staircase_of_legality`).
* `staircaseBound_of_selection` — `GadgetSelection + Section4Legality →
  StaircaseBound`: weighted capacity becomes a *conditional* theorem, not a
  `sorry`.
* `count_bound_of_selection` / `count_bound_trivial_of_selection` —
  `GadgetSelection → |points| ≤ 2^{n'} + [δ ≥ 1/2]·2^{n'-2}`.
* `sendov_lower_three` — the `N = 3` lower bound, **unconditional**.
* `sendov_lower_of_selection` — the arbitrary-`N` lower bound, conditional on
  `GadgetSelection` (packages the trivial-GC plumbing, the Finset max-angle,
  the `δ`-dichotomy and all `Nat.clog` / real arithmetic).
* `sendov_of_hypotheses` — the root theorem, conditional on `GadgetSelection`
  plus the (still missing) upper-bound constructions `SendovUpper`.
-/

open scoped EuclideanGeometry

namespace Jsp404

/-! ## The hypothesis bundle -/

/-- The two selection consequences needed downstream, stated as hypotheses
rather than axioms. Both concern the staircase exponents `kᵢ` (= per-circle
`exponent` sums) of a legal disjoint-circle configuration `V` in the `n`-th
strip `π/λ ∈ [n, n+1)`, `δ = π/λ - n`:

* `low`  (the `δ < 1/2` regime): `Σᵢ 2^{kᵢ} ≤ 2ⁿ`;
* `high` (the `δ < 1` regime):  `Σᵢ 2^{kᵢ} ≤ 2ⁿ + 2^{n-2}`.

Via `W = Σᵢ 2^{(n-1)-kᵢ} = Σᵢ 2^{kᵢ} / 2^{n-1}` these are exactly the `W ≤ 2`
and `W ≤ 5/2` capacities of the skeleton model; the checker certifies
`δ_min ∈ {0, 1/2, 1}` in the complementary regimes, so selection is the
contrapositive. -/
structure GadgetSelection : Prop where
  /-- `W ≤ 2` forces `δ < 1/2`. -/
  low : ∀ (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
      {lam : ℝ} {n : ℕ},
      Section4Legality
        (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam →
      V.forest.Nodup →
      Nat.floor (Real.pi / lam) = n →
      Real.pi / lam - (n : ℝ) < 1 / 2 →
      ((exponents V o e lam).map (2 ^ ·)).sum ≤ 2 ^ n
  /-- `W ≤ 5/2` forces `δ < 1`. -/
  high : ∀ (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
      {lam : ℝ} {n : ℕ},
      Section4Legality
        (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam →
      V.forest.Nodup →
      Nat.floor (Real.pi / lam) = n →
      Real.pi / lam - (n : ℝ) < 1 →
      ((exponents V o e lam).map (2 ^ ·)).sum ≤ 2 ^ n + 2 ^ (n - 2)

/-! ## The `top` field, unconditional (extracted from `staircase_of_legality`) -/

/-- Every staircase exponent is strictly below `n`: the `top` field of
`StaircaseBound`, proved unconditionally via `exponent_le_floor`. -/
theorem exponents_lt_of_floor (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) {lam : ℝ} {n : ℕ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n) (hn1 : 1 ≤ n)
    (hfN : V.forest.Nodup) :
    ∀ k ∈ exponents V o e lam, k < n := by
  intro k hk
  rw [exponents, List.mem_map] at hk
  obtain ⟨ci, hci, rfl⟩ := hk
  have hle := exponent_le_floor (ds := circleDirs V o e ci)
    (circleDirs_sorted V o e ci) (circleDirs_nodup V o e ci)
    (fun x hx => circleDirs_mem_Ico V o e hx)
    (circleDirs_ne_nil V o e hfN hci) hlam
  rw [hn] at hle
  omega

/-! ## Conditional staircase and count bounds -/

/-- `GadgetSelection + legality ⇒ StaircaseBound`. The `top` field is proved;
the `tail` field is exactly the two selection capacities. This replaces the
`sorry` in `staircase_of_legality` with an explicit hypothesis. -/
theorem staircaseBound_of_selection (sel : GadgetSelection) (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) {lam : ℝ} {n : ℕ}
    (hlam : 0 < lam) (hleπ : lam ≤ Real.pi)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hfN : V.forest.Nodup)
    (hlegal : Section4Legality
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam) :
    StaircaseBound n (exponents V o e lam)
      (decide (1 / 2 ≤ Real.pi / lam - (n : ℝ))) := by
  have hn1 : 1 ≤ n := by
    have h1 : 1 ≤ Nat.floor (Real.pi / lam) := by
      rw [Nat.one_le_floor_iff, one_le_div_iff]
      exact Or.inl ⟨hlam, hleπ⟩
    omega
  have htop := exponents_lt_of_floor V o e hlam hn hn1 hfN
  refine ⟨htop, ?_⟩
  rw [← layerCake htop]
  simp only [decide_eq_true_eq]
  by_cases hδ : (1 : ℝ) / 2 ≤ Real.pi / lam - (n : ℝ)
  · rw [if_pos hδ]
    have hlt1 : Real.pi / lam - (n : ℝ) < 1 := by
      have h := Nat.lt_floor_add_one (Real.pi / lam)
      rw [hn] at h
      linarith
    exact sel.high V o e hlegal hfN hn hlt1
  · rw [if_neg hδ]
    simpa using sel.low V o e hlegal hfN hn (not_le.mp hδ)

/-- The packaged conditional count bound: a legal disjoint-circle
configuration in the `n`-th strip has
`|V.points| ≤ 2^{n'} + [δ ≥ 1/2]·2^{n'-2}` where `n' = ⌊π/λ⌋`. -/
theorem count_bound_of_selection (sel : GadgetSelection) (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hd : V.DisjointCircles) (hfN : V.forest.Nodup)
    (hcenters : ∀ g₁ ∈ V.forest, ∀ g₂ ∈ V.forest, g₁ ≠ g₂ →
      g₁.centerOf ≠ g₂.centerOf)
    (hnonempty : ∀ g ∈ V.forest, ∃ q, q ∈ g.points)
    (hptN : ∀ g ∈ V.forest, g.points.Nodup)
    (hGD : ∀ ci ∈ V.forest, ∀ p ∈ ci.points, ∀ q ∈ ci.points,
      p ≠ q → V.GD p q ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hGA : ∀ a ∈ V.points, ∀ b ∈ V.points, ∀ c ∈ V.points,
      a ≠ b → b ≠ c → a ≠ c → V.GA a b c ≤ Real.pi - lam) :
    V.points.length ≤
      2 ^ Nat.floor (Real.pi / lam) +
        (if (1 : ℝ) / 2 ≤ Real.pi / lam - Nat.floor (Real.pi / lam) then
          2 ^ (Nat.floor (Real.pi / lam) - 2) else 0) := by
  have hlegal := legality_of_GC V hd hfN hcenters hnonempty hlam hGA
  have hstair :=
    staircaseBound_of_selection sel V o e hlam hlampi.le rfl hfN hlegal
  have hcb := sendov_count_bound V o e he hd hfN hcenters hnonempty hptN hGD
    hlam hlampi hGA (Nat.floor (Real.pi / lam))
    (decide (1 / 2 ≤ Real.pi / lam - (Nat.floor (Real.pi / lam) : ℝ))) hstair
  simpa only [decide_eq_true_eq] using hcb

/-! ## Trivial-GC plumbing

A bare point list yields the trivial GC `GCfg.trivial pts`, all of whose
circles are singletons. We package the plumbing so the root theorem only
needs the angle bound `∀ distinct triples, ∠ p q r ≤ π - λ`. -/

lemma trivial_disjointCircles {pts : List Plane₂} (h : 2 ≤ pts.length) :
    (GCfg.trivial pts h).DisjointCircles := by
  intro g₁ hg₁ g₂ hg₂ hne p hp₁ hp₂
  obtain ⟨a, -, ha₁⟩ := List.mem_map.mp hg₁
  obtain ⟨b, -, hb₂⟩ := List.mem_map.mp hg₂
  subst ha₁; subst hb₂
  simp [GC.points] at hp₁ hp₂
  exact hne (congrArg GC.prim (hp₁.symm.trans hp₂))

lemma trivial_forest_nodup {pts : List Plane₂} (hnodup : pts.Nodup)
    (h : 2 ≤ pts.length) : (GCfg.trivial pts h).forest.Nodup :=
  hnodup.map fun {a b} h' => by simpa using h'

lemma trivial_centers_distinct {pts : List Plane₂} (h : 2 ≤ pts.length) :
    ∀ g₁ ∈ (GCfg.trivial pts h).forest, ∀ g₂ ∈ (GCfg.trivial pts h).forest,
      g₁ ≠ g₂ → g₁.centerOf ≠ g₂.centerOf := by
  intro g₁ hg₁ g₂ hg₂ hne hab
  obtain ⟨a, -, ha₁⟩ := List.mem_map.mp hg₁
  obtain ⟨b, -, hb₂⟩ := List.mem_map.mp hg₂
  subst ha₁; subst hb₂
  exact hne (congrArg GC.prim (show a = b from hab))

lemma trivial_nonempty {pts : List Plane₂} (h : 2 ≤ pts.length) :
    ∀ g ∈ (GCfg.trivial pts h).forest, ∃ q, q ∈ g.points := by
  intro g hg
  obtain ⟨a, -, ha⟩ := List.mem_map.mp hg
  subst ha
  exact ⟨a, by simp [GC.points]⟩

lemma trivial_points_nodup {pts : List Plane₂} (h : 2 ≤ pts.length) :
    ∀ g ∈ (GCfg.trivial pts h).forest, g.points.Nodup := by
  intro g hg
  obtain ⟨a, -, ha⟩ := List.mem_map.mp hg
  subst ha
  simp [GC.points]

lemma trivial_GD_ne {pts : List Plane₂} (h : 2 ≤ pts.length) :
    ∀ ci ∈ (GCfg.trivial pts h).forest, ∀ p ∈ ci.points, ∀ q ∈ ci.points,
      p ≠ q → (GCfg.trivial pts h).GD p q ≠ 0 := by
  intro ci hci p hp q hq hpq
  obtain ⟨a, -, ha⟩ := List.mem_map.mp hci
  subst ha
  simp [GC.points] at hp hq
  exact absurd (hp.trans hq.symm) hpq

/-- The conditional count bound specialized to a bare point list: if every
angle determined by three distinct points is `≤ π - λ`, then
`|pts| ≤ 2^{⌊π/λ⌋} + [δ ≥ 1/2]·2^{⌊π/λ⌋-2}` with `δ = π/λ - ⌊π/λ⌋`. -/
theorem count_bound_trivial_of_selection (sel : GadgetSelection)
    {pts : List Plane₂} (hnodup : pts.Nodup) (hlen : 2 ≤ pts.length)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hangle : ∀ p q r : Plane₂, p ∈ pts → q ∈ pts → r ∈ pts →
      p ≠ q → r ≠ q → p ≠ r → ∠ p q r ≤ Real.pi - lam) :
    pts.length ≤
      2 ^ Nat.floor (Real.pi / lam) +
        (if (1 : ℝ) / 2 ≤ Real.pi / lam - Nat.floor (Real.pi / lam) then
          2 ^ (Nat.floor (Real.pi / lam) - 2) else 0) := by
  classical
  let o : Orientation ℝ Plane₂ (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let e : Plane₂ := EuclideanSpace.basisFun (Fin 2) ℝ (0 : Fin 2)
  have he : e ≠ 0 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero _
  have hd := trivial_disjointCircles hlen
  have hfN := trivial_forest_nodup hnodup hlen
  have hcenters := trivial_centers_distinct hlen
  have hnonempty := trivial_nonempty hlen
  have hptN := trivial_points_nodup hlen
  have hGD := trivial_GD_ne hlen
  have hGA : ∀ a ∈ (GCfg.trivial pts hlen).points,
      ∀ b ∈ (GCfg.trivial pts hlen).points,
      ∀ c ∈ (GCfg.trivial pts hlen).points,
      a ≠ b → b ≠ c → a ≠ c →
        (GCfg.trivial pts hlen).GA a b c ≤ Real.pi - lam := by
    intro a ha b hb c hc hab hbc hac
    rw [GCfg.trivial_points pts hlen] at ha hb hc
    rw [GCfg.trivial_GA pts hlen ha hb hc hab hbc.symm]
    exact hangle a b c ha hb hc hab hbc.symm hac
  have hcb := count_bound_of_selection sel (GCfg.trivial pts hlen) o e he
    hd hfN hcenters hnonempty hptN hGD hlam hlampi hGA
  rw [GCfg.trivial_points pts hlen] at hcb
  simpa only [decide_eq_true_eq] using hcb

/-! ## `alphaN` arithmetic -/

/-- Unfold `alphaN` on the `N + 4` branch, with the `let` zeta-reduced. -/
lemma alphaN_succ_add (m : ℕ) :
    alphaN (m + 4) =
      if ((m : ℝ) + 4) ≤ 2 ^ (Nat.clog 2 (m + 4) - 1) +
          (2 : ℝ) ^ (((Nat.clog 2 (m + 4) - 1 : ℕ) : ℤ) - 2) then
        (1 - 2 / (2 * ((Nat.clog 2 (m + 4) - 1 : ℕ) : ℝ) + 1)) * Real.pi
      else
        (1 - 1 / (((Nat.clog 2 (m + 4) - 1 : ℕ) : ℝ) + 1)) * Real.pi :=
  rfl

/-- Unfold `alphaN` in the `N ≥ 4` branch, named by `n = Nat.clog 2 N - 1`. -/
lemma alphaN_of_ge_four {N n : ℕ} (hN : 4 ≤ N) (hn : n = Nat.clog 2 N - 1) :
    alphaN N = if (N : ℝ) ≤ 2 ^ n + 2 ^ ((n : ℤ) - 2) then
        (1 - 2 / (2 * n + 1 : ℝ)) * Real.pi
      else (1 - 1 / ((n : ℝ) + 1)) * Real.pi := by
  subst hn
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
  rw [alphaN_succ_add]
  simp only [Nat.cast_add, Nat.cast_ofNat]

/-- `alphaN N < π` for `N ≥ 4`. -/
lemma alphaN_lt_pi {N : ℕ} (hN : 4 ≤ N) : alphaN N < Real.pi := by
  rw [alphaN_of_ge_four hN (n := Nat.clog 2 N - 1) rfl]
  by_cases h : (N : ℝ) ≤ 2 ^ (Nat.clog 2 N - 1) +
      (2 : ℝ) ^ (((Nat.clog 2 N - 1 : ℕ) : ℤ) - 2)
  · rw [if_pos h]
    have hx : (0 : ℝ) < 2 / (2 * ((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1) := by
      positivity
    calc (1 - 2 / (2 * ((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1)) * Real.pi
        < 1 * Real.pi := by
          apply mul_lt_mul_of_pos_right _ Real.pi_pos
          linarith
      _ = Real.pi := one_mul _
  · rw [if_neg h]
    have hx : (0 : ℝ) < 1 / (((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1) := by
      positivity
    calc (1 - 1 / (((Nat.clog 2 N - 1 : ℕ) : ℝ) + 1)) * Real.pi
        < 1 * Real.pi := by
          apply mul_lt_mul_of_pos_right _ Real.pi_pos
          linarith
      _ = Real.pi := one_mul _

/-! ## Ordered triples of distinct points -/

/-- The finite set of ordered triples `((p, q), r)` of distinct points of
`pts`, with `q` the angle vertex. -/
noncomputable def distinctTriples (pts : List Plane₂) :
    Finset ((Plane₂ × Plane₂) × Plane₂) :=
  ((pts.toFinset ×ˢ pts.toFinset) ×ˢ pts.toFinset).filter
    fun t => t.1.1 ≠ t.1.2 ∧ t.2 ≠ t.1.2 ∧ t.1.1 ≠ t.2

lemma mem_distinctTriples {pts : List Plane₂}
    {t : (Plane₂ × Plane₂) × Plane₂} :
    t ∈ distinctTriples pts ↔
      t.1.1 ∈ pts ∧ t.1.2 ∈ pts ∧ t.2 ∈ pts ∧
        t.1.1 ≠ t.1.2 ∧ t.2 ≠ t.1.2 ∧ t.1.1 ≠ t.2 := by
  simp only [distinctTriples, Finset.mem_filter, Finset.mem_product,
    List.mem_toFinset]
  tauto

/-! ## The `N = 3` lower bound, unconditional -/

/-- `N = 3`: three distinct points always determine an angle `≥ π/3`.
Unconditional. -/
theorem sendov_lower_three (C : PtCfg) (hlen : C.pts.length = 3) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN 3 ≤ ∠ p q r := by
  obtain ⟨a, b, c, hpts⟩ := List.length_eq_three.mp hlen
  have hnd : [a, b, c].Nodup := hpts ▸ C.nodup
  rw [List.nodup_cons] at hnd
  obtain ⟨hna, hnd⟩ := hnd
  rw [List.nodup_cons] at hnd
  obtain ⟨hnb, -⟩ := hnd
  have hab : a ≠ b := fun h => hna (List.mem_cons.mpr (Or.inl h))
  have hac : a ≠ c := fun h =>
    hna (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr h)))
  have hbc : b ≠ c := fun h => hnb (List.mem_singleton.mpr h)
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi c hab.symm
  have hα : alphaN 3 = Real.pi / 3 := rfl
  have ha_mem : a ∈ C.pts := by rw [hpts]; simp
  have hb_mem : b ∈ C.pts := by rw [hpts]; simp
  have hc_mem : c ∈ C.pts := by rw [hpts]; simp
  rcases lt_or_ge (∠ a b c) (Real.pi / 3) with hlt1 | hge1
  · rcases lt_or_ge (∠ b c a) (Real.pi / 3) with hlt2 | hge2
    · rcases lt_or_ge (∠ c a b) (Real.pi / 3) with hlt3 | hge3
      · exfalso; linarith [Real.pi_pos]
      · exact ⟨c, a, b, hc_mem, ha_mem, hb_mem, hac.symm, hab.symm, hbc.symm,
          by rw [hα]; exact hge3⟩
    · exact ⟨b, c, a, hb_mem, hc_mem, ha_mem, hbc, hac, hab.symm,
        by rw [hα]; exact hge2⟩
  · exact ⟨a, b, c, ha_mem, hb_mem, hc_mem, hab, hbc.symm, hac,
      by rw [hα]; exact hge1⟩

/-! ## The conditional lower bound for arbitrary `N` -/

/-- The conditional Sendov lower bound: assuming `GadgetSelection`, every
`PtCfg` of `N ≥ 3` distinct points determines an angle `≥ alphaN N`.

Proof sketch: assume all angles `< alphaN N`. The maximum `M = ∠p₀q₀r₀` of the
finitely many distinct-triple angles gives `lam = π - M ∈ (0, π)` with every
angle `≤ π - lam`. The trivial GC turns `C.pts` into a disjoint-circle legal
configuration; `count_bound_trivial_of_selection` yields
`N ≤ 2^{n'} + [δ' ≥ 1/2]·2^{n'-2}` with `n' = ⌊π/lam⌋`. Since
`M < alphaN N`, `lam` exceeds `π - alphaN N`, which forces `n' ≤ n` where
`n = Nat.clog 2 N - 1`; case analysis on `n' < n` versus `n' = n` and on the
two `alphaN` branches contradicts `2^n < N ≤ 2^{n+1}`. -/
theorem sendov_lower_of_selection (sel : GadgetSelection) {N : ℕ}
    (hN : 3 ≤ N) (C : PtCfg) (hlen : C.pts.length = N) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  rcases eq_or_ne N 3 with rfl | hN3
  · exact sendov_lower_three C hlen
  have hN4 : 4 ≤ N := by omega
  by_contra hcon
  push Not at hcon
  classical
  -- The finite set of distinct-triple angles is nonempty (take pts[0,1,2]).
  have hT : (distinctTriples C.pts).Nonempty := by
    refine ⟨(⟨C.pts.get ⟨0, by omega⟩, C.pts.get ⟨1, by omega⟩⟩,
        C.pts.get ⟨2, by omega⟩), ?_⟩
    rw [mem_distinctTriples]
    refine ⟨List.get_mem _ _, List.get_mem _ _, List.get_mem _ _, ?_, ?_, ?_⟩
    · exact C.nodup.get_inj_iff.not.mpr
        fun h => absurd (congrArg Fin.val h) (by decide : ¬(0 : ℕ) = 1)
    · exact C.nodup.get_inj_iff.not.mpr
        fun h => absurd (congrArg Fin.val h) (by decide : ¬(2 : ℕ) = 1)
    · exact C.nodup.get_inj_iff.not.mpr
        fun h => absurd (congrArg Fin.val h) (by decide : ¬(0 : ℕ) = 2)
  -- `M = ∠ p₀ q₀ r₀` = largest determined angle; `M < alphaN N` by `hcon`.
  obtain ⟨⟨⟨p₀, q₀⟩, r₀⟩, ht₀, hmax⟩ :=
    Finset.exists_max_image (distinctTriples C.pts)
      (fun t => ∠ t.1.1 t.1.2 t.2) hT
  rw [mem_distinctTriples] at ht₀
  obtain ⟨hp₀, hq₀, hr₀, hpq₀, hrq₀, hpr₀⟩ := ht₀
  have hMlt : ∠ p₀ q₀ r₀ < alphaN N := hcon p₀ q₀ r₀ hp₀ hq₀ hr₀ hpq₀ hrq₀ hpr₀
  have hMpos : 0 < ∠ p₀ q₀ r₀ := by
    have hsum :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi r₀ hpq₀.symm
    have h2 : ∠ q₀ r₀ p₀ ≤ ∠ p₀ q₀ r₀ :=
      hmax ((q₀, r₀), p₀) (mem_distinctTriples.mpr
        ⟨hq₀, hr₀, hp₀, hrq₀.symm, hpr₀, hpq₀.symm⟩)
    have h3 : ∠ r₀ p₀ q₀ ≤ ∠ p₀ q₀ r₀ :=
      hmax ((r₀, p₀), q₀) (mem_distinctTriples.mpr
        ⟨hr₀, hp₀, hq₀, hpr₀.symm, hpq₀.symm, hrq₀⟩)
    linarith [Real.pi_pos]
  -- `lam = π - M` sits in `(0, π)`.
  generalize hlamdef : Real.pi - ∠ p₀ q₀ r₀ = lam
  have hlam : 0 < lam := by
    rw [← hlamdef]
    exact sub_pos.mpr (hMlt.trans (alphaN_lt_pi hN4))
  have hlampi : lam < Real.pi := by rw [← hlamdef]; linarith [hMpos]
  have hangle : ∀ p q r : Plane₂, p ∈ C.pts → q ∈ C.pts → r ∈ C.pts →
      p ≠ q → r ≠ q → p ≠ r → ∠ p q r ≤ Real.pi - lam := by
    intro p q r hp hq hr hpq hrq hpr
    have hle : ∠ p q r ≤ ∠ p₀ q₀ r₀ :=
      hmax ((p, q), r) (mem_distinctTriples.mpr ⟨hp, hq, hr, hpq, hrq, hpr⟩)
    rw [← hlamdef]
    linarith
  -- Apply the conditional count bound at `n' = ⌊π/lam⌋`.
  have hcb := count_bound_trivial_of_selection sel C.nodup
    (by omega : 2 ≤ C.pts.length) hlam hlampi hangle
  rw [hlen] at hcb
  generalize hndef : Nat.clog 2 N - 1 = n
  generalize hn' : Nat.floor (Real.pi / lam) = n'
  rw [hn'] at hcb
  -- `2^n < N ≤ 2^{n+1}` from `Nat.clog`.
  have hk2 : 2 ≤ Nat.clog 2 N := by
    have hmono := Nat.clog_mono_right 2 hN4
    have h4 : Nat.clog 2 4 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl]
      exact Nat.clog_pow 2 2 (by norm_num)
    omega
  have hn1 : 1 ≤ n := by omega
  have hNlo : 2 ^ n < N :=
    Nat.pow_lt_of_lt_clog (by omega : n < Nat.clog 2 N)
  have hNhi : N ≤ 2 ^ (n + 1) := by
    have hclog : Nat.clog 2 N = n + 1 := by omega
    rw [← hclog]
    exact Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) N
  rw [alphaN_of_ge_four hN4 hndef.symm] at hMlt
  -- Case split on which `alphaN` branch applies.
  by_cases hbr : (N : ℝ) ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ ((n : ℤ) - 2)
  · -- branch A: `alphaN N = (1 - 2/(2n+1))·π`, so `π/lam < n + 1/2`.
    rw [if_pos hbr] at hMlt
    have hlow : 2 * Real.pi / (2 * n + 1) < lam := by
      have hrewrite : Real.pi - (1 - 2 / (2 * n + 1 : ℝ)) * Real.pi
          = 2 * Real.pi / (2 * n + 1) := by
        have h2n : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
        field_simp
        ring
      rw [← hlamdef, ← hrewrite]
      exact sub_lt_sub_left hMlt Real.pi
    have hfrac : Real.pi / lam < (n : ℝ) + 1 / 2 := by
      rw [div_lt_iff₀ hlam]
      have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have key : ((n : ℝ) + 1 / 2) * (2 * Real.pi / (2 * n + 1)) = Real.pi := by
        field_simp
      rw [← key]
      exact mul_lt_mul_of_pos_left hlow (by positivity)
    have hn'le : n' ≤ n := by
      have h2 : n' < n + 1 := by
        rw [← hn', Nat.floor_lt (div_nonneg Real.pi_pos.le hlam.le)]
        push_cast
        linarith
      omega
    rcases lt_or_eq_of_le hn'le with hlt | heq
    · -- `n' < n`: bound `≤ 2^{n'+1} ≤ 2^n < N`, contradiction.
      have hb : (2 : ℕ) ^ n' +
          (if (1 : ℝ) / 2 ≤ Real.pi / lam - (n' : ℝ) then 2 ^ (n' - 2) else 0)
          ≤ 2 ^ n := by
        by_cases hδ : (1 : ℝ) / 2 ≤ Real.pi / lam - (n' : ℝ)
        · rw [if_pos hδ]
          calc 2 ^ n' + 2 ^ (n' - 2) ≤ 2 ^ n' + 2 ^ n' := by
                gcongr
                exact Nat.sub_le _ _
            _ = 2 ^ (n' + 1) := by rw [pow_succ]; ring
            _ ≤ 2 ^ n :=
                Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) (by omega)
        · rw [if_neg hδ]
          simp
          exact Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2)
            (le_of_lt hlt)
      exact (not_le.mpr hNlo) (hcb.trans hb)
    · -- `n' = n` and `δ' < 1/2`: bound `= 2^n < N`, contradiction.
      rw [heq] at hcb
      have hδ : ¬ (1 : ℝ) / 2 ≤ Real.pi / lam - (n : ℝ) := by
        rw [not_le]
        linarith
      rw [if_neg hδ] at hcb
      simp at hcb
      exact (not_le.mpr hNlo) hcb
  · -- branch B: `alphaN N = (1 - 1/(n+1))·π`, so `π/lam < n + 1`.
    rw [if_neg hbr] at hMlt
    have hlow : Real.pi / (n + 1) < lam := by
      have hrewrite : Real.pi - (1 - 1 / ((n : ℝ) + 1)) * Real.pi
          = Real.pi / (n + 1) := by
        have hnn : ((n : ℝ) + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [← hlamdef, ← hrewrite]
      exact sub_lt_sub_left hMlt Real.pi
    have hfrac : Real.pi / lam < (n : ℝ) + 1 := by
      rw [div_lt_iff₀ hlam]
      have hnn : ((n : ℝ) + 1) ≠ 0 := by positivity
      have key : ((n : ℝ) + 1) * (Real.pi / (n + 1)) = Real.pi := by
        field_simp
      rw [← key]
      exact mul_lt_mul_of_pos_left hlow (by positivity)
    have hn'le : n' ≤ n := by
      have h2 : n' < n + 1 := by
        rw [← hn', Nat.floor_lt (div_nonneg Real.pi_pos.le hlam.le)]
        push_cast
        linarith
      omega
    rcases lt_or_eq_of_le hn'le with hlt | heq
    · -- `n' < n`: same uniform bound.
      have hb : (2 : ℕ) ^ n' +
          (if (1 : ℝ) / 2 ≤ Real.pi / lam - (n' : ℝ) then 2 ^ (n' - 2) else 0)
          ≤ 2 ^ n := by
        by_cases hδ : (1 : ℝ) / 2 ≤ Real.pi / lam - (n' : ℝ)
        · rw [if_pos hδ]
          calc 2 ^ n' + 2 ^ (n' - 2) ≤ 2 ^ n' + 2 ^ n' := by
                gcongr
                exact Nat.sub_le _ _
            _ = 2 ^ (n' + 1) := by rw [pow_succ]; ring
            _ ≤ 2 ^ n :=
                Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) (by omega)
        · rw [if_neg hδ]
          simp
          exact Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2)
            (le_of_lt hlt)
      exact (not_le.mpr hNlo) (hcb.trans hb)
    · -- `n' = n`: need `N > 2^n + 2^{n-2}` (ℕ), from `hbr` (ℝ).
      rw [heq] at hcb
      have hNgt : (2 : ℕ) ^ n + 2 ^ (n - 2) < N := by
        have hreal : (2 : ℝ) ^ n + 2 ^ ((n : ℤ) - 2) < (N : ℝ) :=
          lt_of_not_ge hbr
        by_cases hn1' : n = 1
        · subst hn1'
          have h3 : (2 : ℕ) ^ 1 + 2 ^ (1 - 2) = 3 := by norm_num
          rw [h3]
          omega
        · have hn2 : 2 ≤ n := by omega
          have hpow : (2 : ℝ) ^ ((n : ℤ) - 2) = ((2 ^ (n - 2) : ℕ) : ℝ) := by
            have hh : ((n : ℤ) - 2) = (((n - 2 : ℕ) : ℤ)) := by omega
            rw [hh, zpow_natCast]
            norm_cast
          rw [hpow] at hreal
          have hpow2 : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by norm_cast
          rw [← hpow2] at hreal
          exact_mod_cast hreal
      have hb : (2 : ℕ) ^ n +
          (if (1 : ℝ) / 2 ≤ Real.pi / lam - (n : ℝ) then 2 ^ (n - 2) else 0)
          ≤ 2 ^ n + 2 ^ (n - 2) :=
        Nat.add_le_add_left (by split <;> simp) _
      exact (not_le.mpr hNgt) (hcb.trans hb)

/-! ## The conditional root theorem -/

/-- The sharpness hypothesis (Sendov's extremal constructions): for every
`N ≥ 3` there is a configuration all of whose determined angles are
`≤ alphaN N`. This is the second missing ingredient besides
`GadgetSelection`. -/
def SendovUpper : Prop :=
  ∀ N : ℕ, 3 ≤ N → ∃ C : PtCfg, C.pts.length = N ∧
    ∀ p q r : Plane₂, p ∈ C.pts → q ∈ C.pts → r ∈ C.pts →
      p ≠ q → r ≠ q → p ≠ r → ∠ p q r ≤ alphaN N

/-- Conditional root theorem: `GadgetSelection + SendovUpper` gives the full
Sendov minimax statement — both halves of `MainTheorem.sendov_lower` /
`MainTheorem.sendov_upper` for every `N ≥ 3`. -/
theorem sendov_of_hypotheses (sel : GadgetSelection) (hup : SendovUpper)
    (N : ℕ) (hN : 3 ≤ N) :
    (∀ C : PtCfg, C.pts.length = N →
      ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r) ∧
    (∃ C : PtCfg, C.pts.length = N ∧
      ∀ p q r : Plane₂, p ∈ C.pts → q ∈ C.pts → r ∈ C.pts →
        p ≠ q → r ≠ q → p ≠ r → ∠ p q r ≤ alphaN N) :=
  ⟨fun C hC => sendov_lower_of_selection sel hN C hC, hup N hN⟩

end Jsp404
