import Jsp000404.Staircase
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Section-4 legality — the exact contract on the range-1 center system

Sendov's Lemma 3.5 gives `GA(V) = max{A, μ, π - φ}` where `A` is the
maximal angle over center triples, `μ` the maximal internal generalized
angle, and `φ` the margin between internal directions and center lines.
The hypothesis `GA(V) ≤ π - λ` therefore forces, on the top-level center
system `Q = {o₁, …, oₛ}`:

* `A(Q) ≤ π - λ` — every triangle of range-1 centers has all angles
  `≤ π - λ` (Lemma 3.5, case 1: `GA p q r = ∠ oᵢ oⱼ oₖ` for points in
  three different circles).

Equivalently `∠jik + ∠ijk ≥ λ` for *every* triple — the facing-gap
lower bound of (4.12) for every third vertex, not just the extreme
one.  This is the *exact* contract: nothing stronger (in particular
not the sampler's full two-sided angle window, whose lower bound
`α ≥ λ` is not a consequence of `GA ≤ π - λ`) and nothing weaker.

`Section4Legality` packages precisely these provable consequences;
`legality_of_GC` discharges them from the GC hypotheses used by
`total_points_bound`.  `staircase_of_legality` is the missing piece of
Sendov's proof — the optimization he asserted without argument in
Lemma 4.1 ("the maximum is achieved if …").

Empirical status of the target (`check_staircase.lean`, ~10⁵ samples):
under exactly this contract (triangle upper bound only, `modA`), the
weighted budget `Σᵢ 2^{k'(i)} ≤ 2^n + 2^{n-2}·[big]` held for **every**
sampled configuration — all `n ∈ {3,4,5}`, both `δ` regimes, and all
`s ≤ 2n+2`.  Arbitrary (illegal) configurations violate it.
-/

open scoped EuclideanGeometry

namespace Jsp404

/-- **Section-4 legality**: the properties `GA(V) ≤ π - λ` forces on the
range-1 center system `c : Fin s → Plane₂` with `lam = 2π/u`.  All
fields are provable consequences of the GC hypotheses — see
`legality_of_GC`. -/
structure Section4Legality {s : ℕ} (c : Fin s → Plane₂) (lam : ℝ) : Prop
    where
  /-- `λ > 0`. -/
  lam_pos : 0 < lam
  /-- Centers are pairwise distinct (GC circle distinctness). -/
  inj : Function.Injective c
  /-- **Triangle bound** (Lemma 3.5, case 1): every angle of every center
  triangle is `≤ π - λ`.  Equivalently `∠jik + ∠ijk ≥ λ` for every
  triple — the facing-gap lower bound, for all third vertices. -/
  triAngle : ∀ i j k : Fin s, i ≠ j → j ≠ k → i ≠ k →
    ∠ (c i) (c j) (c k) ≤ Real.pi - lam

/-- **Facing-angle lower bound** — the left half of (4.12), for *every*
triple: the two angles adjacent to edge `(i, j)` sum to `≥ λ`
(`∠jik + ∠ijk = π - ∠ikj ≥ λ`).  This is the contract the gap
analysis consumes. -/
lemma Section4Legality.facing_lower {s : ℕ} {c : Fin s → Plane₂}
    {lam : ℝ} (h : Section4Legality c lam) {i j k : Fin s}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    lam ≤ ∠ (c j) (c i) (c k) + ∠ (c i) (c j) (c k) := by
  have hk := h.triAngle i k j hik (Ne.symm hjk) hij
  have hcij : c i ≠ c j := fun e => hij (h.inj e)
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₃ := c k) hcij
  rw [EuclideanGeometry.angle_comm (c k) (c j) (c i)] at hsum
  linarith

/-- **The GC → legality bridge.** The GC well-formedness hypotheses and
the `GA ≤ π - λ` bound of `total_points_bound` yield Section-4 legality
of the range-1 center system. -/
theorem legality_of_GC (V : GCfg)
    (hd : V.DisjointCircles) (hfN : V.forest.Nodup)
    (hcenters : ∀ g₁ ∈ V.forest, ∀ g₂ ∈ V.forest, g₁ ≠ g₂ →
      g₁.centerOf ≠ g₂.centerOf)
    (hnonempty : ∀ g ∈ V.forest, ∃ q, q ∈ g.points)
    {lam : ℝ} (hlam : 0 < lam)
    (hGA : ∀ a ∈ V.points, ∀ b ∈ V.points, ∀ c ∈ V.points,
      a ≠ b → b ≠ c → a ≠ c → V.GA a b c ≤ Real.pi - lam) :
    Section4Legality
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam where
  lam_pos := hlam
  inj := by
    intro i j h
    by_contra hne
    have hgn : V.forest.get i ≠ V.forest.get j :=
      fun hgg => hne (List.nodup_iff_injective_get.mp hfN hgg)
    exact absurd h (hcenters _ (List.get_mem _ _) _ (List.get_mem _ _)
      hgn)
  triAngle := by
    intro i j k hij hjk hik
    have hinj := List.nodup_iff_injective_get.mp hfN
    have hgij : V.forest.get i ≠ V.forest.get j := fun e => hij (hinj e)
    have hgjk : V.forest.get j ≠ V.forest.get k := fun e => hjk (hinj e)
    have hgik : V.forest.get i ≠ V.forest.get k := fun e => hik (hinj e)
    obtain ⟨p, hp⟩ := hnonempty _ (List.get_mem _ _)
    obtain ⟨q, hq⟩ := hnonempty _ (List.get_mem _ _)
    obtain ⟨r, hr⟩ := hnonempty _ (List.get_mem _ _)
    have hf_p := find?_eq_of_mem V hd (List.get_mem _ _) hp
    have hf_q := find?_eq_of_mem V hd (List.get_mem _ _) hq
    have hf_r := find?_eq_of_mem V hd (List.get_mem _ _) hr
    have hq1 : q ∉ (V.forest.get i).points :=
      V.not_mem_of_disjoint hd (List.get_mem _ _) (List.get_mem _ _)
        hgij hq
    have hp2 : p ∉ (V.forest.get j).points :=
      V.not_mem_of_disjoint hd (List.get_mem _ _) (List.get_mem _ _)
        hgij.symm hp
    have hr2 : r ∉ (V.forest.get j).points :=
      V.not_mem_of_disjoint hd (List.get_mem _ _) (List.get_mem _ _)
        hgjk hr
    have hq3 : q ∉ (V.forest.get k).points :=
      V.not_mem_of_disjoint hd (List.get_mem _ _) (List.get_mem _ _)
        hgjk.symm hq
    have hr1 : r ∉ (V.forest.get i).points :=
      V.not_mem_of_disjoint hd (List.get_mem _ _) (List.get_mem _ _)
        hgik hr
    have hpq : p ≠ q := fun e => hq1 (e ▸ hp)
    have hqr : q ≠ r := fun e => hq3 (e.symm ▸ hr)
    have hpr : p ≠ r := fun e => hr1 (e ▸ hp)
    have e := V.GA_three_circles hf_p hf_q hf_r hq1 hp2 hr2 hq3
    have hpV : p ∈ V.points :=
      List.mem_flatMap.mpr ⟨_, List.get_mem _ _, hp⟩
    have hqV : q ∈ V.points :=
      List.mem_flatMap.mpr ⟨_, List.get_mem _ _, hq⟩
    have hrV : r ∈ V.points :=
      List.mem_flatMap.mpr ⟨_, List.get_mem _ _, hr⟩
    have hle := hGA p hpV q hqV r hrV hpq hqr hpr
    rw [e] at hle
    exact hle

/-- **The Section-4 crux** (Sendov's unproved "the maximum is achieved
if …"): legality of the center system yields the staircase bound on the
exponent list.  The `top` field is proved unconditionally via
`exponent_le_floor`; `tail` is the isolated missing argument.

The `big` flag is tied to the regime: `big = true` iff the fractional
part `δ = π/λ - n` satisfies `1/2 ≤ δ`.  Without this coupling the
`big = false` instance is false (certified counterexample below). -/
theorem staircase_of_legality (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) {lam : ℝ} (n : ℕ)
    (big : Bool) (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hbig : big = decide (1 / 2 ≤ Real.pi / lam - n))
    (hfN : V.forest.Nodup)
    (hlegal : Section4Legality
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam) :
    StaircaseBound n (exponents V o e lam) big := by
  have hn1 : 1 ≤ n := by
    have h1 : 1 ≤ Nat.floor (Real.pi / lam) := by
      rw [Nat.one_le_floor_iff, one_le_div_iff]
      exact Or.inl ⟨hlam, le_of_lt hlampi⟩
    omega
  refine ⟨?_, ?_⟩
  · -- top : k'(i) ≤ ⌊π/lam⌋ - 1 = n - 1, unconditionally
    intro k hk
    rw [exponents, List.mem_map] at hk
    obtain ⟨ci, hci, rfl⟩ := hk
    have hle := exponent_le_floor (ds := circleDirs V o e ci)
      (circleDirs_sorted V o e ci) (circleDirs_nodup V o e ci)
      (fun x hx => circleDirs_mem_Ico V o e hx)
      (circleDirs_ne_nil V o e hfN hci) hlam
    rw [hn] at hle
    omega
  · -- tail : the weighted budget — Sendov's omitted optimization.
    -- COUNTEREXAMPLE NOTE (falsification audit): as stated, the `big := false`
    -- instance of this theorem is FALSE for `δ = π/lam - n ≥ 1/2`.  Take
    -- `V = GCfg.trivial [p₀, p₁, p₂, p₃]` with
    --   p₀ = (0,0), p₁ = (1,0), p₂ = (1.365, 0.476), p₃ = (1.272, 0.824)
    -- and `lam = π/3.9` (so `n = ⌊π/lam⌋ = 3`, `δ = 0.9`).  All twelve
    -- center-triangle angles are `≤ 2.2263 < 2.3361 = π - lam` (interval-
    -- certified), so `Section4Legality` holds; the exponent list is
    -- `ks = [2,1,1,1]` (gap quotients `3.186, 2.346, 2.042, 2.339` etc. all
    -- strictly off integer boundaries), giving
    --   `tail = 4 + (2⁰·N(1) + 2¹·N(2)) = 4 + (4 + 2) = 10 ≰ 8 = 2³`.
    -- Hence the universally-quantified `big` cannot be proved: the no-bonus
    -- bound `Σᵢ 2^{kᵢ} ≤ 2^n` is the `δ < 1/2` statement only.  The
    -- correction requires tying `big` to the regime, e.g.
    --   `hbig : big = decide (1/2 ≤ Real.pi / lam - n)`,
    -- under which the remaining content is Sendov's actual omitted
    -- optimization (checker-validated; the gadget/deletion crux).
    sorry

end Jsp404
