import Jsp000404.ProperGaps

/-!
# Strict-remainder normalization of closed ModeA models

`ProperGaps.lean` eliminated negative integer cells (`q = -1, r = 1`)
from a proper closed-remainder model, keeping `0 ≤ r ≤ 1`.  This module
closes the complementary boundary: cells with `r = 1`.  Per cell,

    ε_xg = 1 if r_xg = 1 else 0,   q'_xg = q_xg + ε_xg,   r'_xg = r_xg − ε_xg,

i.e. `(q, 1) ↦ (q + 1, 0)` and every other cell is unchanged.  The map
preserves `pos`, `bits`, the actual gaps `q + r`, `n`, `δ` and therefore
every `angleExpr`, the fan equality, the triangle sums and both angle
bounds.  The output remainder is *strict*: `0 ≤ r' < 1`.

Boundary cases: `(−1, 1) ↦ (0, 0)` — the same target as
`Skeleton.nonnegative` — so under `ModeA + Proper + 0 ≤ δ` the strictified
skeleton is already nonnegative (`strictify_q_nonneg_of_modeA`), and the
two normalizations commute (`nonnegative_strictify_eq`,
`strictify_nonneg_eq_self`).

The weight `W` is **not** preserved in general: `kexp` counts
`max (q − 1) 0`, and `(1, 1) ↦ (2, 0)` raises that cell's score from `0`
to `1`, doubling its dyadic term.  We prove `sk.W n ≤ (sk.strictify r).W n`
(`Skeleton.W_le_strictify_W`), with a strict-increase regression fixture
(`bSk3`), and the capacity transfer `capacity_of_strict_models`:
a `W ≤ B` bound quantified over proper strict-remainder models bounds
every proper closed-remainder model via `W sk ≤ W sk' ≤ B`.

"Strict" means only `r < 1` — no positive gaps, no strict angle bounds,
no general position, and no `δ ≠ 1/2` is claimed.
-/

namespace Jsp404

/-! ## Extensionality helpers -/

/-- `Skeleton` equality from `vtx` equality (the structures have no
`@[ext]` lemmas upstream). -/
lemma Skeleton.ext {s : ℕ} {a b : Skeleton s} (h : a.vtx = b.vtx) :
    a = b := by
  cases a; cases b; simp_all

/-- `VertexData` equality from field equality. -/
lemma VertexData.ext {s : ℕ} {v w : VertexData s}
    (hpos : v.pos = w.pos) (hbits : v.bits = w.bits) (hq : v.q = w.q) :
    v = w := by
  cases v; cases w; simp_all

/-! ## The strictify construction -/

/-- Shift each closed-boundary cell `(q, 1)` to `(q + 1, 0)`.
`pos` and `bits` are untouched, so `Proper` carries over verbatim.
(`noncomputable` because `Decidable (r x g = 1)` on `ℝ` is classical.) -/
noncomputable def Skeleton.strictify {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) : Skeleton s where
  vtx x := { sk.vtx x with
    q := fun g => (sk.vtx x).q g + if r x g = 1 then 1 else 0 }

/-- The strict remainder `r' = r − ε`: `0` on `r = 1` cells, `r` else. -/
noncomputable def Skeleton.strictR {s : ℕ} (_sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) : Fin s → Fin (s - 1) → ℝ :=
  fun x g => r x g - if r x g = 1 then 1 else 0

lemma Skeleton.strictify_proper {s : ℕ} {sk : Skeleton s}
    (r : Fin s → Fin (s - 1) → ℝ) (hp : sk.Proper) :
    (sk.strictify r).Proper := hp

/-- The actual gap is preserved cell-wise: `q' + r' = q + r`. -/
lemma Skeleton.strictify_gap {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1)) :
    (((sk.strictify r).vtx x).q g : ℝ) + sk.strictR r x g =
      ((sk.vtx x).q g : ℝ) + r x g := by
  show ((↑((sk.vtx x).q g + if r x g = 1 then (1 : ℤ) else 0)) : ℝ) +
      (r x g - if r x g = 1 then (1 : ℝ) else 0) =
    ((sk.vtx x).q g : ℝ) + r x g
  by_cases h : r x g = 1
  · rw [ite_eq_left h, ite_eq_left h, h]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    push_cast
    ring

/-- `0 ≤ r'` whenever `0 ≤ r`. -/
lemma Skeleton.strictR_nn {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (hnn : ∀ x g, 0 ≤ r x g)
    (x : Fin s) (g : Fin (s - 1)) : 0 ≤ sk.strictR r x g := by
  show 0 ≤ r x g - if r x g = 1 then (1 : ℝ) else 0
  by_cases h : r x g = 1
  · rw [ite_eq_left h, h]; norm_num
  · rw [ite_eq_right h]; simpa using hnn x g

/-- `r' < 1` whenever `r ≤ 1`: either `r = 1` and `r' = 0`, or `r < 1`
and the cell is unchanged. -/
lemma Skeleton.strictR_lt_one {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (hle : ∀ x g, r x g ≤ 1)
    (x : Fin s) (g : Fin (s - 1)) : sk.strictR r x g < 1 := by
  show r x g - (if r x g = 1 then (1 : ℝ) else 0) < 1
  by_cases h : r x g = 1
  · rw [ite_eq_left h, h]; norm_num
  · rw [ite_eq_right h, sub_zero]
    exact lt_of_le_of_ne (hle x g) h

/-- `r' ≤ 1` (the `ModeA` closed-boundary field). -/
lemma Skeleton.strictR_le_one {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (hle : ∀ x g, r x g ≤ 1)
    (x : Fin s) (g : Fin (s - 1)) : sk.strictR r x g ≤ 1 :=
  (sk.strictR_lt_one r hle x g).le

/-- `q'` only grows: `q ≤ q'`. -/
lemma Skeleton.strictify_q_ge {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1)) :
    (sk.vtx x).q g ≤ ((sk.strictify r).vtx x).q g := by
  show (sk.vtx x).q g ≤ (sk.vtx x).q g + if r x g = 1 then (1 : ℤ) else 0
  by_cases h : r x g = 1 <;> simp [h]

/-- `q' ≥ 0` whenever `q ≥ 0`. -/
lemma Skeleton.strictify_q_nonneg {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1))
    (hq : 0 ≤ (sk.vtx x).q g) : 0 ≤ ((sk.strictify r).vtx x).q g :=
  le_trans hq (sk.strictify_q_ge r x g)

/-- Boundary cell `r = 1`: `(q, 1) ↦ (q + 1, 0)`. -/
lemma Skeleton.strictify_of_rem_eq_one {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1))
    (hr : r x g = 1) :
    ((sk.strictify r).vtx x).q g = (sk.vtx x).q g + 1 ∧
      sk.strictR r x g = 0 := by
  constructor
  · show (sk.vtx x).q g + (if r x g = 1 then (1 : ℤ) else 0) =
      (sk.vtx x).q g + 1
    rw [ite_eq_left hr]
  · show r x g - (if r x g = 1 then (1 : ℝ) else 0) = 0
    rw [ite_eq_left hr, hr]
    norm_num

/-- The negative boundary cell `(−1, 1) ↦ (0, 0)` — the same target as
`Skeleton.nonnegative`, so strictify also repairs the closed-box
negative cells. -/
lemma Skeleton.strictify_neg_one {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1))
    (hq : (sk.vtx x).q g = -1) (hr : r x g = 1) :
    ((sk.strictify r).vtx x).q g = 0 ∧ sk.strictR r x g = 0 := by
  obtain ⟨h1, h2⟩ := sk.strictify_of_rem_eq_one r x g hr
  exact ⟨by rw [h1, hq]; norm_num, h2⟩

/-- `angleExpr` is identical before and after strictification: `pos`,
`bits` are unchanged and every gap `q + r` is preserved. -/
lemma Skeleton.strictify_angle {s n : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (δ : ℝ) (x a b : Fin s) :
    angleExpr n (sk.strictify r) (sk.strictR r) δ x a b =
      angleExpr n sk r δ x a b := by
  have he : (∑ g ∈ (sk.vtx x).arc a b,
      ((((sk.strictify r).vtx x).q g : ℝ) + sk.strictR r x g)) =
      ∑ g ∈ (sk.vtx x).arc a b, (((sk.vtx x).q g : ℝ) + r x g) := by
    exact Finset.sum_congr rfl (fun g _ => sk.strictify_gap r x g)
  change (if (sk.vtx x).bits a = (sk.vtx x).bits b then
    ∑ g ∈ (sk.vtx x).arc a b,
      ((((sk.strictify r).vtx x).q g : ℝ) + sk.strictR r x g)
    else (n : ℝ) + δ - ∑ g ∈ (sk.vtx x).arc a b,
      ((((sk.strictify r).vtx x).q g : ℝ) + sk.strictR r x g)) = _
  rw [he]
  rfl

/-- Mode-A feasibility transports across strictification, at the same
`n` and `δ`: `0 ≤ r' < 1`, same fan equality, same angles. -/
theorem ModeA.strictify {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) :
    ModeA n (sk.strictify r) (sk.strictR r) δ := by
  have hrnn : ∀ x g, 0 ≤ sk.strictR r x g :=
    fun x g => sk.strictR_nn r (fun x g => hA.r_nn x g) x g
  have hrlt : ∀ x g, sk.strictR r x g < 1 :=
    fun x g => sk.strictR_lt_one r (fun x g => hA.r_le x g) x g
  refine ⟨hrnn, fun x g => (hrlt x g).le, ?_, ?_, ?_, ?_⟩
  · intro x
    have hsum : (∑ g, ((((sk.strictify r).vtx x).q g : ℝ)
        + sk.strictR r x g)) =
        ∑ g, (((sk.vtx x).q g : ℝ) + r x g) :=
      Finset.sum_congr rfl (fun g _ => sk.strictify_gap r x g)
    have hf := hA.fan x
    simp only [Finset.sum_add_distrib] at hsum
    push_cast at hf ⊢
    linarith
  · intro a b c hab hac hbc
    simpa only [sk.strictify_angle r δ] using hA.tri a b c hab hac hbc
  · intro x a b hab
    simpa only [sk.strictify_angle r δ] using hA.ang_le x a b hab
  · intro x a b hab
    simpa only [sk.strictify_angle r δ] using hA.ang_nn x a b hab

/-- Under `ModeA + Proper + 0 ≤ δ` the strictified skeleton already has
nonnegative cells: negative `q'` would force `q' = -1, r' = 1`
(`negative_q_boundary`), contradicting `r' < 1`.  This is
`ModeA.q_nonnegative_of_strict` applied to the strictified model. -/
theorem Skeleton.strictify_q_nonneg_of_modeA {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hp : sk.Proper) (hδ : 0 ≤ δ)
    (x : Fin s) (g : Fin (s - 1)) :
    0 ≤ ((sk.strictify r).vtx x).q g :=
  ModeA.q_nonnegative_of_strict hA.strictify (sk.strictify_proper r hp)
    hδ (fun x g => sk.strictR_lt_one r (fun x g => hA.r_le x g) x g) x g

/-! ## Interaction with the `ProperGaps` normalization -/

/-- Strictify-then-nonnegative is strictify: the strictified skeleton is
already nonnegative, so `Skeleton.nonnegative` is the identity on it. -/
theorem Skeleton.strictify_nonneg_eq_self {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hp : sk.Proper) (hδ : 0 ≤ δ) :
    (sk.strictify r).nonnegative = sk.strictify r := by
  apply Skeleton.ext; funext x
  refine VertexData.ext rfl rfl ?_
  funext g
  show max (((sk.strictify r).vtx x).q g) 0 = ((sk.strictify r).vtx x).q g
  exact max_eq_left (sk.strictify_q_nonneg_of_modeA hA hp hδ x g)

/-- Nonnegative-then-strictify is strictify: on the only differing cell
type `(q, r) = (-1, 1)` both routes land on `q' = 0`.  The two
normalizations commute, yielding strict *and* nonnegative cells. -/
theorem Skeleton.nonnegative_strictify_eq {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hp : sk.Proper) (hδ : 0 ≤ δ) :
    (sk.nonnegative).strictify (sk.normalizedR r) = sk.strictify r := by
  apply Skeleton.ext; funext x
  refine VertexData.ext rfl rfl ?_
  funext g
  show (max ((sk.vtx x).q g) 0) +
      (if sk.normalizedR r x g = 1 then (1 : ℤ) else 0) =
    (sk.vtx x).q g + if r x g = 1 then (1 : ℤ) else 0
  by_cases hq : 0 ≤ (sk.vtx x).q g
  · have hn : sk.normalizedR r x g = r x g := by
      show r x g + ((sk.vtx x).q g : ℝ) -
          ((max ((sk.vtx x).q g) 0 : ℤ) : ℝ) = r x g
      rw [max_eq_left hq]
      ring
    rw [max_eq_left hq, hn]
  · obtain ⟨hq', hr'⟩ := hA.negative_q_boundary hp hδ x g (lt_of_not_ge hq)
    have hn : sk.normalizedR r x g = 0 := by
      show r x g + ((sk.vtx x).q g : ℝ) -
          ((max ((sk.vtx x).q g) 0 : ℤ) : ℝ) = 0
      rw [hq', hr']
      norm_num
    rw [max_eq_right (by omega : (sk.vtx x).q g ≤ 0), hn,
      ite_eq_right (by norm_num : (0 : ℝ) ≠ 1), hq', hr', ite_eq_left rfl]
    norm_num

/-! ## The weight does not decrease -/

/-- `kexp` is non-decreasing under strictify, cell-wise from `q ≤ q'`. -/
lemma Skeleton.strictify_kexp_ge {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (v : Fin s) :
    (sk.vtx v).kexp ≤ ((sk.strictify r).vtx v).kexp := by
  unfold VertexData.kexp
  apply Finset.sum_le_sum
  intro g _
  apply max_le_max _ le_rfl
  have := sk.strictify_q_ge r v g
  omega

/-- The deficit `d` is non-increasing under strictify. -/
lemma Skeleton.strictify_d_le {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (n : ℕ) (v : Fin s) :
    (sk.strictify r).d n v ≤ sk.d n v := by
  unfold Skeleton.d
  have := sk.strictify_kexp_ge r v
  omega

/-- `W` is non-decreasing — **not** equal in general: a `(1, 1)` cell
moves to `(2, 0)`, raising `max (q − 1) 0` from `0` to `1`. -/
theorem Skeleton.W_le_strictify_W {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (n : ℕ) :
    sk.W n ≤ (sk.strictify r).W n := by
  unfold Skeleton.W
  apply Finset.sum_le_sum
  intro v _
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
  have := sk.strictify_d_le r n v
  omega

/-! ## Strict-input identity and idempotency -/

/-- On an already-strict remainder, `q` is unchanged cell-wise. -/
lemma Skeleton.strictify_q_eq_self {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1))
    (hr : r x g < 1) :
    ((sk.strictify r).vtx x).q g = (sk.vtx x).q g := by
  show (sk.vtx x).q g + (if r x g = 1 then (1 : ℤ) else 0) =
    (sk.vtx x).q g
  rw [ite_eq_right (ne_of_lt hr), add_zero]

/-- On an already-strict remainder, `r'` is `r`. -/
lemma Skeleton.strictR_eq_self {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (x : Fin s) (g : Fin (s - 1))
    (hr : r x g < 1) : sk.strictR r x g = r x g := by
  show r x g - (if r x g = 1 then (1 : ℝ) else 0) = r x g
  rw [ite_eq_right (ne_of_lt hr), sub_zero]

/-- Strict-input identity: an already-strict model is unchanged. -/
theorem Skeleton.strictify_eq_self_of_strict {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (hr : ∀ x g, r x g < 1) :
    sk.strictify r = sk := by
  apply Skeleton.ext; funext x
  refine VertexData.ext rfl rfl ?_
  funext g
  exact sk.strictify_q_eq_self r x g (hr x g)

theorem Skeleton.strictR_eq_fun_of_strict {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (hr : ∀ x g, r x g < 1) :
    sk.strictR r = r := by
  funext x g
  exact sk.strictR_eq_self r x g (hr x g)

/-- Idempotency: `strictR r` is already strict (`r ≤ 1` suffices), so a
second strictify pass is the identity. -/
theorem Skeleton.strictify_idempotent {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (hle : ∀ x g, r x g ≤ 1) :
    (sk.strictify r).strictify (sk.strictR r) = sk.strictify r :=
  (sk.strictify r).strictify_eq_self_of_strict (sk.strictR r)
    (fun x g => sk.strictR_lt_one r hle x g)

theorem Skeleton.strictR_idempotent {s : ℕ} (sk : Skeleton s)
    (r : Fin s → Fin (s - 1) → ℝ) (hle : ∀ x g, r x g ≤ 1) :
    (sk.strictify r).strictR (sk.strictR r) = sk.strictR r := by
  funext x g
  exact (sk.strictify r).strictR_eq_self (sk.strictR r) x g
    (sk.strictR_lt_one r hle x g)

/-! ## Packaging and capacity transfer -/

/-- Gate for capacity proofs: every proper consistent closed-remainder
model has a proper consistent strict-remainder model of no smaller
weight, with nonnegative integer cells for free. -/
theorem exists_strict_model {s n : ℕ} {sk : Skeleton s}
    (hp : sk.Proper) (hc : sk.Consistent n) :
    ∃ sk' : Skeleton s, ∃ r' : Fin s → Fin (s - 1) → ℝ, ∃ δ : ℝ,
      sk'.Proper ∧ 0 ≤ δ ∧ δ < 1 ∧ (∀ x g, r' x g < 1) ∧
        (∀ x g, 0 ≤ (sk'.vtx x).q g) ∧ ModeA n sk' r' δ ∧
        sk.W n ≤ sk'.W n := by
  obtain ⟨r, δ, hδ0, hδ1, hA⟩ := hc
  exact ⟨sk.strictify r, sk.strictR r, δ,
    sk.strictify_proper r hp, hδ0, hδ1,
    fun x g => sk.strictR_lt_one r (fun x g => hA.r_le x g) x g,
    fun x g => sk.strictify_q_nonneg_of_modeA hA hp hδ0 x g,
    hA.strictify, sk.W_le_strictify_W r n⟩

/-- Capacity transfer: a `W ≤ B` bound proved over all proper
strict-remainder ModeA models (fixed `n`, `δ`) bounds every proper
closed-remainder ModeA model, via `W sk ≤ W sk' ≤ B`. -/
theorem capacity_of_strict_models {s n : ℕ} {δ : ℝ} {B : ℚ}
    (hbound : ∀ sk' : Skeleton s, sk'.Proper →
      ∀ r' : Fin s → Fin (s - 1) → ℝ,
        (∀ x g, r' x g < 1) → ModeA n sk' r' δ → sk'.W n ≤ B)
    {sk : Skeleton s} {r : Fin s → Fin (s - 1) → ℝ}
    (hp : sk.Proper) (hA : ModeA n sk r δ) : sk.W n ≤ B :=
  le_trans (sk.W_le_strictify_W r n)
    (hbound (sk.strictify r) (sk.strictify_proper r hp) (sk.strictR r)
      (fun x g => sk.strictR_lt_one r (fun x g => hA.r_le x g) x g)
      hA.strictify)

/-- Variant where the capacity bound may additionally assume
nonnegative integer cells — available under `0 ≤ δ` because the
strictified model is already nonnegative. -/
theorem capacity_of_strict_nonneg_models {s n : ℕ} {δ : ℝ} {B : ℚ}
    (hbound : ∀ sk' : Skeleton s, sk'.Proper →
      (∀ x g, 0 ≤ (sk'.vtx x).q g) →
      ∀ r' : Fin s → Fin (s - 1) → ℝ,
        (∀ x g, r' x g < 1) → ModeA n sk' r' δ → sk'.W n ≤ B)
    {sk : Skeleton s} {r : Fin s → Fin (s - 1) → ℝ}
    (hp : sk.Proper) (hA : ModeA n sk r δ) (hδ : 0 ≤ δ) : sk.W n ≤ B :=
  le_trans (sk.W_le_strictify_W r n)
    (hbound (sk.strictify r) (sk.strictify_proper r hp)
      (fun x g => sk.strictify_q_nonneg_of_modeA hA hp hδ x g)
      (sk.strictR r)
      (fun x g => sk.strictR_lt_one r (fun x g => hA.r_le x g) x g)
      hA.strictify)

/-! ## Boundary regressions

A three-vertex fixture exercising every boundary profile:

* vertex 0: `(q, r) = (1, 1)` and `(0, 1)` — both `r = 1`, `q ≥ 0`;
* vertex 1: `(−1, 1)` — the closed-box negative boundary — and `(3, 0)`;
* vertex 2: `(2, 1/2)` — a genuinely interior remainder — and `(0, 0)`.
-/

/-- The fixture skeleton.  `pos`/`bits` are degenerate but irrelevant to
the map-level regression (no `Proper`/`ModeA` hypothesis needed). -/
def bSk3 : Skeleton 3 where
  vtx x := {
    pos := fun _ => 0
    bits := fun _ => false
    q := fun g =>
      if x = 0 then (if g = 0 then 1 else 0)
      else if x = 1 then (if g = 0 then -1 else 3)
      else (if g = 0 then 2 else 0) }

/-- The fixture remainder: `r = 1` on vertex 0 (both gaps) and on
vertex 1 gap 0; `r = 0` on vertex 1 gap 1 and vertex 2 gap 1;
`r = 1/2` on vertex 2 gap 0.  (`noncomputable`: `1 / 2 : ℝ`.) -/
noncomputable def bR3 : Fin 3 → Fin (3 - 1) → ℝ := fun x g =>
  if x = 0 then 1
  else if x = 1 then (if g = 0 then 1 else 0)
  else (if g = 0 then 1 / 2 else 0)

-- `(1, 1) ↦ (2, 0)`: the W-increasing profile.
lemma b_v0g0_q : ((bSk3.strictify bR3).vtx 0).q 0 = 2 := by
  have h : bR3 0 0 = 1 := rfl
  show (1 : ℤ) + (if bR3 0 0 = 1 then 1 else 0) = 2
  rw [ite_eq_left h]
  norm_num

lemma b_v0g0_r : bSk3.strictR bR3 0 0 = 0 := by
  have h : bR3 0 0 = 1 := rfl
  show (1 : ℝ) - (if bR3 0 0 = 1 then 1 else 0) = 0
  rw [ite_eq_left h]
  norm_num

-- `(0, 1) ↦ (1, 0)`: `r = 1` at `q = 0` bumps the integer cell too.
lemma b_v0g1_q : ((bSk3.strictify bR3).vtx 0).q 1 = 1 := by
  have h : bR3 0 1 = 1 := rfl
  show (0 : ℤ) + (if bR3 0 1 = 1 then 1 else 0) = 1
  rw [ite_eq_left h]
  norm_num

-- `(−1, 1) ↦ (0, 0)`: the negative boundary cell is repaired.
lemma b_v1g0_q : ((bSk3.strictify bR3).vtx 1).q 0 = 0 := by
  have h : bR3 1 0 = 1 := rfl
  show (-1 : ℤ) + (if bR3 1 0 = 1 then 1 else 0) = 0
  rw [ite_eq_left h]
  norm_num

lemma b_v1g0_r : bSk3.strictR bR3 1 0 = 0 := by
  have h : bR3 1 0 = 1 := rfl
  show (1 : ℝ) - (if bR3 1 0 = 1 then 1 else 0) = 0
  rw [ite_eq_left h]
  norm_num

-- `(3, 0)` unchanged: `r = 0` is already strict.
lemma b_v1g1 : ((bSk3.strictify bR3).vtx 1).q 1 = 3 ∧
    bSk3.strictR bR3 1 1 = 0 := by
  have h : bR3 1 1 = 0 := rfl
  have hne : bR3 1 1 ≠ 1 := by rw [h]; norm_num
  constructor
  · show (3 : ℤ) + (if bR3 1 1 = 1 then 1 else 0) = 3
    rw [ite_eq_right hne]
    norm_num
  · show (0 : ℝ) - (if bR3 1 1 = 1 then 1 else 0) = 0
    rw [ite_eq_right hne]
    norm_num

-- `(2, 1/2)` unchanged: the interior remainder stays put.
lemma b_v2g0 : ((bSk3.strictify bR3).vtx 2).q 0 = 2 ∧
    bSk3.strictR bR3 2 0 = 1 / 2 := by
  have h : bR3 2 0 = 1 / 2 := rfl
  have hne : bR3 2 0 ≠ 1 := by rw [h]; norm_num
  constructor
  · show (2 : ℤ) + (if bR3 2 0 = 1 then 1 else 0) = 2
    rw [ite_eq_right hne]
    norm_num
  · show (1 / 2 : ℝ) - (if bR3 2 0 = 1 then 1 else 0) = 1 / 2
    rw [ite_eq_right hne]
    norm_num

-- `(0, 0)` unchanged.
lemma b_v2g1 : ((bSk3.strictify bR3).vtx 2).q 1 = 0 ∧
    bSk3.strictR bR3 2 1 = 0 := by
  have h : bR3 2 1 = 0 := rfl
  have hne : bR3 2 1 ≠ 1 := by rw [h]; norm_num
  constructor
  · show (0 : ℤ) + (if bR3 2 1 = 1 then 1 else 0) = 0
    rw [ite_eq_right hne]
    norm_num
  · show (0 : ℝ) - (if bR3 2 1 = 1 then 1 else 0) = 0
    rw [ite_eq_right hne]
    norm_num

/-- The zero remainder is already strict: strictify is the identity. -/
lemma b_strictR_zero : (bSk3.strictR fun _ _ => (0 : ℝ)) = fun _ _ => 0 :=
  bSk3.strictR_eq_fun_of_strict _ fun _ _ => zero_lt_one

/-- Weight computation on the fixture: `kexp` per vertex. -/
lemma bSk3_kexp :
    (bSk3.vtx 0).kexp = 0 ∧ (bSk3.vtx 1).kexp = 2 ∧
      (bSk3.vtx 2).kexp = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold VertexData.kexp <;>
    rw [Fin.sum_univ_two] <;> norm_num [bSk3]

lemma bSk3_strictify_kexp :
    ((bSk3.strictify bR3).vtx 0).kexp = 1 ∧
      ((bSk3.strictify bR3).vtx 1).kexp = 2 ∧
        ((bSk3.strictify bR3).vtx 2).kexp = 1 := by
  have h00 : ((bSk3.strictify bR3).vtx 0).q 0 = 2 := b_v0g0_q
  have h01 : ((bSk3.strictify bR3).vtx 0).q 1 = 1 := b_v0g1_q
  have h10 : ((bSk3.strictify bR3).vtx 1).q 0 = 0 := b_v1g0_q
  have h11 : ((bSk3.strictify bR3).vtx 1).q 1 = 3 := b_v1g1.1
  have h20 : ((bSk3.strictify bR3).vtx 2).q 0 = 2 := b_v2g0.1
  have h21 : ((bSk3.strictify bR3).vtx 2).q 1 = 0 := b_v2g1.1
  refine ⟨?_, ?_, ?_⟩ <;> unfold VertexData.kexp <;>
    rw [Fin.sum_univ_two] <;> norm_num [h00, h01, h10, h11, h20, h21]

/-- `W 2 = 7/2` on the fixture. -/
lemma bSk3_W : bSk3.W 2 = 7 / 2 := by
  obtain ⟨k0, k1, k2⟩ := bSk3_kexp
  unfold Skeleton.W Skeleton.d
  rw [Fin.sum_univ_three, k0, k1, k2]
  norm_num

/-- `W 2 = 4` after strictify: vertex 0's `(1, 1) ↦ (2, 0)` doubles its
term `1/2 → 1`, the other vertices are unchanged. -/
lemma bSk3_strictify_W : (bSk3.strictify bR3).W 2 = 4 := by
  obtain ⟨k0, k1, k2⟩ := bSk3_strictify_kexp
  unfold Skeleton.W Skeleton.d
  rw [Fin.sum_univ_three, k0, k1, k2]
  norm_num

/-- Strict weight increase on the fixture: `7/2 < 4`. -/
lemma bSk3_W_strictly_increases :
    bSk3.W 2 < (bSk3.strictify bR3).W 2 := by
  rw [bSk3_W, bSk3_strictify_W]
  norm_num

/-- Sanity: the fixture remainder is a valid closed remainder
(`0 ≤ r ≤ 1`), so `bSk3.strictR bR3` strictness applies. -/
lemma bR3_closed : ∀ x g, 0 ≤ bR3 x g ∧ bR3 x g ≤ 1 := by
  intro x g
  fin_cases x <;> fin_cases g <;> norm_num [bR3]

lemma bSk3_strictR_strict : ∀ x g, bSk3.strictR bR3 x g < 1 :=
  fun x g => bSk3.strictR_lt_one bR3 (fun x g => (bR3_closed x g).2) x g

/-! ## Axiom audit -/

#print axioms Skeleton.strictify_gap
#print axioms Skeleton.strictR_lt_one
#print axioms Skeleton.strictify_angle
#print axioms ModeA.strictify
#print axioms Skeleton.strictify_q_nonneg_of_modeA
#print axioms Skeleton.nonnegative_strictify_eq
#print axioms Skeleton.W_le_strictify_W
#print axioms Skeleton.strictify_eq_self_of_strict
#print axioms Skeleton.strictify_idempotent
#print axioms exists_strict_model
#print axioms capacity_of_strict_models
#print axioms capacity_of_strict_nonneg_models
#print axioms bSk3_W_strictly_increases

end Jsp404
