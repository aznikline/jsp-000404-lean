import Jsp000404.CircleBound

/-!
# The Section-4 staircase — Sendov's Lemma 4.1 as an explicit interface

Sendov's Lemma 4.1 bounds `|P| ≤ Σᵢ 2^{k'(i)}` by `2^n`
(for `0 ≤ δ < 1/2`) or `2^n + 2^{n-2}` (for `1/2 ≤ δ < 1`), where
`n = ⌊u/2⌋` and `δ = u/2 - n`.  Both published versions assert the
maximizing staircase profile without proof; we isolate exactly the tail
bounds needed and prove the algebraic conversion unconditionally.

Sorted decreasing, the claimed profiles are

- `δ < 1/2`: `k = [n-1, n-2, …, n-s+1, n-s+1]`;
- `δ ≥ 1/2`: `k = [n-1, n-2, …, n-s+2, n-s+2, n-s+1]`.

However, enumeration shows legal configurations can place the excess
multiplicity at other levels (e.g. `[3,1,3,1]` with `N(n-1) = 2`), so
no single per-level tail bound is the right contract.  The minimal
sufficient condition — satisfied by both profile shapes — is the
**weighted budget**

`Σ_{m=1}^{n-1} 2^{m-1}·N(m) ≤ Σ 2^{m-1}·(n-m) + bonus`
                                            `= 2^n - n - 1 + bonus`,

equivalently, after the layer-cake `Σᵢ 2^{kᵢ} = s + Σ 2^{m-1}·N(m)`,

`s + Σ_{m=1}^{n-1} 2^{m-1}·N(m) ≤ 2^n + bonus`.

The `s` cancels on both sides, so the uniform form `Σᵢ 2^{kᵢ} ≤ 2^n +
bonus` is meaningful for *all* `s` — no `s ≤ n + 1` hypothesis is
needed (a fortuitous simplification, since a `card` bound `s ≤ n+1`
cannot be derived from the GA hypotheses alone: regular `2n`-gons are
legal).  `bonus = 2^{n-2}` in the `δ ≥ 1/2` regime, else `0`.
-/

namespace Jsp404

/-- The per-circle exponent `k'(i)` of Lemmas 3.7/4.1 for a configuration. -/
noncomputable def exponents (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (lam : ℝ) : List ℕ :=
  V.forest.map fun ci =>
    ∑ j : Fin (circleDirs V o e ci).length,
      (Nat.floor (gapAfter (circleDirs V o e ci) j / lam) - 1)

/-- Tail count: how many exponents reach level `m`. -/
def tailCount (ks : List ℕ) (m : ℕ) : ℕ := (ks.filter (m ≤ ·)).length

/-- **Sendov's Lemma 4.1 staircase**, hypothesis-package form: the
bounds on the exponent list `ks = [k'(1), …, k'(s)]` needed to bound
`Σᵢ 2^{k'(i)}`. `n = ⌊u/2⌋`; `big` selects the `1/2 ≤ δ < 1` regime.

The `tail` field is the *uniform weighted budget* — equivalent to
`Σᵢ 2^{kᵢ} ≤ 2^n + bonus` via `layerCake` — rather than per-level tail
caps: enumeration shows legal profiles may place excess multiplicity
at different levels (`[n-1,n-2,n-2,…]` in the paper, `[3,1,3,1]` in
samples), but all saturate the same budget.  It holds for all `s`,
so no cardinality hypothesis is needed. -/
structure StaircaseBound (n : ℕ) (ks : List ℕ) (big : Bool) : Prop where
  /-- Every exponent is `< n`. -/
  top : ∀ k ∈ ks, k < n
  /-- Weighted budget: `s + Σ_{m=1}^{n-1} 2^{m-1}·N(m) ≤ 2^n + bonus`.
  Equivalent to `Σᵢ 2^{kᵢ} ≤ 2^n + bonus` by the layer-cake identity. -/
  tail : ks.length +
      ∑ m ∈ Finset.Icc 1 (n - 1), 2 ^ (m - 1) * tailCount ks m ≤
    2 ^ n + if big = true then 2 ^ (n - 2) else 0

/-- `k + 2 ≤ 2^{k+1}`. -/
lemma le_two_pow_succ (k : ℕ) : k + 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- Geometric series: `2^k = 1 + Σ_{m=1}^{k} 2^{m-1}`. -/
lemma two_pow_eq (k : ℕ) : 2 ^ k = 1 + ∑ m ∈ Finset.Icc 1 k, 2 ^ (m - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∑ m ∈ Finset.Icc 1 (k + 1), 2 ^ (m - 1) =
        (∑ m ∈ Finset.Icc 1 k, 2 ^ (m - 1)) + 2 ^ k := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
      congr 1
    rw [pow_succ, e]
    omega

/-- Layer-cake: `Σᵢ 2^{kᵢ} = s + Σ_{m=1}^{n-1} 2^{m-1}·N(m)` when all
`kᵢ < n`. -/
lemma layerCake {ks : List ℕ} {n : ℕ} (h : ∀ k ∈ ks, k < n) :
    (ks.map (2 ^ ·)).sum =
      ks.length + ∑ m ∈ Finset.Icc 1 (n - 1), 2 ^ (m - 1) * tailCount ks m := by
  induction ks with
  | nil => simp [tailCount]
  | cons k ks ih =>
    have hk : k < n := h k List.mem_cons_self
    have hks : ∀ k' ∈ ks, k' < n := fun k' hk' => h k' (List.mem_cons_of_mem k hk')
    rw [List.map_cons, List.sum_cons, two_pow_eq, ih hks, List.length_cons]
    have htc : ∀ m : ℕ, tailCount (k :: ks) m =
        tailCount ks m + if m ≤ k then 1 else 0 := by
      intro m
      unfold tailCount
      rw [List.filter_cons]
      by_cases hmk : m ≤ k <;> simp [hmk]
    have hsum : ∀ m ∈ Finset.Icc 1 (n - 1),
        2 ^ (m - 1) * tailCount (k :: ks) m =
          2 ^ (m - 1) * tailCount ks m + if m ≤ k then 2 ^ (m - 1) else 0 := by
      intro m _
      rw [htc m, Nat.mul_add]
      by_cases hmk : m ≤ k <;> simp [hmk]
    rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib]
    have hif : ∑ m ∈ Finset.Icc 1 (n - 1), (if m ≤ k then 2 ^ (m - 1) else 0)
        = ∑ m ∈ Finset.Icc 1 k, 2 ^ (m - 1) := by
      rw [← Finset.sum_subset
        (s₁ := Finset.Icc 1 k) (s₂ := Finset.Icc 1 (n - 1))
        (f := fun m => if m ≤ k then 2 ^ (m - 1) else 0)]
      · apply Finset.sum_congr rfl
        intro m hm
        simp only [Finset.mem_Icc] at hm
        exact if_pos hm.2
      · intro m hm
        simp only [Finset.mem_Icc] at hm ⊢
        omega
      · intro m hm hmk
        simp only [Finset.mem_Icc] at hm hmk
        exact if_neg (by omega)
    rw [hif]
    omega

/-- `∑_{m ∈ Icc 1 k} 2^{m-1} = 2^k - 1`. -/
lemma geom_Icc (k : ℕ) : ∑ m ∈ Finset.Icc 1 k, 2 ^ (m - 1) = 2 ^ k - 1 := by
  have h := two_pow_eq k
  omega

/-- `Σ_{j=1}^{t} j·2^{t-j} = 2^{t+1} - t - 2`. -/
lemma geom_weighted (t : ℕ) :
    ∑ j ∈ Finset.Icc 1 t, j * 2 ^ (t - j) = 2 ^ (t + 1) - t - 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), Nat.sub_self, pow_zero,
      mul_one]
    have hterm : ∀ j ∈ Finset.Icc 1 t,
        j * 2 ^ (t + 1 - j) = 2 * (j * 2 ^ (t - j)) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      rw [show t + 1 - j = t - j + 1 from by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ih]
    have hd : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := pow_succ' 2 (t + 1)
    have hge : t + 2 ≤ 2 ^ (t + 1) := le_two_pow_succ t
    omega

/-- `∑_{m ∈ Icc a (n-1)} 2^{m-1} = 2^{n-1} - 2^{a-1}` for `1 ≤ a ≤ n`. -/
lemma geom_Icc_sub (a n : ℕ) (ha : 1 ≤ a) (han : a ≤ n) :
    ∑ m ∈ Finset.Icc a (n - 1), 2 ^ (m - 1) = 2 ^ (n - 1) - 2 ^ (a - 1) := by
  induction n, han using Nat.le_induction with
  | base => simp [Finset.Icc_eq_empty_of_lt (by omega : a - 1 < a)]
  | succ n han ih =>
    rw [show Finset.Icc a (n + 1 - 1) = Finset.Icc a (n - 1 + 1) from by
      congr 1; omega, Finset.sum_Icc_succ_top (by omega : a ≤ n - 1 + 1), ih]
    rw [show n - 1 + 1 - 1 = n - 1 from by omega,
      show n + 1 - 1 = n from by omega]
    have h2n : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have hge : 2 ^ (a - 1) ≤ 2 ^ (n - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [← Nat.sub_add_comm hge, h2n]

/-- Tail of the staircase sum: `Σ_{m=a}^{n-1} 2^{m-1}(n-m) = 2^n - (n-a+2)·2^{a-1}`
for `1 ≤ a ≤ n`. -/
lemma staircase_tail (n a : ℕ) (ha : 1 ≤ a) (han : a ≤ n) :
    ∑ m ∈ Finset.Icc a (n - 1), 2 ^ (m - 1) * (n - m) =
      2 ^ n - (n - a + 2) * 2 ^ (a - 1) := by
  induction n, han using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty_of_lt (by omega : a - 1 < a), Finset.sum_empty]
    rw [show a - a + 2 = 2 from by omega]
    have h2 : 2 * 2 ^ (a - 1) = 2 ^ a := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2]
    simp
  | succ n han ih =>
    rw [show Finset.Icc a (n + 1 - 1) = Finset.Icc a (n - 1 + 1) from by
      congr 1; omega, Finset.sum_Icc_succ_top (by omega : a ≤ n - 1 + 1)]
    have hterm : ∀ m ∈ Finset.Icc a (n - 1),
        2 ^ (m - 1) * (n + 1 - m) = 2 ^ (m - 1) * (n - m) + 2 ^ (m - 1) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      rw [show n + 1 - m = n - m + 1 from by omega, Nat.mul_succ]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ih,
      geom_Icc_sub a n ha han]
    rw [show n + 1 - (n - 1 + 1) = 1 from by omega, mul_one,
      show n - 1 + 1 - 1 = n - 1 from by omega]
    have h2n : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have hge' : 2 ^ (a - 1) ≤ 2 ^ (n - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hge : (n - a + 2) * 2 ^ (a - 1) ≤ 2 ^ n := by
      have h : n - a + 2 ≤ 2 ^ (n - a + 1) := le_two_pow_succ _
      calc (n - a + 2) * 2 ^ (a - 1) ≤ 2 ^ (n - a + 1) * 2 ^ (a - 1) :=
          Nat.mul_le_mul_right _ h
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
    have hmerge : (n - a + 2) * 2 ^ (a - 1) + 2 ^ (a - 1) =
        (n + 1 - a + 2) * 2 ^ (a - 1) := by
      rw [show n + 1 - a + 2 = n - a + 2 + 1 from by omega]
      ring
    have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ, mul_two]
    omega

/-- `Σ_{m=1}^{n-1} 2^{m-1}(n - m) = 2^n - n - 1`. -/
lemma staircase_sum_low (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 (n - 1), 2 ^ (m - 1) * (n - m) = 2 ^ n - n - 1 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := staircase_tail (n + 1) 1 (by omega) (by omega)
    rw [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, Nat.mul_one] at h
    rw [show n + 1 - 1 = n from by omega] at h
    exact h

/-- `k ≤ 2^{k-1}` for `k ≥ 1`. -/
lemma le_two_pow_pred : ∀ k : ℕ, 1 ≤ k → k ≤ 2 ^ (k - 1)
  | 1, _ => le_rfl
  | k + 2, _ => by
    have ih := le_two_pow_pred (k + 1) (by omega)
    have h2 : 2 ^ (k + 2 - 1) = 2 * 2 ^ (k + 1 - 1) := by
      rw [← pow_succ']
      congr 1
    have h1 : 0 < 2 ^ (k + 1 - 1) := pow_pos (by omega) _
    omega

/-- **Conditional Sendov bound**: under the `StaircaseBound` weighted
budget, `Σᵢ 2^{kᵢ} ≤ 2^n + 2^{n-2}·[big]` — immediate from the
layer-cake identity. -/
theorem staircase_apply (n : ℕ) (ks : List ℕ) (big : Bool)
    (h : StaircaseBound n ks big) :
    (ks.map (2 ^ ·)).sum ≤
      2 ^ n + if big = true then 2 ^ (n - 2) else 0 := by
  rw [layerCake h.top]
  exact h.tail

/-- `δ < 1/2` regime: the staircase bound gives `Σᵢ 2^{kᵢ} ≤ 2^n`. -/
theorem staircase_apply_low (n : ℕ) (ks : List ℕ)
    (h : StaircaseBound n ks false) :
    (ks.map (2 ^ ·)).sum ≤ 2 ^ n := by
  have h1 := staircase_apply n ks false h
  simpa using h1

/-- `δ ≥ 1/2` regime: `Σᵢ 2^{kᵢ} ≤ 2^n + 2^{n-2}` — Sendov's stated
bonus bound. -/
theorem staircase_apply_big (n : ℕ) (ks : List ℕ)
    (h : StaircaseBound n ks true) :
    (ks.map (2 ^ ·)).sum ≤ 2 ^ n + 2 ^ (n - 2) := by
  have h1 := staircase_apply n ks true h
  simpa using h1

/-- **Lower-bound chain, complete modulo the staircase crux**: under the
same geometric hypotheses as `total_points_bound`, plus the
`StaircaseBound` tail interface instantiated on the actual exponent
list, the total point count is `≤ 2^n` (`δ < 1/2`) or
`≤ 2^n + 2^{n-2}` (`δ ≥ 1/2`). -/
theorem sendov_count_bound (V : GCfg) (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) (he : e ≠ 0)
    (hd : V.DisjointCircles) (hfN : V.forest.Nodup)
    (hcenters : ∀ g₁ ∈ V.forest, ∀ g₂ ∈ V.forest, g₁ ≠ g₂ →
      g₁.centerOf ≠ g₂.centerOf)
    (hnonempty : ∀ g ∈ V.forest, ∃ q, q ∈ g.points)
    (hptN : ∀ g ∈ V.forest, g.points.Nodup)
    (hGD : ∀ ci ∈ V.forest, ∀ p ∈ ci.points, ∀ q ∈ ci.points,
      p ≠ q → V.GD p q ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hGA : ∀ a ∈ V.points, ∀ b ∈ V.points, ∀ c ∈ V.points,
      a ≠ b → b ≠ c → a ≠ c → V.GA a b c ≤ Real.pi - lam)
    (n : ℕ) (big : Bool)
    (hstair : StaircaseBound n (exponents V o e lam) big) :
    V.points.length ≤ 2 ^ n + if big = true then 2 ^ (n - 2) else 0 := by
  apply le_trans (total_points_bound V o e hd hfN he hcenters hnonempty
    hptN hGD hlam hlampi hGA)
  have h1 := staircase_apply n _ big hstair
  unfold exponents at h1
  rw [List.map_map] at h1
  exact h1

end Jsp404
