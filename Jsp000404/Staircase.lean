import Jsp000404.CircleBound

/-!
# The Section-4 staircase — Sendov's Lemma 4.1 as an explicit interface

Sendov's Lemma 4.1 bounds `|P| ≤ Σᵢ 2^{k'(i)}` by `2^n`
(for `0 ≤ δ < 1/2`) or `2^n + 2^{n-2}` (for `1/2 ≤ δ < 1`), where
`n = ⌊u/2⌋` and `δ = u/2 - n`.  Both published versions assert the
maximizing staircase profile without proof; we isolate exactly the tail
bounds needed and prove the algebraic conversion unconditionally.

Sorted decreasing, the claimed profiles are

- `δ < 1/2`: `k₍ᵢ₎ ≤ n - i` for `i ≤ s-1`, `k₍ₛ₎ ≤ n - s + 1`;
- `δ ≥ 1/2`: `k₍ᵢ₎ ≤ n - i` for `i ≤ s-2`, `k₍ₛ₋₁₎ ≤ n - s + 2`,
  `k₍ₛ₎ ≤ n - s + 1`.

Equivalently, for the tail counts `N(m) = #{i : k'(i) ≥ m}`:

- `N(m) ≤ n - m` for `n - s + 3 ≤ m ≤ n - 1` (both regimes), and
  `N(m) ≤ 0` for `m ≥ n`;
- in the `δ ≥ 1/2` regime the level `m = n - s + 2` may reach `s - 1`.
- `s = 2` is exceptional (both exponents equal `n - 1`).
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

/-- **Sendov's Lemma 4.1 staircase**, hypothesis-package form: the tail
bounds on the exponent list `ks = [k'(1), …, k'(s)]` needed to bound
`Σᵢ 2^{k'(i)}`. `n = ⌊u/2⌋`; `big` selects the `1/2 ≤ δ < 1` regime. -/
structure StaircaseBound (n : ℕ) (ks : List ℕ) (big : Bool) : Prop where
  /-- Every exponent is `< n`. -/
  top : ∀ k ∈ ks, k < n
  /-- At most `n + 1` circles (the `m = 0` boundary level). -/
  card : 3 ≤ ks.length → ks.length ≤ n + 1
  /-- Tail bounds at the staircase levels `n + 2 - s ≤ m < n`:
  at most `n - m` exponents reach `m`, except that in the `δ ≥ 1/2` regime
  the bottom staircase level `m = n + 2 - s` may reach `s - 1`.  Levels
  below `n + 2 - s` impose no constraint beyond the trivial `≤ s`. -/
  tail : 3 ≤ ks.length → ∀ m : ℕ, n + 2 - ks.length ≤ m → m < n →
    tailCount ks m ≤
      if big ∧ m = n + 2 - ks.length then ks.length - 1 else n - m

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

/-- **Conditional Sendov bound**: under the `StaircaseBound` tail-count
interface, `Σᵢ 2^{kᵢ} ≤ 2^n`, plus a `2^{n+1-s}` bonus in the `δ ≥ 1/2`
regime (where the bottom staircase level may carry `s - 1` exponents
instead of `s - 2`). -/
theorem staircase_apply (n : ℕ) (ks : List ℕ) (big : Bool)
    (h : StaircaseBound n ks big) :
    (ks.map (2 ^ ·)).sum ≤
      2 ^ n + if big = true then 2 ^ (n + 1 - ks.length) else 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have e : ks = [] := by
      cases ks with
      | nil => rfl
      | cons k _ => exact absurd (h.top k List.mem_cons_self) (by omega)
    simp [e]
  rcases Nat.lt_or_ge ks.length 3 with hs | hs
  · -- s ≤ 2: every exponent < n bounds each term by `2^{n-1}`
    have hb' : ∀ k ∈ ks, 2 ^ k ≤ 2 ^ (n - 1) := fun k hk =>
      Nat.pow_le_pow_right (by omega) (by have := h.top k hk; omega)
    rcases ks with _ | ⟨k₁, _ | ⟨k₂, ks'⟩⟩
    · simp
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      have hb1 : 2 ^ k₁ ≤ 2 ^ n :=
        le_trans (hb' k₁ List.mem_cons_self)
          (Nat.pow_le_pow_right (by omega) (by omega))
      cases hb : big
      · simpa using hb1
      · have e : (2 : ℕ) ^ (n + 1 - [k₁].length) = 2 ^ n := by
          show 2 ^ (n + 1 - 1) = 2 ^ n
          congr 1
        rw [e]
        omega
    · have e : ks' = [] := by
        cases ks' with
        | nil => rfl
        | cons _ _ =>
          exfalso
          simp only [List.length_cons] at hs
          omega
      subst e
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      have hb1 := hb' k₁ List.mem_cons_self
      have hb2 := hb' k₂ (List.mem_cons_of_mem _ List.mem_cons_self)
      have h2 : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      cases hb : big
      · have hle : 2 ^ k₁ + 2 ^ k₂ ≤ 2 ^ n := by omega
        simpa using hle
      · have e : (2 : ℕ) ^ (n + 1 - [k₁, k₂].length) = 2 ^ (n - 1) := by
          show 2 ^ (n + 1 - 2) = 2 ^ (n - 1)
          congr 1
        rw [e]
        omega
  · -- s ≥ 3: split the layer-cake sum at `a = n + 2 - s`
    have hscard : ks.length ≤ n + 1 := h.card hs
    have hdis : Disjoint (Finset.Icc 1 (n + 2 - ks.length - 1))
        (Finset.Icc (n + 2 - ks.length) (n - 1)) := by
      rw [Finset.disjoint_left]
      intro m hm hmem
      simp only [Finset.mem_Icc] at hm hmem
      omega
    have hsplit : Finset.Icc 1 (n - 1) =
        Finset.Icc 1 (n + 2 - ks.length - 1) ∪
          Finset.Icc (n + 2 - ks.length) (n - 1) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hmain : (ks.map (2 ^ ·)).sum =
        ks.length +
          (∑ m ∈ Finset.Icc 1 (n + 2 - ks.length - 1),
              2 ^ (m - 1) * tailCount ks m +
            ∑ m ∈ Finset.Icc (n + 2 - ks.length) (n - 1),
              2 ^ (m - 1) * tailCount ks m) := by
      rw [layerCake h.top, hsplit, Finset.sum_union hdis]
    -- per-term bound on the staircase levels
    have hcap : ∀ m ∈ Finset.Icc (n + 2 - ks.length) (n - 1),
        2 ^ (m - 1) * tailCount ks m ≤ 2 ^ (m - 1) * (n - m) +
          (if big ∧ m = n + 2 - ks.length then
            2 ^ (n + 1 - ks.length) else 0) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      have ht := h.tail hs m (by omega) (by omega)
      by_cases hb : big ∧ m = n + 2 - ks.length
      · obtain ⟨hbb, rfl⟩ := hb
        rw [if_pos ⟨hbb, rfl⟩] at ht ⊢
        calc 2 ^ (n + 2 - ks.length - 1) * tailCount ks (n + 2 - ks.length)
            ≤ 2 ^ (n + 2 - ks.length - 1) * (ks.length - 1) :=
              Nat.mul_le_mul_left _ ht
          _ = 2 ^ (n + 2 - ks.length - 1) *
                (n - (n + 2 - ks.length) + 1) := by
              rw [show ks.length - 1 = n - (n + 2 - ks.length) + 1 from by
                omega]
          _ = 2 ^ (n + 2 - ks.length - 1) * (n - (n + 2 - ks.length)) +
                2 ^ (n + 2 - ks.length - 1) := by ring
          _ = 2 ^ (n + 2 - ks.length - 1) * (n - (n + 2 - ks.length)) +
                2 ^ (n + 1 - ks.length) := by
              congr 1
              congr 1
              omega
      · rw [if_neg hb] at ht ⊢
        calc 2 ^ (m - 1) * tailCount ks m ≤ 2 ^ (m - 1) * (n - m) :=
              Nat.mul_le_mul_left _ ht
          _ ≤ 2 ^ (m - 1) * (n - m) + 0 := by omega
    -- the `big` bonus appears at exactly one level
    have hsumif : ∑ m ∈ Finset.Icc (n + 2 - ks.length) (n - 1),
        (if big ∧ m = n + 2 - ks.length then 2 ^ (n + 1 - ks.length) else 0)
          = if big = true then 2 ^ (n + 1 - ks.length) else 0 := by
      by_cases hb : big = true
      · simp only [hb, true_and]
        rw [Finset.sum_ite_eq',
          if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩), ite_true]
      · have hbf : big = false := by simpa using hb
        simp [hbf]
    -- assemble the two halves
    have hhigh : ∑ m ∈ Finset.Icc (n + 2 - ks.length) (n - 1),
        2 ^ (m - 1) * tailCount ks m ≤
        (2 ^ n - ks.length * 2 ^ (n + 1 - ks.length)) +
          (if big = true then 2 ^ (n + 1 - ks.length) else 0) := by
      calc _ ≤ ∑ m ∈ Finset.Icc (n + 2 - ks.length) (n - 1),
            (2 ^ (m - 1) * (n - m) +
              (if big ∧ m = n + 2 - ks.length then
                2 ^ (n + 1 - ks.length) else 0)) :=
            Finset.sum_le_sum fun m hm => hcap m hm
        _ = (∑ m ∈ Finset.Icc (n + 2 - ks.length) (n - 1),
              2 ^ (m - 1) * (n - m)) +
            ∑ m ∈ Finset.Icc (n + 2 - ks.length) (n - 1),
              (if big ∧ m = n + 2 - ks.length then
                2 ^ (n + 1 - ks.length) else 0) :=
            Finset.sum_add_distrib
        _ = _ := by
            have e1 : n - (n + 2 - ks.length) + 2 = ks.length := by omega
            have e2 : n + 2 - ks.length - 1 = n + 1 - ks.length := by omega
            rw [staircase_tail n (n + 2 - ks.length) (by omega) (by omega),
              e1, e2, hsumif]
    have hlow : (∑ m ∈ Finset.Icc 1 (n + 2 - ks.length - 1),
        2 ^ (m - 1) * tailCount ks m) + ks.length ≤
        ks.length * 2 ^ (n + 1 - ks.length) := by
      have hle : ∑ m ∈ Finset.Icc 1 (n + 2 - ks.length - 1),
          2 ^ (m - 1) * tailCount ks m ≤
          ks.length * (2 ^ (n + 1 - ks.length) - 1) := by
        calc _ ≤ ∑ m ∈ Finset.Icc 1 (n + 2 - ks.length - 1),
              2 ^ (m - 1) * ks.length :=
              Finset.sum_le_sum fun m _ =>
                Nat.mul_le_mul_left _ (List.length_filter_le _ _)
          _ = (∑ m ∈ Finset.Icc 1 (n + 2 - ks.length - 1), 2 ^ (m - 1)) *
                ks.length :=
              (Finset.sum_mul ..).symm
          _ = ks.length * (2 ^ (n + 1 - ks.length) - 1) := by
              have e : n + 2 - ks.length - 1 = n + 1 - ks.length := by omega
              rw [geom_Icc, e, Nat.mul_comm]
      have hX : 0 < 2 ^ (n + 1 - ks.length) := pow_pos (by omega) _
      have hmerge : ks.length * (2 ^ (n + 1 - ks.length) - 1) + ks.length =
          ks.length * 2 ^ (n + 1 - ks.length) := by
        rw [Nat.mul_sub_one]
        exact Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hX)
      omega
    -- final linear combination
    have hsle : ks.length ≤ 2 ^ (ks.length - 1) :=
      le_two_pow_pred _ (by omega)
    have hb2 : ks.length * 2 ^ (n + 1 - ks.length) ≤ 2 ^ n := by
      calc ks.length * 2 ^ (n + 1 - ks.length)
          ≤ 2 ^ (ks.length - 1) * 2 ^ (n + 1 - ks.length) :=
            Nat.mul_le_mul_right _ hsle
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
    rw [hmain]
    cases hb : big <;> simp [hb] at hhigh ⊢ <;> omega

/-- `δ < 1/2` regime: the staircase bound gives `Σᵢ 2^{kᵢ} ≤ 2^n`. -/
theorem staircase_apply_low (n : ℕ) (ks : List ℕ)
    (h : StaircaseBound n ks false) :
    (ks.map (2 ^ ·)).sum ≤ 2 ^ n := by
  have h1 := staircase_apply n ks false h
  simpa using h1

/-- `δ ≥ 1/2` regime with `s ≥ 3`: `Σᵢ 2^{kᵢ} ≤ 2^n + 2^{n-2}`. -/
theorem staircase_apply_big (n : ℕ) (ks : List ℕ)
    (h : StaircaseBound n ks true) (hs : 3 ≤ ks.length) :
    (ks.map (2 ^ ·)).sum ≤ 2 ^ n + 2 ^ (n - 2) := by
  have h1 := staircase_apply n ks true h
  have e : 2 ^ (n + 1 - ks.length) ≤ 2 ^ (n - 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  simp only [ite_true] at h1
  exact le_trans h1 (Nat.add_le_add_left e _)

end Jsp404
