import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Saturated structure — the strict-remainder L2/L3 layer

Formalization of the saturation lemmas verified computationally by the
strict checker (`tools/strict_check.py`, base commit `b334239`).  The
checker output is *evidence only*; nothing here depends on Python.

## λ-normalized semantics

The projective circle at a vertex has length `T = n + δ` with
`0 ≤ δ < 1`.  Each cyclic gap decomposes as `q j + r j` with integer
cell `q j : ℕ` and remainder `0 ≤ r j < 1`.  The row exponent of a
vertex is

  `k = ∑ j, (q j - 1)`   (natural subtraction, i.e. `max(q-1,0)`),

matching `gapScore lam x = ⌊x/lam⌋₊ - 1` of `Deletion.lean` and the
`qs` cells of `tools/generic_model.py`.  A vertex is *saturated* when
`k = n - 1` (deficit `d = 0`).

## Contents

* `saturated_cells_unique` — **B1**: a saturated fan has exactly one
  positive cell `q b = n`; all other cells vanish and `∑ r = δ`.
* `ProjFan` — the local fan model of `generic_model.vertex_variants`:
  `arc` is the non-wrapping linear gap-sum, `angle` is `arc` or
  `T - arc` according to the 2π-lift `bit`s.
* `ProjFan.saturated_angle_le` — **L2-min**: at a saturated vertex
  every incident angle is `≤ δ`.
* `ProjFan.saturated_bits_iff` — **full L2**: different bits iff the
  linear arc contains a positive cell (= the unique big gap); the
  wrap corollary `saturated_bits_all_eq_last` is the checker's
  all-equal-bit degenerate case.
* `FanSystem.two_saturated_ge_half` — **L3**: two saturated vertices
  force `δ ≥ 1/2`, for arbitrary `s ≥ 3`.
* `saturated_cells_unique_of_gaps` — **bridge**: the repository's
  actual `⌊g/λ⌋₊ - 1` exponent (`gapScore`, hence `exponents`)
  instantiates B1.

All theorems are proved with standard axioms only; `#print axioms`
appears at the end of the file.
-/

namespace Jsp404

open Finset

section Cells

variable {m : ℕ}

/-- **B1 — saturated cells are unique.**  A fan whose exponent
`∑ j, (q j - 1)` equals `n - 1`, whose real gap sum is
`T ∈ [n, n+1)`, and whose remainders are nonnegative has exactly one
positive cell, of value `n`; the remainders then sum to `T - n = δ`.

The arithmetic mechanism: `∑ (q-1) = ∑q - #{q>0} = n-1` together with
`∑q ≤ T < n+1`, i.e. `∑q ≤ n`, forces `#{q>0} = 1` and `∑q = n`. -/
theorem saturated_cells_unique {q : Fin m → ℕ} {r : Fin m → ℝ}
    {n : ℕ} {T : ℝ} (hn : 2 ≤ n) (_hnT : (n : ℝ) ≤ T) (hT : T < n + 1)
    (hr : ∀ j, 0 ≤ r j)
    (hfan : ∑ j : Fin m, ((q j : ℝ) + r j) = T)
    (hsat : ∑ j : Fin m, (q j - 1) = n - 1) :
    ∃ b : Fin m, q b = n ∧ (∀ j, j ≠ b → q j = 0)
      ∧ (∀ b', 0 < q b' → b' = b)
      ∧ ∑ j : Fin m, r j = T - n := by
  classical
  set P : Finset (Fin m) := Finset.univ.filter fun j => 0 < q j with hP
  set S : ℕ := ∑ j : Fin m, q j with hS
  -- Only positive cells contribute to the truncated sum.
  have hsplit : ∑ j : Fin m, (q j - 1) = ∑ j ∈ P, (q j - 1) := by
    rw [hP, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 0 < q j
    · simp [h]
    · have hz : q j = 0 := Nat.eq_zero_of_not_pos h
      simp [hz]
  -- `S = ∑_P q = ∑_P (q-1) + card P`.
  have hSP : ∑ j ∈ P, q j = S := by
    rw [hS, hP, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 0 < q j
    · simp [h]
    · have hz : q j = 0 := Nat.eq_zero_of_not_pos h
      simp [hz]
  have hcard : S = ∑ j ∈ P, (q j - 1) + P.card := by
    have h1 : ∀ j ∈ P, q j = (q j - 1) + 1 := by
      intro j hj
      exact (Nat.sub_add_cancel (Finset.mem_filter.mp hj).2).symm
    rw [← hSP, Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    simp
  -- `∑ q = (n - 1) + card P`.
  have hSeq : S = n - 1 + P.card := by
    rw [hsplit] at hsat
    omega
  -- Real bound: `∑ q ≤ T < n+1`, so `S ≤ n`.
  have hSle : S ≤ n := by
    have h1 : (S : ℝ) ≤ T := by
      have e : (S : ℝ) = ∑ j : Fin m, (q j : ℝ) := by
        rw [hS]; exact Nat.cast_sum _ _
      rw [Finset.sum_add_distrib] at hfan
      have hrnn : 0 ≤ ∑ j : Fin m, r j :=
        Finset.sum_nonneg fun j _ => hr j
      linarith
    have h2 : (S : ℝ) < (n : ℝ) + 1 := lt_of_le_of_lt h1 hT
    have h3 : S < n + 1 := by exact_mod_cast h2
    omega
  -- `card P = 1`: at most 1 from `S ≤ n`, at least 1 since
  -- `S ≥ n-1 ≥ 1` excludes the all-zero fan.
  have hcard1 : P.card = 1 := by
    have hge : 1 ≤ P.card := by
      show 0 < P.card
      rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
      intro hPe
      have hz : ∀ j : Fin m, q j = 0 := by
        intro j
        by_contra h0
        have hjm : j ∈ P := by
          rw [hP]
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ j, Nat.pos_of_ne_zero h0⟩
        rw [hPe] at hjm
        exact Finset.notMem_empty j hjm
      have hS0 : S = 0 := by rw [hS]; simp [hz]
      omega
    omega
  have hSn' : S = n := by omega
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard1
  have hbq : q b = n := by
    have hPb : ∑ j ∈ P, q j = q b := by
      rw [hb]; exact Finset.sum_singleton _ _
    have hSq : S = q b := by rw [← hSP]; exact hPb
    omega
  refine ⟨b, hbq, ?_, ?_, ?_⟩
  · intro j hj
    by_contra h0
    have hjm : j ∈ P := by
      rw [hP]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ j, Nat.pos_of_ne_zero h0⟩
    rw [hb] at hjm
    exact hj (Finset.mem_singleton.mp hjm)
  · intro b' hb'
    have hbm : b' ∈ P := by
      rw [hP]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b', hb'⟩
    rw [hb] at hbm
    exact Finset.mem_singleton.mp hbm
  · -- `∑ r = T - n` from the fan equality.
    rw [Finset.sum_add_distrib] at hfan
    have e : (∑ j : Fin m, (q j : ℝ)) = (S : ℝ) := by
      rw [hS]; exact (Nat.cast_sum _ _).symm
    have hSn : (S : ℝ) = (n : ℝ) := by exact_mod_cast hSn'
    linarith

end Cells

/-! ### The local fan model -/

/-- **Local fan at one vertex**, matching `vertex_variants` of
`tools/generic_model.py`: `m` directions sit at positions `Fin m` on
the projective circle of length `T`; gap `j` lies between positions
`j` and `j+1` (cyclically); `bit j` is the 2π-lift of the ray at
position `j`.  The checker's `order`/`pos` relabeling is absorbed:
positions are the index type directly. -/
structure ProjFan (m : ℕ) where
  q : Fin m → ℕ
  r : Fin m → ℝ
  bit : Fin m → Bool

namespace ProjFan

variable {m : ℕ}

/-- Length of gap `j` in λ-units. -/
def gap (f : ProjFan m) (j : Fin m) : ℝ := (f.q j : ℝ) + f.r j

/-- **Non-wrapping linear arc** between positions `i j`: the sum of
gaps `t` with `min i j ≤ t < max i j` — exactly
`arc(pos[u], pos[v])` of `generic_model.py`, which never wraps. -/
def arc (f : ProjFan m) (i j : Fin m) : ℝ :=
  ∑ t ∈ Finset.Ico (min i j) (max i j), f.gap t

/-- The projective angle between directions `i j` on a circle of
length `T`: the linear arc when the 2π-lifts agree, else its
projective complement `T - arc`. -/
def angle (f : ProjFan m) (T : ℝ) (i j : Fin m) : ℝ :=
  if f.bit i = f.bit j then f.arc i j else T - f.arc i j

variable {f : ProjFan m} {T : ℝ}

/-- Cap dichotomy I: different bits force the linear arc to be `≥ 1`
(otherwise the complement angle exceeds `T - 1`).  This is the exact
content of the 2-constraint strict MUS found on every `(0,0,1,*)`
skeleton (an `∠ ≤ π−λ` cap forcing `r ≥ 1`). -/
theorem arc_ge_one_of_bit_ne
    (hcap : ∀ i j : Fin m, i ≠ j → f.angle T i j ≤ T - 1)
    {i j : Fin m} (hij : i ≠ j) (hb : f.bit i ≠ f.bit j) :
    1 ≤ f.arc i j := by
  have hc := hcap i j hij
  unfold angle at hc
  rw [ite_eq_right hb] at hc
  linarith

/-- Cap dichotomy II: equal bits bound the linear arc by `T - 1`. -/
theorem arc_le_of_bit_eq
    (hcap : ∀ i j : Fin m, i ≠ j → f.angle T i j ≤ T - 1)
    {i j : Fin m} (hij : i ≠ j) (hb : f.bit i = f.bit j) :
    f.arc i j ≤ T - 1 := by
  have hc := hcap i j hij
  unfold angle at hc
  rw [ite_eq_left hb] at hc
  exact hc

/-- Local bit rule: a strictly small arc (`arc < 1`) must have equal
bits — the contrapositive of `arc_ge_one_of_bit_ne`. -/
theorem bit_eq_of_arc_lt_one
    (hcap : ∀ i j : Fin m, i ≠ j → f.angle T i j ≤ T - 1)
    {i j : Fin m} (hij : i ≠ j) (h : f.arc i j < 1) :
    f.bit i = f.bit j := by
  by_contra hb
  have h1 := arc_ge_one_of_bit_ne hcap hij hb
  linarith

/-- **L2-min — saturated incident angles.**  At a saturated vertex
(`∑ (q-1) = n-1`), every incident angle is `≤ T - n = δ`.

Mechanism: the unique big cell `b` has `gap b ≥ n`.  If the linear arc
`i→j` contains `b` then `arc ≥ n > T-1`, so the cap forces different
bits and the angle is the complement `T - arc ≤ T - n`.  If the arc
avoids `b`, all its cells vanish, so `arc ≤ ∑ r = δ`; different bits
would then give an angle `≥ n > T - 1`, so the bits are equal and the
angle is `arc ≤ δ`. -/
theorem saturated_angle_le {n : ℕ}
    (hn : 2 ≤ n) (hnT : (n : ℝ) ≤ T) (hT : T < n + 1)
    (hr : ∀ j, 0 ≤ f.r j)
    (hfan : ∑ j : Fin m, f.gap j = T)
    (hsat : ∑ j : Fin m, (f.q j - 1) = n - 1)
    (hcap : ∀ i j : Fin m, i ≠ j → f.angle T i j ≤ T - 1)
    {i j : Fin m} (hij : i ≠ j) :
    f.angle T i j ≤ T - n := by
  obtain ⟨b, hbn, hbo, -, hsr⟩ :=
    saturated_cells_unique (q := f.q) (r := f.r) hn hnT hT hr
      (by simpa [gap] using hfan) hsat
  have hgnn : ∀ t, 0 ≤ f.gap t := fun t =>
    add_nonneg (Nat.cast_nonneg _) (hr t)
  by_cases hb : b ∈ Finset.Ico (min i j) (max i j)
  · -- The arc contains the big gap: `arc ≥ n`, so bits must differ.
    have hA : (n : ℝ) ≤ f.arc i j := by
      have h1 : f.gap b ≤ f.arc i j :=
        Finset.single_le_sum (fun t _ => hgnn t) hb
      have hgb : (n : ℝ) ≤ f.gap b := by
        unfold gap
        have hbn' : (f.q b : ℝ) = n := by exact_mod_cast hbn
        linarith [hr b]
      linarith
    have hbit : f.bit i ≠ f.bit j := by
      intro he
      have hc := hcap i j hij
      unfold angle at hc
      rw [ite_eq_left he] at hc
      linarith
    unfold angle
    rw [ite_eq_right hbit]
    linarith
  · -- The arc avoids the big gap: all its cells vanish, so
    -- `arc ≤ ∑ r = δ`; different bits would violate the cap.
    have hsmall : f.arc i j ≤ ∑ t : Fin m, f.r t := by
      have h1 : f.arc i j = ∑ t ∈ Finset.Ico (min i j) (max i j), f.r t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htb : t ≠ b := fun e => hb (e ▸ ht)
        have hq : f.q t = 0 := hbo t htb
        unfold gap
        simp [hq]
      rw [h1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun t _ _ => hr t)
    rw [hsr] at hsmall
    have hbit : f.bit i = f.bit j := by
      by_contra hb2
      have hc := hcap i j hij
      unfold angle at hc
      rw [ite_eq_right hb2] at hc
      linarith
    unfold angle
    rw [ite_eq_left hbit]
    linarith

/-- **Full L2 — the bit/crossing predicate.**  At a saturated vertex,
two directions have different 2π-lifts iff their linear arc contains a
positive cell — by B1 that cell is the unique big gap `q b = n`.
This is the exact strict-checker predicate (wrap big gap ⇒ the right
side is empty, hence all bits equal). -/
theorem saturated_bits_iff {n : ℕ}
    (hn : 2 ≤ n) (hnT : (n : ℝ) ≤ T) (hT : T < n + 1)
    (hr : ∀ j, 0 ≤ f.r j)
    (hfan : ∑ j : Fin m, f.gap j = T)
    (hsat : ∑ j : Fin m, (f.q j - 1) = n - 1)
    (hcap : ∀ i j : Fin m, i ≠ j → f.angle T i j ≤ T - 1)
    {i j : Fin m} (hij : i ≠ j) :
    (f.bit i ≠ f.bit j) ↔
      ∃ t ∈ Finset.Ico (min i j) (max i j), 0 < f.q t := by
  obtain ⟨b, hbn, hbo, -, hsr⟩ :=
    saturated_cells_unique (q := f.q) (r := f.r) hn hnT hT hr
      (by simpa [gap] using hfan) hsat
  have hbmem_of_pos : ∀ t ∈ Finset.Ico (min i j) (max i j), 0 < f.q t →
      t = b := by
    intro t ht htq
    by_contra htb
    have hq : f.q t = 0 := hbo t htb
    omega
  have hiff : (∃ t ∈ Finset.Ico (min i j) (max i j), 0 < f.q t) ↔
      b ∈ Finset.Ico (min i j) (max i j) := by
    constructor
    · rintro ⟨t, ht, htq⟩
      rwa [hbmem_of_pos t ht htq] at ht
    · intro hb
      exact ⟨b, hb, by rw [hbn]; omega⟩
  rw [hiff]
  constructor
  · -- different bits ⇒ the arc contains `b`: else `arc ≤ δ` and the
    -- complement angle is `≥ n > T-1`, contradicting the cap.
    intro hbit
    by_contra hb
    have hsmall : f.arc i j ≤ ∑ t : Fin m, f.r t := by
      have h1 : f.arc i j = ∑ t ∈ Finset.Ico (min i j) (max i j), f.r t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htb : t ≠ b := fun e => hb (e ▸ ht)
        have hq : f.q t = 0 := hbo t htb
        unfold gap
        simp [hq]
      rw [h1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun t _ _ => hr t)
    rw [hsr] at hsmall
    have hc := hcap i j hij
    unfold angle at hc
    rw [ite_eq_right hbit] at hc
    linarith
  · -- arc contains `b` ⇒ `arc ≥ n`; equal bits would put the angle
    -- above the cap.
    intro hb he
    have hgnn : ∀ t, 0 ≤ f.gap t := fun t =>
      add_nonneg (Nat.cast_nonneg _) (hr t)
    have hA : (n : ℝ) ≤ f.arc i j := by
      have h1 : f.gap b ≤ f.arc i j :=
        Finset.single_le_sum (fun t _ => hgnn t) hb
      have hgb : (n : ℝ) ≤ f.gap b := by
        unfold gap
        have hbn' : (f.q b : ℝ) = n := by exact_mod_cast hbn
        linarith [hr b]
      linarith
    have hc := hcap i j hij
    unfold angle at hc
    rw [ite_eq_left he] at hc
    linarith

/-- **Wrap corollary of full L2.**  If the unique big cell sits at the
last position (the wrap gap of the cyclic order), no linear arc
contains it, so every direction pair has equal bits — the checker's
all-equal-bit degenerate case. -/
theorem saturated_bits_all_eq_last {m n : ℕ} (f : ProjFan (m + 1))
    (hn : 2 ≤ n) (hnT : (n : ℝ) ≤ T) (hT : T < n + 1)
    (hr : ∀ j, 0 ≤ f.r j)
    (hfan : ∑ j : Fin (m + 1), f.gap j = T)
    (hsat : ∑ j : Fin (m + 1), (f.q j - 1) = n - 1)
    (hcap : ∀ i j : Fin (m + 1), i ≠ j → f.angle T i j ≤ T - 1)
    (hlast : ∀ t : Fin (m + 1), 0 < f.q t → t = Fin.last m)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    f.bit i = f.bit j := by
  by_contra hb
  have h := (saturated_bits_iff hn hnT hT hr hfan hsat hcap hij).mp hb
  obtain ⟨t, ht, htq⟩ := h
  rw [hlast t htq, Finset.mem_Ico] at ht
  exact (not_le_of_gt ht.2) (Fin.le_last _)

end ProjFan

/-! ### The global fan system and L3 -/

/-- Position of the direction to vertex `j` inside vertex `i`'s cyclic
order — the inverse of `dir i` (the checker's `pos`).  Defined for all
`j`; meaningful exactly when `j ≠ i`, since `dir i` misses only `i`. -/
noncomputable def posOf {t : ℕ} (dir : Fin (t + 1) → Fin (t + 2))
    (j : Fin (t + 2)) : Fin (t + 1) :=
  if h : ∃ p, dir p = j then Classical.choose h
  else ⟨0, by omega⟩

theorem posOf_spec {t : ℕ} {dir : Fin (t + 1) → Fin (t + 2)}
    (hinj : Function.Injective dir) {i : Fin (t + 2)}
    (hne : ∀ p, dir p ≠ i) {j : Fin (t + 2)} (hji : j ≠ i) :
    dir (posOf dir j) = j := by
  have hex : ∃ p, dir p = j := by
    have hcard : (Finset.univ.image dir).card = t + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    have hsub : Finset.univ.image dir ⊆ Finset.univ.erase i := by
      intro x hx
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨hne p, Finset.mem_univ _⟩
    have hcard2 : (Finset.univ.erase i : Finset (Fin (t + 2))).card = t + 1 := by
      have h := Finset.card_erase_of_mem (Finset.mem_univ i)
      rw [Finset.card_fin] at h
      omega
    have heq : Finset.univ.image dir = Finset.univ.erase i :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hjm : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    rw [← heq] at hjm
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hjm
    exact ⟨p, hp⟩
  unfold posOf
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

theorem posOf_ne {t : ℕ} {dir : Fin (t + 1) → Fin (t + 2)}
    (hinj : Function.Injective dir) {i : Fin (t + 2)}
    (hne : ∀ p, dir p ≠ i) {j k : Fin (t + 2)}
    (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k) :
    posOf dir j ≠ posOf dir k := by
  intro e
  have h1 := posOf_spec hinj hne hji
  have h2 := posOf_spec hinj hne hki
  rw [e] at h1
  exact hjk (h1.symm.trans h2)

/-- **Global fan system** — `s+3` vertices (so `s ≥ 3` is automatic),
each with a `ProjFan` over the `s+2` other directions.  Every field is
part of the strict mode-A contract checked by
`tools/generic_model.py build_case(strict=True)`:

* `dir` is the checker's `order` (position ↔ vertex);
* `fan_sum` is the per-vertex fan equality `∑ gaps = n+δ`;
* `cap` is `∠ ≤ n+δ−1` on every position pair — the
  `Section4Legality.triAngle` contract in λ-units;
* `tri` is the triangle sum `∠i{j,k}+∠j{i,k}+∠k{i,j} = n+δ`. -/
structure FanSystem (s n : ℕ) (δ : ℝ) where
  fan : Fin (s + 3) → ProjFan (s + 2)
  dir : (v : Fin (s + 3)) → Fin (s + 2) → Fin (s + 3)
  dir_ne : ∀ v p, dir v p ≠ v
  dir_inj : ∀ v, Function.Injective (dir v)
  hδ0 : 0 ≤ δ
  hδ1 : δ < 1
  hr : ∀ v p, 0 ≤ (fan v).r p
  hr1 : ∀ v p, (fan v).r p < 1
  fan_sum : ∀ v, ∑ p : Fin (s + 2), (fan v).gap p = n + δ
  cap : ∀ (v : Fin (s + 3)) (i j : Fin (s + 2)), i ≠ j →
      (fan v).angle (n + δ) i j ≤ n + δ - 1
  tri : ∀ (i j k : Fin (s + 3)) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k),
      (fan i).angle (n + δ) (posOf (dir i) j) (posOf (dir i) k)
      + (fan j).angle (n + δ) (posOf (dir j) i) (posOf (dir j) k)
      + (fan k).angle (n + δ) (posOf (dir k) i) (posOf (dir k) j)
        = n + δ

namespace FanSystem

/-- Deficit-0 vertices: exponent `n - 1`. -/
def Saturated {s n : ℕ} {δ : ℝ} (F : FanSystem s n δ)
    (v : Fin (s + 3)) : Prop :=
  ∑ p : Fin (s + 2), ((F.fan v).q p - 1) = n - 1

variable {s n : ℕ} {δ : ℝ} (F : FanSystem s n δ)

/-- **L3 — two saturated vertices force `δ ≥ 1/2`.**  For any third
vertex `w`, L2-min gives `∠u{v,w} ≤ δ` and `∠v{u,w} ≤ δ`; the
triangle sum then gives `∠w{u,v} ≥ n - δ`, and the cap bounds it by
`n + δ - 1`, so `n - δ ≤ n + δ - 1`. -/
theorem two_saturated_ge_half (hn : 2 ≤ n) {u v w : Fin (s + 3)}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : F.Saturated u) (hv : F.Saturated v) :
    (1 : ℝ) / 2 ≤ δ := by
  have hT : (n : ℝ) ≤ n + δ := by linarith [F.hδ0]
  have hT1 : (n : ℝ) + δ < n + 1 := by linarith [F.hδ1]
  have hU' := ProjFan.saturated_angle_le hn hT hT1 (F.hr u)
      (F.fan_sum u) hu (F.cap u)
      (posOf_ne (F.dir_inj u) (F.dir_ne u) huv.symm huw.symm hvw)
  have hU : (F.fan u).angle (n + δ)
      (posOf (F.dir u) v) (posOf (F.dir u) w) ≤ δ := by linarith
  have hV' := ProjFan.saturated_angle_le hn hT hT1 (F.hr v)
      (F.fan_sum v) hv (F.cap v)
      (posOf_ne (F.dir_inj v) (F.dir_ne v) huv hvw.symm huw)
  have hV : (F.fan v).angle (n + δ)
      (posOf (F.dir v) u) (posOf (F.dir v) w) ≤ δ := by linarith
  have hW : (F.fan w).angle (n + δ)
      (posOf (F.dir w) u) (posOf (F.dir w) v) ≤ n + δ - 1 :=
    F.cap w _ _
      (posOf_ne (F.dir_inj w) (F.dir_ne w) huw hvw huv)
  have htri := F.tri u v w huv huw hvw
  linarith

/-- **L3 contrapositive** — two saturated vertices are impossible
below `δ = 1/2`: the strict disappearance of the `(0,0,·,·)` deficit
profiles found by the strict checker. -/
theorem two_saturated_lt_half_impossible {s n : ℕ} {δ : ℝ}
    (F : FanSystem s n δ) (hn : 2 ≤ n) {u v w : Fin (s + 3)}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : F.Saturated u) (hv : F.Saturated v) (hδ : δ < 1 / 2) :
    False :=
  absurd (F.two_saturated_ge_half hn huv huw hvw hu hv) (not_le.mpr hδ)

end FanSystem

/-! ### Bridge to the repository's exponent -/

/-- **Bridge — `Nat.floor (g/λ)` cells instantiate B1.**  For positive
gaps `g : Fin m → ℝ` summing to `π` with `n = ⌊π/λ⌋₊`, a saturated row
(`∑ j, (⌊g j/λ⌋₊ - 1) = n - 1` — the `gapScore`/`exponents` summand of
`Deletion.lean`) has exactly one cell of value `n`; all other cells
vanish.

The decomposition `g j / λ = q j + r j` with `r j ∈ [0,1)` is the
fractional part: `q j := ⌊g j/λ⌋₊`, `r j := g j/λ - q j`, and the fan
sum is `∑ g j / λ = π/λ = n + δ` for `δ := π/λ - n`. -/
theorem saturated_cells_unique_of_gaps {m : ℕ} {g : Fin m → ℝ}
    {lam : ℝ} (hlam : 0 < lam) (hg : ∀ j, 0 < g j) {n : ℕ}
    (hn : 2 ≤ n) (hnf : Nat.floor (Real.pi / lam) = n)
    (hsum : ∑ j : Fin m, g j = Real.pi)
    (hsat : ∑ j : Fin m, (Nat.floor (g j / lam) - 1) = n - 1) :
    ∃ b : Fin m, Nat.floor (g b / lam) = n
      ∧ (∀ j, j ≠ b → Nat.floor (g j / lam) = 0)
      ∧ (∀ b', 0 < Nat.floor (g b' / lam) → b' = b) := by
  have hq : ∀ j, 0 ≤ g j / lam :=
    fun j => div_nonneg (hg j).le hlam.le
  have hrnn : ∀ j, 0 ≤ g j / lam - (Nat.floor (g j / lam) : ℝ) := by
    intro j
    have h : (Nat.floor (g j / lam) : ℝ) ≤ g j / lam :=
      Nat.floor_le (hq j)
    linarith
  have hfan : ∑ j : Fin m,
      ((Nat.floor (g j / lam) : ℝ)
        + (g j / lam - (Nat.floor (g j / lam) : ℝ)))
      = Real.pi / lam := by
    have e : ∀ j, (Nat.floor (g j / lam) : ℝ)
        + (g j / lam - (Nat.floor (g j / lam) : ℝ)) = g j / lam :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => e j]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, hsum]
  have hnT : (n : ℝ) ≤ Real.pi / lam := by
    have h : (Nat.floor (Real.pi / lam) : ℝ) ≤ Real.pi / lam :=
      Nat.floor_le (div_nonneg Real.pi_nonneg hlam.le)
    rw [hnf] at h
    exact_mod_cast h
  have hT : Real.pi / lam < (n : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hnf] at h
    exact_mod_cast h
  have hb := saturated_cells_unique
      (q := fun j => Nat.floor (g j / lam))
      (r := fun j => g j / lam - (Nat.floor (g j / lam) : ℝ))
      hn hnT hT hrnn hfan hsat
  exact hb.imp fun b hb => ⟨hb.1, hb.2.1, hb.2.2.1⟩

/-! ### Sanity checks -/

section Sanity

/-- Concrete saturated fan, big gap at the **last** position (the wrap
gap): `q = [0,0,4]`, `r j = 1/6`, `T = 9/2` (`n = 4`, `δ = 1/2`).
B1 applies and the unique positive cell is `b = 2`.  This also
instantiates the admissible boundary `δ = 1/2`. -/
example : ∃ b : Fin 3, b = 2 := by
  obtain ⟨b, -, -, hb3, -⟩ := saturated_cells_unique (m := 3) (n := 4)
      (T := (9 : ℝ)/2)
      (q := fun j : Fin 3 => if j = 2 then 4 else 0)
      (r := fun _ : Fin 3 => (1 : ℝ)/6)
      (by norm_num) (by norm_num) (by norm_num)
      (fun _ => by norm_num)
      (by simp [Fin.sum_univ_three]; norm_num)
      (by decide)
  exact ⟨b, (hb3 2 (by decide)).symm⟩

/-- Concrete saturated fan, big gap at a **non-wrap** position:
`q = [0,4,0]`, `T = 9/2`.  B1 returns `b = 1`. -/
example : ∃ b : Fin 3, b = 1 := by
  obtain ⟨b, -, -, hb3, -⟩ := saturated_cells_unique (m := 3) (n := 4)
      (T := (9 : ℝ)/2)
      (q := fun j : Fin 3 => if j = 1 then 4 else 0)
      (r := fun _ : Fin 3 => (1 : ℝ)/6)
      (by norm_num) (by norm_num) (by norm_num)
      (fun _ => by norm_num)
      (by simp [Fin.sum_univ_three]; norm_num)
      (by decide)
  exact ⟨b, (hb3 1 (by decide)).symm⟩

end Sanity

end Jsp404

#print axioms Jsp404.saturated_cells_unique
#print axioms Jsp404.ProjFan.saturated_angle_le
#print axioms Jsp404.ProjFan.saturated_bits_iff
#print axioms Jsp404.ProjFan.saturated_bits_all_eq_last
#print axioms Jsp404.FanSystem.two_saturated_ge_half
#print axioms Jsp404.FanSystem.two_saturated_lt_half_impossible
#print axioms Jsp404.saturated_cells_unique_of_gaps
