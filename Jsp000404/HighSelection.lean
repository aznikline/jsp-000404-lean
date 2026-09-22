import Jsp000404.HighDebt
import Jsp000404.GadgetSelection

/-!
# High selection — the mechanical lemma stack of lane B (wave 2)

This file closes the *mechanical* nodes of the Lane-B decomposition
(`notes/LANE_B.md` §6), leaving `AllBadStrip` as the single explicitly
named open node (owned by lane B3).

## Definitions

* `Skeleton.saturated sk n v` — `k_v = n − 1` (deficit `d_v = 0`).
* `VertexData.badAt v t` — the bit-step condition at gap `t`:
  for every `a ≠ b`, `bits a ≠ bits b ↔ t ∈ arc a b`.
* `VertexData.bad v n` — some gap `t` is a heavy cell (`q_t = n`,
  all others `0`) *and* the bits split at it.

## Proved here (no `sorry`)

* `ModeA.sum_q_le` — mode A with `δ < 1` forces `Σ q ≤ n`.
* `VertexData.kexp_le` / `Skeleton.d_nonneg` — checker-style `q`-data
  (`0 ≤ q`, `Σ q ≤ n`) gives `k_v ≤ n − 1`, i.e. `d_v ≥ 0`.
* `saturated_iff` — `k_v = n − 1` iff `q = (n, 0, …, 0)` up to
  position (the §4 algebra), for `2 ≤ n`.
* `VertexData.badAt_or` / `saturated_dichotomy` — the saturated-vertex
  dichotomy of §4: either a direct arc contains the heavy cell
  (pure cap), or a complementary arc avoids it (fan+charge), or `v`
  is bad.
* `weight_ge_two_sat` — `5/2 < W` at `s = 4` gives two saturated
  vertices; the interface lift of `dyadic_two_zeros4`.
* `bad_saturated_angle_le` — at a bad saturated vertex every angle
  is `≤ δ` (the key geometric input: `Σ r_v = δ`, `arcQ ∈ {0, n}`).
* `three_sat_has_good` — three saturated vertices cannot all be bad
  in a mode-A-consistent skeleton with `2 ≤ n` and `δ < 1`: the
  triangle equality `Σ ∠ = n + δ ≤ 3δ` would force `n ≤ 2δ < 2`.
* `good_saturated_gadget` — `¬ bad` at a saturated vertex yields an
  explicit valid gadget of bound `≥ 1`: the pure-cap gadget
  (direct arc ∋ heavy cell) or the fan+charge gadget
  (complementary arc ∌ heavy cell).
* `gadgetSelection_high` — the full Lane-B reduction: assuming the
  `AllBadStrip` proposition (the lane-B3 node), every consistent
  `W > 5/2` skeleton admits a bound-`≥ 1` gadget.

## Open (elsewhere)

`AllBadStrip` — the two-saturated all-bad strip construction —
is stated as a `Prop` (`Jsp404.AllBadStrip`); lane B3 owns it.
-/

namespace Jsp404

open Finset
open Classical

/-! ### Definitions -/

namespace VertexData

variable {s : ℕ} (v : VertexData s)

/-- The bit-step condition at gap `t`: for every pair `a ≠ b` of
other vertices, the bits differ iff the arc `a → b` contains `t`.
This is `bad(v)` of `notes/LANE_B.md` §4 ("bits = threshold step at
`t*`, up to global flip"). -/
def badAt (t : Fin (s - 1)) : Prop :=
  ∀ a b : Fin s, a ≠ b → (v.bits a ≠ v.bits b ↔ t ∈ v.arc a b)

/-- `v` is *bad* at level `n`: a heavy cell `q_t = n` (all other
cells `0`) whose gap is exactly the bit-step cut.  A bad vertex
admits no local `δ ≥ 1` gadget. -/
def bad (n : ℕ) : Prop :=
  ∃ t : Fin (s - 1),
    v.q t = (n : ℤ) ∧ (∀ g ≠ t, v.q g = 0) ∧ v.badAt t

end VertexData

/-- Saturated vertex: `k_v = n − 1`, i.e. deficit `d_v = 0`. -/
def Skeleton.saturated {s : ℕ} (sk : Skeleton s) (n : ℕ)
    (v : Fin s) : Prop :=
  (sk.vtx v).kexp = (n : ℤ) - 1

theorem Skeleton.d_eq_zero_iff_saturated {s : ℕ} (sk : Skeleton s)
    (n : ℕ) (v : Fin s) :
    sk.d n v = 0 ↔ sk.saturated n v := by
  unfold Skeleton.d Skeleton.saturated VertexData.kexp
  omega

/-! ### `Σ q ≤ n` from mode A -/

theorem ModeA.sum_q_le {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hδ : δ < 1) (v : Fin s) :
    ∑ g, (sk.vtx v).q g ≤ (n : ℤ) := by
  have hf := hA.fan v
  have hr : (0 : ℝ) ≤ ∑ g, r v g :=
    Finset.sum_nonneg fun g _ => hA.r_nn v g
  have hlt : ((∑ g, (sk.vtx v).q g : ℤ) : ℝ) < (n : ℝ) + 1 := by
    have hcast : ((∑ g, (sk.vtx v).q g : ℤ) : ℝ)
        = ∑ g, ((sk.vtx v).q g : ℝ) := by push_cast; ring
    rw [hcast]
    linarith
  have : (∑ g, (sk.vtx v).q g : ℤ) < (n : ℤ) + 1 := by
    exact_mod_cast hlt
  omega

/-! ### `kexp ≤ n − 1` (i.e. `d ≥ 0`) from checker-style `q`-data -/

theorem VertexData.kexp_le {s n : ℕ} (v : VertexData s) (hn : 1 ≤ n)
    (hq : ∀ g, 0 ≤ v.q g) (hqn : ∑ g, v.q g ≤ (n : ℤ)) :
    v.kexp ≤ (n : ℤ) - 1 := by
  classical
  unfold VertexData.kexp
  set P := Finset.univ.filter (fun g => 2 ≤ v.q g) with hP
  have hsplit : ∑ g, max (v.q g - 1) 0
      = ∑ g ∈ P, (v.q g - 1) := by
    rw [hP, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : 2 ≤ v.q g
    · rw [if_pos hg, max_eq_left (by omega : (0:ℤ) ≤ v.q g - 1)]
    · rw [if_neg hg, max_eq_right (by omega : v.q g - 1 ≤ 0)]
  rw [hsplit]
  by_cases hPn : P.Nonempty
  · have hcard : (1 : ℤ) ≤ (P.card : ℤ) := by
      have : 1 ≤ P.card := Finset.card_pos.mpr hPn
      exact_mod_cast this
    have hsum : ∑ g ∈ P, (v.q g - 1) = (∑ g ∈ P, v.q g) - P.card := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        mul_one]
    rw [hsum]
    have hle : ∑ g ∈ P, v.q g ≤ ∑ g, v.q g :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => hq g)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hPn
    rw [hPn, Finset.sum_empty]
    omega

theorem Skeleton.d_nonneg {s n : ℕ} (sk : Skeleton s) (hn : 1 ≤ n)
    (hq : ∀ v g, 0 ≤ (sk.vtx v).q g)
    (hqn : ∀ v, ∑ g, (sk.vtx v).q g ≤ (n : ℤ)) (v : Fin s) :
    0 ≤ sk.d n v := by
  unfold Skeleton.d
  have := (sk.vtx v).kexp_le hn (hq v) (hqn v)
  omega

/-! ### `saturated_iff`: `k_v = n − 1 ↔ q = (n, 0, …, 0)` -/

theorem saturated_iff {s n : ℕ} (hn : 2 ≤ n) {v : VertexData s}
    (hq : ∀ g, 0 ≤ v.q g) (hqn : ∑ g, v.q g ≤ (n : ℤ)) :
    v.kexp = (n : ℤ) - 1 ↔
      ∃ t : Fin (s - 1),
        v.q t = (n : ℤ) ∧ ∀ g ≠ t, v.q g = 0 := by
  classical
  constructor
  · intro hk
    -- some cell has `q_t ≥ 2`
    have hpos : ∃ t : Fin (s - 1), 0 < max (v.q t - 1) 0 := by
      by_contra h
      push_neg at h
      have hle : ∑ g, max (v.q g - 1) 0 ≤ 0 :=
        Finset.sum_nonpos fun g _ => h g
      have : (1 : ℤ) ≤ (n : ℤ) - 1 := by omega
      unfold VertexData.kexp at hk
      omega
    obtain ⟨t, ht⟩ := hpos
    have hqt2 : 2 ≤ v.q t := by
      rcases lt_max_iff.mp ht with h | h <;> omega
    have hmaxt : max (v.q t - 1) 0 = v.q t - 1 :=
      max_eq_left (by omega)
    -- split the sums at `t`
    have hkexp : max (v.q t - 1) 0
        + ∑ g ∈ Finset.univ.erase t, max (v.q g - 1) 0
        = (n : ℤ) - 1 := by
      have h := Finset.add_sum_erase Finset.univ
        (fun g => max (v.q g - 1) 0) (Finset.mem_univ t)
      unfold VertexData.kexp at hk
      rw [hk] at h
      exact h
    have hqsum : v.q t + ∑ g ∈ Finset.univ.erase t, v.q g
        ≤ (n : ℤ) := by
      have h := Finset.add_sum_erase Finset.univ v.q
        (Finset.mem_univ t)
      rw [← h] at hqn
      exact hqn
    -- the slack `q_g − max(q_g−1,0)` is nonneg and sums to ≤ 0
    have hterm : ∀ g ∈ Finset.univ.erase t,
        (0 : ℤ) ≤ v.q g - max (v.q g - 1) 0 := by
      intro g _
      have h0 := hq g
      have hle : max (v.q g - 1) 0 ≤ v.q g :=
        max_le (by omega) h0
      omega
    have hslack : ∑ g ∈ Finset.univ.erase t,
        (v.q g - max (v.q g - 1) 0) ≤ 0 := by
      rw [Finset.sum_sub_distrib]
      have h1 : ∑ g ∈ Finset.univ.erase t, v.q g ≤ (n : ℤ) - v.q t :=
        by omega
      have h2 : ∑ g ∈ Finset.univ.erase t, max (v.q g - 1) 0
          = (n : ℤ) - v.q t := by
        rw [hmaxt] at hkexp
        omega
      linarith
    have hslack0 : ∑ g ∈ Finset.univ.erase t,
        (v.q g - max (v.q g - 1) 0) = 0 :=
      le_antisymm hslack
        (Finset.sum_nonneg fun g hg => hterm g hg)
    have hall : ∀ g ∈ Finset.univ.erase t,
        v.q g - max (v.q g - 1) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun g hg => hterm g hg)).mp hslack0
    refine ⟨t, ?_, ?_⟩
    · -- `q_t = n`: the erase-sums give `n − q_t = 0`
      have h2 : ∑ g ∈ Finset.univ.erase t, max (v.q g - 1) 0
          = (n : ℤ) - v.q t := by
        rw [hmaxt] at hkexp
        omega
      have hz : ∑ g ∈ Finset.univ.erase t, max (v.q g - 1) 0 = 0 := by
        apply Finset.sum_eq_zero
        intro g hg
        have := hall g hg
        omega
      omega
    · intro g hg
      have hgm : g ∈ Finset.univ.erase t :=
        Finset.mem_erase.mpr ⟨hg, Finset.mem_univ g⟩
      have h0 := hq g
      have := hall g hgm
      -- `q g = max (q g − 1) 0` with `q g ≥ 0` forces `q g = 0`
      by_contra hg0
      have : 1 ≤ v.q g := by omega
      have : max (v.q g - 1) 0 = v.q g - 1 := max_eq_left (by omega)
      omega
  · rintro ⟨t, hqt, hsupp⟩
    unfold VertexData.kexp
    rw [Finset.sum_eq_single t]
    · rw [hqt]
      have : (0 : ℤ) ≤ (n : ℤ) - 1 := by omega
      exact max_eq_left this
    · intro g _ hgt
      rw [hsupp g hgt]
      norm_num
    · simp

/-! ### The saturated-vertex dichotomy (pure logic) -/

/-- The dichotomy of `notes/LANE_B.md` §4: either a direct arc
contains `t` (pure-cap gadget), or a complementary arc avoids `t`
(fan+charge gadget), or `v` is bad at `t`. -/
theorem VertexData.badAt_or {s : ℕ} (v : VertexData s)
    (t : Fin (s - 1)) :
    (∃ a b : Fin s, a ≠ b ∧ v.bits a = v.bits b ∧ t ∈ v.arc a b)
    ∨ (∃ a b : Fin s, a ≠ b ∧ v.bits a ≠ v.bits b ∧ t ∉ v.arc a b)
    ∨ v.badAt t := by
  classical
  by_cases h : v.badAt t
  · exact Or.inr (Or.inr h)
  · unfold VertexData.badAt at h
    push_neg at h
    obtain ⟨a, b, hab, hiff⟩ := h
    rcases hiff with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · exact Or.inr (Or.inl ⟨a, b, hab, hP, hQ⟩)
    · exact Or.inl ⟨a, b, hab, hP, hQ⟩

/-- `saturated_dichotomy`: at a saturated vertex `v` (checker-style
`q`-data, `k_v = n − 1`), either a same-bit arc contains the heavy
cell (the pure-cap case), or a complementary arc avoids it (the
fan+charge case), or `v` is bad. -/
theorem saturated_dichotomy {s n : ℕ} (hn : 2 ≤ n)
    {v : VertexData s}
    (hq : ∀ g, 0 ≤ v.q g) (hqn : ∑ g, v.q g ≤ (n : ℤ))
    (hsat : v.kexp = (n : ℤ) - 1) :
    (∃ t : Fin (s - 1), ∃ a b : Fin s,
        v.q t = (n : ℤ) ∧ (∀ g ≠ t, v.q g = 0) ∧
        a ≠ b ∧ v.bits a = v.bits b ∧ t ∈ v.arc a b)
    ∨ (∃ t : Fin (s - 1), ∃ a b : Fin s,
        v.q t = (n : ℤ) ∧ (∀ g ≠ t, v.q g = 0) ∧
        a ≠ b ∧ v.bits a ≠ v.bits b ∧ t ∉ v.arc a b)
    ∨ v.bad n := by
  obtain ⟨t, hqt, hsupp⟩ := (saturated_iff hn hq hqn).mp hsat
  rcases v.badAt_or t with h | h | hbad
  · obtain ⟨a, b, hab, hbits, ht⟩ := h
    exact Or.inl ⟨t, a, b, hqt, hsupp, hab, hbits, ht⟩
  · obtain ⟨a, b, hab, hbits, ht⟩ := h
    exact Or.inr (Or.inl ⟨t, a, b, hqt, hsupp, hab, hbits, ht⟩)
  · exact Or.inr (Or.inr ⟨t, hqt, hsupp, hbad⟩)

/-! ### Arc-`q` support: `arcQ ∈ {0, n}` at a heavy cell -/

theorem VertexData.arcQ_eq_ite {s n : ℕ} (v : VertexData s)
    {t : Fin (s - 1)} (hqt : v.q t = (n : ℤ))
    (hsupp : ∀ g ≠ t, v.q g = 0) (a b : Fin s) :
    v.arcQ a b = if t ∈ v.arc a b then (n : ℤ) else 0 := by
  classical
  unfold VertexData.arcQ
  by_cases ht : t ∈ v.arc a b
  · rw [if_pos ht]
    rw [Finset.sum_eq_single t]
    · exact hqt
    · intro g _ hgt
      exact hsupp g hgt
    · simp [ht]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro g hg
    exact hsupp g (fun hgt => ht (hgt ▸ hg))

theorem VertexData.sum_q_eq {s n : ℕ} (v : VertexData s)
    {t : Fin (s - 1)} (hqt : v.q t = (n : ℤ))
    (hsupp : ∀ g ≠ t, v.q g = 0) :
    ∑ g, v.q g = (n : ℤ) := by
  classical
  rw [Finset.sum_eq_single t]
  · exact hqt
  · intro g _ hgt
    exact hsupp g hgt
  · simp

/-! ### `weight_ge_two_sat`: the interface lift of `dyadic_two_zeros4` -/

theorem weight_ge_two_sat {n : ℕ} {sk : Skeleton 4}
    (hd : ∀ v, 0 ≤ sk.d n v)
    (hW : (5 : ℚ) / 2 < sk.W n) :
    2 ≤ (Finset.univ.filter (sk.saturated n)).card := by
  classical
  have hcast : ∀ v : Fin 4, (((sk.d n v).toNat : ℤ)) = sk.d n v :=
    fun v => Int.toNat_of_nonneg (hd v)
  have hWR : (sk.W n : ℝ)
      = ∑ i : Fin 4, (2 : ℝ) ^ (-(sk.d n i)) := by
    simp only [Skeleton.W]
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Rat.cast_zpow, Rat.cast_ofNat]
  have hW' : (5 : ℝ) / 2
      < ∑ i : Fin 4, (2 : ℝ) ^ (-(((sk.d n i).toNat : ℕ) : ℤ)) := by
    have hsum : (∑ i : Fin 4,
          (2 : ℝ) ^ (-(((sk.d n i).toNat : ℕ) : ℤ)))
        = ∑ i : Fin 4, (2 : ℝ) ^ (-(sk.d n i)) :=
      Finset.sum_congr rfl fun i _ => by rw [hcast i]
    rw [hsum, ← hWR]
    have hlt : (((5 : ℚ) / 2 : ℚ) : ℝ) < (sk.W n : ℝ) :=
      Rat.cast_lt.mpr hW
    push_cast at hlt
    exact hlt
  obtain ⟨i, j, hij, hi0, hj0⟩ :=
    dyadic_two_zeros4 (fun v => (sk.d n v).toNat) hW'
  have hsi : sk.saturated n i :=
    (sk.d_eq_zero_iff_saturated n i).mp (by
      have h2 := hcast i
      have hi0' : (sk.d n i).toNat = 0 := hi0
      rw [hi0'] at h2
      simpa using h2.symm)
  have hsj : sk.saturated n j :=
    (sk.d_eq_zero_iff_saturated n j).mp (by
      have h2 := hcast j
      have hj0' : (sk.d n j).toNat = 0 := hj0
      rw [hj0'] at h2
      simpa using h2.symm)
  have hsub : ({i, j} : Finset (Fin 4))
      ⊆ Finset.univ.filter (sk.saturated n) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsj⟩
  have hcard : ({i, j} : Finset (Fin 4)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hij
  have hle := Finset.card_le_card hsub
  omega

/-- Packaged version: `d ≥ 0` from checker-style `q`-data. -/
theorem weight_ge_two_sat' {n : ℕ} (hn : 1 ≤ n) {sk : Skeleton 4}
    (hq : ∀ v g, 0 ≤ (sk.vtx v).q g)
    (hqn : ∀ v, ∑ g, (sk.vtx v).q g ≤ (n : ℤ))
    (hW : (5 : ℚ) / 2 < sk.W n) :
    2 ≤ (Finset.univ.filter (sk.saturated n)).card :=
  weight_ge_two_sat
    (fun v => sk.d_nonneg hn hq hqn v) hW

/-- Consistent version: `Σ q ≤ n` comes from the mode-A solution. -/
theorem weight_ge_two_sat_of_consistent {n : ℕ} (hn : 1 ≤ n)
    {sk : Skeleton 4}
    (hq : ∀ v g, 0 ≤ (sk.vtx v).q g)
    (hcons : sk.Consistent n)
    (hW : (5 : ℚ) / 2 < sk.W n) :
    2 ≤ (Finset.univ.filter (sk.saturated n)).card := by
  obtain ⟨r, δ, _hδ0, hδ1, hA⟩ := hcons
  exact weight_ge_two_sat' hn hq
    (fun v => hA.sum_q_le hδ1 v) hW

/-! ### `three_sat_has_good`: three bad saturated vertices force `n ≤ 2δ` -/

/-- At a bad saturated vertex every angle is at most `δ`:
direct angles see `arcQ = 0` (the heavy gap is outside the arc) and
complementary angles see `arcQ = n` (the heavy gap is inside), while
the fan equality gives `Σ_g r_{v,g} = δ`. -/
theorem bad_saturated_angle_le {s n : ℕ} {sk : Skeleton s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) {v a b : Fin s} (hab : a ≠ b)
    {t : Fin (s - 1)} (hqt : (sk.vtx v).q t = (n : ℤ))
    (hsupp : ∀ g ≠ t, (sk.vtx v).q g = 0)
    (hbad : (sk.vtx v).badAt t) :
    angleExpr n sk r δ v a b ≤ δ := by
  have hsumq : ∑ g, (sk.vtx v).q g = (n : ℤ) :=
    (sk.vtx v).sum_q_eq hqt hsupp
  have hsumr : ∑ g, r v g = δ := by
    have hf := hA.fan v
    have hqR : ((∑ g, (sk.vtx v).q g : ℤ) : ℝ) = (n : ℝ) := by
      exact_mod_cast hsumq
    rw [hqR] at hf
    linarith
  have hbadab := hbad a b hab
  have hArcQ := (sk.vtx v).arcQ_eq_ite hqt hsupp a b
  by_cases hbits : (sk.vtx v).bits a = (sk.vtx v).bits b
  · -- direct: `t ∉ arc`, `arcQ = 0`, `∠ = Σ_arc r ≤ Σ r = δ`
    have ht : t ∉ (sk.vtx v).arc a b :=
      fun ht => hbadab.mpr ht hbits
    unfold angleExpr
    rw [if_pos hbits, Finset.sum_add_distrib]
    have hA0 : ∑ g ∈ (sk.vtx v).arc a b, ((sk.vtx v).q g : ℝ)
        = 0 := by
      have h : (sk.vtx v).arcQ a b = 0 := by
        rw [hArcQ, if_neg ht]
      unfold VertexData.arcQ at h
      exact_mod_cast h
    rw [hA0, zero_add]
    calc ∑ g ∈ (sk.vtx v).arc a b, r v g
        ≤ ∑ g, r v g :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _)
            (fun g _ _ => hA.r_nn v g)
      _ = δ := hsumr
  · -- complementary: `t ∈ arc`, `arcQ = n`, `∠ = δ − Σ_arc r ≤ δ`
    have ht : t ∈ (sk.vtx v).arc a b := hbadab.mp hbits
    unfold angleExpr
    rw [if_neg hbits, Finset.sum_add_distrib]
    have hAn : ∑ g ∈ (sk.vtx v).arc a b, ((sk.vtx v).q g : ℝ)
        = (n : ℝ) := by
      have h : (sk.vtx v).arcQ a b = (n : ℤ) := by
        rw [hArcQ, if_pos ht]
      unfold VertexData.arcQ at h
      exact_mod_cast h
    have hnn : (0 : ℝ) ≤ ∑ g ∈ (sk.vtx v).arc a b, r v g :=
      Finset.sum_nonneg fun g _ => hA.r_nn v g
    linarith

/-- Three saturated vertices cannot all be bad: each triangle angle
would be `≤ δ`, so `n + δ ≤ 3δ`, i.e. `n ≤ 2δ < 2`. -/
theorem three_sat_has_good {s n : ℕ} (hn : 2 ≤ n)
    {sk : Skeleton s} {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hδ : δ < 1)
    (h3 : ∃ u v w : Fin s, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        sk.saturated n u ∧ sk.saturated n v ∧ sk.saturated n w) :
    ∃ v, sk.saturated n v ∧ ¬ (sk.vtx v).bad n := by
  obtain ⟨u, v, w, huv, huw, hvw, hsu, hsv, hsw⟩ := h3
  by_contra hcon
  push_neg at hcon
  obtain ⟨tu, htu, hsuppu, hbadu⟩ := hcon u hsu
  obtain ⟨tv, htv, hsuppv, hbadv⟩ := hcon v hsv
  obtain ⟨tw, htw, hsuppw, hbadw⟩ := hcon w hsw
  have hle1 := bad_saturated_angle_le hA hvw htu hsuppu hbadu
  have hle2 := bad_saturated_angle_le hA huw htv hsuppv hbadv
  have hle3 := bad_saturated_angle_le hA huv htw hsuppw hbadw
  have htri := hA.tri u v w huv huw hvw
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Extract three distinct members of a finset of card `≥ 3`. -/
theorem three_of_card_three {α : Type*} [DecidableEq α]
    {S : Finset α} (h : 3 ≤ S.card) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have h2 : 2 ≤ (S.erase a).card := by
    rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase a).card)
  obtain ⟨hba, hbS⟩ := Finset.mem_erase.mp hb
  have h1 : 1 ≤ ((S.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c, hc⟩ :=
    Finset.card_pos.mp (by omega : 0 < ((S.erase a).erase b).card)
  obtain ⟨hcb, hc'⟩ := Finset.mem_erase.mp hc
  obtain ⟨hca, hcS⟩ := Finset.mem_erase.mp hc'
  exact ⟨a, b, c, hba.symm, hca.symm, hcb.symm, ha, hbS, hcS⟩

/-- Cardinal form: `3 ≤ #{v | saturated v}` yields a good saturated
vertex. -/
theorem three_sat_has_good' {s n : ℕ} (hn : 2 ≤ n)
    {sk : Skeleton s} {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hδ : δ < 1)
    (h3 : 3 ≤ (Finset.univ.filter (sk.saturated n)).card) :
    ∃ v, sk.saturated n v ∧ ¬ (sk.vtx v).bad n := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ :=
    three_of_card_three h3
  rw [Finset.mem_filter] at ha hb hc
  exact three_sat_has_good hn hA hδ
    ⟨a, b, c, hab, hac, hbc, ha.2, hb.2, hc.2⟩

/-! ### `formSum` field lemmas and fan-only gadget arithmetic -/

namespace LinForm

theorem coef_formSum {s : ℕ} (l : List (LinForm s)) (v : Fin s)
    (g : Fin (s - 1)) :
    (formSum l).coef v g = (l.map fun f => f.coef v g).sum := by
  induction l with
  | nil => rfl
  | cons f fs ih =>
      show (f + formSum fs).coef v g = f.coef v g + (fs.map _).sum
      rw [show (f + formSum fs).coef v g
          = f.coef v g + (formSum fs).coef v g from
        congrFun (congrFun (coef_add f (formSum fs)) v) g, ih]

theorem dco_formSum {s : ℕ} (l : List (LinForm s)) :
    (formSum l).dco = (l.map fun f => f.dco).sum := by
  induction l with
  | nil => rfl
  | cons f fs ih =>
      show (f + formSum fs).dco = f.dco + (fs.map _).sum
      rw [dco_add, ih]

theorem con_formSum {s : ℕ} (l : List (LinForm s)) :
    (formSum l).con = (l.map fun f => f.con).sum := by
  induction l with
  | nil => rfl
  | cons f fs ih =>
      show (f + formSum fs).con = f.con + (fs.map _).sum
      rw [con_add, ih]

end LinForm

private theorem finRange_map_sum {s : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Fin s → M) :
    ((List.finRange s).map F).sum = ∑ w : Fin s, F w :=
  rfl

namespace Gadget

/-- For a gadget with no links, the residual coefficient on
`r_{x,gg}` is just the fan weight at `x`. -/
theorem coef_eq_fans {s : ℕ} (n : ℕ) (sk : Skeleton s) (g : Gadget s)
    (hl : g.links = []) (x : Fin s) (gg : Fin (s - 1)) :
    g.coef n sk x gg = g.fans x := by
  show (LinForm.formSum _).coef x gg = _
  rw [hl, List.map_nil, List.append_nil, LinForm.coef_formSum,
    List.map_map, finRange_map_sum]
  rw [Finset.sum_eq_single x]
  · show (g.fans x • fanForm n sk x).coef x gg = g.fans x
    rw [show (g.fans x • fanForm n sk x).coef x gg
        = g.fans x * (fanForm n sk x).coef x gg from
      congrFun (congrFun (LinForm.coef_smul _ _) x) gg]
    show g.fans x * (if x = x then (1:ℤ) else 0) = g.fans x
    rw [if_pos rfl, mul_one]
  · intro w _ hwx
    show (g.fans w • fanForm n sk w).coef x gg = 0
    rw [show (g.fans w • fanForm n sk w).coef x gg
        = g.fans w * (fanForm n sk w).coef x gg from
      congrFun (congrFun (LinForm.coef_smul _ _) x) gg]
    show g.fans w * (if x = w then (1:ℤ) else 0) = 0
    rw [if_neg (Ne.symm hwx), mul_zero]
  · simp

/-- For a gadget with no links, `dco = -Σ fans`. -/
theorem dco_eq_neg_fans {s : ℕ} (n : ℕ) (sk : Skeleton s)
    (g : Gadget s) (hl : g.links = []) :
    (g.form n sk).dco = -∑ w : Fin s, g.fans w := by
  show (LinForm.formSum _).dco = _
  rw [hl, List.map_nil, List.append_nil, LinForm.dco_formSum,
    List.map_map, finRange_map_sum]
  have hterm : ∀ w : Fin s,
      (g.fans w • fanForm n sk w).dco = -g.fans w := by
    intro w
    rw [LinForm.dco_smul]
    show g.fans w * (-1) = -g.fans w
    rw [mul_neg, mul_one]
  show (∑ w : Fin s, (g.fans w • fanForm n sk w).dco)
      = -∑ w : Fin s, g.fans w
  rw [Finset.sum_congr rfl fun w _ => hterm w,
    Finset.sum_neg_distrib]

/-- For a gadget with no links,
`con = Σ_w fans_w · (Σ q_w − n)`. -/
theorem con_eq_fans {s : ℕ} (n : ℕ) (sk : Skeleton s) (g : Gadget s)
    (hl : g.links = []) :
    (g.form n sk).con
      = ∑ w : Fin s,
        g.fans w * ((∑ g, (sk.vtx w).q g) - (n : ℤ)) := by
  show (LinForm.formSum _).con = _
  rw [hl, List.map_nil, List.append_nil, LinForm.con_formSum,
    List.map_map, finRange_map_sum]
  apply Finset.sum_congr rfl
  intro w _
  show (g.fans w • fanForm n sk w).con = _
  rw [LinForm.con_smul]
  show g.fans w * ((∑ g, (sk.vtx w).q g) - (n : ℤ)) = _
  rfl

end Gadget

/-! ### The two local gadget constructions -/

/-- Pure-cap gadget: a single `piLam` cap on a direct arc
containing the heavy cell (`arcQ = n` gives bound `1`). -/
def pureCapGadget {s : ℕ} (v a b : Fin s) (t : Fin (s - 1)) :
    Gadget s where
  fans := fun _ => 0
  links := []
  charges := []
  caps := [⟨v, .piLam, a, b, t, 1⟩]

/-- Fan+charge gadget: fan weight `+1` at `v`, one complementary
charge on an arc avoiding the heavy cell (`arcQ = 0` gives `K = 1`,
fan form gives `c = 1`, `C = 0`). -/
def fanChargeGadget {s : ℕ} (v a b : Fin s) : Gadget s where
  fans := fun w => if w = v then 1 else 0
  links := []
  charges := [(v, a, b)]
  caps := []

theorem pureCapGadget_valid {s n : ℕ} {sk : Skeleton s}
    {v a b : Fin s} {t : Fin (s - 1)}
    (hab : a ≠ b) (hdir : (sk.vtx v).bits a = (sk.vtx v).bits b) :
    (pureCapGadget v a b t).Valid n sk := by
  classical
  have hfans : (pureCapGadget v a b t).fans = fun _ => (0 : ℤ) := rfl
  have hcaps : (pureCapGadget v a b t).caps
      = [⟨v, .piLam, a, b, t, 1⟩] := rfl
  have hcoef : ∀ x : Fin s, ∀ gg : Fin (s - 1),
      (pureCapGadget v a b t).coef n sk x gg = 0 := by
    intro x gg
    rw [Gadget.coef_eq_fans n sk _ rfl x gg, hfans]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [hfans]
    exact Or.inr (Or.inr rfl)
  · intro l hl
    cases hl
  · intro e he
    cases he
  · exact List.Pairwise.nil
  · intro e he
    rw [hcaps, List.mem_singleton] at he
    subst he
    exact ⟨by norm_num, hab, not_ne_iff.mpr hdir⟩
  · intro x gg
    rw [hcoef x gg]
    simp only [neg_zero, max_self]
    apply List.sum_nonneg
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨e, he, rfl⟩ := hy
    rw [List.mem_filter] at he
    obtain ⟨he1, -⟩ := he
    rw [hcaps, List.mem_singleton] at he1
    subst he1
    show (0 : ℤ) ≤ (1 : ℤ) * 1
    norm_num
  · show (0 : ℤ)
      < (pureCapGadget v a b t).cc n sk
        + (pureCapGadget v a b t).uu
    have hcc : (pureCapGadget v a b t).cc n sk = 0 := by
      show -((pureCapGadget v a b t).form n sk).dco = 0
      rw [Gadget.dco_eq_neg_fans n sk _ rfl]
      have : ∑ w : Fin s, (pureCapGadget v a b t).fans w = 0 := by
        rw [hfans]
        exact Finset.sum_const_zero
      rw [this]
      norm_num
    have huu : (pureCapGadget v a b t).uu = 1 := by
      show ((pureCapGadget v a b t).caps.map
          fun e => e.m * e.u).sum = 1
      rw [hcaps]
      simp only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      show (1 : ℤ) * (1 : ℤ) + 0 = 1
      norm_num
    rw [hcc, huu]
    norm_num

theorem pureCapGadget_bound {s n : ℕ} {sk : Skeleton s}
    {v a b : Fin s} {t : Fin (s - 1)}
    (hArcQ : (sk.vtx v).arcQ a b = (n : ℤ)) :
    (pureCapGadget v a b t).bound n sk = 1 := by
  classical
  have hfans : (pureCapGadget v a b t).fans = fun _ => (0 : ℤ) := rfl
  have hcaps : (pureCapGadget v a b t).caps
      = [⟨v, .piLam, a, b, t, 1⟩] := rfl
  have hcc : (pureCapGadget v a b t).cc n sk = 0 := by
    show -((pureCapGadget v a b t).form n sk).dco = 0
    rw [Gadget.dco_eq_neg_fans n sk _ rfl]
    have : ∑ w : Fin s, (pureCapGadget v a b t).fans w = 0 := by
      rw [hfans]
      exact Finset.sum_const_zero
    rw [this]
    norm_num
  have hCC : (pureCapGadget v a b t).CC n sk = 0 := by
    show -((pureCapGadget v a b t).form n sk).con = 0
    rw [Gadget.con_eq_fans n sk _ rfl]
    have : ∑ w : Fin s, (pureCapGadget v a b t).fans w
        * ((∑ g, (sk.vtx w).q g) - (n : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      rw [hfans]
      show (0 : ℤ) * _ = 0
      rw [zero_mul]
    rw [this]
    norm_num
  have hK : (pureCapGadget v a b t).K n sk = 0 := rfl
  have hBcap : (pureCapGadget v a b t).Bcap n sk = -1 := by
    show ((pureCapGadget v a b t).caps.map
        fun e => e.m * e.B n sk).sum = -1
    rw [hcaps]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    show (1 : ℤ) * ((n : ℤ) - 1 - (sk.vtx v).arcQ a b) + 0 = -1
    rw [hArcQ]
    norm_num
  have huu : (pureCapGadget v a b t).uu = 1 := by
    show ((pureCapGadget v a b t).caps.map
        fun e => e.m * e.u).sum = 1
    rw [hcaps]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    show (1 : ℤ) * (1 : ℤ) + 0 = 1
    norm_num
  unfold Gadget.bound
  rw [hcc, huu, hK, hBcap, hCC]
  norm_num

theorem fanChargeGadget_valid {s n : ℕ} {sk : Skeleton s}
    {v a b : Fin s} {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hab : a ≠ b)
    (hcomp : (sk.vtx v).comp a b)
    (hArcQ0 : (sk.vtx v).arcQ a b = 0) :
    (fanChargeGadget v a b).Valid n sk := by
  classical
  have hfans : (fanChargeGadget v a b).fans
      = fun w => if w = v then (1 : ℤ) else 0 := rfl
  have hcharges : (fanChargeGadget v a b).charges
      = [(v, a, b)] := rfl
  have hcaps : (fanChargeGadget v a b).caps = [] := rfl
  -- the charge arc is nonempty: `1 ≤ Σ_arc r` from the
  -- complementary angle bound
  have hne : ((sk.vtx v).arc a b).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hcb := Gadget.charge_bound n sk hA hab hcomp
    rw [hArcQ0, hne, Finset.sum_empty] at hcb
    norm_num at hcb
  have hfansum : ∑ w : Fin s, (fanChargeGadget v a b).fans w
      = 1 := by
    rw [Finset.sum_eq_single v]
    · show (if v = v then (1 : ℤ) else 0) = 1
      rw [if_pos rfl]
    · intro w _ hwv
      show (if w = v then (1 : ℤ) else 0) = 0
      rw [if_neg hwv]
    · simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    show (if w = v then (1 : ℤ) else 0) = 1 ∨
      (if w = v then (1 : ℤ) else 0) = -1 ∨
        (if w = v then (1 : ℤ) else 0) = 0
    by_cases hw : w = v
    · rw [if_pos hw]
      exact Or.inl rfl
    · rw [if_neg hw]
      exact Or.inr (Or.inr rfl)
  · intro l hl
    cases hl
  · intro e he
    rw [hcharges, List.mem_singleton] at he
    subst he
    show (v, a, b).2.1 ≠ (v, a, b).2.2
      ∧ (sk.vtx (v, a, b).1).comp (v, a, b).2.1 (v, a, b).2.2
      ∧ ((sk.vtx (v, a, b).1).arc (v, a, b).2.1 (v, a, b).2.2).Nonempty
      ∧ ∀ gg ∈ (sk.vtx (v, a, b).1).arc (v, a, b).2.1 (v, a, b).2.2,
          0 < (fanChargeGadget v a b).coef n sk (v, a, b).1 gg
    refine ⟨hab, hcomp, hne, ?_⟩
    intro gg _
    show (0 : ℤ) < (fanChargeGadget v a b).coef n sk v gg
    rw [Gadget.coef_eq_fans n sk _ rfl v gg]
    show (0 : ℤ) < if v = v then 1 else 0
    rw [if_pos rfl]
    norm_num
  · rw [hcharges]
    apply List.pairwise_cons.mpr
    exact ⟨fun y hy => (List.not_mem_nil hy).elim,
      List.Pairwise.nil⟩
  · intro e he
    rw [hcaps] at he
    cases he
  · intro x gg
    have hc0 : (0 : ℤ) ≤ (fanChargeGadget v a b).coef n sk x gg := by
      rw [Gadget.coef_eq_fans n sk _ rfl x gg]
      show (0 : ℤ) ≤ if x = v then (1 : ℤ) else 0
      by_cases hx : x = v
      · rw [if_pos hx]; norm_num
      · rw [if_neg hx]
    have hmax : max (-((fanChargeGadget v a b).coef n sk x gg)) 0
        = 0 := max_eq_right (neg_nonpos.mpr hc0)
    rw [hmax, hcaps]
    simp
  · show (0 : ℤ)
      < (fanChargeGadget v a b).cc n sk
        + (fanChargeGadget v a b).uu
    have hcc : (fanChargeGadget v a b).cc n sk = 1 := by
      show -((fanChargeGadget v a b).form n sk).dco = 1
      rw [Gadget.dco_eq_neg_fans n sk _ rfl, hfansum]
      norm_num
    have huu : (fanChargeGadget v a b).uu = 0 := by
      show ((fanChargeGadget v a b).caps.map
          fun e => e.m * e.u).sum = 0
      rw [hcaps]
      simp
    rw [hcc, huu]
    norm_num

theorem fanChargeGadget_bound {s n : ℕ} {sk : Skeleton s}
    {v a b : Fin s}
    (hne : ((sk.vtx v).arc a b).Nonempty)
    (hArcQ0 : (sk.vtx v).arcQ a b = 0)
    (hsumq : ∑ g, (sk.vtx v).q g = (n : ℤ)) :
    (fanChargeGadget v a b).bound n sk = 1 := by
  classical
  have hfans : (fanChargeGadget v a b).fans
      = fun w => if w = v then (1 : ℤ) else 0 := rfl
  have hcharges : (fanChargeGadget v a b).charges
      = [(v, a, b)] := rfl
  have hcaps : (fanChargeGadget v a b).caps = [] := rfl
  have hfansum : ∑ w : Fin s, (fanChargeGadget v a b).fans w
      = 1 := by
    rw [Finset.sum_eq_single v]
    · show (if v = v then (1 : ℤ) else 0) = 1
      rw [if_pos rfl]
    · intro w _ hwv
      show (if w = v then (1 : ℤ) else 0) = 0
      rw [if_neg hwv]
    · simp
  have hcc : (fanChargeGadget v a b).cc n sk = 1 := by
    show -((fanChargeGadget v a b).form n sk).dco = 1
    rw [Gadget.dco_eq_neg_fans n sk _ rfl, hfansum]
    norm_num
  have hcon0 : ((fanChargeGadget v a b).form n sk).con = 0 := by
    rw [Gadget.con_eq_fans n sk _ rfl]
    rw [Finset.sum_eq_single v]
    · show (if v = v then (1 : ℤ) else 0)
          * ((∑ g, (sk.vtx v).q g) - (n : ℤ)) = 0
      rw [if_pos rfl, one_mul, hsumq]
      norm_num
    · intro w _ hwv
      show (if w = v then (1 : ℤ) else 0) * _ = 0
      rw [if_neg hwv, zero_mul]
    · simp
  have hCC : (fanChargeGadget v a b).CC n sk = 0 := by
    show -((fanChargeGadget v a b).form n sk).con = 0
    rw [hcon0]
    norm_num
  have hK : (fanChargeGadget v a b).K n sk = 1 := by
    show ((fanChargeGadget v a b).charges.map
        fun e => (fanChargeGadget v a b).chargeGain n sk e.1
          e.2.1 e.2.2).sum = 1
    rw [hcharges]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    show (fanChargeGadget v a b).chargeGain n sk v a b = 1
    unfold Gadget.chargeGain
    rw [dif_pos hne]
    have hmin : (((sk.vtx v).arc a b).image
        ((fanChargeGadget v a b).coef n sk v)).min'
          (hne.image ((fanChargeGadget v a b).coef n sk v))
        = 1 := by
      have hmem := Finset.min'_mem _
        (hne.image ((fanChargeGadget v a b).coef n sk v))
      rw [Finset.mem_image] at hmem
      obtain ⟨gg, _, hgg⟩ := hmem
      rw [← hgg, Gadget.coef_eq_fans n sk _ rfl v gg]
      show (if v = v then (1 : ℤ) else 0) = 1
      rw [if_pos rfl]
    rw [hmin, hArcQ0]
    norm_num
  have hBcap : (fanChargeGadget v a b).Bcap n sk = 0 := by
    show ((fanChargeGadget v a b).caps.map
        fun e => e.m * e.B n sk).sum = 0
    rw [hcaps]
    simp
  have huu : (fanChargeGadget v a b).uu = 0 := by
    show ((fanChargeGadget v a b).caps.map
        fun e => e.m * e.u).sum = 0
    rw [hcaps]
    simp
  unfold Gadget.bound
  rw [hcc, huu, hK, hBcap, hCC]
  norm_num

/-! ### `good_saturated_gadget` -/

/-- A saturated vertex that is not bad admits a bound-`1` gadget:
the pure cap on a direct arc through the heavy cell, or the
fan+charge gadget on a complementary arc avoiding it. -/
theorem good_saturated_gadget {s n : ℕ} {sk : Skeleton s}
    {v : Fin s} {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) {t : Fin (s - 1)}
    (hqt : (sk.vtx v).q t = (n : ℤ))
    (hsupp : ∀ g ≠ t, (sk.vtx v).q g = 0)
    (hnb : ¬ (sk.vtx v).badAt t) :
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) ≤ g.bound n sk := by
  classical
  rcases (sk.vtx v).badAt_or t with h | h | hbad
  · obtain ⟨a, b, hab, hbits, ht⟩ := h
    have hArcQ : (sk.vtx v).arcQ a b = (n : ℤ) := by
      rw [(sk.vtx v).arcQ_eq_ite hqt hsupp a b, if_pos ht]
    exact ⟨pureCapGadget v a b t,
      pureCapGadget_valid hab hbits,
      (pureCapGadget_bound hArcQ).ge⟩
  · obtain ⟨a, b, hab, hbits, ht⟩ := h
    have hArcQ0 : (sk.vtx v).arcQ a b = 0 := by
      rw [(sk.vtx v).arcQ_eq_ite hqt hsupp a b, if_neg ht]
    have hne : ((sk.vtx v).arc a b).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hcb := Gadget.charge_bound n sk hA hab hbits
      rw [hArcQ0, hne, Finset.sum_empty] at hcb
      norm_num at hcb
    have hsumq : ∑ g, (sk.vtx v).q g = (n : ℤ) :=
      (sk.vtx v).sum_q_eq hqt hsupp
    exact ⟨fanChargeGadget v a b,
      fanChargeGadget_valid hA hab hbits hArcQ0,
      (fanChargeGadget_bound hne hArcQ0 hsumq).ge⟩
  · exact absurd hbad hnb

/-- Packaged form: takes `saturated`/`bad` plus the checker `q`
bounds, produces `t` via `saturated_iff`. -/
theorem good_saturated_gadget' {s n : ℕ} (hn : 2 ≤ n)
    {sk : Skeleton s} {v : Fin s}
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ)
    (hq : ∀ g, 0 ≤ (sk.vtx v).q g)
    (hqn : ∑ g, (sk.vtx v).q g ≤ (n : ℤ))
    (hsat : sk.saturated n v) (hnb : ¬ (sk.vtx v).bad n) :
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) ≤ g.bound n sk := by
  obtain ⟨t, hqt, hsupp⟩ := (saturated_iff hn hq hqn).mp hsat
  exact good_saturated_gadget hA hqt hsupp
    (fun hb => hnb ⟨t, hqt, hsupp, hb⟩)

/-! ### The open node and the assembled reduction -/

/-- **Lane B3's node** (`all_bad_strip`, `notes/LANE_B.md` §6 H4):
a consistent `W > 5/2` skeleton in which *every* saturated vertex is
bad still admits a bound-`≥ 1` gadget.  CHECKER-VALIDATED; not
proved — left open for lane B3. -/
def AllBadStrip (s n : ℕ) : Prop :=
  ∀ sk : Skeleton s, sk.Consistent n → (5 : ℚ) / 2 < sk.W n →
    (∀ v : Fin s, sk.saturated n v → (sk.vtx v).bad n) →
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) ≤ g.bound n sk

/-- The assembled Lane-B reduction: modulo `AllBadStrip`, every
consistent `W > 5/2` skeleton at `s = 4`, `n ≥ 2` with checker-style
nonnegative `q`-cells admits a valid gadget of bound `≥ 1`
(score `≥ 2`). -/
theorem gadgetSelection_high {n : ℕ} (hn : 2 ≤ n) {sk : Skeleton 4}
    (hq : ∀ v g, 0 ≤ (sk.vtx v).q g)
    (hcons : sk.Consistent n)
    (hW : (5 : ℚ) / 2 < sk.W n)
    (hstrip : AllBadStrip 4 n) :
    ∃ g : Gadget 4, g.Valid n sk ∧ (1 : ℚ) ≤ g.bound n sk := by
  classical
  obtain ⟨r, δ, hδ0, hδ1, hA⟩ := hcons
  have hqn : ∀ v : Fin 4, ∑ g, (sk.vtx v).q g ≤ (n : ℤ) :=
    fun v => hA.sum_q_le hδ1 v
  have h2 := weight_ge_two_sat' (by omega : 1 ≤ n) hq hqn hW
  by_cases h3 : 3 ≤ (Finset.univ.filter (sk.saturated n)).card
  · obtain ⟨v, hsv, hnbv⟩ := three_sat_has_good' hn hA hδ1 h3
    exact good_saturated_gadget' hn hA (hq v) (hqn v) hsv hnbv
  · by_cases hall : ∀ v : Fin 4,
        sk.saturated n v → (sk.vtx v).bad n
    · exact hstrip sk ⟨r, δ, hδ0, hδ1, hA⟩ hW hall
    · push_neg at hall
      obtain ⟨v, hsv, hnbv⟩ := hall
      exact good_saturated_gadget' hn hA (hq v) (hqn v) hsv hnbv

end Jsp404
