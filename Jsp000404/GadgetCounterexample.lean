import Jsp000404.GadgetSelection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Gadget counterexample — `GadgetSelectionLow` is FALSE as stated

The Lean skeleton model (`VertexData`) does **not** require

* `pos : Fin s → Fin (s - 1)` to be injective on the other vertices
  (the checker always uses a genuine permutation `order`), nor
* `q : Fin (s - 1) → ℤ` to be nonneg (the checker uses `0 ≤ q ≤ n`).

This admits a **ghost vertex**: collapse every other vertex's position
to `0`.  All arcs at `v` are empty, so every angle `∠v{a,b}` is the
empty direct arc `0` — no angle bound touches `v` at all — while a
signed cell vector `q = (M, -M + c)` keeps `Σq` small (fan feasible)
and makes `k_v = Σ_g max (q_g - 1) 0` arbitrarily large, inflating
`W` without bound.  Because `v` supplies angle `0` to every triangle
it inhabits, the *other* vertices must cover the whole triangle sum
`n + δ`; at `s = 3`, `n = 2`, `δ = 0` this is feasible with two
complementary arcs at value `n - 1 + δ = 1`.

The skeleton below (`ghostSk`) therefore satisfies

* `ModeA 2 ghostSk ghostR 0` with `δ = 0`  (so `Consistent`),
* `ghostSk.W 2 = 3 > 2`,

and by the *already proved* soundness theorem `gadget_ge_half`
(`bound ≥ 1/2` forces `δ ≥ 1/2` on every mode-A solution) **no**
valid gadget can attain `bound ≥ 1/2`: any such gadget would
contradict the `δ = 0` solution.  Hence

    `GadgetSelectionLow 3 2`   is FALSE, and therefore
    `∀ s n, GadgetSelectionLow s n`  is FALSE

(and the same instance disproves `GadgetSelectionHigh 3 2`, since
`W = 3 > 5/2`).

The repair: restrict to *proper* skeletons — `pos` injective on the
other vertices — matching the checker's `order = permutation`.
`GadgetSelectionLowP` below is the corrected, still-open statement;
`selection_low_soundP` is its proved soundness reduction.

## Data

`v0` (ghost): `pos = (0,0,0)`, `bits = fff`, `q = (3,-2)`, `r = (½,½)`.
`v1`: `pos = (0,0,1)`, `bits = fft`, `q = (0,0)`, `r = (1,1)`.
`v2`: `pos = (0,1,0)`, `bits = ftf`, `q = (0,0)`, `r = (1,1)`.

Angles: all `∠0{·,·} = 0`; `∠1{0,2} = ∠1{1,2} = ∠2{0,1} = ∠2{1,2} = 1`
(complementary arcs `{0}` with `q = 0`, `r = 1`); `∠1{0,1} = ∠2{0,2} = 0`
(empty direct arcs).  Triangle: `0 + 1 + 1 = 2 = n + δ`.  `k = (2,0,0)`,
`W = 2 + 1/2 + 1/2 = 3`.
-/

namespace Jsp404

/-- The ghost skeleton at `s = 3`, `n = 2`. -/
def ghostSk : Skeleton 3 where
  vtx v := match v with
    | 0 => ⟨fun _ => 0, fun _ => false, ![3, -2]⟩
    | 1 => ⟨![0, 0, 1], ![false, false, true], ![0, 0]⟩
    | _ => ⟨![0, 1, 0], ![false, true, false], ![0, 0]⟩

/-- The mode-A solution: `r = (½,½)` at the ghost, `r = (1,1)`
elsewhere, `δ = 0`. -/
noncomputable def ghostR : Fin 3 → Fin 2 → ℝ := fun v _ =>
  if v = 0 then 1 / 2 else 1

/-- Value of `∠x{a,b}` for the ghost skeleton (verified below):
`1` on the four complementary `{0}`-arcs, `0` elsewhere. -/
private noncomputable def angVal : Fin 3 → Fin 3 → Fin 3 → ℝ
  | 0, _, _ => 0
  | 1, 0, 2 => 1
  | 1, 1, 2 => 1
  | 1, 2, 0 => 1
  | 1, 2, 1 => 1
  | 2, 0, 1 => 1
  | 2, 1, 0 => 1
  | 2, 1, 2 => 1
  | 2, 2, 1 => 1
  | _, _, _ => 0

/-- Arc values for the ghost skeleton: `{0}` for the complementary
arcs, `∅` elsewhere (all of `v0`'s arcs are empty — the ghost).
At `v1` the pairs containing `2` see gap `0`; at `v2` the pairs
containing `1`. -/
private def arcVal : Fin 3 → Fin 3 → Fin 3 → Finset (Fin (3 - 1))
  | 1, 0, 2 => {0}
  | 1, 1, 2 => {0}
  | 1, 2, 0 => {0}
  | 1, 2, 1 => {0}
  | 2, 0, 1 => {0}
  | 2, 1, 0 => {0}
  | 2, 1, 2 => {0}
  | 2, 2, 1 => {0}
  | _, _, _ => ∅

private theorem ghost_arc (x a b : Fin 3) :
    (ghostSk.vtx x).arc a b = arcVal x a b := by
  fin_cases x <;> fin_cases a <;> fin_cases b <;> native_decide

private theorem ghost_angle (x a b : Fin 3) :
    angleExpr 2 ghostSk ghostR 0 x a b = angVal x a b := by
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    (simp only [angleExpr, angVal, ghost_arc, arcVal]
     <;> simp only [ghostSk, ghostR, Matrix.cons_val_zero,
       Matrix.cons_val_one, Matrix.head_cons]
     <;> norm_num)

/-- The ghost data is a genuine mode-A solution at `δ = 0`. -/
theorem ghostSk_modeA : ModeA 2 ghostSk ghostR 0 where
  r_nn := by
    intro v g
    fin_cases v <;> fin_cases g <;> simp [ghostR] <;> norm_num
  r_le := by
    intro v g
    fin_cases v <;> fin_cases g <;> simp [ghostR] <;> norm_num
  fan := by
    intro v
    fin_cases v <;>
      (rw [Fin.sum_univ_two, Fin.sum_univ_two]
       <;> simp only [ghostR, ghostSk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
       <;> norm_num)
  tri := by
    intro a b h hab hah hbh
    fin_cases a <;> fin_cases b <;> fin_cases h <;>
      (try simp_all [ghost_angle, angVal] <;> norm_num)
  ang_le := by
    intro x a b hab
    fin_cases x <;> fin_cases a <;> fin_cases b <;>
      (try simp_all [ghost_angle, angVal] <;> norm_num)
  ang_nn := by
    intro x a b hab
    fin_cases x <;> fin_cases a <;> fin_cases b <;>
      (try simp_all [ghost_angle, angVal] <;> norm_num)

/-- `ghostSk` is mode-A consistent (with `δ = 0`). -/
theorem ghostSk_consistent : ghostSk.Consistent 2 :=
  ⟨ghostR, 0, le_refl 0, by norm_num, ghostSk_modeA⟩

/-- Its dyadic mass is `3`: `k = (2,0,0)` gives
`W = 2 + 1/2 + 1/2`. -/
theorem ghostSk_W : (2 : ℚ) < ghostSk.W 2 := by
  native_decide

/-- **The LOW selection proposition is false at `(3,2)`**: a
consistent `W > 2` skeleton admits no `bound ≥ 1/2` gadget — the
`δ = 0` solution forbids it by `gadget_ge_half`. -/
theorem not_gadgetSelectionLow_3_2 :
    ¬ GadgetSelectionLow 3 2 := by
  intro hsel
  have h := selection_low_sound hsel ghostSk_modeA
    (le_refl (0 : ℝ)) (by norm_num) ghostSk_W
  norm_num at h

/-- The same instance disproves the HIGH selection proposition
(`W = 3 > 5/2` but `δ = 0`). -/
theorem not_gadgetSelectionHigh_3_2 :
    ¬ GadgetSelectionHigh 3 2 := by
  intro hsel
  have h := selection_high_sound hsel ghostSk_modeA
    (le_refl (0 : ℝ)) (by norm_num) (by
      have := ghostSk_W; unfold Skeleton.W at *; native_decide)
  norm_num at h

/-- The universally-quantified selection statement is false. -/
theorem not_gadgetSelectionLow_all :
    ¬ (∀ s n, GadgetSelectionLow s n) :=
  fun h => not_gadgetSelectionLow_3_2 (h 3 2)

/-- The universally-quantified HIGH statement is false. -/
theorem not_gadgetSelectionHigh_all :
    ¬ (∀ s n, GadgetSelectionHigh s n) :=
  fun h => not_gadgetSelectionHigh_3_2 (h 3 2)

/-! ### The repair: proper skeletons -/

/-- A skeleton is *proper* when `pos` is injective on the other
vertices — i.e. the fan order is a genuine permutation, as in the
checker (`order : Perm others`). -/
def Skeleton.Proper {s : ℕ} (sk : Skeleton s) : Prop :=
  ∀ v : Fin s, ∀ a b : Fin s, a ≠ v → b ≠ v →
    (sk.vtx v).pos a = (sk.vtx v).pos b → a = b

/-- `ghostSk` is not proper: at `v = 0` the distinct vertices `1, 2`
share position `0`. -/
theorem ghostSk_not_proper : ¬ ghostSk.Proper := by
  intro h
  have := h 0 1 2 (by decide) (by decide) (by decide)
  exact absurd this (by decide)

/-! ### Boundary: where the original statement still holds

The counterexample is minimal along both axes:

* `s ≤ 2`: the statement is *vacuous* — `W ≤ 2` (or no consistent
  skeleton) for every skeleton, so the implication holds.
* `n = 0`: every skeleton with `s ≥ 2` is inconsistent
  (`0 ≤ ∠ ≤ δ − 1` is impossible), so the implication holds.
* `s = 3, n = 2`: FALSE (`ghostSk`).

What remains genuinely open is the repaired proposition
`GadgetSelectionLowP` below. -/

/-- At `n = 0`, `ang_le` gives `∠ ≤ δ - 1` while `ang_nn` gives
`∠ ≥ 0` — impossible whenever an angle exists (`s ≥ 2`). -/
theorem not_consistent_zero {s : ℕ} (hs : 2 ≤ s) (sk : Skeleton s) :
    ¬ sk.Consistent 0 := by
  obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  rintro ⟨r, δ, _hδ0, hδ1, hA⟩
  have h01 : (⟨0, by omega⟩ : Fin (s' + 1)) ≠ ⟨1, by omega⟩ :=
    fun h => by simp at h
  have hnn := hA.ang_nn 0 _ _ h01
  have hle := hA.ang_le 0 _ _ h01
  simp only [Nat.cast_zero, zero_sub] at hle
  linarith

/-- For `n = 0` and `s ≥ 2` the LOW statement is vacuously true. -/
theorem gadgetSelectionLow_n0 {s : ℕ} (hs : 2 ≤ s) :
    GadgetSelectionLow s 0 := by
  intro sk hcons _
  exact absurd hcons (not_consistent_zero hs sk)

/-- For `n = 0` and `s ≥ 2` the HIGH statement is vacuously true. -/
theorem gadgetSelectionHigh_n0 {s : ℕ} (hs : 2 ≤ s) :
    GadgetSelectionHigh s 0 := by
  intro sk hcons _
  exact absurd hcons (not_consistent_zero hs sk)

/-- `s = 0`: `W = 0`, never `> 2` — vacuous. -/
theorem W_eq_zero_s0 (sk : Skeleton 0) (n : ℕ) : sk.W n = 0 := by
  unfold Skeleton.W
  exact Finset.sum_eq_zero fun v _ => Fin.elim0 v

theorem gadgetSelectionLow_s0 (n : ℕ) : GadgetSelectionLow 0 n := by
  intro sk _ hW
  rw [W_eq_zero_s0 sk n] at hW
  norm_num at hW

theorem gadgetSelectionHigh_s0 (n : ℕ) : GadgetSelectionHigh 0 n := by
  intro sk _ hW
  rw [W_eq_zero_s0 sk n] at hW
  norm_num at hW

/-- `s = 1`: `W = 2^{1-n} ≤ 2`, never `> 2` — vacuous. -/
theorem W_le_two_s1 (sk : Skeleton 1) (n : ℕ) : sk.W n ≤ 2 := by
  have hsum1 : ∀ f : Fin 1 → ℚ, ∑ i, f i = f 0 := Fin.sum_univ_one
  have hsum0 : ∀ f : Fin (1 - 1) → ℤ, ∑ i, f i = 0 :=
    fun _ => Finset.sum_eq_zero fun _ h => absurd h (by simp)
  unfold Skeleton.W Skeleton.d VertexData.kexp
  rw [hsum1, hsum0]
  simp only [sub_zero]
  by_cases hn : n = 0
  · subst hn; norm_num
  · have hn1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow : (2 : ℚ) ^ (-((n : ℤ) - 1)) ≤ 1 := by
      apply zpow_le_one_of_nonpos₀ (by norm_num)
      omega
    linarith

theorem gadgetSelectionLow_s1 (n : ℕ) : GadgetSelectionLow 1 n := by
  intro sk _ hW
  have := W_le_two_s1 sk n
  linarith

theorem gadgetSelectionHigh_s1 (n : ℕ) : GadgetSelectionHigh 1 n := by
  intro sk _ hW
  have := W_le_two_s1 sk n
  linarith

/-- `s = 2`: a consistent skeleton has `q ≤ n` at every vertex, hence
`k_v ≤ n - 1`, `d_v ≥ 0`, and `W ≤ 2` — vacuous. -/
theorem W_le_two_s2 (sk : Skeleton 2) {n : ℕ}
    (hcons : sk.Consistent n) : sk.W n ≤ 2 := by
  obtain ⟨r, δ, _hδ0, hδ1, hA⟩ := hcons
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact absurd ⟨r, δ, _hδ0, hδ1, hA⟩
      (not_consistent_zero (le_refl 2) sk)
  have sum1r : ∀ f : Fin (2 - 1) → ℝ, ∑ g, f g = f 0 :=
    fun _ => Fin.sum_univ_one _
  have sum1z : ∀ f : Fin (2 - 1) → ℤ, ∑ g, f g = f 0 :=
    fun _ => Fin.sum_univ_one _
  -- per-vertex exponent bound
  have hq : ∀ v : Fin 2, ((sk.vtx v).q 0 : ℤ) ≤ (n : ℤ) := by
    intro v
    have hf := hA.fan v
    have e1 : (∑ g : Fin (2 - 1), r v g) = r v 0 := sum1r _
    have e2 : (∑ g : Fin (2 - 1), (sk.vtx v).q g)
        = (sk.vtx v).q 0 := sum1z _
    rw [e1, e2] at hf
    have hr := hA.r_nn v 0
    -- q = n + δ - r ≤ n + δ < n + 1
    have hlt : ((sk.vtx v).q 0 : ℝ) < (n : ℝ) + 1 := by
      linarith
    have hltz : (sk.vtx v).q 0 < (n : ℤ) + 1 := by
      exact_mod_cast hlt
    omega
  have hk : ∀ v : Fin 2, (sk.vtx v).kexp ≤ (n : ℤ) - 1 := by
    intro v
    unfold VertexData.kexp
    have e3 : (∑ g : Fin (2 - 1), max ((sk.vtx v).q g - 1) 0)
        = max ((sk.vtx v).q 0 - 1) 0 := sum1z _
    rw [e3]
    have hqv := hq v
    have hnz : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    by_cases hq0 : (sk.vtx v).q 0 ≤ 1
    · rw [max_eq_right (by omega : (sk.vtx v).q 0 - 1 ≤ 0)]
      omega
    · rw [max_eq_left (by omega : 0 ≤ (sk.vtx v).q 0 - 1)]
      omega
  have hd : ∀ v : Fin 2, 0 ≤ sk.d n v := by
    intro v
    unfold Skeleton.d
    have := hk v; omega
  have hterm : ∀ v : Fin 2, (2 : ℚ) ^ (-(sk.d n v)) ≤ 1 := by
    intro v
    apply zpow_le_one_of_nonpos₀ (by norm_num)
    have := hd v; omega
  unfold Skeleton.W
  rw [Fin.sum_univ_two]
  linarith [hterm 0, hterm 1]

theorem gadgetSelectionLow_s2 (n : ℕ) : GadgetSelectionLow 2 n := by
  intro sk hcons hW
  have := W_le_two_s2 sk hcons
  linarith

theorem gadgetSelectionHigh_s2 (n : ℕ) : GadgetSelectionHigh 2 n := by
  intro sk hcons hW
  have := W_le_two_s2 sk hcons
  linarith

/-- The corrected LOW selection proposition.  `Consistent` still
excludes phantoms; `Proper` excludes ghosts.  OPEN (this is the
surviving form of the original crux). -/
def GadgetSelectionLowP (s n : ℕ) : Prop :=
  ∀ sk : Skeleton s, sk.Proper → sk.Consistent n → 2 < sk.W n →
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) / 2 ≤ g.bound n sk

/-- The corrected HIGH selection proposition (lane B counterpart). -/
def GadgetSelectionHighP (s n : ℕ) : Prop :=
  ∀ sk : Skeleton s, sk.Proper → sk.Consistent n →
    (5 : ℚ) / 2 < sk.W n →
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) ≤ g.bound n sk

/-- Soundness of the repaired LOW reduction — identical proof. -/
theorem selection_low_soundP {s n : ℕ} (hsel : GadgetSelectionLowP s n)
    {sk : Skeleton s} (hp : sk.Proper)
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hW : 2 < sk.W n) : (1 : ℝ) / 2 ≤ δ := by
  obtain ⟨g, hV, hb⟩ := hsel sk hp ⟨r, δ, hδ0, hδ1, hA⟩ hW
  apply g.gadget_ge_half n sk hA hV
  have hcap := bound_half_unfold g hb
  push_cast at hcap ⊢
  linarith

/-- Soundness of the repaired HIGH reduction. -/
theorem selection_high_soundP {s n : ℕ}
    (hsel : GadgetSelectionHighP s n) {sk : Skeleton s}
    (hp : sk.Proper)
    {r : Fin s → Fin (s - 1) → ℝ} {δ : ℝ}
    (hA : ModeA n sk r δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hW : (5 : ℚ) / 2 < sk.W n) : (1 : ℝ) ≤ δ := by
  obtain ⟨g, hV, hb⟩ := hsel sk hp ⟨r, δ, hδ0, hδ1, hA⟩ hW
  apply g.gadget_ge_one n sk hA hV
  have hcap := bound_one_unfold g hb
  push_cast at hcap ⊢
  linarith

/-! ### The repaired propositions on the vacuous boundary -/

theorem gadgetSelectionLowP_n0 {s : ℕ} (hs : 2 ≤ s) :
    GadgetSelectionLowP s 0 := by
  intro sk _ hcons _
  exact absurd hcons (not_consistent_zero hs sk)

theorem gadgetSelectionHighP_n0 {s : ℕ} (hs : 2 ≤ s) :
    GadgetSelectionHighP s 0 := by
  intro sk _ hcons _
  exact absurd hcons (not_consistent_zero hs sk)

theorem gadgetSelectionLowP_s0 (n : ℕ) : GadgetSelectionLowP 0 n := by
  intro sk _ _ hW
  rw [W_eq_zero_s0 sk n] at hW
  norm_num at hW

theorem gadgetSelectionHighP_s0 (n : ℕ) : GadgetSelectionHighP 0 n := by
  intro sk _ _ hW
  rw [W_eq_zero_s0 sk n] at hW
  norm_num at hW

theorem gadgetSelectionLowP_s1 (n : ℕ) : GadgetSelectionLowP 1 n := by
  intro sk _ _ hW
  have := W_le_two_s1 sk n
  linarith

theorem gadgetSelectionHighP_s1 (n : ℕ) : GadgetSelectionHighP 1 n := by
  intro sk _ _ hW
  have := W_le_two_s1 sk n
  linarith

theorem gadgetSelectionLowP_s2 (n : ℕ) : GadgetSelectionLowP 2 n := by
  intro sk _ hcons hW
  have := W_le_two_s2 sk hcons
  linarith

theorem gadgetSelectionHighP_s2 (n : ℕ) : GadgetSelectionHighP 2 n := by
  intro sk _ hcons hW
  have := W_le_two_s2 sk hcons
  linarith

end Jsp404

#print axioms Jsp404.not_gadgetSelectionLow_3_2
#print axioms Jsp404.not_gadgetSelectionHigh_3_2
#print axioms Jsp404.ghostSk_modeA
