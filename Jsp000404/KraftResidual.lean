import Mathlib

/-!
# K3a — defect-histogram / residual-capacity algebra

For a defect function `d : Fin s → ℕ` write `a_r = #{i | d i = r}` and
`K = Σᵢ 2^{−dᵢ}` the Kraft sum.  The *residual prefix capacity* at
level `m` against a cap `B` is

    R_m = 2^m · (B − Σ_{r ≤ m} a_r·2^{−r}).

`B = 1` is the low-regime cap (`R^L`), `B = 5/4` the high-regime cap
(`R^H`, i.e. `5·2^{m−2} − Σ a_r·2^{m−r}` for `m ≥ 2`).

This file proves, in pure `ℚ`-arithmetic (no geometry, no `sorry`):

* `kraftSum_eq_hist` — `K = Σ_{r ≤ M} a_r·2^{−r}` for `d ≤ M`;
* `kraftResidual_eq_partial` — `R_m = 2^m·(B − Σ_{r≤m} a_r·2^{−r})`;
* `kraftResidual_succ` — the recurrence `R_{m+1} = 2·R_m − a_{m+1}`;
* `kraftResidual_eq` — `R_M = 2^M·(B − K)` when `d ≤ M`;
* `kraft_le_iff_residual_nonneg` — `K ≤ B ↔ 0 ≤ R_M`;
* `kraftResidual_neg_mono` — once negative, always negative
  (`R_m < 0 → R_{m+1} < 0`), so `K ≤ B ↔ ∀ m, 0 ≤ R_m`;
* `kraft_gt_iff_exists_residual_neg` — `K > B ↔ ∃ m, R_m < 0`;
* `exists_min_overfull_level` — if `K > B`, the *first* overfull
  level `m ≥ 1`: `R_{m−1} ≥ 0` but `a_m > 2·R_{m−1}`.

Every tight profile sits exactly at `R = 0` (`[2,2,2,2]`,
`[1,2,3,3]` at `B = 1`; `[2]^5`, `[1,2,2,2]`, `[1,1,3,3]` at
`B = 5/4`), so the residual is the sharp certificate coordinate.

The remaining mathematical crux (K3b) is then exactly: *for the defect
function of a legal configuration no level is ever overfull* —
a minimal-overfull-block statement that feeds the gadget lane's
`DebtChain`/`ResidualWitness` machinery.
-/

namespace Jsp404

open Finset

variable {s : ℕ}

/-- Number of rows with defect exactly `r`: `a_r = #{i | d i = r}`. -/
def defectCount (d : Fin s → ℕ) (r : ℕ) : ℕ :=
  (univ.filter fun i => d i = r).card

/-- The Kraft sum `K = Σᵢ 2^{−dᵢ}` of a defect function. -/
def kraftSum (d : Fin s → ℕ) : ℚ := ∑ i, (1 / 2 : ℚ) ^ d i

/-- The `d`-fibers partition the index set when `d ≤ M`. -/
theorem univ_eq_biUnion_fiber (d : Fin s → ℕ) {M : ℕ}
    (hM : ∀ i, d i ≤ M) :
    (univ : Finset (Fin s)) =
      (Finset.range (M + 1)).biUnion
        fun r => univ.filter fun i => d i = r := by
  ext i
  constructor
  · intro _
    rw [mem_biUnion]
    exact ⟨d i, mem_range.mpr (Nat.lt_succ_iff.mpr (hM i)),
      mem_filter.mpr ⟨mem_univ i, rfl⟩⟩
  · intro _; exact mem_univ i

/-- The Kraft sum decomposes over the defect histogram. -/
theorem kraftSum_eq_hist (d : Fin s → ℕ) {M : ℕ} (hM : ∀ i, d i ≤ M) :
    kraftSum d =
      ∑ r ∈ Finset.range (M + 1), defectCount d r * (1 / 2 : ℚ) ^ r := by
  classical
  rw [kraftSum, univ_eq_biUnion_fiber d hM]
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro r _
    have hcong : ∀ i ∈ univ.filter (fun i => d i = r),
        (1 / 2 : ℚ) ^ d i = (1 / 2 : ℚ) ^ r :=
      fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]
    rfl
  · intro r _ r' _ hrr'
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact hrr' ((Finset.mem_filter.mp hi).2.symm.trans
      (Finset.mem_filter.mp hi').2)

/-- `a_r = 0` when no index has defect `r`. -/
theorem defectCount_eq_zero_of_forall_ne {d : Fin s → ℕ} {r : ℕ}
    (h : ∀ i, d i ≠ r) : defectCount d r = 0 := by
  rw [defectCount, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem]
  intro i hi
  exact h i (Finset.mem_filter.mp hi).2

/-- `a_r = 0` above the maximum defect. -/
theorem defectCount_eq_zero_of_lt {d : Fin s → ℕ} {M r : ℕ}
    (hM : ∀ i, d i ≤ M) (hr : M < r) : defectCount d r = 0 :=
  defectCount_eq_zero_of_forall_ne fun i => by
    have := hM i; omega

/-- Residual prefix capacity at level `m` against cap `B`:
`R_m = 2^m·B − Σ_{r ≤ m} a_r·2^{m−r}`. -/
def kraftResidual (B : ℚ) (d : Fin s → ℕ) (m : ℕ) : ℚ :=
  2 ^ m * B -
    ∑ r ∈ Finset.range (m + 1), (defectCount d r : ℚ) * 2 ^ (m - r)

/-- `R_m = 2^m·(B − Σ_{r≤m} a_r·2^{−r})`: the residual is `2^m` times
the cap minus the partial Kraft sum. -/
theorem kraftResidual_eq_partial (B : ℚ) (d : Fin s → ℕ) (m : ℕ) :
    kraftResidual B d m =
      2 ^ m * (B -
        ∑ r ∈ Finset.range (m + 1), defectCount d r * (1 / 2 : ℚ) ^ r) := by
  unfold kraftResidual
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hrM := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have key : (2 : ℚ) ^ m * (1 / 2) ^ r = (2 : ℚ) ^ (m - r) := by
    rw [div_pow, one_pow, one_div,
      pow_sub₀ (2 : ℚ) (by norm_num) hrM]
  rw [mul_left_comm, key]

/-- The residual recurrence `R_{m+1} = 2·R_m − a_{m+1}`:
each level doubles the remaining capacity, then the level-`(m+1)`
rows pay one slot each. -/
theorem kraftResidual_succ (B : ℚ) (d : Fin s → ℕ) (m : ℕ) :
    kraftResidual B d (m + 1) =
      2 * kraftResidual B d m - defectCount d (m + 1) := by
  unfold kraftResidual
  have h2 : ∀ r ∈ Finset.range (m + 1),
      (defectCount d r : ℚ) * 2 ^ (m + 1 - r) =
        2 * (defectCount d r * 2 ^ (m - r)) := by
    intro r hr
    have hrm := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [show m + 1 - r = m - r + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
    Finset.sum_congr rfl h2, ← Finset.mul_sum, pow_succ]
  ring

/-- At the maximum defect level the residual is the exact Kraft
deficit: `R_M = 2^M·(B − K)`. -/
theorem kraftResidual_eq (B : ℚ) (d : Fin s → ℕ) {M : ℕ}
    (hM : ∀ i, d i ≤ M) :
    kraftResidual B d M = 2 ^ M * (B - kraftSum d) := by
  rw [kraftResidual_eq_partial, kraftSum_eq_hist d hM]

/-- The Kraft bound is exactly nonnegativity of the top residual. -/
theorem kraft_le_iff_residual_nonneg (B : ℚ) (d : Fin s → ℕ) {M : ℕ}
    (hM : ∀ i, d i ≤ M) :
    kraftSum d ≤ B ↔ 0 ≤ kraftResidual B d M := by
  rw [kraftResidual_eq B d hM]
  constructor
  · intro h
    exact mul_nonneg (by positivity) (sub_nonneg.mpr h)
  · intro h
    by_contra hK
    push Not at hK
    have : (2 : ℚ) ^ M * (B - kraftSum d) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hK)
    linarith

/-- Once the residual is negative it stays negative:
`R_{m+1} = 2·R_m − a_{m+1} ≤ 2·R_m < 0`. -/
theorem kraftResidual_neg_mono (B : ℚ) (d : Fin s → ℕ) {m : ℕ}
    (h : kraftResidual B d m < 0) : kraftResidual B d (m + 1) < 0 := by
  rw [kraftResidual_succ]
  have hnn : (0 : ℚ) ≤ defectCount d (m + 1) := by positivity
  linarith

/-- The residual can never recover: `R_m < 0 → R_{m+t} < 0`. -/
theorem kraftResidual_neg_forall_add (B : ℚ) (d : Fin s → ℕ) {m : ℕ}
    (t : ℕ) (h : kraftResidual B d m < 0) :
    kraftResidual B d (m + t) < 0 := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    rw [Nat.add_succ]
    exact kraftResidual_neg_mono B d ih

/-- The partial Kraft sum never exceeds the total `K`. -/
theorem partial_kraftSum_le (d : Fin s → ℕ) {M : ℕ}
    (hM : ∀ i, d i ≤ M) (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1), defectCount d r * (1 / 2 : ℚ) ^ r
      ≤ kraftSum d := by
  rcases lt_or_ge m (M + 1) with hm | hm
  · rw [kraftSum_eq_hist d hM]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun r _ _ => by positivity)
  · have heq : ∑ r ∈ Finset.range (m + 1),
        defectCount d r * (1 / 2 : ℚ) ^ r = kraftSum d := by
      rw [kraftSum_eq_hist d hM]
      symm
      apply Finset.sum_subset
        (Finset.range_subset_range.mpr (by omega))
      intro r _ hnr
      rw [Finset.mem_range, Nat.lt_succ_iff] at hnr
      push Not at hnr
      simp [defectCount_eq_zero_of_lt hM hnr]
    rw [heq]

/-- `K ≤ B` iff the residual is nonnegative at *every* level. -/
theorem kraft_le_iff_residual_forall_nonneg (B : ℚ) (d : Fin s → ℕ)
    {M : ℕ} (hM : ∀ i, d i ≤ M) :
    kraftSum d ≤ B ↔ ∀ m, 0 ≤ kraftResidual B d m := by
  constructor
  · intro h m
    rw [kraftResidual_eq_partial]
    exact mul_nonneg (by positivity)
      (sub_nonneg.mpr (le_trans (partial_kraftSum_le d hM m) h))
  · intro h
    exact (kraft_le_iff_residual_nonneg B d hM).mpr (h M)

/-- `K > B` iff some level is overfull (`R_m < 0`). -/
theorem kraft_gt_iff_exists_residual_neg (B : ℚ) (d : Fin s → ℕ)
    {M : ℕ} (hM : ∀ i, d i ≤ M) :
    B < kraftSum d ↔ ∃ m, kraftResidual B d m < 0 := by
  constructor
  · intro h
    exact ⟨M, not_le.mp
        ((kraft_le_iff_residual_nonneg B d hM).not.mp
          (not_le.mpr h))⟩
  · rintro ⟨m, hm⟩
    rcases lt_or_ge m (M + 1) with hmM | hmM
    · have hneg : kraftResidual B d M < 0 := by
        obtain ⟨t, rfl⟩ :=
          Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp hmM)
        exact kraftResidual_neg_forall_add B d t hm
      exact not_le.mp
        ((kraft_le_iff_residual_nonneg B d hM).not.mpr
          (not_le.mpr hneg))
    · -- `m > M`: all fibers are counted, `R_m = 2^m·(B − K)`.
      have heq : ∑ r ∈ Finset.range (m + 1),
          defectCount d r * (1 / 2 : ℚ) ^ r = kraftSum d := by
        rw [kraftSum_eq_hist d hM]
        symm
        apply Finset.sum_subset
          (Finset.range_subset_range.mpr (by omega))
        intro r _ hnr
        rw [Finset.mem_range, Nat.lt_succ_iff] at hnr
        push Not at hnr
        simp [defectCount_eq_zero_of_lt hM hnr]
      rw [kraftResidual_eq_partial, heq] at hm
      by_contra hK
      push Not at hK
      have hnn : 0 ≤ (2 : ℚ) ^ m * (B - kraftSum d) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hK)
      linarith

/-- `R₀ = B − a₀`; when every defect is positive (`a₀ = 0`), `R₀ = B`. -/
theorem kraftResidual_zero (B : ℚ) (d : Fin s → ℕ)
    (hd1 : ∀ i, 1 ≤ d i) : kraftResidual B d 0 = B := by
  unfold kraftResidual
  have ha0 : defectCount d 0 = 0 :=
    defectCount_eq_zero_of_forall_ne fun i => by
      have := hd1 i; omega
  simp [Finset.range_one, ha0]

/-- **The first overfull level.**  If `K > B` and every defect is
`≥ 1`, there is a minimal `m ≥ 1` with `R_m < 0`: all shallower
levels were feasible (`R_{m−1} ≥ 0`), yet the level-`m` defect count
exceeds the doubled residual capacity (`a_m > 2·R_{m−1}`).

This is the intended entry point of the K3b proof: the minimal
overfull block `{i | d i ≤ m}` pays more than its prefix capacity,
and the minimality is what the `DebtChain`/`ResidualWitness`
construction needs. -/
theorem exists_min_overfull_level (B : ℚ) (d : Fin s → ℕ) {M : ℕ}
    (hB : 0 ≤ B) (hM : ∀ i, d i ≤ M) (hd1 : ∀ i, 1 ≤ d i)
    (h : B < kraftSum d) :
    ∃ m, 1 ≤ m ∧ m ≤ M ∧ kraftResidual B d m < 0 ∧
        0 ≤ kraftResidual B d (m - 1) ∧
        2 * kraftResidual B d (m - 1) < defectCount d m := by
  classical
  have hRM : kraftResidual B d M < 0 := by
    rw [kraftResidual_eq B d hM]
    calc (2 : ℚ) ^ M * (B - kraftSum d)
        < (2 : ℚ) ^ M * 0 :=
          mul_lt_mul_of_pos_left (sub_neg.mpr h) (by positivity)
      _ = 0 := mul_zero _
  have hne : ∃ m, kraftResidual B d m < 0 := ⟨M, hRM⟩
  set m := Nat.find hne with hm_def
  have hm : kraftResidual B d m < 0 := Nat.find_spec hne
  have hm1 : 1 ≤ m := by
    by_contra h0
    push Not at h0
    rw [Nat.lt_one_iff] at h0
    rw [h0, kraftResidual_zero B d hd1] at hm
    linarith
  refine ⟨m, hm1, ?_, hm, ?_, ?_⟩
  · by_contra hgt
    push Not at hgt
    exact absurd hRM (Nat.find_min hne hgt)
  · have hlt : m - 1 < m := by omega
    exact not_lt.mp (Nat.find_min hne hlt)
  · have hsucc := kraftResidual_succ B d (m - 1)
    rw [Nat.sub_add_cancel hm1] at hsucc
    linarith

/-- Kraft sum of a constant defect function. -/
theorem kraftSum_const {t k : ℕ} :
    kraftSum (fun _ : Fin t => k) = t * (1 / 2 : ℚ) ^ k := by
  simp [kraftSum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-! ### Sanity checks on the observed tight profiles -/

/-- `[2,2,2,2]` is low-tight: `K = 1`, `R₂ = 0`. -/
example : kraftSum (fun _ : Fin 4 => 2) = 1 := by
  rw [kraftSum_const]; norm_num

example : kraftResidual 1 (fun _ : Fin 4 => 2) 2 = 0 := by
  rw [kraftResidual_eq 1 _ (fun _ => Nat.le_refl 2), kraftSum_const]
  norm_num

/-- `[1,2,3,3]` is low-tight: `K = 1`, and `R₂ = 1`, `R₃ = 0`. -/
example : kraftSum (![1, 2, 3, 3] : Fin 4 → ℕ) = 1 := by
  simp [kraftSum, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

example : kraftResidual 1 (![1, 2, 3, 3] : Fin 4 → ℕ) 3 = 0 := by
  rw [kraftResidual_eq 1 _
    (fun i => by fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one])]
  simp [kraftSum, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- `[2]^5` is high-tight: `K = 5/4`, `R₂ = 0` — the discovered
high-regime no-saturation boundary. -/
example : kraftSum (fun _ : Fin 5 => 2) = 5 / 4 := by
  rw [kraftSum_const]; norm_num

example : kraftResidual (5 / 4) (fun _ : Fin 5 => 2) 2 = 0 := by
  rw [kraftResidual_eq (5 / 4) _ (fun _ => Nat.le_refl 2),
    kraftSum_const]
  norm_num

/-- `[1,2,2,2]` is high-tight: `K = 5/4`, `R₂ = 0`. -/
example : kraftResidual (5 / 4)
    (![1, 2, 2, 2] : Fin 4 → ℕ) 2 = 0 := by
  rw [kraftResidual_eq (5 / 4) _
    (fun i => by fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one])]
  simp [kraftSum, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- `[1,1,3,3]` is high-tight: `K = 5/4`, `R₂ = 1`, `R₃ = 0`. -/
example : kraftResidual (5 / 4)
    (![1, 1, 3, 3] : Fin 4 → ℕ) 3 = 0 := by
  rw [kraftResidual_eq (5 / 4) _
    (fun i => by fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one])]
  simp [kraftSum, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

end Jsp404
