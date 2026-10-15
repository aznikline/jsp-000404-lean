import Jsp000404.K3bGeometryPart4

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- **Leaf-0001 signed residual certificate.**  The geometric source
of `P = 1 + 2δ`, `P ≥ 3` for the `n = 4` mixed skeleton, instantiated
through `ResidualWitness.ge_of` at `τ = 1`.  Conclusion `5·λ ≤ π`,
i.e. `π/λ − 4 ≥ 1`: the system's `δ` is `≥ 1`.

Hypotheses (the certificate's `order`/`bits`/`qs` data, all on the
actual `dirRep` values of the configuration):
* `h012 h013 h014` — cyclic order of row 0 is `(1,2,3,4)`;
* `h301 h302 h304` — cyclic order of row 3 is `(0,1,2,4)`;
* `h203` — direction 1 lies on the `0 → 3` arc of row 2;
* `hb*` — the eight orientation bits (arc vs complement branch);
* `hq03 hq33` — the two nonzero declared cell counts
  (`q03 = 4`, `q33 = 3`), as lower bounds on the wrap gaps. -/
theorem leaf_0001_cert {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    (h012 : dirArc o e c 0 1 2 ≤ dirArc o e c 0 1 3)
    (h013 : dirArc o e c 0 1 3 ≤ dirArc o e c 0 1 4)
    (h014 : 0 < dirArc o e c 0 1 4)
    (h301 : dirArc o e c 3 0 1 ≤ dirArc o e c 3 0 2)
    (h302 : dirArc o e c 3 0 2 ≤ dirArc o e c 3 0 4)
    (h304 : 0 < dirArc o e c 3 0 4)
    (h203 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (hb102 : (o.oangle (c 0 - c 1) (c 2 - c 1)).toReal < 0)
    (hb012 : 0 ≤ (o.oangle (c 1 - c 0) (c 2 - c 0)).toReal)
    (hb021 : 0 ≤ (o.oangle (c 0 - c 2) (c 1 - c 2)).toReal)
    (hb203a : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb023 : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hb213 : (o.oangle (c 1 - c 2) (c 3 - c 2)).toReal < 0)
    (hb324 : (o.oangle (c 2 - c 3) (c 4 - c 3)).toReal < 0)
    (hq03 : (4 : ℝ) * lam ≤ dirArc o e c 0 4 1)
    (hq33 : (3 : ℝ) * lam ≤ dirArc o e c 3 4 0) :
    (5 : ℝ) * lam ≤ Real.pi := by
  classical
  have hmem : ∀ i j : Fin 5,
      dirRep o e c i j ∈ Set.Ico 0 Real.pi :=
    fun _ _ => linRep_mem_Ico _
  -- fan equations: the two cyclic chains sum to π
  have F0 : dirArc o e c 0 1 2 + dirArc o e c 0 2 3 +
      dirArc o e c 0 3 4 + dirArc o e c 0 4 1 = Real.pi :=
    cyclicDiff_chain4 (hmem 0 1) (hmem 0 2) (hmem 0 3) (hmem 0 4)
      h012 h013 h014
  have F3 : dirArc o e c 3 0 1 + dirArc o e c 3 1 2 +
      dirArc o e c 3 2 4 + dirArc o e c 3 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 3 0) (hmem 3 1) (hmem 3 2) (hmem 3 4)
      h301 h302 h304
  have eV3 : dirArc o e c 3 0 2 =
      dirArc o e c 3 0 1 + dirArc o e c 3 1 2 :=
    cyclicDiff_eq_add_of_le (hmem 3 0) (hmem 3 1) (hmem 3 2) h301
  -- the certificate is the general signed chain at
  -- x = (0,1,2,3,4), L = 3, a = 4, b = 3, n = 4:  (†) gives
  -- δ = π/λ − 4 ≥ (4 + 3 + 3 − 8)/2 = 1.
  let fv : ℕ → Fin 5 := fun k =>
    ⟨k % 5, Nat.mod_lt _ (by norm_num : 0 < 5)⟩
  have hδ := signed_chain_cert o e hleg hlam he (L := 3) (n := 4)
    (by norm_num) fv
    (by intro i j hi hj hij h
        apply hij
        have hv : i % 5 = j % 5 := congrArg Fin.val h
        omega)
    (by -- hfanL: Σ_{i<3} A_{i+1} + H_0 = π, from the row-0 chain
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
      show dirArc o e c 0 1 2 + dirArc o e c 0 2 3 +
        dirArc o e c 0 3 4 + dirArc o e c 0 4 1 = Real.pi
      exact F0)
    (by -- hfanR: S_3 + D_3 + H_L = π, from the row-3 chain + split
      show dirArc o e c 3 0 2 + dirArc o e c 3 2 4 +
        dirArc o e c 3 4 0 = Real.pi
      linarith)
    (by intro i hi
        have hi2 : i < 2 := Finset.mem_range.mp hi
        interval_cases i
        · -- dirArc 1 0 0 ≤ dirArc 1 0 2: the split point is x 0
          show dirArc o e c 1 0 0 ≤ dirArc o e c 1 0 2
          have hz : dirArc o e c 1 0 0 = 0 := by
            simp [dirArc, cyclicDiff]
          rw [hz]
          exact cyclicDiff_nonneg (hmem 1 0).2 (hmem 1 2).1
        · exact h203)
    (by intro i hi
        have hi2 : i < 2 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb012
        · exact hb203a)
    (by intro i hi
        have hi2 : i < 2 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb102
        · exact hb023)
    (by intro i hi
        have hi2 : i < 2 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb021
        · exact hb032)
    (by intro i hi
        have hi3 : i < 3 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb102
        · exact hb213
        · exact hb324)
    4 3
    (by exact_mod_cast hq03)
    (by exact_mod_cast hq33)
  have hδ' : (1 : ℝ) ≤ Real.pi / lam - 4 := by linarith
  have hδ'' : (5 : ℝ) ≤ Real.pi / lam := by linarith
  exact (le_div_iff₀ hlam).mp hδ''

/-- **The `L = 2 → 3` extension on the leaf-0001 skeleton.**  The
same directions also certify the shorter chain `x = (0,1,2,3)`
(right fan at row `x_L = 2`) — data not used by `leaf_0001_cert`:
the row-0 wrap split `h031` (direction `4` lies on the forward arc
`3 → 1`), the row-2 fan chain `h203 h2034 h204`, the row-2 wrap
split `h230` and the prefix boundary bound `hq20` — together with
the new piece (triangle `△(0,2,3)`, demand at apex `3`, right fan
at row `3`) they give the extension.  The conclusion shows both
thresholds: the prefix has `σ = 4+3+2−8 = 1` (`δ ≥ 1/2`), the
extended chain `σ' = 2` (`δ ≥ 1`), and the ledger is
`Δσ = 1 + b' − b − q = 1 + 3 − 3 − 0 = 1`. -/
theorem leaf_0001_extend_cert {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    (h012 : dirArc o e c 0 1 2 ≤ dirArc o e c 0 1 3)
    (h013 : dirArc o e c 0 1 3 ≤ dirArc o e c 0 1 4)
    (h014 : 0 < dirArc o e c 0 1 4)
    (h301 : dirArc o e c 3 0 1 ≤ dirArc o e c 3 0 2)
    (h302 : dirArc o e c 3 0 2 ≤ dirArc o e c 3 0 4)
    (h304 : 0 < dirArc o e c 3 0 4)
    (h203 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (h2034 : dirArc o e c 2 0 3 ≤ dirArc o e c 2 0 4)
    (h204 : 0 < dirArc o e c 2 0 4)
    (h031 : dirArc o e c 0 3 4 ≤ dirArc o e c 0 3 1)
    (h230 : dirArc o e c 2 3 4 ≤ dirArc o e c 2 3 0)
    (hb102 : (o.oangle (c 0 - c 1) (c 2 - c 1)).toReal < 0)
    (hb012 : 0 ≤ (o.oangle (c 1 - c 0) (c 2 - c 0)).toReal)
    (hb021 : 0 ≤ (o.oangle (c 0 - c 2) (c 1 - c 2)).toReal)
    (hb203a : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb023 : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hb213 : (o.oangle (c 1 - c 2) (c 3 - c 2)).toReal < 0)
    (hb324 : (o.oangle (c 2 - c 3) (c 4 - c 3)).toReal < 0)
    (hq03 : (4 : ℝ) * lam ≤ dirArc o e c 0 4 1)
    (hq33 : (3 : ℝ) * lam ≤ dirArc o e c 3 4 0)
    (hq20 : (3 : ℝ) * lam ≤ dirArc o e c 2 3 0) :
    (1 : ℝ) / 2 ≤ Real.pi / lam - 4 ∧ (1 : ℝ) ≤ Real.pi / lam - 4 := by
  classical
  have hmem : ∀ i j : Fin 5,
      dirRep o e c i j ∈ Set.Ico 0 Real.pi :=
    fun _ _ => linRep_mem_Ico _
  have F0 : dirArc o e c 0 1 2 + dirArc o e c 0 2 3 +
      dirArc o e c 0 3 4 + dirArc o e c 0 4 1 = Real.pi :=
    cyclicDiff_chain4 (hmem 0 1) (hmem 0 2) (hmem 0 3) (hmem 0 4)
      h012 h013 h014
  have F2 : dirArc o e c 2 0 1 + dirArc o e c 2 1 3 +
      dirArc o e c 2 3 4 + dirArc o e c 2 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 2 0) (hmem 2 1) (hmem 2 3) (hmem 2 4)
      h203 h2034 h204
  have F3 : dirArc o e c 3 0 1 + dirArc o e c 3 1 2 +
      dirArc o e c 3 2 4 + dirArc o e c 3 4 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 3 0) (hmem 3 1) (hmem 3 2) (hmem 3 4)
      h301 h302 h304
  have eV3 : dirArc o e c 3 0 2 =
      dirArc o e c 3 0 1 + dirArc o e c 3 1 2 :=
    cyclicDiff_eq_add_of_le (hmem 3 0) (hmem 3 1) (hmem 3 2) h301
  have e01 : dirArc o e c 0 3 1 =
      dirArc o e c 0 3 4 + dirArc o e c 0 4 1 :=
    cyclicDiff_eq_add_of_le (hmem 0 3) (hmem 0 4) (hmem 0 1) h031
  have e20 : dirArc o e c 2 3 0 =
      dirArc o e c 2 3 4 + dirArc o e c 2 4 0 :=
    cyclicDiff_eq_add_of_le (hmem 2 3) (hmem 2 4) (hmem 2 0) h230
  -- the extension: x = (0,1,2,3,4), old chain L = 2 (prefix
  -- [0,1,2,3]), new piece adds x 4 = 4
  let fv : ℕ → Fin 5 := fun k =>
    ⟨k % 5, Nat.mod_lt _ (by norm_num : 0 < 5)⟩
  have hboth := signed_chain_extend o e hleg hlam he (L := 2) (n := 4)
    (by norm_num) fv
    (by intro i j hi hj hij h
        apply hij
        have hv : i % 5 = j % 5 := congrArg Fin.val h
        omega)
    (by -- old hfanL: dirArc012 + dirArc023 + dirArc031 = π
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
      show dirArc o e c 0 1 2 + dirArc o e c 0 2 3 +
        dirArc o e c 0 3 1 = Real.pi
      linarith)
    (by -- old hfanR: dirArc201 + dirArc213 + dirArc230 = π
      show dirArc o e c 2 0 1 + dirArc o e c 2 1 3 +
        dirArc o e c 2 3 0 = Real.pi
      linarith)
    (by intro i hi
        have hi1 : i < 1 := Finset.mem_range.mp hi
        interval_cases i
        show dirArc o e c 1 0 0 ≤ dirArc o e c 1 0 2
        have hz : dirArc o e c 1 0 0 = 0 := by
          simp [dirArc, cyclicDiff]
        rw [hz]
        exact cyclicDiff_nonneg (hmem 1 0).2 (hmem 1 2).1)
    (by intro i hi
        have hi1 : i < 1 := Finset.mem_range.mp hi
        interval_cases i
        exact hb012)
    (by intro i hi
        have hi1 : i < 1 := Finset.mem_range.mp hi
        interval_cases i
        exact hb102)
    (by intro i hi
        have hi1 : i < 1 := Finset.mem_range.mp hi
        interval_cases i
        exact hb021)
    (by intro i hi
        have hi2 : i < 2 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb102
        · exact hb213)
    4 3
    (by -- hH0: 4λ ≤ dirArc 0 3 1, from hq03 + e01
      show (4 : ℝ) * lam ≤ dirArc o e c 0 3 1
      have hnn : 0 ≤ dirArc o e c 0 3 4 :=
        cyclicDiff_nonneg (hmem 0 3).2 (hmem 0 4).1
      linarith)
    (by exact_mod_cast hq20)
    (by exact h031)
    (by exact h203)
    (by exact hb203a)
    (by exact hb023)
    (by exact hb032)
    (by exact hb324)
    (by -- hfanRN: dirArc302 + dirArc324 + dirArc340 = π
      show dirArc o e c 3 0 2 + dirArc o e c 3 2 4 +
        dirArc o e c 3 4 0 = Real.pi
      linarith)
    4 3
    (by exact_mod_cast hq03)
    (by exact_mod_cast hq33)
  obtain ⟨hpre, hext'⟩ := hboth
  constructor <;> linarith

/-- Under `⌊π/λ⌋ = 4` the leaf-0001 certificate data is outright
contradictory — the skeleton is infeasible in the `n = 4` regime. -/
theorem leaf_0001_absurd {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    (hn : ⌊Real.pi / lam⌋₊ = 4)
    (h012 : dirArc o e c 0 1 2 ≤ dirArc o e c 0 1 3)
    (h013 : dirArc o e c 0 1 3 ≤ dirArc o e c 0 1 4)
    (h014 : 0 < dirArc o e c 0 1 4)
    (h301 : dirArc o e c 3 0 1 ≤ dirArc o e c 3 0 2)
    (h302 : dirArc o e c 3 0 2 ≤ dirArc o e c 3 0 4)
    (h304 : 0 < dirArc o e c 3 0 4)
    (h203 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (hb102 : (o.oangle (c 0 - c 1) (c 2 - c 1)).toReal < 0)
    (hb012 : 0 ≤ (o.oangle (c 1 - c 0) (c 2 - c 0)).toReal)
    (hb021 : 0 ≤ (o.oangle (c 0 - c 2) (c 1 - c 2)).toReal)
    (hb203a : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb023 : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hb213 : (o.oangle (c 1 - c 2) (c 3 - c 2)).toReal < 0)
    (hb324 : (o.oangle (c 2 - c 3) (c 4 - c 3)).toReal < 0)
    (hq03 : (4 : ℝ) * lam ≤ dirArc o e c 0 4 1)
    (hq33 : (3 : ℝ) * lam ≤ dirArc o e c 3 4 0) : False := by
  have h1 := leaf_0001_cert o e hleg hlam he h012 h013 h014 h301 h302
    h304 h203 hb102 hb012 hb021 hb203a hb023 hb032 hb213 hb324
    hq03 hq33
  have hf' : Real.pi / lam < 5 := by
    have hf := Nat.lt_floor_add_one (Real.pi / lam)
    rw [hn] at hf
    exact_mod_cast hf
  rw [div_lt_iff₀ hlam] at hf'
  linarith

/-- **The endpoint-fan certificate on the leaf-0046 skeleton.**  The
chain `x = (0,1,2,3,4)` with `L = 3` closes at the right ENDPOINT
`x 4` (the row-4 fan telescopes to `S_4 + H'_3 = π`) instead of a
right fan at `x L = 3` — the variant-B shape.  Per-demand cell
bounds `m = (1,1,2)`: the first two demand arcs carry one cell from
the complement-angle bound `∠ ≤ π − λ`, the last keeps its
`q_{32} = 2` baseline.  Score `σ = 4+2+(1+1+2)−8 = 2`, so `δ ≥ 1`
and `5λ ≤ π`. -/
theorem leaf_0046_certB {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    (h012 : dirArc o e c 0 1 2 ≤ dirArc o e c 0 1 3)
    (h013 : dirArc o e c 0 1 3 ≤ dirArc o e c 0 1 4)
    (h014 : 0 < dirArc o e c 0 1 4)
    (h401 : dirArc o e c 4 0 1 ≤ dirArc o e c 4 0 2)
    (h402 : dirArc o e c 4 0 2 ≤ dirArc o e c 4 0 3)
    (h403 : 0 < dirArc o e c 4 0 3)
    (h2013 : dirArc o e c 2 0 1 ≤ dirArc o e c 2 0 3)
    (h3024 : dirArc o e c 3 0 2 ≤ dirArc o e c 3 0 4)
    (hb102 : (o.oangle (c 0 - c 1) (c 2 - c 1)).toReal < 0)
    (hb012 : 0 ≤ (o.oangle (c 1 - c 0) (c 2 - c 0)).toReal)
    (hb021 : 0 ≤ (o.oangle (c 0 - c 2) (c 1 - c 2)).toReal)
    (hb203a : 0 ≤ (o.oangle (c 2 - c 0) (c 3 - c 0)).toReal)
    (hb023 : (o.oangle (c 0 - c 2) (c 3 - c 2)).toReal < 0)
    (hb032 : 0 ≤ (o.oangle (c 0 - c 3) (c 2 - c 3)).toReal)
    (hb304a : 0 ≤ (o.oangle (c 3 - c 0) (c 4 - c 0)).toReal)
    (hb034 : (o.oangle (c 0 - c 3) (c 4 - c 3)).toReal < 0)
    (hb043 : 0 ≤ (o.oangle (c 0 - c 4) (c 3 - c 4)).toReal)
    (hb213 : (o.oangle (c 1 - c 2) (c 3 - c 2)).toReal < 0)
    (hq03 : (4 : ℝ) * lam ≤ dirArc o e c 0 4 1)
    (hq43 : (2 : ℝ) * lam ≤ dirArc o e c 4 3 0)
    (hq32 : (2 : ℝ) * lam ≤ dirArc o e c 3 2 4) :
    (5 : ℝ) * lam ≤ Real.pi := by
  classical
  have hmem : ∀ i j : Fin 5,
      dirRep o e c i j ∈ Set.Ico 0 Real.pi :=
    fun _ _ => linRep_mem_Ico _
  -- fan equations: row 0 and row 4 cyclic chains sum to π
  have F0 : dirArc o e c 0 1 2 + dirArc o e c 0 2 3 +
      dirArc o e c 0 3 4 + dirArc o e c 0 4 1 = Real.pi :=
    cyclicDiff_chain4 (hmem 0 1) (hmem 0 2) (hmem 0 3) (hmem 0 4)
      h012 h013 h014
  have F4 : dirArc o e c 4 0 1 + dirArc o e c 4 1 2 +
      dirArc o e c 4 2 3 + dirArc o e c 4 3 0 = Real.pi :=
    cyclicDiff_chain4 (hmem 4 0) (hmem 4 1) (hmem 4 2) (hmem 4 3)
      h401 h402 h403
  -- telescope the row-4 fan into the complement identity S_4 + H'_3 = π
  have e401 : dirArc o e c 4 0 2 =
      dirArc o e c 4 0 1 + dirArc o e c 4 1 2 :=
    cyclicDiff_eq_add_of_le (hmem 4 0) (hmem 4 1) (hmem 4 2) h401
  have e402 : dirArc o e c 4 0 3 =
      dirArc o e c 4 0 2 + dirArc o e c 4 2 3 :=
    cyclicDiff_eq_add_of_le (hmem 4 0) (hmem 4 2) (hmem 4 3) h402
  have hcomp : dirArc o e c 4 0 3 + dirArc o e c 4 3 0 = Real.pi := by
    linarith
  -- demand bounds: D_1, D_2 via complement bits + triAngle; D_3 = hq32
  have hd0 : lam ≤ dirArc o e c 1 0 2 := by
    have hA : ∠ (c 0) (c 1) (c 2) =
        Real.pi - dirArc o e c 1 0 2 :=
      dirRep_arc_eq_pi_sub_angle o e he
        (hleg.inj.ne (by decide)) (hleg.inj.ne (by decide)) hb102
    have h := hleg.triAngle 0 1 2 (by decide) (by decide) (by decide)
    linarith
  have hd1 : lam ≤ dirArc o e c 2 1 3 := by
    have hA : ∠ (c 1) (c 2) (c 3) =
        Real.pi - dirArc o e c 2 1 3 :=
      dirRep_arc_eq_pi_sub_angle o e he
        (hleg.inj.ne (by decide)) (hleg.inj.ne (by decide)) hb213
    have h := hleg.triAngle 1 2 3 (by decide) (by decide) (by decide)
    linarith
  -- the certificate is signed_chain_certB at
  -- x = (0,1,2,3,4), L = 3, a = 4, b' = 2, m = (1,1,2), n = 4:
  -- σ = 4+2+4−8 = 2, so δ ≥ 1.
  let fv : ℕ → Fin 5 := fun k =>
    ⟨k % 5, Nat.mod_lt _ (by norm_num : 0 < 5)⟩
  have hδ := signed_chain_certB o e hleg hlam he (L := 3) (n := 4)
    (by norm_num) fv
    (by intro i j hi hj hij h
        apply hij
        have hv : i % 5 = j % 5 := congrArg Fin.val h
        omega)
    (by -- hfanL: Σ_{i<3} A_{i+1} + H_0 = π, from the row-0 chain
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
      show dirArc o e c 0 1 2 + dirArc o e c 0 2 3 +
        dirArc o e c 0 3 4 + dirArc o e c 0 4 1 = Real.pi
      exact F0)
    (by -- hcomp: S_4 + H'_3 = π, telescoped from the row-4 chain
      show dirArc o e c 4 0 3 + dirArc o e c 4 3 0 = Real.pi
      exact hcomp)
    (by intro i hi
        have hi3 : i < 3 := Finset.mem_range.mp hi
        interval_cases i
        · show dirArc o e c 1 0 0 ≤ dirArc o e c 1 0 2
          have hz : dirArc o e c 1 0 0 = 0 := by
            simp [dirArc, cyclicDiff]
          rw [hz]
          exact cyclicDiff_nonneg (hmem 1 0).2 (hmem 1 2).1
        · exact h2013
        · exact h3024)
    (by intro i hi
        have hi3 : i < 3 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb012
        · exact hb203a
        · exact hb304a)
    (by intro i hi
        have hi3 : i < 3 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb102
        · exact hb023
        · exact hb034)
    (by intro i hi
        have hi3 : i < 3 := Finset.mem_range.mp hi
        interval_cases i
        · exact hb021
        · exact hb032
        · exact hb043)
    (fun i => if i ≤ 1 then 1 else 2)
    (by intro i hi
        have hi3 : i < 3 := Finset.mem_range.mp hi
        interval_cases i
        · conv_lhs => norm_num
          exact hd0
        · conv_lhs => norm_num
          exact hd1
        · conv_lhs => norm_num
          exact hq32)
    4 2
    (by exact_mod_cast hq03)
    (by exact_mod_cast hq43)
  have hδ' : (1 : ℝ) ≤ Real.pi / lam - 4 := by
    norm_num [Finset.sum_range_succ] at hδ
    linarith
  have hδ'' : (5 : ℝ) ≤ Real.pi / lam := by linarith
  exact (le_div_iff₀ hlam).mp hδ''


end Jsp404
