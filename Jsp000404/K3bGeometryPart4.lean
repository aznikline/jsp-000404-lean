import Jsp000404.K3bGeometryPart3

namespace Jsp404

open Finset
open scoped EuclideanGeometry EuclideanSpace

variable (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)

/-- **One triangle piece of a signed residual chain.**  For distinct
centers `i0, j, jp` (with `jm` the previous chain element, possibly
`i0` itself), the cyclic-order split `hsplit` — direction `jm` lies
on the forward arc `i0 → jp` at `j` — plus the three orientation
bits give the triangle relation

    dirArc i0 j jp + dirArc jp i0 j = dirArc j i0 jm + dirArc j jm jp

i.e. `A + S' = S + D` in the chain notation: the apex-`j` angle is
the complement `π − dirArc j i0 jp`, which `cyclicDiff_eq_add_of_le`
splits through `jm` into `S + D`.  The other two angles are the arc
branch, giving `A` and `S'` respectively. -/
theorem tri_piece_rel {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (he : e ≠ 0)
    {i0 jm j jp : Fin s}
    (h0j : i0 ≠ j) (h0jp : i0 ≠ jp) (hjjp : j ≠ jp)
    (hsplit : dirArc o e c j i0 jm ≤ dirArc o e c j i0 jp)
    (hb0 : 0 ≤ (o.oangle (c j - c i0) (c jp - c i0)).toReal)
    (hbj : (o.oangle (c i0 - c j) (c jp - c j)).toReal < 0)
    (hbjp : 0 ≤ (o.oangle (c i0 - c jp) (c j - c jp)).toReal) :
    dirArc o e c i0 j jp + dirArc o e c jp i0 j =
      dirArc o e c j i0 jm + dirArc o e c j jm jp := by
  have hinj := hleg.inj
  have A0 : ∠ (c j) (c i0) (c jp) = dirArc o e c i0 j jp :=
    dirRep_arc_eq_angle o e hleg he h0j.symm h0jp hjjp hb0
  have Aj : ∠ (c i0) (c j) (c jp) =
      Real.pi - dirArc o e c j i0 jp :=
    dirRep_arc_eq_pi_sub_angle o e he
      (hinj.ne h0j) (hinj.ne hjjp.symm) hbj
  have Ajp : ∠ (c i0) (c jp) (c j) = dirArc o e c jp i0 j :=
    dirRep_arc_eq_angle o e hleg he h0jp hjjp.symm h0j hbjp
  have T := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c i0) (p₂ := c j) (p₃ := c jp) (hinj.ne h0j.symm)
  rw [EuclideanGeometry.angle_comm (c j) (c jp) (c i0),
    EuclideanGeometry.angle_comm (c jp) (c i0) (c j)] at T
  have eT : dirArc o e c j i0 jp =
      dirArc o e c j i0 jm + dirArc o e c j jm jp :=
    cyclicDiff_eq_add_of_le (linRep_mem_Ico _) (linRep_mem_Ico _)
      (linRep_mem_Ico _) hsplit
  linarith

/-- **Signed residual chain, arbitrary length.**  A chain of distinct
centers `x 0, x 1, …, x (L+1)` with `L ≥ 2`.  Writing
`A_j = dirArc (x 0)(x j)(x (j+1))`,
`D_j = dirArc (x j)(x (j-1))(x (j+1))`,
`S_j = dirArc (x j)(x 0)(x (j-1))`  (`S_1 = 0`),
`H_0 = dirArc (x 0)(x (L+1))(x 1)`,
`H_L = dirArc (x L)(x (L+1))(x 0)`,

each interior triangle `△(x0, x_{j+1}, x_{j+2})` contributes
`A_{j+1} + S_{j+2} = S_{j+1} + D_{j+1}` via `tri_piece_rel`; the
telescoping sum plus the two boundary fan closures gives

    2π = A_L + H_0 + H_L + Σ_{j=1}^{L} D_j.                    (★)

`triAngle` through the `hbD` complement bits gives `D_j ≥ λ`;
`A_L ≥ 0` and `H_0 ≥ aλ`, `H_L ≥ bλ` then yield the threshold
through `ResidualWitness.ge_of`:

    δ = π/λ − n ≥ (a + b + L − 2n) / 2.                        (†)

Hypotheses are the certificate's geometric data: boundary fan
closures `hfanL hfanR`, per-interior order split `hsplit`, the
orientation bits `hbA hbT hbS hbD`, and the two cell lower bounds. -/
theorem signed_chain_cert {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    {L n : ℕ} (hL : 2 ≤ L) (x : ℕ → Fin s)
    (hx : ∀ i j : ℕ, i ≤ L + 1 → j ≤ L + 1 → i ≠ j → x i ≠ x j)
    (hfanL : (∑ i ∈ Finset.range L,
        dirArc o e c (x 0) (x (i + 1)) (x (i + 2)))
      + dirArc o e c (x 0) (x (L + 1)) (x 1) = Real.pi)
    (hfanR : dirArc o e c (x L) (x 0) (x (L - 1))
      + dirArc o e c (x L) (x (L - 1)) (x (L + 1))
      + dirArc o e c (x L) (x (L + 1)) (x 0) = Real.pi)
    (hsplit : ∀ i ∈ Finset.range (L - 1),
      dirArc o e c (x (i + 1)) (x 0) (x i)
        ≤ dirArc o e c (x (i + 1)) (x 0) (x (i + 2)))
    (hbA : ∀ i ∈ Finset.range (L - 1),
      0 ≤ (o.oangle (c (x (i + 1)) - c (x 0))
        (c (x (i + 2)) - c (x 0))).toReal)
    (hbT : ∀ i ∈ Finset.range (L - 1),
      (o.oangle (c (x 0) - c (x (i + 1)))
        (c (x (i + 2)) - c (x (i + 1)))).toReal < 0)
    (hbS : ∀ i ∈ Finset.range (L - 1),
      0 ≤ (o.oangle (c (x 0) - c (x (i + 2)))
        (c (x (i + 1)) - c (x (i + 2)))).toReal)
    (hbD : ∀ i ∈ Finset.range L,
      (o.oangle (c (x i) - c (x (i + 1)))
        (c (x (i + 2)) - c (x (i + 1)))).toReal < 0)
    (a b : ℕ)
    (hH0 : a * lam ≤ dirArc o e c (x 0) (x (L + 1)) (x 1))
    (hHL : b * lam ≤ dirArc o e c (x L) (x (L + 1)) (x 0)) :
    ((a : ℝ) + b + L - 2 * n) / 2 ≤ Real.pi / lam - n := by
  have hinj := hleg.inj
  -- the triangle relations, each sourced from tri_piece_rel
  have hrel : ∀ i ∈ Finset.range (L - 1),
      dirArc o e c (x 0) (x (i + 1)) (x (i + 2))
        + dirArc o e c (x (i + 2)) (x 0) (x (i + 1)) =
      dirArc o e c (x (i + 1)) (x 0) (x i)
        + dirArc o e c (x (i + 1)) (x i) (x (i + 2)) := by
    intro i hi
    have hiL : i < L - 1 := Finset.mem_range.mp hi
    have hd01 : x 0 ≠ x (i + 1) :=
      hx 0 (i + 1) (by omega) (by omega) (by omega)
    have hd02 : x 0 ≠ x (i + 2) :=
      hx 0 (i + 2) (by omega) (by omega) (by omega)
    have hd12 : x (i + 1) ≠ x (i + 2) :=
      hx (i + 1) (i + 2) (by omega) (by omega) (by omega)
    exact tri_piece_rel o e hleg he hd01 hd02 hd12
      (hsplit i hi) (hbA i hi) (hbT i hi) (hbS i hi)
  -- telescoped sum of the relations
  have tele : ∀ k : ℕ, k ≤ L - 1 →
      (∑ i ∈ Finset.range k,
          dirArc o e c (x 0) (x (i + 1)) (x (i + 2)))
        + dirArc o e c (x (k + 1)) (x 0) (x k) =
      (∑ i ∈ Finset.range k,
          dirArc o e c (x (i + 1)) (x i) (x (i + 2)))
        + dirArc o e c (x 1) (x 0) (x 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkk : k < L - 1 := by omega
      have hrelk := hrel k (Finset.mem_range.mpr hkk)
      have ihk := ih (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  have htele := tele (L - 1) le_rfl
  have eL1 : x (L - 1 + 1) = x L := by congr 1; omega
  have hS1 : dirArc o e c (x 1) (x 0) (x 0) = 0 := by
    simp [dirArc, cyclicDiff]
  rw [eL1, hS1] at htele
  -- split the last summand off each boundary sum
  have eL2 : x (L - 1 + 2) = x (L + 1) := by congr 1; omega
  have hsplitA : (∑ i ∈ Finset.range L,
      dirArc o e c (x 0) (x (i + 1)) (x (i + 2))) =
    (∑ i ∈ Finset.range (L - 1),
        dirArc o e c (x 0) (x (i + 1)) (x (i + 2)))
      + dirArc o e c (x 0) (x L) (x (L + 1)) := by
    nth_rw 1 [show L = L - 1 + 1 from by omega]
    rw [Finset.sum_range_succ, eL1, eL2]
  have hsplitD : (∑ i ∈ Finset.range L,
      dirArc o e c (x (i + 1)) (x i) (x (i + 2))) =
    (∑ i ∈ Finset.range (L - 1),
        dirArc o e c (x (i + 1)) (x i) (x (i + 2)))
      + dirArc o e c (x L) (x (L - 1)) (x (L + 1)) := by
    nth_rw 1 [show L = L - 1 + 1 from by omega]
    rw [Finset.sum_range_succ, eL1, eL2]
  -- the master identity (★)
  have hstar : 2 * Real.pi =
      dirArc o e c (x 0) (x L) (x (L + 1))
      + dirArc o e c (x 0) (x (L + 1)) (x 1)
      + dirArc o e c (x L) (x (L + 1)) (x 0)
      + ∑ i ∈ Finset.range L,
          dirArc o e c (x (i + 1)) (x i) (x (i + 2)) := by
    rw [hsplitA] at hfanL
    rw [hsplitD]
    linarith
  -- the demand bounds: D_{i+1} ≥ λ from triAngle + complement bits
  have hDge : ∀ i ∈ Finset.range L,
      lam ≤ dirArc o e c (x (i + 1)) (x i) (x (i + 2)) := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    have hd1 : x i ≠ x (i + 1) :=
      hx i (i + 1) (by omega) (by omega) (by omega)
    have hd2 : x (i + 1) ≠ x (i + 2) :=
      hx (i + 1) (i + 2) (by omega) (by omega) (by omega)
    have hd3 : x i ≠ x (i + 2) :=
      hx i (i + 2) (by omega) (by omega) (by omega)
    have hA : ∠ (c (x i)) (c (x (i + 1))) (c (x (i + 2))) =
        Real.pi - dirArc o e c (x (i + 1)) (x i) (x (i + 2)) :=
      dirRep_arc_eq_pi_sub_angle o e he
        (hinj.ne hd1) (hinj.ne hd2.symm) (hbD i hi)
    have h := hleg.triAngle (x i) (x (i + 1)) (x (i + 2)) hd1 hd2 hd3
    linarith
  have hsumD : (L : ℝ) * lam ≤
      ∑ i ∈ Finset.range L,
        dirArc o e c (x (i + 1)) (x i) (x (i + 2)) := by
    have hs := Finset.sum_le_sum (s := Finset.range L)
      (f := fun _ : ℕ => lam)
      (g := fun i => dirArc o e c (x (i + 1)) (x i) (x (i + 2)))
      (fun i hi => hDge i hi)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    exact hs
  have hAL : 0 ≤ dirArc o e c (x 0) (x L) (x (L + 1)) :=
    cyclicDiff_nonneg (linRep_mem_Ico _).2 (linRep_mem_Ico _).1
  -- the parameterized residual backend at τ = (a+b+L−2n)/2
  have hcancel : lam * (Real.pi / lam) = Real.pi :=
    mul_div_cancel₀ _ hlam.ne'
  exact ResidualWitness.ge_of
    ⟨dirArc o e c (x 0) (x L) (x (L + 1))
        + ∑ i ∈ Finset.range L,
            dirArc o e c (x (i + 1)) (x i) (x (i + 2)),
     0, 2 * n * lam
        - dirArc o e c (x 0) (x (L + 1)) (x 1)
        - dirArc o e c (x L) (x (L + 1)) (x 0),
     L * lam, 2 * lam, 0, 0, Real.pi / lam - n⟩
    (τ := ((a : ℝ) + b + L - 2 * n) / 2)
    (by show _ - 0 - 2 * lam * (Real.pi / lam - n) = _; linarith)
    (by show (L : ℝ) * lam ≤ _; linarith)
    (by show (0 : ℝ) ≤ 0 + 0 * (Real.pi / lam - n); linarith)
    (by show (0 : ℝ) < 2 * lam + 0; linarith)
    (by show ((a : ℝ) + b + L - 2 * n) / 2 * (2 * lam + 0) ≤
        L * lam - 0 - (2 * n * lam
          - dirArc o e c (x 0) (x (L + 1)) (x 1)
          - dirArc o e c (x L) (x (L + 1)) (x 0)); linarith)

/-- **Signed chain, endpoint-fan variant.**  Same telescoped chain
`x 0 … x (L+1)` (`L ≥ 2`), but the right closure is the full fan at
the ENDPOINT `x (L+1)` — the complement identity
`S_{L+1} + H'_L = π` — and the triangulation runs through `j = L`
(the last triangle `△(x0, x_L, x_{L+1})` includes the right-fan
vertex).  Master identity:

    2π = H_0 + H'_L + Σ_{j=1}^{L} D_j.

Each demand arc carries an arbitrary cell bound `m i · λ` — in the
model's `r = gap/λ − q` normalization a demand angle gives `q+1`
cells and an unconsumed arc keeps its `q` baseline — so the score is
`σ = a + b' + Σ m_i − 2n` and `δ ≥ σ/2` through `ge_of`. -/
theorem signed_chain_certB {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    {L n : ℕ} (hL : 2 ≤ L) (x : ℕ → Fin s)
    (hx : ∀ i j : ℕ, i ≤ L + 1 → j ≤ L + 1 → i ≠ j → x i ≠ x j)
    (hfanL : (∑ i ∈ Finset.range L,
        dirArc o e c (x 0) (x (i + 1)) (x (i + 2)))
      + dirArc o e c (x 0) (x (L + 1)) (x 1) = Real.pi)
    (hcomp : dirArc o e c (x (L + 1)) (x 0) (x L)
      + dirArc o e c (x (L + 1)) (x L) (x 0) = Real.pi)
    (hsplit : ∀ i ∈ Finset.range L,
      dirArc o e c (x (i + 1)) (x 0) (x i)
        ≤ dirArc o e c (x (i + 1)) (x 0) (x (i + 2)))
    (hbA : ∀ i ∈ Finset.range L,
      0 ≤ (o.oangle (c (x (i + 1)) - c (x 0))
        (c (x (i + 2)) - c (x 0))).toReal)
    (hbT : ∀ i ∈ Finset.range L,
      (o.oangle (c (x 0) - c (x (i + 1)))
        (c (x (i + 2)) - c (x (i + 1)))).toReal < 0)
    (hbS : ∀ i ∈ Finset.range L,
      0 ≤ (o.oangle (c (x 0) - c (x (i + 2)))
        (c (x (i + 1)) - c (x (i + 2)))).toReal)
    (m : ℕ → ℕ)
    (hmD : ∀ i ∈ Finset.range L,
      (m i : ℝ) * lam
        ≤ dirArc o e c (x (i + 1)) (x i) (x (i + 2)))
    (a b : ℕ)
    (hH0 : a * lam ≤ dirArc o e c (x 0) (x (L + 1)) (x 1))
    (hHL : b * lam ≤ dirArc o e c (x (L + 1)) (x L) (x 0)) :
    ((a : ℝ) + b + (∑ i ∈ Finset.range L, (m i : ℝ)) - 2 * n) / 2
      ≤ Real.pi / lam - n := by
  have hinj := hleg.inj
  -- the triangle relations, each sourced from tri_piece_rel
  have hrel : ∀ i ∈ Finset.range L,
      dirArc o e c (x 0) (x (i + 1)) (x (i + 2))
        + dirArc o e c (x (i + 2)) (x 0) (x (i + 1)) =
      dirArc o e c (x (i + 1)) (x 0) (x i)
        + dirArc o e c (x (i + 1)) (x i) (x (i + 2)) := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    have hd01 : x 0 ≠ x (i + 1) :=
      hx 0 (i + 1) (by omega) (by omega) (by omega)
    have hd02 : x 0 ≠ x (i + 2) :=
      hx 0 (i + 2) (by omega) (by omega) (by omega)
    have hd12 : x (i + 1) ≠ x (i + 2) :=
      hx (i + 1) (i + 2) (by omega) (by omega) (by omega)
    exact tri_piece_rel o e hleg he hd01 hd02 hd12
      (hsplit i hi) (hbA i hi) (hbT i hi) (hbS i hi)
  -- telescoped sum of the relations
  have tele : ∀ k : ℕ, k ≤ L →
      (∑ i ∈ Finset.range k,
          dirArc o e c (x 0) (x (i + 1)) (x (i + 2)))
        + dirArc o e c (x (k + 1)) (x 0) (x k) =
      (∑ i ∈ Finset.range k,
          dirArc o e c (x (i + 1)) (x i) (x (i + 2)))
        + dirArc o e c (x 1) (x 0) (x 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkk : k < L := by omega
      have hrelk := hrel k (Finset.mem_range.mpr hkk)
      have ihk := ih (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  have htele := tele L le_rfl
  have hS1 : dirArc o e c (x 1) (x 0) (x 0) = 0 := by
    simp [dirArc, cyclicDiff]
  rw [hS1] at htele
  -- the master identity: 2π = H_0 + H'_L + Σ D
  have hstar : 2 * Real.pi =
      dirArc o e c (x 0) (x (L + 1)) (x 1)
      + dirArc o e c (x (L + 1)) (x L) (x 0)
      + ∑ i ∈ Finset.range L,
          dirArc o e c (x (i + 1)) (x i) (x (i + 2)) := by
    linarith
  have hPbound : ((a : ℝ) + b
        + ∑ i ∈ Finset.range L, (m i : ℝ)) * lam ≤
      dirArc o e c (x 0) (x (L + 1)) (x 1)
      + dirArc o e c (x (L + 1)) (x L) (x 0)
      + ∑ i ∈ Finset.range L,
          dirArc o e c (x (i + 1)) (x i) (x (i + 2)) := by
    rw [add_mul, add_mul, Finset.sum_mul]
    exact add_le_add (add_le_add hH0 hHL)
      (Finset.sum_le_sum fun i hi => hmD i hi)
  -- the parameterized residual backend
  have hcancel : lam * (Real.pi / lam) = Real.pi :=
    mul_div_cancel₀ _ hlam.ne'
  exact ResidualWitness.ge_of
    ⟨dirArc o e c (x 0) (x (L + 1)) (x 1)
        + dirArc o e c (x (L + 1)) (x L) (x 0)
        + ∑ i ∈ Finset.range L,
            dirArc o e c (x (i + 1)) (x i) (x (i + 2)),
     0, 2 * n * lam,
     (a + b + ∑ i ∈ Finset.range L, (m i : ℝ)) * lam,
     2 * lam, 0, 0, Real.pi / lam - n⟩
    (τ := ((a : ℝ) + b
        + (∑ i ∈ Finset.range L, (m i : ℝ)) - 2 * n) / 2)
    (by show _ - 0 - 2 * lam * (Real.pi / lam - n) = _; linarith)
    (by linarith)
    (by show (0 : ℝ) ≤ 0 + 0 * (Real.pi / lam - n); linarith)
    (by show (0 : ℝ) < 2 * lam + 0; linarith)
    (by ring_nf; linarith)

/-- **One-piece extension of a signed chain.**  Given the full data
of a length-`L` chain certificate (left fan, interior splits and
bits, demands, right fan at `x L`, boundary budgets `a`, `b`) plus
the new piece — the wrap-arc split `hext` (new endpoint `x (L+2)`
is the next direction after `x (L+1)` in row `x 0`), the new
triangle `△(x0, x_L, x_{L+1})` data `hsplitN hbAN hbTN hbSN`, the
new demand `hbDN` at apex `x_{L+1}` with arms `{x_L, x_{L+2}}`, the
new right-fan closure `hfanRN` at `x_{L+1}`, and fresh boundary
bounds — the conclusion is the pair of thresholds

    (a + b + L − 2n)/2 ≤ δ   ∧   (a' + b' + (L+1) − 2n)/2 ≤ δ,

so the score ledger is `σ' − σ = 1 + (a' + b') − (a + b)`; when the
new left boundary is the old one minus the absorbed gap's cells,
`a' = a − q`, this is `σ' − σ = 1 + b' − b − q` — the old `b` is
replaced, not kept. -/
theorem signed_chain_extend {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlam : 0 < lam) (he : e ≠ 0)
    {L n : ℕ} (hL : 2 ≤ L) (x : ℕ → Fin s)
    (hx : ∀ i j : ℕ, i ≤ L + 2 → j ≤ L + 2 → i ≠ j → x i ≠ x j)
    (hfanL : (∑ i ∈ Finset.range L,
        dirArc o e c (x 0) (x (i + 1)) (x (i + 2)))
      + dirArc o e c (x 0) (x (L + 1)) (x 1) = Real.pi)
    (hfanR : dirArc o e c (x L) (x 0) (x (L - 1))
      + dirArc o e c (x L) (x (L - 1)) (x (L + 1))
      + dirArc o e c (x L) (x (L + 1)) (x 0) = Real.pi)
    (hsplit : ∀ i ∈ Finset.range (L - 1),
      dirArc o e c (x (i + 1)) (x 0) (x i)
        ≤ dirArc o e c (x (i + 1)) (x 0) (x (i + 2)))
    (hbA : ∀ i ∈ Finset.range (L - 1),
      0 ≤ (o.oangle (c (x (i + 1)) - c (x 0))
        (c (x (i + 2)) - c (x 0))).toReal)
    (hbT : ∀ i ∈ Finset.range (L - 1),
      (o.oangle (c (x 0) - c (x (i + 1)))
        (c (x (i + 2)) - c (x (i + 1)))).toReal < 0)
    (hbS : ∀ i ∈ Finset.range (L - 1),
      0 ≤ (o.oangle (c (x 0) - c (x (i + 2)))
        (c (x (i + 1)) - c (x (i + 2)))).toReal)
    (hbD : ∀ i ∈ Finset.range L,
      (o.oangle (c (x i) - c (x (i + 1)))
        (c (x (i + 2)) - c (x (i + 1)))).toReal < 0)
    (a b : ℕ)
    (hH0 : a * lam ≤ dirArc o e c (x 0) (x (L + 1)) (x 1))
    (hHL : b * lam ≤ dirArc o e c (x L) (x (L + 1)) (x 0))
    (hext : dirArc o e c (x 0) (x (L + 1)) (x (L + 2))
        ≤ dirArc o e c (x 0) (x (L + 1)) (x 1))
    (hsplitN : dirArc o e c (x L) (x 0) (x (L - 1))
        ≤ dirArc o e c (x L) (x 0) (x (L + 1)))
    (hbAN : 0 ≤ (o.oangle (c (x L) - c (x 0))
        (c (x (L + 1)) - c (x 0))).toReal)
    (hbTN : (o.oangle (c (x 0) - c (x L))
        (c (x (L + 1)) - c (x L))).toReal < 0)
    (hbSN : 0 ≤ (o.oangle (c (x 0) - c (x (L + 1)))
        (c (x L) - c (x (L + 1)))).toReal)
    (hbDN : (o.oangle (c (x L) - c (x (L + 1)))
        (c (x (L + 2)) - c (x (L + 1)))).toReal < 0)
    (hfanRN : dirArc o e c (x (L + 1)) (x 0) (x L)
      + dirArc o e c (x (L + 1)) (x L) (x (L + 2))
      + dirArc o e c (x (L + 1)) (x (L + 2)) (x 0) = Real.pi)
    (a' b' : ℕ)
    (hH0' : a' * lam ≤ dirArc o e c (x 0) (x (L + 2)) (x 1))
    (hHL' : b' * lam ≤ dirArc o e c (x (L + 1)) (x (L + 2)) (x 0)) :
    ((a : ℝ) + b + L - 2 * n) / 2 ≤ Real.pi / lam - n ∧
    ((a' : ℝ) + b' + (L + 1) - 2 * n) / 2 ≤ Real.pi / lam - n := by
  have hinj := hleg.inj
  -- extended left fan: Σ_{i<L+1} A + H_0' = π
  have hfanL' : (∑ i ∈ Finset.range (L + 1),
      dirArc o e c (x 0) (x (i + 1)) (x (i + 2)))
    + dirArc o e c (x 0) (x (L + 2)) (x 1) = Real.pi := by
    rw [Finset.sum_range_succ]
    have htele : dirArc o e c (x 0) (x (L + 1)) (x 1) =
        dirArc o e c (x 0) (x (L + 1)) (x (L + 2))
          + dirArc o e c (x 0) (x (L + 2)) (x 1) :=
      cyclicDiff_eq_add_of_le (linRep_mem_Ico _) (linRep_mem_Ico _)
        (linRep_mem_Ico _) hext
    linarith
  -- extended interior bundles: i = L-1 is the new piece
  have hsplit' : ∀ i ∈ Finset.range L,
      dirArc o e c (x (i + 1)) (x 0) (x i)
        ≤ dirArc o e c (x (i + 1)) (x 0) (x (i + 2)) := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    rcases eq_or_lt_of_le (by omega : i ≤ L - 1) with h | h
    · have e1 : i + 1 = L := by omega
      have e2 : i + 2 = L + 1 := by omega
      rw [e1, e2, h]
      exact hsplitN
    · exact hsplit i (Finset.mem_range.mpr (by omega))
  have hbA' : ∀ i ∈ Finset.range L,
      0 ≤ (o.oangle (c (x (i + 1)) - c (x 0))
        (c (x (i + 2)) - c (x 0))).toReal := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    rcases eq_or_lt_of_le (by omega : i ≤ L - 1) with h | h
    · have e1 : i + 1 = L := by omega
      have e2 : i + 2 = L + 1 := by omega
      rw [e1, e2]
      exact hbAN
    · exact hbA i (Finset.mem_range.mpr (by omega))
  have hbT' : ∀ i ∈ Finset.range L,
      (o.oangle (c (x 0) - c (x (i + 1)))
        (c (x (i + 2)) - c (x (i + 1)))).toReal < 0 := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    rcases eq_or_lt_of_le (by omega : i ≤ L - 1) with h | h
    · have e1 : i + 1 = L := by omega
      have e2 : i + 2 = L + 1 := by omega
      rw [e1, e2]
      exact hbTN
    · exact hbT i (Finset.mem_range.mpr (by omega))
  have hbS' : ∀ i ∈ Finset.range L,
      0 ≤ (o.oangle (c (x 0) - c (x (i + 2)))
        (c (x (i + 1)) - c (x (i + 2)))).toReal := by
    intro i hi
    have hiL : i < L := Finset.mem_range.mp hi
    rcases eq_or_lt_of_le (by omega : i ≤ L - 1) with h | h
    · have e1 : i + 1 = L := by omega
      have e2 : i + 2 = L + 1 := by omega
      rw [e1, e2]
      exact hbSN
    · exact hbS i (Finset.mem_range.mpr (by omega))
  have hbD' : ∀ i ∈ Finset.range (L + 1),
      (o.oangle (c (x i) - c (x (i + 1)))
        (c (x (i + 2)) - c (x (i + 1)))).toReal < 0 := by
    intro i hi
    have hiL : i < L + 1 := Finset.mem_range.mp hi
    rcases eq_or_lt_of_le (by omega : i ≤ L) with h | h
    · have e1 : i + 1 = L + 1 := by omega
      have e2 : i + 2 = L + 2 := by omega
      have e3 : i = L := by omega
      rw [e1, e2, e3]
      exact hbDN
    · exact hbD i (Finset.mem_range.mpr (by omega))
  have hx' : ∀ i j : ℕ, i ≤ L + 1 → j ≤ L + 1 → i ≠ j →
      x i ≠ x j :=
    fun i j hi hj hne => hx i j (by omega) (by omega) hne
  refine ⟨signed_chain_cert o e hleg hlam he hL x hx'
      hfanL hfanR hsplit hbA hbT hbS hbD a b hH0 hHL, ?_⟩
  have hnew := signed_chain_cert o e hleg hlam he (L := L + 1)
    (n := n) (by omega) x hx
    hfanL' hfanRN hsplit' hbA' hbT' hbS' hbD' a' b' hH0' hHL'
  simpa using hnew


end Jsp404
