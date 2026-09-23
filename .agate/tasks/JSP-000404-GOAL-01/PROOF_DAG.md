# Proof DAG — arbitrary-N Sendov count bound

REVISED (P1): no separate `AngleSystem` class — geometry rows are the
closed system. `directionRow`/`cycGaps` already give real consecutive
arcs; `erase_directionRow` proves deletion = sub-config row; legality
fields of `Section4Legality` are defined on the center configuration
directly, so heredity is `c' = c ∘ v.succAbove` reindexing.

```
Section4Legality c λ  (geometry: injective centers, ∠ ≤ π−λ)
        │
        ▼  P1  [Base3Bridge.lean — s=3 instance DONE]
rowScore λ (directionRow i) = g(∠ᵢ) + g(π−∠ᵢ)
        │
        ▼  P2  [erase_directionRow — ALREADY PROVED]
directionRow (c∘v.succAbove) i' =
  (directionRow c (v.succAbove i')).erase (dirRep .. v)
        │
        ▼  P3  [sum_potential_erase / removable_iff — ALREADY PROVED]
        │
        ▼  P2  [erase_preserves]
merge = drop direction i→t, replace two adjacent gaps by their sum
        angles unchanged ⇒ ALL constraints hereditary
        │
        ▼  P3  [potential identity — reuse Deletion.lean algebra]
F(A−t) = F(A) − 2^{k_t} + G_t,
  G_t = Σ_{i≠t} 2^{k_i}(2^{g_{it}}−1),  k'_i = k_i + g_{it}
        │
        ▼  P4  [Cert Lemma — SOLE CRUX]
F(A) > cap  ⟹  ∃t: G_t ≥ 2^{k_t}
        │
        ▼  P5
induction on s (well-founded descent, F non-decreasing along cert chain)
  base s=3: base3_low / base3_high  [DONE]
        │
        ▼
Σᵢ 2^{kᵢ} ≤ 2^n (δ<1/2) | 2^n + 2^{n−2} (δ≥1/2)
        │
        ▼
StaircaseBound.tail → sendov_count_bound → JSP-000404
```

## Invariants

- cap = uniform `2^n` / `2^n+2^{n−2}` (per-δ). NOT the paper's
  per-s sharp `2^n+2^{n−s+1}` — unattainable on the abstract class
  (feasible F=20 > C₄=18 exists at s=4 δ-high), unnecessary for the
  final theorem.
- Descent only needs cert on `F > cap`. Sparse low-F assignments may
  have no removable vertex — verified consistent (n=3 s=4: all 572
  top-F feasible have joint cert+feasible merge).

## Kraft-route DAG (supersedes the Cert formulation of P4)

```
K0  potential ↔ Kraft                       DONE (Deletion/Induction)
    potential = 2^n·Σᵢ(1/2)^{cᵢ}; cap ⟺ Σ(1/2)^c ≤ 1 + ¼[big]

K1  Saturation structure                    DONE (Deletion.lean)
    c_i = 1 ⟹ ∃! dominant gap G ≥ nλ,
    complement ≤ π − nλ                     [rowDefect_eq_one]

K2  Saturation geometry                     DONE (Induction.lean)
    arc dichotomy                           [cyclicDiff_le_or_ge]
    c_i = 1 ⟹ ∠jik ≤ π − nλ = δλ            [angle_le_pi_sub_of_saturation]
    2 saturated + δ < 1/2 ⟹ ⊥               [not_two_saturated_of_delta_lt_half]
      (δ = 1/2 phase transition now kernel-derived via facing_lower)

K3  Kraft packing                    ⟵ SOLE REMAINING CRUX
    case split (glue PROVED, `kraft_packing_of_legality`):
      saturated count ≤ 2 for n ≥ 2   [not_three_saturated]
      ≤ 1 in low regime               [not_two_saturated_of_delta_lt_half]
    ── residual-capacity reformulation (KraftResidual.lean) ──
      a_r = #{i|c_i=r},  R_m = 2^m·B − Σ_{r≤m} a_r·2^{m−r}
      B = 1 low / 5/4 high;   R_{m+1} = 2R_m − a_{m+1}
      K3a  recurrence + R_M = 2^M(B−K) + K≤B ↔ ∀m R_m≥0   DONE
      K3b  K>B ⟹ first overfull level m: R_{m−1}≥0,
           a_m > 2R_{m−1}              [exists_min_overfull_level]
           m ≥ 2 in geometry           [exists_first_overfull_level_
                                        ge_two — not_three_saturated]
           certificate families wired to real geometry:
             polygon: t-cycle, Σ∠=(t−2)π ⟹ tλ≤2π
               [cycle_cert — hsum still a premise]
             fat-arc (non-polygon): arc of directionRow i with
               Σ⌊g/λ⌋ ≥ n on ccw branch ⟹ (n+1)λ ≤ π
               [arc_overflow_geometric_of_cells — fully wired:
                rnn bounds + Ico telescoping + cyclicDiff_dirRep
                + triAngle; only checkable certificate data as
                hypotheses]
             signed chain (arbitrary L, kernel-checked):
               tri_piece_rel — one triangle piece: arc split +
                 orientation bits ⟹ A_j + S_{j+1} = S_j + D_j
               signed_chain_cert — telescoped pieces + boundary
                 fan closures ⟹ 2π = A_L+H_0+H_L+ΣD_j (★),
                 hence δ ≥ (a+b+L−2n)/2 (†) via ge_of
               leaf_0001_cert — now the L=3, a=4, b=3, n=4
                 instance; leaf_0001_absurd unchanged
               signed_chain_extend — old L-chain data + new piece
                 (wrap split, △(x0,x_L,x_{L+1}) bits, new demand at
                 x_{L+1}, new right fan, fresh a′b′) ⟹ σ/2≤δ ∧ σ′/2≤δ;
                 ledger σ′−σ = 1+b′−b−q (old b is REPLACED)
               leaf_0001_extend_cert — regression: the leaf-0001
                 skeleton certifies the L=2 prefix [0,1,2,3]
                 (σ=1, δ≥1/2) and its extension (σ′=2, δ≥1);
                 Δσ = 1+3−3−0 = +1
             signed chain, endpoint-fan variant B (kernel-checked):
               signed_chain_certB — right closure at endpoint
                 x_{L+1} via complement S_{L+1}+H′_L = π,
                 triangulation through j = L, per-demand bounds
                 m_j·λ (r = gap/λ − q normalization: a demand is
                 worth q+1 cells); 2π = H_0+H′_L+ΣD_j ⟹
                 δ ≥ (a+b′+Σm−2n)/2
               leaf_0046_certB — regression: L=3, a=4, b′=2,
                 m=(1,1,2), σ=2 ⟹ δ ≥ 1 (5λ ≤ π)
               template synthesis (tools/template_cert.py —
                 verifier-checked candidate construction, not a
                 recognizer): shapes A/B/C cover 448/519 n4_high,
                 341/401 n4_low, 0/101 s6; +fat-arc → 452, 381, 40;
                 residual leaves use mixed-sign supports (e.g.
                 leaf_0177: +△(0,1,3) paired with −△(0,1,2))
               skeleton-driven certB scan (tools/certb_scan.py —
                 hypothesis-availability diagnostic): cap-derived
                 bounds (same bits → ∠=arc → cap ⟹ wrap ≥ λ) and
                 qs baselines lift coverage to s6 101/101,
                 n4_high 387/519, n4_low 285/401 — variant C is
                 geometrically a b′=1 instance of B
               coverage scan (tools/chain_scan.py, offline,
                 skeleton-driven): 3487 valid chains across 1021
                 leaves; 923 one-piece extensions with
                 Δσ ∈ {−3..+2}; the earlier "13 saturated chains"
                 was a support-driven artifact — prefix chains were
                 invisible to it
           → DebtChain/ResidualWitness  ⟵ THE remaining implication:
             produce SOME certificate (fat arc, polygon, signed
             chain, or other) FROM the overfull level — selection
             unproved; chain family is a wired template, not a
             completeness claim
      K3c  witness → δ ≥ 1/2 (low) / δ ≥ 1 (high)  [debt_residual_ge,
           threshold-parametric, DONE in gadget arithmetic;
           ResidualWitness.ge_of exposes τ at witness level]
    compatibility layer (`KraftPacking` bundle, kept as interface):
      K3-C-low   δ<1/2, ∀i cᵢ≥2  ⟹ K ≤ 1
      K3-C-high  ∀i cᵢ≥2         ⟹ K ≤ 5/4  (≤1 FALSE: [2]^5 @ δ=1/2)
      K3-B   low, d_v=1     ⟹ rest ≤ 1/2
      K3-A1  high, d_v=1    ⟹ rest ≤ 3/4
      K3-A2  d_u=d_v=1      ⟹ rest ≤ 1/4
    tight profiles all sit at R = 0:
      [2,2,2,2] [1,2,3,3] [1,2,2,2] [1,1,3,3] [2]^5
    ABCEDF cross-map: d_v = c_v−1, W = 2K; their open
      GadgetSelectionLow/High are the SAME theorem contrapositively —
      no proved S=0 packing to import.

K4  potential_le_sendovCap                  DONE modulo K3
    [potential_le_sendovCap_of_packing: KraftPacking → cap, proved]
```
