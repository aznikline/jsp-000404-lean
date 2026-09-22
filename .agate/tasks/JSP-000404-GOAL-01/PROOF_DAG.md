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
    four open cases (`KraftPacking` bundle):
      K3-C-low   δ<1/2, ∀i cᵢ≥2  ⟹ K ≤ 1
      K3-C-high  ∀i cᵢ≥2         ⟹ K ≤ 5/4  (≤1 FALSE: [2]^5 @ δ=1/2)
      K3-B   low, d_v=1     ⟹ rest ≤ 1/2
      K3-A1  high, d_v=1    ⟹ rest ≤ 3/4
      K3-A2  d_u=d_v=1      ⟹ rest ≤ 1/4
    tight profiles: [2,2,2,2] [1,2,3,3] [1,2,2,2] [1,1,3,3]
    ABCEDF cross-map: d_v = c_v−1, W = 2K; their open
      GadgetSelectionLow/High are the SAME theorem contrapositively —
      no proved S=0 packing to import.

K4  potential_le_sendovCap                  DONE modulo K3
    [potential_le_sendovCap_of_packing: KraftPacking → cap, proved]
```
