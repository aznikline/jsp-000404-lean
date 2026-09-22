# Proof DAG — arbitrary-N Sendov count bound

```
Section4Legality (geometry: center system, λ-gap legality)
        │
        ▼  P1  [AngleSystem.lean]
AngleSystem s λ
  fan : cyclic order of directions at each vertex
  gap : consecutive real gaps ≥ 0, Σ = π
  ang : per-triple angle = designated contiguous arc
  legality: ∀ triple angles ≤ π − λ (+ facing, block constraints)
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
