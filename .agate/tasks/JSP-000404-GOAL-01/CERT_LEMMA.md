# Cert Lemma — the sole mathematical crux

## Statement (target)

```
feasible(A) ∧ F(A) > cap  ⟹  ∃t : Σ_{i≠t} 2^{k_i}(2^{g_{it}}−1) ≥ 2^{k_t}
```

with `g_{it} = auto_{it} + carry_{it}` (auto = both flank cells ≥1;
carry requires remainder `r_a+r_b ≥ 1`, LP-feasible in the system).

## Verified (empirical, exact-rational, NOT theorems)

- s=4 n=3 δ=1/4: 572/572 LP-feasible F≥7 have joint cert+merge-feasible.
- s=4 n=4 δ=1/4: 512/512 F≥15.  δ=3/4: 296+4/300 (cert at higher k).
- s=4 n=4 δ=3/4 full: 302/302 hard-feasible.
- s=5 n=4: all 14 F=17 debt-survivors LP-infeasible; δ=3/4 maxF(+debt)=20=cap.
- Abstract maxF = uniform cap in every tested regime.

## Falsified (counterexamples on file)

- `Σ 2^{k_i}E_i ≥ F`: best wE = F−2 (56/572 top-F).
- `Σ 2^{k_i}E_i ≥ F−s+1`: deficit 8 > slack 3 at δ=3/4
  (assignment `[(0,0,4),(0,1,3),(0,3,1),(3,0,1)]`, ks=[3,2,2,2]).
- min-k cert: 4/300 δ=3/4 only at k=2.
- extremal (min∪max)-k cert: 12/400 δ=3/4 cert only at middle k=2.
- zero-emitter charge map; max-gap vertex CertA∨CertC; boundary
  emitter; ρ/σ terminal cycle; every min-k receives gain (29% fail on
  random); universal per-vertex emission; min-k deletion rule.

## Structural facts (proved on the model, empirical for assignments)

- zero-emitter ⟺ saturated (C_z = n, budget B_z = δ < 1 ⇒ no carry
  possible) AND active cells pairwise non-adjacent (no auto pair).
- Emission edges strictly ascend in k when no cert exists (else the
  single edge gives cert).
- Cert locations observed at min-k, max-k, and middle k — genuinely
  incidence-structural.
- The merge at angle level preserves ALL constraints trivially
  (merged gap = previously-existing triangle arc). The earlier
  non-closure was an artifact of the cell-only abstraction.

## Layer-cake form

`cert(t) ⟺ Σ_{j≥1} 2^{j−1}·A_j(t) ≥ 2^{k_t}` where `A_j(t)` counts
emitters whose gain reaches across level j.  The top level j = k_t
alone needs `2^{k_t−1}` of coverage — half the demand at one level.

## Connection to Lead's gadget lane

`gadgetSelection` (W-form, `W = Σ 2^{(n−1)−k_i}`) is the dual-weight
version of the same crux.  If their Hall/Kraft gadget machinery
closes first, it should transfer to this statement — and vice versa.
