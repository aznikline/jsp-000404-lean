# Model contract — skeleton semantics used by certB scan

Source of truth: `tools/generic_model.py` (integration version,
margin-capable), `Jsp000404/K3bGeometry.lean` (kernel-checked theorems).

## Skeleton rows

Each leaf stores `skeleton`: per-vertex rows `{v, order, bits, qs}`.

- `order` : cyclic order of the other vertices' projective direction
  representatives (dirRep ∈ [0,π)) around the cut; a permutation.
- `bits`  : 2π-lift bit per ray — actual direction θ = ρ + π·bit.
- `qs`    : integer cell counts ⌊gap/λ⌋ of the m cyclic gaps
  (gap i between order[i] and order[i+1]); the r-variables model the
  remainder: gap = q·λ + r·λ, 0 ≤ r < 1.

## Direction decode (mandate §4A)

    side(u,v) at row r = (+1 if pos(v)>pos(u) else −1)
                         flipped iff bits(u) ≠ bits(v)

+1 ⇒ ∠(u,r,v) = dirArc(r,u,v)  (forward arc u→v on the π-circle);
−1 ⇒ ∠(u,r,v) = π − dirArc(r,u,v).

Matches `generic_model.vertex_variants` and Lean's
`dirRep_arc_eq_pi_sub_angle` (oangle<0 ⇒ complement).

Gauge invariance: rotating a row's cut (rotate order/qs by one, flip
the moved ray's bit) preserves every side(); bare bit equality does
not survive (leaf_0002 regression).  Rotating order without updating
bits is NOT a legal transform.

## Budgets (mandate §4C)

D ≥ q·λ (qs baseline) and D ≥ λ (complement-branch demand cap) combine
by **max**: m = max(q,1).  Never add.  Same for boundary caps.

## Scores (mandate §4D)

σ = a + b + Σ m_j − 2n computed over ℤ (Python int / Lean ℝ cast).
Low target σ ≥ 1; high σ ≥ 2.  δ binds to the original system via
`δ = π/λ − n`, `⌊π/λ⌋ = n`.

## certB hypothesis bundle (signed_chain_certB)

chain x_0…x_{L+1}, L ≥ 2, injective on range(L+2);
hfanL (row x_0 fan tiles + wrap = π); hcomp (row x_{L+1} two arcs = π);
hsplit per piece; hbA/hbT/hbS side bits; hmD demand bounds m_j·λ;
hH0, hHL boundary bounds.  Conclusion: (a+b+Σm−2n)/2 ≤ δ.

Variant C (terminal angle cap ∠ ≤ π−λ) is geometrically the b′=1
instance of certB: the cap bounds S_{L+1}, and H′_L = π − S_{L+1} ≥ λ.

## What the scan numbers mean

certB-covered = the leaf's skeleton ADMITS a certB hypothesis bundle
with σ ≥ 2τ.  It does not produce multipliers or claim the leaf's own
saved certificate uses this shape; columns RAW_HIT /
HYPOTHESES_CHECKED / CERT_REPLAYED / GEOMETRY_BRIDGED are tracked
separately in CERTB_COVERAGE.json / RESEARCH_LEDGER.md.
