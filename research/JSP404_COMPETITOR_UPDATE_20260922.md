# Competitor update — 2026-09-22 snapshot `9d331c9`

Checked remote `jerrylijize1224-star/jsp404-lean-partial` on the owner
lane date of this note.  HEAD moved from the cross-map base
`a6a363f` (2026-09-21) to `9d331c9c3ce776055c2f9eb45016e5ff03aa1c30`
(commit msg: "Prove actual finite-centre triangle restriction and
exponent bounds").  New snapshot zip `jsp404-gap-restriction-20260922.zip`;
new Lean files `FiniteGapRestriction.lean`, `FiniteMaximalCentres.lean`.

## What they added

For `FiniteClusterModel` (actual sorted direction charts, real
Euclidean angles, model hypothesis `AngleBound ((1-1/t)·π)`):

| theorem | content | our analogue |
|---|---|---|
| `gapIndex_le_triangle` | `K_b ≤ triangleVertexCapacity t (∠abc/π)` — restricting to two anchor directions merges cyclic gaps without decreasing capacity | `gapScore_merge` (`Deletion.lean:36`) is the same merge monotonicity, unconnected |
| `triple_capacity_le_triangle` | per-triple `Σ 2^{K_i}` bounded by triangle capacities | — |
| `gapIndex_le_pred` | every local exponent `≤ n−1` (≥3 centres) | deficit `≥ 0` |
| `triple_capacity_low` | `δ < 1/2` ⇒ any triple `Σ 2^{K_i} ≤ 2^n`, i.e. `Σ 2^{-d_i} ≤ 2` | — |
| `triple_capacity_high` | `δ < 1` ⇒ `Σ 2^{K_i} ≤ 2^n + 2^{n-2}`, i.e. `Σ 2^{-d_i} ≤ 5/2` | — |
| `maximal_exponents_low` | `δ < 1/2` ⇒ at most 1 saturated exponent | **≡ `two_saturated_ge_half`** (contrapositive form) |
| `maximal_exponents_high` | `δ < 1` ⇒ at most 2 saturated exponents | ≡ strict checker's "3 saturated ⇒ δ ≥ 1" boundary law |

This closes the explicit triangle-restriction premise their earlier
`jsp404-maximal-centres.md` admitted ("now derived for actual finite
centre models", per their README).  Cadence: 7 commits / 5 days,
daily snapshot releases.

## Comparison vs our Lane A (`SaturatedStructure.lean`, `a340c39`)

- **Same endpoint laws.**  Their `maximal_exponents_low/high` are our
  L3 and the strict 3-saturated boundary law, but proved via
  gap-merge capacity monotonicity on the real model rather than our
  direct L2-min angle argument on `FanSystem`.
- **Their cert is strictly stronger per triple**: weighted
  `Σ 2^{K_i}` bounds control non-saturated exponents too; our L3 is a
  count bound only.  However, for a third vertex beside two saturated
  they get only `K_c ≤ n−2` (`d_c ≥ 1`); our strict checker shows
  `d_c ≥ 2` is forced — one level sharper, unproved by either side.
- **Integration depth is comparable, not clearly ahead**: their model
  carries real angles but still assumes `FiniteClusterModel` +
  `AngleBound`; the ordinary-configuration reduction is open on both
  sides (our `circleDirs`/`gapAfter` wiring of the bridge is the same
  pending step).
- **Same wall acknowledged by both**: the sharp total-capacity bound
  for ≥5 centres (= our S=0 Kraft problem) is unproved; they state
  the exponent-count bound "does not control the total of all smaller
  weights".  `SendovClaim` remains an unproved `Prop`.

## Implications for Lead

1. **No main-theorem race alert.**  They converged to the same
   saturation-count laws we just Lean'd — Lane A stays a cert-lemma
   supplier, not a differentiation.
2. **Actionable target**: per-triple weighted bound
   `Σ_{triple} 2^{-d_i} ≤ 5/2` (δ<1) / `≤ 2` (δ<1/2) is stronger than
   our count L3 and is exactly what `gapScore_merge` +
   triangle-angle data could plausibly supply — candidate cert lemma
   for the high-regime owner, reaching parity with
   `triple_capacity_high` while our strict `d_c ≥ 2` observation would
   exceed it.
3. **Strict finding retains edge**: the `(0,0,1,*)` disappearance
   (`d_c ≥ 2`) is sharper than their `n−2` bound — if provable via
   side-consistency, it is content they do not have.

No competitor code was read into or copied into the Lean sources;
this note is attribution/awareness only.
