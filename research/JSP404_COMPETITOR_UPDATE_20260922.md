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

## Integration follow-up (current goal branch, 2026-09-22)

The original archive at the stated commit was independently downloaded
and its SHA-256 verified:
`ef51d31c5bab1a0292b2de62dff8499339e2032b7071fdf712c651a5d3cdfc3d`.
The two new Lean files and their report were read. The archive was not
independently rebuilt in this follow-up; its sources were not copied into
our proof library.

The per-triple bounds are useful local constraints, but do not supply a
global capacity theorem. For example, six exponents all equal to zero
meet every three-term high bound for n = 2, yet their total weight is 6,
larger than the target cap 5. This is an arithmetic illustration of the
remaining inference, not a legal geometric counterexample.

Two comparisons in the original note need qualification:

- Our current integration already has an ordinary-configuration lower
  pipeline conditional on capacity and an unconditional all-N upper
  construction. The direct geometric certificate route is connected to
  the full root, including n = 1. The abstract skeleton adapter is still
  open, but is not needed if the geometric route closes.
- The proposed stronger deficit bound needs at least four centers and
  its further geometric/consistency conditions stated explicitly. It
  fails for a strict three-center model: at n = 4, delta = 3/4, triangle
  angles in lambda units (3/4, 3/4, 13/4) give exponents (3,3,2), hence
  deficits (0,0,1). Its complementary gaps are (4,4,3/2), with all floor
  remainders strictly below one. This is compatible with the per-triple
  high cap; a bare "two saturated implies all others have deficit >= 2"
  statement must not be used.

The value of this update is its explicit triangle-restriction mechanism
and scope comparison. It is not the missing arbitrary-size proof. See
`notes/STATUS.md` for the current, subsequently updated integration state.
