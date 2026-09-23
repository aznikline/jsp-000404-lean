# Live obligations — actual source-verified

All statements below are read back from `lane/integration` source at
9945ee8, not from stale owner docs.

## Root gap

`MainTheorem.sendov_lower` — N≥9 branch is `sorry` (line 20).  Everything
else at the root is proved.

## The one consumer

`CertificateIntegration.GeometricCertificates`:

    ∀ o e (he : e ≠ 0) (n : ℕ) (3 ≤ n) (lam : ℝ) (0 < lam) (lam < π)
      (⌊π/λ⌋₊ = n) (big : Bool) (big = false → π/λ − n < 1/2) :
      CertExists o e n big lam

`Induction.CertExists`: for every legal `t ≥ 4` configuration with
`sendovCap n big < potential`, the `EmissionDichotomy` holds.

Equivalent workload (via `removable_of_dichotomy`, proved): an
over-capacity legal configuration has a removable vertex.

## Regime split (defect coordinate c_i = rowDefect = n−1−k_i… verify
against `Deletion.rowDefect`; K = Σ 2^{−c_i}, S = #{c_i = 1})

| tag | regime | S | target |
|---|---|---|---|
| R-LOW0  | n≥3, δ<1/2  | 0 | K ≤ 1   |
| R-HIGH1 | n≥3, ½≤δ<1  | 1 | K ≤ 5/4 |  ← MAIN
| R-HIGH0 | n≥3, ½≤δ<1  | 0 | K ≤ 5/4 |

R-HIGH1 subdomain split (2026-10-14, `OneSaturatedHigh.lean`, axioms
clean, arbitrary n/s):

- **Narrow anchor window — CLOSED.**  If the rays from the saturated
  center `v` to all other centers pairwise fit in an angle
  `β < α = (n+1)λ − π = (1−δ)λ`, then
  `potential ≤ 2^n < sendovCap n true`
  (`one_saturated_capacity_of_narrow_window`,
  `potential_le_two_pow_of_saturated_narrow`).  The `δ ≥ 1/2`
  hypothesis is used exactly once: `α ≤ λ/2`, which makes the anchor
  offsets satisfy `anchored_rowScore_eq_linear`'s `theta ≤ λ/2`
  premise and makes the corridor width `< (n−1)λ` fit `n−1` bins.
  Saturation is NOT used in the bound itself — the subdomain is
  defined purely by the ray spread.
- **Residual — OPEN.**  Anchor-ray spread in `[α, δλ)` (the window
  guaranteed by `saturated_ray_window` is `δλ < λ`, so this range is
  nonempty iff `δ > 1/2`).  The 4-point example in
  `notes/ONE_SATURATED_HIGH_GEOMETRY.md` lives here (spread ≈ 29°,
  α ≈ 4.3°).  Needs a different argument: the corridor is too wide
  for `n−1` bins, but the capacity still only needs
  `rest ≤ 3·2^{n−2}` vs the `2^{n−1}` the corridor gives.

Remaining after that: R-LOW0, R-HIGH0, then assemble
`GeometricCertificates` → `CertExists` → root.

Closed already (do NOT redo): n=1 both regimes; n=2 both regimes;
LOW with ≥1 saturated; HIGH with ≥2 saturated; LOW with S=0? —
NO, `PentagonPacking.strict_no_saturation_counterexample` shows a
strict no-saturation model with K=5/4 exists (the shortcut
"S=0 ⇒ K≤1 in low" is FALSE); low no-saturation needs real work
(R-LOW0).

## Forbidden dependencies

- `maxGap_boundary_emission` — FALSIFIED (s=2, s=3, s=4 square
  countermodels in `MaxGapCountermodel{,2}`).  Do not depend on it or
  on any unrepaired restatement.
- `exists_removable_vertex` / `exists_removable_hull_vertex`
  (Deletion.lean:1290,1298) — historical sorries, isolated; do NOT
  add new consumers.
- `staircase_of_legality` tail (Section4Legality.lean:165) — historical
  sorry; the live path uses `staircaseBound_of_selection` instead.
- `sorry`/`admit`/custom axioms/`native_decide` trust — none new.

## Suggested attack shape (from research notes, all unproved)

- Quarter-face on fixed uniform cover: FALSIFIED (13-pt integer
  counterexample, `ONE_SATURATED_HIGH_RESEARCH.md`).
- Two-group G/H split with narrow G + two-anchor H: sufficient but
  existence FALSIFIED (4-pt exact example, `ONE_SATURATED_HIGH_GEOMETRY.md`).
- Adaptive angular two-cover with per-vertex active-bin bounds:
  sufficient + certified on the 13-pt obstruction; existence OPEN.
  This is the most promising live mechanism.
- certB/signed-chain family: every admissible hypothesis bundle
  replays to a real certificate via per-end {fan,cap} boundary
  topology (773 witnesses; s6 101/101, n4_high 387/407 checked,
  n4_low 285/285).  Residual leaves: n4_high 20 rejected + 112
  unclassified, n4_low 116 unclassified — leaf_0177-type mixed-sign
  supports confirmed NOT certB.  Witnesses ≠ selection.
