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
- **Small configurations — CLOSED.**  If `s ≤ 4` total centers then
  `potential ≤ 2^n + 2^{n-2} = sendovCap n true`
  (`potential_le_high_of_saturated_small`): the anchor contributes
  `2^{n−1}` and each of the ≤ 3 remaining rows has defect ≥ 2, hence
  exponent ≤ n−2 — pure counting, no geometry beyond `rowCells ≤ n`.
- **Bottom-clump — CLOSED.**  If a non-anchor row's chord directions
  all lie in `[λ, λ+w₀)` with `w₀·n < π−λ`, then
  `potential ≤ 2^n + 2^{n-2}`
  (`potential_le_high_of_saturated_clump`): an adaptive width-`>w₀`
  cover puts all of that row's chords in one bin, so its cube is
  `2^{n−1}` vs actual weight `≤2^{n−2}` — exactly the needed
  quarter-cube slack.  Covers the `(O,P,Q,R)` equality family with
  `w₀ = λ/3` (row Q's directions `9λ/8, 5λ/4 ∈ [λ, 4λ/3)`); that family
  is independently closed by the `s ≤ 4` theorem.  SCOPE LIMIT (Lead):
  the premise anchors the interval at `λ` — middle-seated narrow rows
  are NOT covered.
  Required generalizing `anchored_rowScore_eq_linear` /
  `directionRow_anchor_cons` from `θ ≤ λ/2` to `θ ≤ λ` (done, axioms
  clean).
- **Endpoint windows / sliver exclusivity — FORMALIZED.**
  `chord_in_endpoint_window`, `saturated_chord_endpoint_window`,
  `saturated_chord_minmax_window`, `saturated_chord_{top,bot}_sliver`
  (ConeCorridor.lean, axioms clean): per-chord disjunction
  `dir ∈ [θᵢ+λ, π−λ+θⱼ] ∨ [θⱼ+λ, π−λ+θᵢ]`; chord above `π−λ+t`
  (below `λ+t`) needs an endpoint ray above `t` (below `t`).
  NOTE: these bound chord DIRECTIONS, not bin occupancy — a bin
  straddling the sliver threshold is not yet bridged.
- **Per-row sliver occupancy — FIRST BRIDGE FORMALIZED.**
  `saturated_row_{bot,top}_sliver_forces_{low,high}` and
  `saturated_row_{bot,top}_sliver_card_le_one` (ConeCorridor.lean,
  axioms clean): in a row `w` with `θ_w ≥ t` (resp. `θ_w ≤ u`), every
  direction below `λ+t` (above `π−λ+u`) is incident to a low (high)
  endpoint; if that endpoint is unique, the row contributes ≤ 1 sliver
  direction.  The extreme row itself is deliberately NOT covered — it
  may hold many sliver chords and needs separate charging.  Remaining
  gap for bin-level charging: bins straddling the sliver boundary and
  duplicate charging between top/bottom slivers.
- **Single-outlier deletion — CLOSED.**  If deleting one non-anchor
  `q` leaves the surviving anchor rays pairwise within `β < α`, then
  `potential ≤ 2^{n−2} + 2^n` (`potential_le_high_of_saturated_delete_narrow`):
  the deleted row's weight `≤ 2^{n−2}` is paid explicitly and the
  reduced configuration is bounded by the narrow-window theorem.
  The anchor stays saturated under deletion (`rowScore_eraseIdx'` +
  `one_le_rowDefect`); no removability of `q`, no uniqueness of
  saturation after deletion.  Corollary `potential_le_high_of_saturated_one_outlier`:
  if all anchor rays except one lie strictly below `α`, cap holds.
- **Slack-certificate family — CLOSED (interface).**
  `potential_le_high_of_saturated_slack_family`: a family `T` of
  non-anchor rows occupying ≤ r bins each with defect ≥ r+1 gives
  `|T|·2^{n−r−1}` total slack; `|T| ≥ 2^{r−1}` closes the quarter.
  Subsumes clump (r=1) and the two-small-row certificate (r=2).
  Consumers must supply geometric/bin occupancy bounds — the sliver
  exclusivity lemmas are the intended source.
  Phase-shift analysis (negative result): a uniform cover's feasible
  phase window is `< α < width`, so middle-seated clumps cannot be
  captured by re-phasing — the clump theorem's bottom-prefix
  restriction is intrinsic to uniform covers.
- **Residual — OPEN.**  `s ≥ 5`, anchor-ray spread in `[α, δλ]`
  (non-strict — no strictness lemma; the window guaranteed by
  `saturated_ray_window` is `δλ < λ`, so this range is nonempty iff
  `δ > 1/2`), `Σ_{w≠v} 2^{2−c_w} > 3`, AT LEAST TWO anchor rays reach
  `α` (`θ_{s−2} ≥ α`, else `one_outlier` closes it), AND no non-anchor
  row has all chords in the bottom prefix `[λ, λ+w₀)`, `w₀·n < π−λ`.
  Middle-seated narrow rows remain in the residual.
  The corridor `[λ, π−λ+σ]` now needs `n` bins; the target is a
  quarter-cube saving `H + Σ_v S_v ≥ 2^{n−2}` where `H` are cover
  holes and `S_v = 2^{n−a_v} − 2^{k_v}` the per-row slack (Lead: the
  identity `H + ΣSᵢ = 2^n − ΣWᵢ` is exact for a fixed cover —
  repartitioning cannot increase the total, only redistribute).
  Bounded-corpus defect profiles are all boundary-type `(1,2,2,2,3)`
  — the profile conjecture "≤3 defect-2 rows" cannot be validated or
  refuted from the corpus (all leaves are s = 5).

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
