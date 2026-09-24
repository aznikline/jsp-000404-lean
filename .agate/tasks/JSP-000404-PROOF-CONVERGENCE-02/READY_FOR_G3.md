# READY_FOR_G3 — Owner batch @ b2a7c32

OWNER_REVIEW_SHA   = b2a7c3220bd1a0eb4e892d040da9dd33d61307d9
TESTED_CODE_SHA    = b2a7c3220bd1a0eb4e892d040da9dd33d61307d9
READY_DELIVERY_SHA = (this commit; see git rev-parse HEAD after push)

## Build evidence

- `lake build Jsp000404` → PASS, 8997 jobs (on b2a7c32 worktree).
- Axiom audit: `M3_AXIOM_CHECK.txt` (this tree).  Every new declaration
  prints `[propext, Classical.choice, Quot.sound]`.
- Root `MainTheorem` still carries the pre-existing `sorryAx`
  (unchanged, reported separately).

## Batch contents (all under `Jsp404.`)

Geometric subdomain capacity closures (R-HIGH1, 1/2 ≤ δ < 1, S = 1):
- `one_saturated_capacity_of_narrow_window`,
  `potential_le_two_pow_of_saturated_narrow` — anchor-ray spread < α
  closes via the LOW m = n−1 corridor chain.
- `potential_le_high_of_saturated_small` — s ≤ 4 (total centers).
- `potential_le_high_of_saturated_clump` — a non-anchor row whose chord
  directions all lie in the bottom prefix `[λ, λ+w₀)` with
  `w₀·n < π−λ` (i.e. `w₀ < B = (π−λ)/n < λ`).
  Scope: bottom-prefix only; middle-seated narrow rows NOT covered.
- `potential_le_high_of_saturated_delete_narrow` — single-outlier
  deletion: deleting one non-anchor `q` with surviving rays in a
  window `< α` gives `F(c) ≤ 2^{n−2} + F(c∖{q}) ≤ 2^{n−2} + 2^n`;
  anchor stays saturated (score non-decreasing under erase,
  defect-1 caps it at n−1).  No removability or post-deletion
  uniqueness assumed.
- `potential_le_high_of_saturated_one_outlier` — at most one
  non-anchor ray `≥ α` closes; residual forces `θ_{s−2} ≥ α`.
- `potential_le_high_of_saturated_slack_family` — certificate-family
  interface: T non-anchor rows with bin-occupancy ≤ r and defect
  ≥ r+1 each give slack `2^{n−r−1}`; |T| ≥ `2^{r−1}` closes the
  quarter.  Premises explicit: `theta`/`width` corridor cover
  (`hcover`, `hcoverlt`), `hocc`, `hdef`, `hcard`.
  CONDITIONAL-USEFUL: upstream "such T exists" obligation open.

Structural lemmas (ConeCorridor/AnchoredRows):
- `chord_in_endpoint_window`,
  `saturated_chord_{endpoint,minmax}_window`,
  `saturated_chord_{top,bot}_sliver` — endpoint-refined chord windows,
  sliver exclusivity at chord level.
- `saturated_row_{bot,top}_sliver_{forces_*,card_le_one}` — per-row
  bridge: non-extreme rows have ≤ 1 sliver direction, incident to the
  extreme ray.  Extreme row deliberately excluded.
- `anchored_rowScore_eq_linear`/`directionRow_anchor_cons` generalized
  `θ ≤ λ/2` → `θ ≤ λ`.

## Explicitly NOT claimed

- R-HIGH1 general closure; existence of the slack-family `T`;
  general `SelectionP`; `sendov_lower` N ≥ 9.
- Chord-level sliver facts do NOT imply bin-level exclusivity
  (threshold-straddling bins, extreme-row multi-chords, top/bottom
  double charging all remain open — recorded in LIVE_OBLIGATIONS).

## Known negative results (recorded, not blocking)

- Phase-shifting a uniform `n`-bin cover cannot capture
  middle-seated clumps (phase window `< α < width`).
- Two-point deletion cannot close the two-high-ray case
  (cost `2^{n−1}` + `F(c') ≤ 2^n` exceeds `5·2^{n−2}`).
