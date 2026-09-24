# G3 scope review — owner batch @ b2a7c32 (pre-verification, awaiting READY_FOR_G3)

MERGE_CANDIDATE_SHA = 321c85958ad2d0c2fc3016ab9e43760e9b51618e
OWNER_REVIEW_SHA    = b2a7c3220bd1a0eb4e892d040da9dd33d61307d9
INTEGRATION_REVIEW_BASE_SHA = 0889f5d4ac3ea830bf751b0fedd65f3866a70736

Combination build: 8969 jobs, green (verified on this worktree).
Bridge regression: all 12 bridge `#print axioms` re-verified on the
combination tree — standard axioms only.

## Checklist against the review criteria

| Criterion | Result |
|---|---|
| New sorries / admit / native_decide / custom axioms in added files (`OneSaturatedHigh`, `K3bGeometry`) | NONE |
| Forbidden deps (`maxGap_boundary_emission`, `exists_removable_*`, `staircase_of_legality`) in new/modified files | NONE |
| `Deletion.lean` diff | additive only: `one_le_rowDefect` (proved); deprecated sorries untouched |
| Geometric-subdomain results mis-stated as full `GadgetSelectionP` | NONE — all new theorems are `potential_le_*` / `chord_*` / `sliver_*` / `arc_*` / `signed_chain_cert*` under explicit geometric or certificate premises |
| Chord-level vs row-level vs bin-level inflation | NOT FOUND in statements; `LIVE_OBLIGATIONS.md` itself records the residual gaps honestly (chord directions ≠ bin occupancy; extreme row excluded from `sliver_card_le_one`; bins straddling the sliver boundary not yet bridged) |
| `slack_family` premises | EXPLICIT — corridor cover (`theta`/`width`/`hcover`/`hcoverlt`), occupancy `≤ r`, defect `≥ r+1`, `|T| ≥ 2^{r−1}` all retained as hypotheses; upstream "T exists" obligation open ⇒ CONDITIONAL-USEFUL |
| Axiom audits (combination tree) | `one_saturated_capacity_of_narrow_window`, `potential_le_two_pow_of_saturated_narrow`, `potential_le_high_of_saturated_{small,clump,slack_family,delete_narrow,one_outlier}`, plus bridge 12 — all `[propext, Classical.choice, Quot.sound]` |
| New-theorem axiom audit vs root audit | reported separately; `MainTheorem` root still carries pre-existing `sorryAx` (unchanged by this batch) |

## Preliminary verdict

Batch is honest and well-scoped: real geometric/bin-level premises,
no level inflation found in statements, no forbidden dependencies,
deprecated placeholders untouched.

**Pending the owner's READY_FOR_G3.md** — the formal verdict requires
diffing the owner's own claim list against these checks.  Expected
verdict shape: subdomain closures PROVED-in-scope;
`slack_family` CONDITIONAL-USEFUL (sufficient condition, upstream
family-existence open); nothing signed as general selection.
