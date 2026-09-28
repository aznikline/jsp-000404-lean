# AIR_FAILOVER_BASELINE — JSP-000404

TAKEOVER_TIME          = 2026-09-28 ~00:15 CST
FAILOVER_TRIGGER       = condition 2 (owner remote silent ~10h, stopped at a clean
                         ledger/status checkpoint) + condition 5 (user handed over
                         the AIR-emergency-owner mandate)
OWNER_LAST_REMOTE_SHA  = 4542b78e50a6f76df3d5bdeb6cb9bdd1ffd3edfc
INTEGRATION_SHA        = 4b45f6a2e9a714983765ce16a3cfded9c4599581
TAKEOVER_BASE_SHA      = 4b45f6a2e9a714983765ce16a3cfded9c4599581
ANCESTOR_CHECK         = owner ⊆ integration (merge-base = 4542b78) → Case A
UNRECOVERED_LOCAL_WORK = UNKNOWN (jsp-wt-merge holds an uncommitted
                         PentagonGadgetBridge.lean + research note by an
                         unknown holder; a same-name COMMITTED file now
                         exists on integration — the local copy will conflict
                         on pull; registered as unrecoverable/unowned WIP)
AIR_OWNER_BRANCH       = agent/jsp404-air-emergency-owner-20260928

## Root state at takeover base

ROOT_BUILD             = PASS, `lake build`, 9007 jobs, 0 errors (warnings only)
TESTED_CODE_SHA        = 4b45f6a2e9a714983765ce16a3cfded9c4599581

KNOWN_ROOT_SORRY (full inventory, `declaration uses sorry` warnings):
- MainTheorem.lean:11        `sendov_lower` — the actual open goal (N≥9 lower)
- Section4Legality.lean:139  historical legality tail (deprecated path)
- Deletion.lean:1290,1298    `exists_removable_vertex`,
                             `exists_removable_hull_vertex` — deprecated,
                             FORBIDDEN as new dependencies
- GeometricDeletion.lean:627 `maxGap_boundary_emission` — PROVED FALSE,
                             countermodels archived, FORBIDDEN
- PentagonGadgetBridge.lean:36 `opponent_pentagon_high_bound` — NEW on
                             integration via the 4b45f6a merge; honest open
                             obligation; containment verified: only the root
                             import references it, NO downstream consumer,
                             not in MainTheorem's dependency cone.

KNOWN_FORBIDDEN_DEPENDENCIES = Deletion.{exists_removable_vertex,
  exists_removable_hull_vertex}, GeometricDeletion.maxGap_boundary_emission,
  staircase tail, countermodel files as proof inputs.

## Last proved frontier (from owner ledger/STATUS)

LAST_PROVED_CASE       = mixed two-in at a high row fully excluded in five
                         points: `mixed_two_in_excluded` = central
                         (a611ba8) + outer-low + outer-high (cbeef48).
                         Also: deletion rigidity of defect-2 rows
                         (DeletionRigidity), full-in mixed-star exclusion
                         (MixedStarExclusion), Type I/II witness chains,
                         `shortWitness_no_cycle`, projection descent,
                         `four_defect_two_tiling`,
                         `potential_le_high_of_saturated_four_eq` (R≤2 cap),
                         `exists_two_short_end_rows_of_four`.

LIVE_BLOCKER (owner's own OPEN list, five-point R-HIGH1):
  same-side two-in (F/F and L/L), 0/1-in receivers, low-defect endpoints,
  R=4, general m. Then R-LOW0 / R-HIGH0 → CertExists → sendov_lower.

## Audit snapshot

Recent key theorems (in-build `#print axioms` output): all
`[propext, Classical.choice, Quot.sound]` — including
star_chord_window, star_receiver_high_is_mixed, shortWitness_no_cycle,
psi_min_row_ends_big, mixed-star machinery, deletion rigidity,
one_saturated/potential_le_high_* family, GeomSkeleton bridge (12),
StrictRemainderNormalization (13).

TREE_CLEAN             = yes (fresh worktree at TAKEOVER_BASE)

## Next action

Phase 1 per takeover doc: same-side two-in branch synthesis
(tools/same_side_two_in_branch.py) → Lean leaves →
`same_side_two_in_{F,L}_impossible` →
`five_point_R3_high_receiver_short_indegree_le_one`.
Review debt (non-blocking): G3 READY batch b2a7c32 formal scope verdict;
AIR_CHALLENGE_MIXED_STAR five-point review.
