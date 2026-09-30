# GOAL — JSP404: five-point capacity wiring, arbitrary-size lift, high-defect tail

Stored 2026-09-30 (UTC). Owner branch: `agent/jsp404-air-emergency-owner-20260928`.
Base snapshot for this goal: `cdd315b25e49f069a2b5323fb58689ad987d6331`.

## Scope (per Lead)

1. Original five-point capacity consumer: Section4Legality -> SatChart via
   `saturated_ray_window`, T = {defect-2 non-anchor rows}, transport across
   reference changes, consume the R>=3 closure and weight counting.
2. Merge HIGH capacity for total size <= 5; shrink the CertExists obligation
   to t >= 6 by an assembly lemma (no change to `CertExists`).
3. Arbitrary-size lift: at most two defect-2 non-anchor rows under a
   saturated anchor, via `Section4Legality.erase` + `deletion_rigidity`.
4. Two-low-row position classification via the three pairkills at arbitrary
   size (theta-region exclusivity: below-a / between / above-b).
5. High-defect tail: `sum_T 2^(n-c_i) <= (3-r) Q`, r = #defect-2 rows.
6. M3 (R-HIGH1) then LOW0/HIGH0/M4/final root.

Not in scope: redoing the old witness-DAG routes (0/1-in, low-defect
terminals, R4 graphs), strictify as a "lossless" transform, geometric
realizability of the model, remote duplication, force-push.

## Deliverable fields (tracked in STATUS / RESEARCH_LEDGER)

REMOTE_BRANCH / REMOTE_EXACT_HEAD / LOCAL_HEAD / TESTED_CODE_SHA /
INTEGRATION_BASE_SHA / EVIDENCE_PATHS /
FIVE_POINT_SATCHART_PROFILE / FIVE_POINT_ORIGINAL_CAPACITY /
HIGH_CAPACITY_SIZE_LE_FIVE / HIGH_CERT_REDUCTION_TO_T_GE_SIX /
GENERAL_DEFECT_TWO_CARD_LE_TWO / GENERAL_TWO_LOW_POSITION /
TAIL_R2 / TAIL_R1 / TAIL_R0 /
M3 / LOW0 / HIGH0 / M4 / FINAL_ROOT /
MODULE_BUILD / FULL_ROOT_BUILD / NEW_AXIOMS / ASSUMPTION_AUDIT /
INDEPENDENT_REVIEW / PUSH_STATUS / TREE_CLEAN /
LIVE_BLOCKER / NEXT_ACTION

## Audit rules

- print/#print axioms outputs persisted per checkpoint; exit codes recorded.
- Standard axioms only: propext, Classical.choice, Quot.sound.
- Existing sorries (MainTheorem.sendov_lower, exists_removable_vertex,
  maxGap_boundary_emission, cross-row emission lemma) remain documented.
- Independent review stays PENDING until a real reviewer inspects a
  fixed SHA; owner self-review does not count.
