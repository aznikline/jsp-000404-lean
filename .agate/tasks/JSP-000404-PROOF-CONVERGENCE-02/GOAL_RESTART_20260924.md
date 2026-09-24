# GOAL_RESTART_20260924 — M3/M4 远端对齐与完整证明推进

Source: Lead directive pasted into active session 2026-09-24.
Continuation of JSP-000404 proof-convergence Goal; not a restart of M0/M1.

Snapshot at Goal receipt:
- OWNER_BRANCH=agent/jsp404-proof-convergence-02-owner
- OWNER_SNAPSHOT=b2a7c3220bd1a0eb4e892d040da9dd33d61307d9
- INTEGRATION_SNAPSHOT=204f26ad2bc9aa445a98d8615c43476237aacccd
- G3_SNAPSHOT=83d3dcf4b7e96255f78487584ed80baf748aa3be

Execution order per Goal:
1. fetch/readback + consume LEAD_SYNC_20260924.md, G3_SCOPE_REVIEW_b2a7c32.md
2. READY_FOR_G3.md pinning OWNER_REVIEW_SHA=b2a7c32 (batch scope:
   geometric subdomain closures + structural lemmas + slack_family
   under explicit bin-occupancy/defect premises; NOT claiming
   R-HIGH1, universal T existence, or SelectionP)
3. merge lane/integration@204f26a into owner branch, build merged tree
4. math: A double-end residual deletion, B full-corridor end-bin
   obstruction, C quantitative boundary-bin lemma

Notation discipline: s = total centers, m = s-1 non-anchor;
source Fin(s+1) args converted explicitly. c_i = rowDefect = n-k_i,
d_i = c_i - 1, K = F/2^n, W = 2K.

In-flight at Goal receipt (this commit batch, NOT part of b2a7c32):
- defect_two_rows_le_three, four_defect_two_tiling (volume obstruction
  pair; compiled, axioms clean) — belongs to next review batch.
