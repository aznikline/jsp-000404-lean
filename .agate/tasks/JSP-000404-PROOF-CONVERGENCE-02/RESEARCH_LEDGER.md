# Research ledger — JSP-000404-PROOF-CONVERGENCE-02

Each entry freezes: candidate / inputs / consumer / falsifier /
success criterion.  Outcomes marked TESTED/FALSIFIED/OPEN.

## 2026-09-23 — M0 integration port

- Candidate: port `K3bGeometry.lean` from cert-source 9ae8230 onto
  integration 9945ee8 with minimal edits.
- Dependency closure: cert-side `Induction`/`Statement`/
  `GeometricDeletion` NOT overwritten.  Integration already proves
  `not_three_saturated` (SaturationPacking) and `debt_residual_ge`
  with matching signature — only `ResidualWitness.ge_of`
  (ChainWitness +13) and `one_le_rowDefect` (Deletion +29) needed.
- Outcome: full build 8996 jobs PASS; axiom audit of all 11 ported
  declarations: `[propext, Classical.choice, Quot.sound]` only.
- `sendov_lower` N≥9 sorry is the only root gap; consumer is
  `CertExists` (n≥3) via `GeometricCertificates`/`GadgetSelection`.
  Historical sorries (`staircase_of_legality.tail`,
  `exists_removable_vertex{,_hull}`, `maxGap_boundary_emission`) are
  NOT in the live path — forbidden/new-dependency list stands.

## 2026-09-23 — M1a certB decode calibration

- Candidate: bits-only branch decode in certb_scan misreads arcs when
  positions matter (Lead's §4A).
- Inputs: three cert dirs (519+401+101 leaves); leaf_0002 row-0 cut
  rotation regression.
- Falsifier: gauge transform must leave every accepted bundle's
  verdict unchanged.
- Findings:
  * side-decode is gauge-invariant (verified: bits_eq(1,2) flips
    under cut rotation, side(1,2) stays +1; σ 2→2).  bits-only
    decode drops σ 2→1 on the rotated representative — reproduces
    Lead's mini-recomputation and explains it: the moved ray's bit
    flips so a bare equality inverts while the physical oangle sign
    is preserved by the pos+flip compensation.
  * Corrected coverage: n4_high 387→407, n4_low 285 (unchanged),
    s6 101 (unchanged).  Position decode both adds hits (side=−1 can
    hold with equal bits when positions cross the cut) and removes
    false ones.
  * m_j = max(q,1) confirmed (no q+1 anywhere); σ integral.
- Status: HYPOTHESES_CHECKED level only.

## Open next

- M1b: emit per-hit witness JSON (chain, pieces, sides, m/a/b sources,
  constraint IDs) + independent replay on a bounded sample; one
  corrected union pass (A ∪ B ∪ fat ∪ proved families).
- M2: leaf_0177-family mixed-sign certificate — check whether it
  survives under the corrected decode or needs a second theorem.
- M3: R-HIGH1 — see LIVE_OBLIGATIONS; the live mechanism candidates
  are the adaptive two-cover (ONE_SATURATED_HIGH_GEOMETRY) and the
  certB endpoint-closure family.  Fixed-cover quarter-face is
  FALSIFIED; do not retry.
