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

## 2026-09-23 — M1b witness emission + replay

- Candidate: certB hypothesis bundles replay to real LP certificates.
- Inputs: all bundles reaching σ ≥ 2τ in the three cert dirs.
- Method (`tools/certb_witness.py`): for each hit enumerate each
  boundary slot independently as {fan_e, cap_e} (fan and cap at the
  same end double-count — cap is `span ≤ π−λ` i.e. the complement arc
  ≥ λ, one cell, an ALTERNATIVE realization of the same boundary
  term); synthesize canonical multipliers (boundary +1, tris −1,
  demands +1); submit to `verify_cert`; keep the best topology.
- Findings:
  * First version always added both fans → 0/101 replayed.  Root
    cause: cap is not additive slack on top of a fan — it replaces
    the fan when the terminal-angle legality bound is the source of
    the boundary cell.  Confirmed against saved leaf_0002 cert
    (fan5 +1/2, 4 tris −1/2, 5 angs +1/2 incl. cap ∠015; no fan0).
  * CERT_REPLAYED: s6 101/101, n4_high 387/407 checked (20 rejected —
    bundle claims σ but no topology replays within 8 candidates),
    n4_low 285/285.
  * Topology distribution: n4_high {fan,fan}246 {fan,cap}141;
    n4_low {fan,fan}184 {fan,cap}97 {cap,fan}4; s6 {cap,cap}57
    {cap,fan}44 — the proved n=2 regime never uses two fans,
    consistent with tightness needing both cap bonuses.
  * Variant C is confirmed as a boundary-slot choice of variant B,
    not a separate identity.
  * leaf_0177 still UNCLASSIFIED — mixed-sign two-row support is a
    genuinely different family.
  * 45/45 sampled witnesses re-verify from file independently.
- Status: CERT_REPLAYED (EMPIRICAL) — witnesses produced, not
  selection.

## Open next

- M1b done: 773 witnesses emitted (witnesses/*.jsonl), 45/45 sampled
  re-verify from file.  Union pass pending.
- M2: leaf_0177-family mixed-sign certificate — confirmed NOT covered
  by certB under the corrected decode; second theorem needed (or a
  real geometric mechanism that subsumes it).
- M3: R-HIGH1 — see LIVE_OBLIGATIONS; the live mechanism candidates
  are the adaptive two-cover (ONE_SATURATED_HIGH_GEOMETRY) and the
  certB endpoint-closure family.  Fixed-cover quarter-face is
  FALSIFIED; do not retry.
