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

## 2026-09-23 — M2 detour family (mixed-sign supports)

- Candidate: the leaf_0177-type support (2 fans + signed triangle
  pair sharing an edge + demand caps) is a real geometric family.
- Decode of leaf_0177's saved cert, item by item: fans at rows 1,2;
  +△(0,1,3) −△(0,1,2) (shared edge 0-1); caps ∠012 ≤ π−λ and
  ∠124 ≤ π−λ become demands `dirArc(1;0,2) ≥ λ`,
  `dirArc(2;1,4) ≥ λ` via complement decode; free `rnn/gnn` absorb
  qs baselines.  The identity:
      dirArc(u;a,x) + dirArc(a;w,u) = dirArc(w;a,x) + ∠wxu
  — the negative triangle is NOT a loose relaxation; it re-routes
  one fan arc through vertex w plus a hinge angle at x.
- Kernel-checked: `detour_arc_swap` (pure geometric identity from
  three decode equations + two triangle angle sums),
  `two_fan_detour_cert` (2π = residual sum ⇒ δ ≥ (B−2n)/2 via ge_of),
  `leaf_0177_detour_cert` (full skeleton instantiation, B=10, δ≥1).
  Axioms: [propext, Classical.choice, Quot.sound] only.
- Empirical reach (tools/detour_witness.py, canonical multipliers
  + greedy demand augmentation + verify_cert):
  n4_high 179/519, n4_low 114/401, s6 0 (cap regime).
  Union certB ∪ detour ∪ fat/poly ∪ template-A/C:
  n4_high 489/519 (residual 30), n4_low 383/401 (residual 18),
  s6 101/101.
- leaf_0177 itself now CERT_REPLAYED under the detour family.
- Status: PROVED (the two Lean theorems) + EMPIRICAL (coverage).

## Transfer family (slack transport)

- Residual leaves after certB ∪ detour ∪ fat/poly ∪ templates (30 in
  n4_high) decompose as *single-fan* certificates: one fan equality
  plus a signed combination of triangle angle-sums transporting arcs
  between rows.
- `dirArc_triangle_transfer` PROVED: in △vuw with apex decode pattern
  (direct, complement, direct),
  `dirArc(u;v,w) = dirArc(v;u,w) + dirArc(w;v,u)` — the same arc
  re-measured at other vertices carries a different q-baseline; the
  difference is harvested cell slack.  All 71 single-fan/single-tri
  leaves in n4_high use exactly this DCD pattern.
- `detour_arc_compose` PROVED: two detours sharing the anchor
  `dirArc(w;a,x)` eliminate it, giving a row-to-row transfer with a
  signed correction term; negative image arcs absorbed by r<1 caps.
- Instances: `leaf_0970_transfer_cert` (π = 3 arcs + transfer, δ≥1),
  `leaf_0968_transfer_cert` (fan1 + ∆014−∆013 + ∆023−∆024 + demand
  ∠013≤π−λ + rle41 cap ⇒ π≥5λ).  Axioms clean.
- tools/transfer_witness.py (T1/T2 recognizers + verify_cert):
  n4_high 360 (T1 338 / T2 22), n4_low 302, s6 29.
  50/50 sampled witnesses re-verify independently.
- **Union coverage now EXHAUSTIVE on bounded corpus:**
  n4_high 519/519, n4_low 401/401, s6 101/101 (EMPIRICAL).

## Open next

- M1b done; M2 done (detour + transfer families kernel-checked,
  witnesses replayed).
- M3: R-HIGH1 — bounded corpus admits a certificate for every leaf;
  the live question is the *universal selection theorem*: prove that
  S=1 + K>5/4 forces one of {certB endpoint chain, detour, transfer,
  fat-arc, polygon} for arbitrary n.  Candidate mechanisms: the
  saturated row's fan is tight (Σq = n or n−1), and over-capacity
  defects (profile (1,2,2,2,3) at n=4) force a transferable arc —
  see LIVE_OBLIGATIONS.  Fixed-cover quarter-face is FALSIFIED; the
  simple narrow-subcone/two-anchor partition is FALSIFIED by the
  exact 4-point configuration; do not retry.
