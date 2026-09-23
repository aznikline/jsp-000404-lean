# JSP-000404-PROOF-CONVERGENCE-02 — status

Owner branch `agent/jsp404-proof-convergence-02-owner`, worktree
`D:/op/sunyuchen/jsp-000404-pc02`, semantic base `lane/integration`.

## Milestone board

| Gate | Status |
|---|---|
| M0 remote/model/DAG alignment + minimal certB port, no integration regression | DONE (build 8996 jobs, axioms clean) |
| M1 certB direction/max calibration + bounded witness pass | DONE — decode fixed, leaf_0002 regression reproduced, 773 witnesses emitted and independently re-verified |
| M2 reusable live-domain construction/extension lemma | pending |
| M3 R-HIGH1 arbitrary n≥3, s capacity closed | pending |
| M4 remaining live cases + full lower bound | pending |

## What is proved on this base (from integration, verified by build)

- Upper bound all N≥3 (`sendov_upper`), extremal ≤ formula
  (`alpha_le_alphaN`), N=3..8 lower + equality, n=1 and n=2 strips,
  LOW with a saturated center, HIGH with two saturated centers.
- `sendov_lower` N≥9: **sorry** (MainTheorem.lean:20).  Sole root gap.
- Conditional path proved: `GeometricCertificates` (n≥3 `CertExists`)
  → `GadgetSelection` → `StaircaseBound` → count bound → lower →
  equality (`CertificateIntegration`, `Integration`, `Induction`).

## certB port (this round)

`Jsp000404/K3bGeometry.lean` ported from cert-source `9ae8230` with
minimal edits only:

- added `import Jsp000404.SaturationPacking` (integration already
  proves `not_three_saturated` there; cert branch had it in
  `Induction`);
- `geomDefectCount_one_le_two` call site adapted to the integration
  signature (`he` earlier, explicit `hs2 : 2 ≤ s` derived from the
  3-element subset);
- `ResidualWitness.ge_of` added to `ChainWitness.lean` (+13 lines);
- `one_le_rowDefect` added to `Deletion.lean` (+29 lines);
- `Jsp000404.lean` root gains the `K3bGeometry` import.

NOT ported: cert branch's `Induction.lean` additions (`KraftPacking`
structure, `kraft_packing_of_legality`, `potential_le_sendovCap_of_packing`),
its `Statement.lean` (deleted there — kept integration's), its shorter
`GeometricDeletion.lean` docstring, `MainTheorem.lean`, `tools/generic_model.py`
(integration's newer `strict` margin mode kept).

All ported declarations audited: axioms
`[propext, Classical.choice, Quot.sound]` only.

## certB direction calibration (mandate §4)

`tools/certb_scan.py` rewritten with the position-aware decode:

    side(u,v) at row r = (+1 if pos(v)>pos(u) else −1), flipped when
    lift bits differ.

+1 ⇒ ∠ = dirArc(u→v);  −1 ⇒ ∠ = π − dirArc(u→v).

All hbA/hbT/hbS/demand/cap checks now consume `side`, not bare bit
equality.  Budgets combine by `max` (mandate §4C); σ is a Python int
(may go negative; no truncation).

leaf_0002 regression (§4B) reproduced and explained: rotating row 0's
cut moves vertex 1 to the end of `order[0]` and flips its lift bit.
The physical `side(1,2)` stays +1, but `bits_eq(1,2)` flips — the old
bits-only decoder then rejects piece j=1's hbA and the best score on
the rotated skeleton drops 2→1.  Position-aware decode keeps σ=2 on
both representatives.

## Corrected certB coverage — hypotheses AND replayed witnesses

| dataset | HYPOTHESES_CHECKED (σ ≥ 2τ) | CERT_REPLAYED | rejected | unclassified |
|---|---|---|---|---|
| certs_n4_high (τ=1) | 407/519 | 387 | 20 | 112 |
| certs_n4_low (τ=½) | 285/401 | 285 | 0 | 116 |
| certs_s6 (n=2, τ=1) | 101/101 | 101 | 0 | 0 |

Boundary topologies among replayed witnesses: n4_high
{fan,fan}:246 + {fan,cap}:141; n4_low {fan,fan}:184 + {fan,cap}:97 +
{cap,fan}:4; s6 {cap,cap}:57 + {cap,fan}:44.  The s6 regime NEVER uses
two fans — it needs both cap bonuses, consistent with the n=2
tightness.

Key structural finding: each boundary slot of the certB identity is
independently realized by the endpoint fan (arc + qs baseline) OR by
the terminal angle cap (span ≤ π−λ ⇒ complement ≥ λ, one cell).  The
saved s6 certificates use exactly the cap topology — the earlier
"variant C" is not a separate family but a boundary-slot choice of
variant B.  Adding fan and cap at the same end double-counts.

Witnesses: `witnesses/{n4_high,n4_low,s6}.jsonl` — chain, cut,
per-piece sides/splits, gap ranges, qs baselines, cap sources, orig
ids, exact multipliers, eliminated form.  45/45 sampled records
re-verify independently from file.

leaf_0177's mixed-sign support decoded item-by-item into the
**detour identity** `dirArc(u;a,x) + dirArc(a;w,u) = dirArc(w;a,x) +
∠wxu` and is now kernel-checked as `detour_arc_swap` +
`two_fan_detour_cert` + `leaf_0177_detour_cert`.  The detour family
replays 179 n4_high / 114 n4_low leaves (tools/detour_witness.py);
four-family union coverage: n4_high 489/519 (residual 30),
n4_low 383/401 (residual 18), s6 101/101.

## Live obligations

See LIVE_OBLIGATIONS.md.  R-HIGH1 is the main target: n≥3,
1/2≤δ<1, exactly one saturated center (S=1), prove K≤5/4.
