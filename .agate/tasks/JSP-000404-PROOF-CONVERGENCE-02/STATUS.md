# JSP-000404 — AIR Owner round report 2026-10-02 (GLOBAL_R2_EMISSION + LEDGER)

REMOTE_BRANCH=agent/jsp404-air-emergency-owner-20260928
REMOTE_EXACT_HEAD=a6de321fac805e05ccc75604ec9e2d2d08254b54
LOCAL_HEAD=366a120
TESTED_CODE_SHA=366a120 (full root build 9010 jobs, exit 0)
INTEGRATION_BASE_SHA=c2b4c9931385bc9a65ce022ae73533b5c8845e4c
EVIDENCE_PATHS=Jsp000404/FivePointCapacity.lean
  (defect_two_big_ends_theta_extremal ~1653,
   r2_residual_tail_emission ~2056,
   r2_tail_delete_closed ~2278,
   tail_weight_ledger ~2411,
   minimal_excess_eq_least_weight ~2440),
  Jsp000404/MixedStarExclusion.lean (up_of_theta_lt'),
  verification/r2-global-build.txt (full root, 9010 jobs, exit 0),
  verification/r2-global-axioms.txt (full multiline, no truncation)

GLOBAL_R2_TAIL_EMISSION=PROVED — `r2_residual_tail_emission` drops the
`hbetween` ordering hypothesis entirely: for ANY position type, an
over-capacity R2 configuration emits a real short chord from one of the
two defect-2 rows into a defect>=3 row.  The unifier is the new lemma
`defect_two_big_ends_theta_extremal` (any size): a defect-2 row with
both end gaps >= lam has row span <= beta < lam; if it were not a
global theta-extremum, `up_of_theta_lt'` (new general-size version in
MixedStarExclusion — the old `up_of_theta_lt` is Fin-4-scoped) produces
Up x h and Up h y, and `up_cap` forces |dirRep h y - dirRep x h| >= lam,
contradicting the span bound.  Residual routing: short end -> witness;
witness in tail -> done; witness on the other low row -> either that
row has a short end (no-return lemmas push the next witness to the
tail) or it is double-big hence extremal hence min/max-clump capacity
contradicts hover.

R2_TAIL_DELETE_CLOSED=PROVED — `r2_tail_delete_closed` (s >= 5, i.e.
>= 6 centers): deleting any tail row q keeps the anchor defect-1
(scores only rise), keeps a',b' at defect 2 via two calls of
deletion_rigidity (swapped i/j roles — the lemma only pins the i'
row), and keeps every other survivor at defect >= 3 (defect 1 would
dual-saturate and contradict rowScore_add_three_le_of_two_saturated;
defect 2 would violate defect_two_rows_le_two on the reduced config).
This licenses strong induction on R2 itself, no fallback to unfinished
general M3.

DYADIC_LEDGER_AND_NORMAL_FORM=arithmetic layer PROVED, config-layer
instantiation NOT done.  `tail_weight_ledger` is the pure Finset/Nat
identity W_q^- + w_q = W + G_q with G_q = sum_{r != q} w_r(2^{g_r}-1),
W_q^- = sum_{r != q} w_r * 2^{g_r}.  `minimal_excess_eq_least_weight`
packages the minimal-counterexample arithmetic: given the ledger per
deletion, reduced-capacity bound W_q^- <= Q, least weight u = w q0
dividing all weights and Q, and W > Q, it concludes Delta = u,
W = Q + u (i.e. F = 5Q + u), G_{q0} = 0, and W_{q0}^- = Q.  Feeding
these from an actual R2 induction on s (reduced-config potential
decomposition + the Fin.predAbove transport over Q.succAbove) is the
remaining glue; deliberately NOT wired this round because the closing
step needs the G6 geometry and no sorry/placeholder is allowed.

SIX_CENTRE_122333=OPEN — the real geometric attack, unchanged: rule out
a (1,2,2,3,3,3) profile where deleting any of the three defect-3 points
leaves every survivor gain 0.  Data available for the contradiction:
the two low rows' position class, all-position emission chord, and
three independent zero-gain deletions with real Up/triangle caps.
No claim of progress here this round.

HONEST_BOUNDARY: this round delivers all-position R2 emission, R2
tail-deletion closedness, and the ledger/normal-form arithmetic —
NOT tail capacity, NOT EmissionDichotomy, NOT M3, NOT R2 capacity,
NOT the Sendov theorem.  The "only sorry is sendov_lower" phrasing
from previous rounds was imprecise: pre-existing placeholders at
Deletion.lean:1294/1304, PentagonGadgetBridge.lean:41,
Section4Legality.lean:165, GeometricDeletion.lean:644, and
MainTheorem.lean:20 are all still present; the new chain provably
does not depend on any of them (axiom audit below).

NEW_AXIOMS=none; all nine audited declarations depend only on
[propext, Classical.choice, Quot.sound]; no sorryAx in the new chain.
FULL_ROOT_BUILD=PASS (9010 jobs, 0 errors).

---

# JSP-000404 — AIR Owner round report 2026-10-01 (R2_TOP_CLUMP_CLOSED)

REMOTE_BRANCH=agent/jsp404-air-emergency-owner-20260928
REMOTE_EXACT_HEAD=55700f3
LOCAL_HEAD=55700f3
TESTED_CODE_SHA=55700f3 (full root build 9010 jobs, exit 0)
INTEGRATION_BASE_SHA=c2b4c9931385bc9a65ce022ae73533b5c8845e4c
EVIDENCE_PATHS=Jsp000404/IntervalPacking.lean (first-gap pin lemma),
  Jsp000404/OneSaturatedHigh.lean (free-start slack_sum_start),
  Jsp000404/FivePointCapacity.lean (max_receiver_clump ~1420-1660,
    between_residual_tail_emission ~1800-1980),
  verification/r2-between-residual-build.txt,
  verification/r2-between-axioms.txt (full multiline, no truncation)

R2_TOP_CLUMP=CLOSED — the "theta_b <= 2*beta - lam is a true geometric
gap" verdict from the previous round is SUPERSEDED AND FALSIFIED.
The blocker analysis covered the overly broad corridor
[lam, pi-lam+beta]; the actual corridor under the global theta-max b
is tightened by saturated_chord_minmax_window to
[lam, U] with U = theta_b + pi - lam, which contains every actual
non-anchor chord for ALL parameters.  New pieces:
  IntervalPacking.linearGapScore_first_ge_of_big_ends_floor_one
    (mirror pin: tail floor = 1 + defect 2 + big ends + total <= n
    => first floor = n-1, head >= left + (n-1)*lam)
  OneSaturatedHigh.potential_le_high_of_saturated_slack_sum_start
    (free-start slack assembly: arbitrary start <= lam, corridor
    upper bound + per-row right budgets as explicit hypotheses;
    anchored-row left is still theta i, lam <= dir still supplied by
    chord_in_corridor, not by S <= dir)
  FivePointCapacity.potential_le_high_of_saturated_max_receiver_clump
    (top row pinned into [U-beta, U]; free grid
    w = (pi-2lam+beta)/n, S = lam + theta_b - beta satisfies
    beta < w < lam, 0 < S <= lam, S + n*w = U < pi;
    occupancy 1 in the last bin (U-w, U] — uniformBin's last-bin
    clamping keeps x = U; slack Q = 2^{n-2} via slack_sum_start)
R2_BETWEEN_TAIL_EMISSION=PROVED — between_residual_tail_or_top's
  second disjunct consumed: top-clump datum on b (theta-max, defect 2,
  double-big ends, shared chord > theta_b + pi - 2*lam) feeds
  max_receiver_clump, contradicting hover.  Delivered as renamed
  theorem between_residual_tail_emission: pure low-source ->
  defect>=3 receiver short-chord emission, NO top-clump disjunct.

SCOPE: this closes only the BETWEEN low-low residual.  It is NOT
BETWEEN total capacity, NOT EmissionDichotomy, NOT M3, NOT the full
Sendov theorem.  A single real short chord is not yet sufficient
tail-weight control.

EXACT_RATIONAL_REGRESSION=independent replay (Fraction arithmetic,
1872 parameter sets incl. 468 in the old t <= 2*beta - lam "hard
region" and 504 boundary cases): 0 failures.  Scalar coverage check
only — not a geometric proof.  The provided attachment packet path
(sandbox:/mnt/data/...) was not reachable in this environment; the
replay here is an independent reimplementation of the stated checks.

NEW_AXIOMS=none; linearGapScore_first_ge_of_big_ends_floor_one,
  slack_sum_start, max_receiver_clump, between_residual_tail_emission
  all depend only on [propext, Classical.choice, Quot.sound]; no
  sorryAx anywhere in the new chain.
FULL_ROOT_BUILD=PASS (9010 jobs, 0 errors; sole sorry is
  MainTheorem.sendov_lower — known unfinished)
PUSH_STATUS=<pending push>
TREE_CLEAN=only docs delta pending

──────────────────────────────────────────────────────────────────────

# JSP-000404 — AIR Owner round report 2026-10-01 (R2_ANCHOR_EXTREME_BETWEEN)

REMOTE_BRANCH=agent/jsp404-air-emergency-owner-20260928
REMOTE_EXACT_HEAD=aa2cd31
LOCAL_HEAD=aa2cd31
TESTED_CODE_SHA=aa2cd31 (full root build rerun this round)
INTEGRATION_BASE_SHA=c2b4c9931385bc9a65ce022ae73533b5c8845e4c
EVIDENCE_PATHS=Jsp000404/IntervalPacking.lean (tail-gap pin lemmas),
  Jsp000404/OneSaturatedHigh.lean (anchor-deletion promotion,
  SortedLE helpers made public),
  Jsp000404/FivePointCapacity.lean (~1010-1760, R2 chain),
  verification/r2-between-residual-build.txt,
  verification/r2-between-axioms.txt

R2_ANCHOR_DELETION=PROVED (90b88c3)
  rowDefect_succAbove_eq_one_of_big_ends: both anchored end gaps >= lam
  imply deleting the saturated anchor raises the row to saturation.
  gap = cyclicDiff branch order handled (eq-test first, then <).
R2_DOUBLE_PROMOTION_CAP=PROVED (90b88c3)
  potential_le_high_of_saturated_delete_anchor_sat_pair +
  potential_le_high_of_saturated_two_low_big_ends: both defect-2 rows
  double-big-ended => each is defect-1 after anchor deletion =>
  two-saturated capacity consumer closes.  Contrapositive: over-capacity
  residual forces >= 1 genuinely short end on the low rows.
R2_MIN_RECEIVER_CLUMP=PROVED (90b88c3)
  potential_le_high_of_saturated_min_receiver_clump: theta-min defect-2
  row, big last end, some element < theta+2*lam => whole row pinned in
  [theta+lam, theta+lam+beta] => occupancy 1 => slack_sum => cap.
  Re-referencing to e' = P_h - A done via directionRow_reference_shift +
  insertionSort_projectiveShift (no reflection transport assumed).
R2_BETWEEN_EMISSION=PROVED (e98081f)
  between_residual_emission: over-capacity BETWEEN config exhibits a
  short end chord at a low row; receiver either a defect->=3 interior
  row (real low->tail emission) or the other low row (two low-low
  alternatives left explicit).
R2_BETWEEN_STRENGTHENED=PROVED (9732709 + aa2cd31)
  between_residual_tail_or_top: the b->a low-low alternative is
  ELIMINATED (a short-last => no-immediate-return forces tail witness;
  a big-last => shared chord < theta_a+2*lam feeds min-receiver clump,
  contradicting over-capacity).  The a->b alternative reduces to:
  tail-emission (b short-first, first witness leaves {a,b} via
  defect_two_short_first_witness_ne_source) OR an explicit top-clump
  datum on b: theta-max defect-2, double-big ends, shared chord
  dirRep b a > theta_b + pi - 2*lam.
NEW_AXIOMS=none; all new decls axiom-clean [propext, Classical.choice,
  Quot.sound]; no sorryAx anywhere in the R2 chain.
FULL_ROOT_BUILD=PASS (9010 jobs, 0 errors; sole sorry is
  MainTheorem.sendov_lower — known unfinished)
PUSH_STATUS=PUSHED through aa2cd31
TREE_CLEAN=yes

LIVE_BLOCKER=R-HIGH1 tail + BETWEEN top-clump: SUPERSEDED (see round
  report above).  The cover-feasibility obstruction recorded below was
  derived for the overly broad corridor [lam, pi-lam+beta]; the actual
  corridor under the theta-max row is [lam, theta_b+pi-lam] and the
  free-start grid closes ALL parameters.  Historical analysis retained
  for the audit trail:
  Cover-feasibility analysis (see RESEARCH_LEDGER): a
  corridor-anchored uniform cover with a single bin containing the
  top-clump interval [theta_b+(n-1)*lam, theta_b+(n-1)*lam+beta] exists
  iff theta_b > 2*beta - lam; for theta_b <= 2*beta - lam (large-delta
  regime, possible only when beta >= lam/2) the lead's "upper-end
  aligned" cover cannot contain the full corridor [lam, pi-lam+beta]
  either — that regime needs a genuinely different argument (e.g.
  consuming the joint a-last-short + b-double-big structure, or a
  slack_sum variant with free bin start).
ALL_ABOVE/ALL_BELOW position types: not yet routed (each still needs a
  real distance bound, ordering alone insufficient — recorded below).

──────────────────────────────────────────────────────────────────────

# JSP-000404 — AIR Owner round report 2026-09-30 (GENERAL_LIFT_AND_TAIL)

REMOTE_BRANCH=agent/jsp404-air-emergency-owner-20260928
REMOTE_EXACT_HEAD=9b031df
LOCAL_HEAD=9b031df
TESTED_CODE_SHA=86e9ef3 (OneSaturatedHigh axioms run)
INTEGRATION_BASE_SHA=c2b4c9931385bc9a65ce022ae73533b5c8845e4c
EVIDENCE_PATHS=Jsp000404/OneSaturatedHigh.lean (new thms ~4200-5030),
  Jsp000404/FivePointCapacity.lean (Sections 5/6), RESEARCH_LEDGER.md

FIVE_POINT_SATCHART_PROFILE=PROVED (pre-round)
FIVE_POINT_ORIGINAL_CAPACITY=PROVED (429e876)
HIGH_CAPACITY_SIZE_LE_FIVE=PROVED (429e876)
HIGH_CERT_REDUCTION_TO_T_GE_SIX=CONDITIONAL-USEFUL (429e876)
GENERAL_DEFECT_TWO_CARD_LE_TWO=PROVED (8ada8a5)
GENERAL_TWO_LOW_POSITION=PROVED (f5670db, theta_regions_collapse +
  defect_two_pair_theta_cluster)
FIVE_POINT_RESIDUAL_PROFILE=PROVED (b5d1e4a, five_point_residual_defect_ge_three)

TAIL_R2=OPEN — consumers proved: slack_family, delete_pair (606188e),
  slack_sum + strict_slack (4d240e5).  Residual constraints proved:
  defect-2 rows perfectly packed occ=2 (86e9ef3); <=1 defect-3 row
  can be at occ<=2; every cover has Sigma slack < Q.
  Missing: geometric supply of strict margins / pair at occ<=2.
TAIL_R1=OPEN — same blocker, weaker budget.
TAIL_R0=OPEN — same blocker.

M3=OPEN (high-defect tail supply)
LOW0=OPEN
HIGH0=OPEN
M4=pending
FINAL_ROOT=OPEN (sendov_lower sorry remains)

MODULE_BUILD=PASS (OneSaturatedHigh, all new decls axiom-clean)
FULL_ROOT_BUILD=not rerun this round
NEW_AXIOMS=none
ASSUMPTION_AUDIT=clean: [propext, Classical.choice, Quot.sound] on all
  new declarations
INDEPENDENT_REVIEW=PENDING (no reviewer available; self-review only)
PUSH_STATUS=PUSHED through 9b031df
TREE_CLEAN=yes

LIVE_BLOCKER=R-HIGH1 tail: supply a family T (in one valid uniform
  n-bin cover) with strict occupancy margins summing
  Sigma_T 2^{n-d_i} >= 2^{n-2}, i.e. two defect>=3 rows at occ<=2
  or an equivalent partial-margin sum; OR rule out the perfect-
  packing boundary (all defect-2 rows at occ=2, now PROVED forced
  in the violating domain) geometrically.
NEXT_ACTION=geometric supply of a strict occupancy deficit — either
  break perfect packing of an extreme defect-2 row via the
  theta_regions_collapse position classification, or route through
  delete_pair by bounding the post-deletion survivor span < alpha
  using the same position data.

---

# JSP-000404-PROOF-CONVERGENCE-02 — status

Owner branch `agent/jsp404-proof-convergence-02-owner`, worktree
`D:/op/sunyuchen/jsp-000404-pc02`, semantic base `lane/integration`.

## Milestone board

| Gate | Status |
|---|---|
| M0 remote/model/DAG alignment + minimal certB port, no integration regression | DONE (build 8996 jobs, axioms clean) |
| M1 certB direction/max calibration + bounded witness pass | DONE — decode fixed, leaf_0002 regression reproduced, 773 witnesses emitted and independently re-verified |
| M2 reusable live-domain construction/extension lemma | DONE — detour/transfer families kernel-checked; bounded corpus 100% (EMPIRICAL) |
| M3 R-HIGH1 arbitrary n≥3, s capacity closed | IN PROGRESS — narrow-window subdomain CLOSED (`OneSaturatedHigh`, axioms clean); residual `α ≤ spread < δλ` OPEN |
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
replays 179 n4_high / 114 n4_low leaves (tools/detour_witness.py).

**Transfer family** (new): the residual leaves decomposed into
single-fan certificates.  `dirArc_triangle_transfer` — the
single-triangle arc transfer `dirArc(u;v,w) = dirArc(v;u,w) +
dirArc(w;v,u)` under apex pattern (direct, complement, direct) — is
the elementary slack-transport move: the same geometric arc costs a
different `q`-baseline in different rows.  `detour_arc_compose`
eliminates a shared anchor arc between two detours, giving the
row-to-row transfer with signed correction (negative image arcs
absorbed by `r<1` caps).  Kernel-checked instances:
`leaf_0970_transfer_cert` (fan + one transfer) and
`leaf_0968_transfer_cert` (fan + double-detour composition).
`tools/transfer_witness.py` replays T1/T2 witnesses:
n4_high 360 (T1 338, T2 22), n4_low 302, s6 29.

**Union coverage is now exhaustive on the bounded corpus:**
n4_high 519/519, n4_low 401/401, s6 101/101 — every skeleton leaf
admits at least one verify_cert-checked arc-budget certificate among
{certB endpoint chains, detour, transfer T1/T2, fat-arc, polygon,
template A/B/C}.  This is EMPIRICAL coverage, not a selection proof;
but it shows the certificate grammar is expressively complete on the
sample and sharpens the M3 question to: why does over-capacity
*force* one of these shapes.

## Live obligations

See LIVE_OBLIGATIONS.md.  R-HIGH1 is the main target: n≥3,
1/2≤δ<1, exactly one saturated center (S=1), prove K≤5/4.

### 2026-10-14 — R-HIGH1 subdomain progress

- `potential_le_high_of_saturated_small` PROVED (axioms clean):
  R-HIGH1 closed for s ≤ 4; tight — the (O,P,Q,R) equality family
  sits at s = 4 in the wide-window regime (closed, not residual).
- Corpus defect profiles scanned: n4_high all (1,2,2,2,3) at s = 5.
  Profile conjectures not supported — corpus samples only s = 5.
- Residual restated as quarter-cube aggregate:
  H + Σ_v (2^{n−a_v} − 2^{k_v}) ≥ 2^{n−2}  under an n-bin corridor
  cover.  Extreme-sliver reachability facts derived (unformalized).

### 2026-10-14 — R-HIGH1: bottom-clump subdomain closed

- `potential_le_high_of_saturated_clump` PROVED (axioms clean,
  root build PASS 8997 jobs): a non-anchor row whose chord directions
  all fit in [λ, λ+w₀), w₀·n < π−λ, supplies the full quarter-cube
  slack (cube 2^{n−1} vs weight 2^{n−2}) via an adaptive uniform cover.
  Closes the tight (O,P,Q,R) equality family.
- `AnchoredRows`: `theta ≤ λ/2` relaxed to `theta ≤ λ` in
  `directionRow_anchor_cons` and `anchored_rowScore_eq_linear`
  (residual window needs θ up to δλ); callers updated, axioms clean.
- Residual sharpened (Lead-corrected): s ≥ 5, spread σ ∈ [α, δλ]
  (non-strict), rest > 3·2^{n−2}, AND no non-anchor row has all chords
  in the bottom prefix [λ, λ+w₀) with w₀·n < π−λ.  Middle-seated narrow
  rows are NOT excluded — the clump interval is anchored at λ.
  Equality-family parameter fixed: w₀ = λ/3 (not λ/8).

### 2026-10-14 — R-HIGH1: single-outlier deletion closure

- `potential_le_high_of_saturated_delete_narrow` PROVED (axioms clean,
  module + root build PASS 8997 jobs): delete one non-anchor `q`; if the
  surviving anchor rays are pairwise within `β < α`, then
  `potential ≤ 2^{n−2} + 2^n`.  The deleted row's weight is paid by its
  defect `≥ 2`; the anchor stays saturated after deletion since
  `rowScore_eraseIdx'` never lowers a score and `one_le_rowDefect` caps
  scores at `n−1`.  No removability of `q`, no post-deletion uniqueness.
- `potential_le_high_of_saturated_one_outlier` PROVED (axioms clean):
  chart-level corollary — if all anchor rays except one lie strictly
  below `α`, cap holds (finite max `M < α` supplies pairwise bound).
- Residual sharpened: now requires `θ_{s−2} ≥ α` (at least two rays at
  height ≥ α), plus the existing `σ ∈ [α, δλ]`, `Σ 2^{2−c} > 3`,
  `s ≥ 5`, no bottom-prefix clump.
- Doc fixes per Lead review already landed: clump prefix scope,
  `w₀ = λ/3` for the equality family, `B = (π−λ)/n < λ`, `σ ≤ δλ`
  non-strict, four-point family excluded as residual witness.

### 2026-10-14 — R-HIGH1: slack-certificate family

- `potential_le_high_of_saturated_slack_family` PROVED (axioms clean,
  root build PASS 8997 jobs): under an n-bin corridor cover (width < λ,
  n·width < π−λ), a family T of non-anchor rows each occupying ≤ r bins
  with defect ≥ r+1 contributes slack 2^{n−r−1} each; |T| ≥ 2^{r−1}
  aggregates to the full 2^{n−2} quarter.  Unifies the certificate
  grammar: r=1,|T|=1 is exactly the clump theorem; r=2,|T|=2 is the
  two-small-row certificate of ONE_SATURATED_HIGH_RESEARCH.md §slack.
  Premises are geometric/bin-level occupancy + defect, not a renamed
  aggregate.
- Also this round: `saturated_row_{bot,top}_sliver_{forces_*,card_le_one}`
  (ConeCorridor, axioms clean) — per-row sliver occupancy bridge.

### 2026-10-14 — R-HIGH1: Goal-A/B 落地 + 体积刚性 + 高缺陷行存在

- `potential_le_high_of_saturated_delete_span` PROVED (Goal task A):
  delete ANY non-anchor ray; survivor span `< (n+1)λ−π` gives the cap.
  Both extreme deletions instantiate it → residual must satisfy
  `θ_{m−1}−θ_1 ≥ α` AND `θ_m−θ_2 ≥ α` (double-end spread), hence both
  extreme gaps `≤ (2δ−1)λ < λ`.
- `first_bin_straddles` / `last_bin_straddles` /
  `sliver_threshold_lt_width` PROVED (Goal task B, IntervalPacking):
  full-corridor n-bin cover + residual spread forces `θ₂ < width` —
  bottom sliver strictly inside bin 0, shared with middle chords.
  **No bin is sliver-exclusive**; sliver charging must be fractional.
- `defect_two_rows_le_three` + `four_defect_two_tiling` PROVED:
  defect-2 rows carry cube volume `2^{n−2}`; ≤3 coexist with a 5th
  non-anchor row; exactly-4 is the hole-free perfect tiling = abstract
  negative control profile (1,2,2,2,3).
- `exists_two_rows_defect_ge_three` PROVED: s≥5 residual supplies
  `≥ s−3 ≥ 2` defect-≥3 rows — the r=2 slack_family candidates.
- Sharpened crux (ledger): residual needs rows with `a_i < d_i`
  (occupancy strictly below defect); strictness in
  `linearGapScore + occ ≤ n` arises exactly from same-bin adjacent
  directions or uncharged bin-skips — the geometric input still owed.
- Remote: `75c95d1` on `agent/jsp404-proof-convergence-02-owner`;
  merge `349d3ef` absorbed `lane/integration@204f26a`; READY_FOR_G3
  published for batch `b2a7c32` (`7566549`).  Build: 9000 jobs PASS;
  all new decls `[propext, Classical.choice, Quot.sound]`.

### 2026-09-24 — 修正余量目标 + 正确 strict-prefix 落地

Lead 三处修正全部落实（GOAL_STRICT_MARGIN_20260924.md 存档）：
- 范围：`defect_two_rows_le_three`/`exists_two_rows_defect_ge_three`
  域为 m ≥ 5（s_total ≥ 6）；**m = 4（总五点）不在任何闭包中**——
  `potential_le_high_of_saturated_small` 只覆盖 s_total ≤ 4。
  `four_defect_two_tiling` 剖面更正为 (1,2,2,2,2)。
- 账本：正确恒等式 `H+ΣS = (4−D)Q`，cap ⟺ `D ≤ 3` ⟺ `H+ΣS ≥ Q`；
  撤回 "ΣS ≥ (D−3)Q" 目标（负对照 n=3, c=(2,2,2,3), a=2s:
  Q=2, Σw=7, ΣC=8, H=0, ΣS=1 —— 错目标成立、cap 不成立）。
- strict-prefix 起点：`left = θ_i`（行自身锚射线），非 λ；
  λ=4π/15 反例记录在案。

新定理（全部公理干净，9000 jobs PASS）：
- `linearGapScore_add_one_le_empty_bins` / `_uniform_bins`：
  `gapScore(first−left)+1 ≤ bin(first)` ⟹ `score + occ + 1 ≤ m`。
- `gapScore_add_one_le_of_gap`：`1≤b ∧ first−left < (b+1)λ` ⟹ 严格。
- `gapScore_add_one_le_of_cover`：cover 位置版
  `first ≤ λ+(b+1)w ∧ θ_i > (b+1)w − bλ` ⟹ 严格。
- `rowDefect_add_one_le_of_strict_prefix`（行级消费者）：
  严格前缀 ⟹ `occ + 1 ≤ c_i`，即 `S_i ≥ 2^{n−a_i−1}`。

未证上游（诚实记录）：哪些真实几何条件供给 `hfirst`
（即某行首方向欠费一档）——残余的最低行/极端行的首方向分布。

### 2026-09-24b — 五点计数等价 + 三行紧性刚性

边界修正（Lead 复核）：hfirst 的完整等价式是
`gapScore(first−θ_i)+1 ≤ b ⟺ b ≥ 1 ∧ ⌊(first−θ_i)/λ⌋₊ ≤ b`——
单独 `f ≤ b` 在 `b = 0` 时不蕴含严格前缀。源码签名已含 `1 ≤ b`，仅修报告表述。

新定理（全部 [propext, Classical.choice, Quot.sound]，9000 jobs PASS）：
- `potential_le_high_of_saturated_four_eq`：m=4 非锚行、全部 defect ≥ 2、
  `R = #{defect=2} ≤ 2` ⟹ cap（纯权重计数：R·Q + (4−R)·Q/2 ≤ 3Q）。
  **五点残余精确等价于 `R ≤ 2`**——R ≥ 3 时三行已贡献 3Q、第四行严格为正。
- `three_defect_two_rows_tight`：s ≥ 4 且 |T|=3 全 defect-2 ⟹
  每行占用恰好 2 箱（occ=2, C_i=Q, S_i=0）——若某行 occ ≤ 1，其立方
  ≥ 2^{n−1} 加另两行各 ≥Q 及第四行正体积 ⟹ Σ > 4Q = 2^n。

五点残余现归约为一个纯几何命题：**合法配置中不存在三个
defect-2 行同时保持 occ=2 的零余量紧性**。可用出口（任选其一）：
某 defect-2 行 hfirst（occ+1 ≤ 2 矛盾 occ=2）、后缀/内部严格边际、
铺砌排除、删除、或直接容量论证。
注意方向：packing 在此域内排除了 hfirst，不能循环供给 hfirst；
必须引入跨行真实几何。

### 2026-09-24c — 共享弦几何排除（Lead 路线落地）

撤回：2026-09-24b 条 3 的"小 δ 子域可闭合"——defect-2 缺 Type I
（rowBig=1, rowCells=n−1）分支，且 span<w ⟹ occ=1 有精确反例。
δ∈[1/2,1) 全域仍在目标域。详见 RESEARCH_LEDGER 2026-09-24c。

新定理（全部 [propext, Classical.choice, Quot.sound]，PASS）：
- `linearGapScore_span_le_of_big_ends`（IntervalPacking）+ 配套
  linearBigCount/linearFloorSum 机制。
- `row_span_le_delta_of_defect_two_ends`：defect-2 行两端 gap ≥λ
  ⟹ 方向跨度 ≤ δλ。
- `three_defect_two_rows_big_ends_impossible`：三行全两端大间隙 ⟹
  三共享弦入 [U−δλ,U]，Fin 3 子构型单箱权界 3≤2 矛盾。
- `exists_short_end_of_three_defect_two`：至少一行短端 gap <λ。

OPEN：Type I defect-2、内部大间隙 Type II、短端 witness 的
端点窗消费（card≤1 引理接 chord 计数）、最终 R≤2。

### 2026-09-24c（续）— 短端 witness 消费链落地

- `short_first_gap_gives_lower` / `short_last_gap_gives_higher`：
  端点窗引理接真实顶点——短首 gap ⟹ 更低 θ 弦端点，短尾 gap ⟹
  更高 θ 弦端点（均带回 dirRep = head/getLast 的见证等式）。
- `exists_crossing_witness_of_three_defect_two`：∃ r∈{i,j,k},
  ∃ u≠r 跨侧顶点。
- `first_gap_ge_of_theta_min` / `last_gap_ge_of_theta_max`：
  全局极值行短端必朝内。
- 全部 [propext, Classical.choice, Quot.sound]，3272 jobs PASS。

残余：短端行定位（是三行中哪一行/哪一侧）与 witness u 的身份
（第四行 l 或另一 defect-2 行）未钉死；Type I 与内部大间隙
Type II 形态仍 OPEN。

### 2026-09-24c（续2）— R=4 强化：至少两行短端

- `exists_two_short_end_rows_of_four`（s=4 四行全 defect-2）：
  若至多一行短端，其余三行构成全两端大间隙 defect-2 三元组，
  与 three_defect_two_rows_big_ends_impossible 矛盾。
  ⟹ R=4 时短端行数 ≥2。R=3 仍只得 ≥1。

### 2026-09-26 — MIXED_TWO_IN_CENTRAL 已关闭（混合两入中间弦排除）

- 新模块 `Jsp000404/MixedTwoInCentral.lean`：
  `mixed_two_in_central`（u<z<w 不可能，全部六个 Up 叶）+
  `two_in_mixed_central_exclusion`（消费者：c_H=3 ∧ z<u∨w<z）。
- 首消费 `five_point_high_receiver_not_full_in` 得 Q 非短弦界；
  跨行链：P 零增益→唯一计分 gap≥(n−1)λ，Q 双端大→span≤β，
  逼 R 相邻大 gap；镜像独立证明。
- 公理 [propext, Classical.choice, Quot.sound]；全根构建 PASS 9005 jobs。
- OPEN：同侧两入、混合外侧 c_H=3、z=u/w 共线排除、0/1 入、
  低缺陷终点、R=4、一般 m、M3/M4；五点 R≤2 未闭。air PENDING。

### 2026-09-26 — 方向互异已证 + 零进位余数引理（B 步）

- `legal_dirRep_ne`：合法配置中 dirRep H a ≠ dirRep H b（oangle∈{0,π}→共线→triAngle 矛盾）；
  `SatChart.hleg_sub` 把合法性限制到非锚子族。
- `two_in_mixed_central_exclusion` 的 z≠u、z≠w 假设已消除，自动推导。
- 新模块 `Jsp000404/FivePointZeroCarry.lean`：
  `mergeGain_eq_zero_iff_frac{,'}` + `_frac_lt{,'}`——x<λ≤y 时
  μ=0 ⟺ x + (y − ⌊y/λ⌋·λ) < λ（余数不进位条件，可跨共享弦相加）。
- 已接入根导入；模块构建 PASS（8965 jobs）。
- OPEN：混合外侧 c_H=3 两分支的零进位求和攻击（主攻中）、
  同侧两入、0/1 入、低缺陷终点、R=4、一般 m、M3/M4。air PENDING。


### 2026-09-27 — 混合外侧两入全部排除（outer-low + outer-high）

- `mixed_two_in_outer_low` / `mixed_two_in_outer_high`：六点定位 `z` 在接收弦外两侧均不可能。
  `Up(H,Q)` 支由 cap `|z−w| ≥ λ` 直接冲出 `z>π`/`z<0`；`Up(Q,H)` 下三叶
  相邻大 gap 击杀，两叶（`y<x<t` 与镜像）靠缺陷-2 行的分数集中
  `（n−1)λ ≤ 单 gap` 冲过走廊上界。
- `mixed_two_in_excluded`：中心 + 双外侧合拢——五点 R=3 的混合两入接收者**整体不可能**。
- 验证：模块构建 PASS（8964 jobs）；全根构建 PASS（9006 jobs）；
  六条定理公理均 [propext, Classical.choice, Quot.sound]，无 sorry/admit。
- OPEN：同侧两入、0/1 入接收者、低缺陷终点、R=4、一般 m、M3/M4；
  五点 R≤2 未闭合。air PENDING。
