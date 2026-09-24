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

## LP-duality reframing of selection (2026-10-14)

- Per skeleton (order, bits, qs), the model LP in remainder variables
  r_ij ∈ [0,1) and δ minimizes δ subject to fan equalities, triangle
  relations, and legality bounds.  Over-capacity leaves are exactly
  those with LP-min-δ ≥ τ.
- Certificate existence per leaf is *automatic* by Farkas duality;
  the empirical content of the 100% union coverage is that the
  certificates stay inside the small grammar {fan, tri-transfer,
  detour pair, fat-arc, polygon, endpoint chain} — supports of size
  ≤ ~7.
- The defect/remainder identity: Σ_j r_ij = (n − cells_i) + δ
  = c_i − big_i + δ, hence 2^{−c_i} = 2^{δ − Σ_j r_ij − big_i}
  ≤ 2^{δ − Σr_i}.  So K > cap is a condition on row remainder sums:
  over-capacity means some weighted remainder-sum profile is too
  large, i.e. the primal asks whether small Σr_i can satisfy
  legality.  Selection = proving primal infeasibility at δ < τ for
  every legal over-capacity skeleton — a purely combinatorial
  statement about (order, bits, qs) once the skeleton axioms are
  fixed.  No metric content remains at that layer.
- Consequence for M3: the live theorem is "every legal skeleton with
  K > cap has infeasible r-LP at δ < τ", equivalently a canonical
  Farkas/transport construction.  The saturated row in R-HIGH1 is
  the natural anchor: defect 1 means Σr_A = δ (big=1) or 1+δ
  (big=0) — a tight or near-tight fan whose arcs are the transport
  sources.

## R-HIGH1 narrow-window reduction (2026-10-14, kernel-checked)

STATEMENT: for `n ≥ 3`, `δ ≥ 1/2`, `s ≥ 1`, a legal `s+1`-center
configuration whose anchor rays `c w − c v` pairwise fit in an angle
`β < α = (n+1)λ − π = (1−δ)λ` has `potential ≤ 2^n`
(`one_saturated_capacity_of_narrow_window`,
`potential_le_two_pow_of_saturated_narrow` in
`Jsp000404/OneSaturatedHigh.lean`; axioms
`[propext, Classical.choice, Quot.sound]`).

ACTUAL_INPUTS: `Section4Legality c lam` (inj + triAngle only — the
proof never uses `big`, `Proper`, or ModeA beyond what legality
provides), `Nat.floor (π/λ) = n`, `0 < λ`, `δ ≥ 1/2`, the spread
hypothesis `hspread`, `β < α`.  The `rowDefect = 1` premise is kept
in the signature (as `_hsat`) for API documentation but is NOT
consumed — the narrow window is the whole mechanism.

CONSUMER: the residual complement inside `CertExists`'s `potential >
sendovCap` branch, once a case split on the anchor-ray spread is
inserted upstream (not yet wired — the capacity theorems and the
`CertExists` consumer are still on separate sides of the split).

FALSIFIER: none for this subdomain; the theorem is proved for all
`n ≥ 3`, `s ≥ 1`.  Note the bound `2^n` is *strictly* below the cap
`5·2^{n−2}` — the subdomain has one full power-of-2 of slack.

SUCCESS_CRITERION: met for the narrow subdomain.  The precise open
residual is `α ≤ spread < δλ` (nonempty iff `δ > 1/2`).  The key
arithmetic fact exposed by the reduction: in the residual case the
corridor `[λ, π−λ+β]` has width `≥ (n−1)λ`, so `n−1` bins fail by an
arbitrarily small amount, while the capacity target still allows
`rest ≤ 3·2^{n−2}` against the corridor's `2^{n−1}`.  Two candidate
next moves (both unproved):
  (a) use `n` bins on the full corridor `π−λ+β ≤ π` and harvest the
      bin containing the wrap-around chords — the saturated anchor's
      own `n`-cell occupies exactly one bin, which may force an empty
      bin among the remaining rows (a "bin deficit" argument);
  (b) split the residual by whether a second center sees a narrow
      fan, reducing toward the two-anchor machinery of
      `TwoSaturatedHigh`/`TwoAnchoredRows` without requiring
      saturation at the second anchor.

## M3 candidate — small-s counting closure (PROVED)

STATEMENT: `potential_le_high_of_saturated_small` — for any legal
configuration with 2 ≤ s ≤ 4 centers, saturated anchor row defect = 1,
and all other rows defect ≥ 2: potential ≤ 2^n + 2^{n−2}.  Axioms
clean.  This closes R-HIGH1 for s ≤ 4 including the tight
(O,P,Q,R) equality family.

ACTUAL_INPUTS: legality, 0 < λ, ⌊π/λ⌋ = n, 2 ≤ n; per-row
`rowCells ≤ n` (already proved: `rowCells_le_of_floor`).
CONSUMER: not yet wired into CertExists; a subdomain capacity theorem.
FALSIFIER: none — proved, and shown tight by the s=4 equality family.
SUCCESS_CRITERION: met for s ≤ 4; residual is s ≥ 5.

## Corpus defect-profile scan (EMPIRICAL, frozen)

All 519 n4_high leaves have profile (1,2,2,2,3) — s = 5, K = 11/8;
all 401 n4_low leaves (1,2,2,3); all 101 s6 leaves (2,2,2,2,2,2).
The conjecture "residual ⇒ ≤ 3 defect-2 rows" is neither supported
nor refuted — the corpus only samples s = 5 for HIGH.  No promotion.

## Residual structure facts (derived, not yet formalized)

In the residual, order anchor rays 0 = θ₁ < … < θ_{s−1} = σ.  A chord
u→w with θ_u < θ_w has dir ∈ [θ_u + λ, π − λ + θ_w].  Consequently:

- top sliver (π−λ+θ_{s−2}, π−λ+σ] is reachable only by chords whose
  endpoint is Q = θ_{s−1};
- bottom sliver [λ, λ+θ₂) only by chords from P = θ₁;
- every non-anchor row's anchor direction θ_W ∈ [0,σ] lies below the
  corridor start λ.

With n bins on the corridor the disjoint-cube bound is
Σ_v 2^{n−a_v} ≤ 2^n; the target Σ_{w≠v} 2^{k_w} ≤ 3·2^{n−2} is
equivalent to the aggregate inequality  H + Σ_v S_v ≥ 2^{n−2}  with
H = holes, S_v = 2^{n−a_v} − 2^{k_v} ≥ 0.  This is the sharpest
restatement so far: slack (a_v < c_v, i.e. rows whose chords clump
into few bins) and holes must sum to a quarter cube.

## 2026-10-14 — Clump-row quarter-cube (PROVED, kernel-clean)

STATEMENT (`potential_le_high_of_saturated_clump`, OneSaturatedHigh.lean):
unique saturated center, all other rows defect ≥ 2, chart e with
anchor rays θ ∈ [0, δλ]; if some non-anchor row i* has all chord
dirReps in [λ, λ+w₀) with w₀·n < π−λ, then potential ≤ 2^n + 2^{n−2}.
ACTUAL_INPUTS: legality, λ>0, ⌊π/λ⌋=n, n≥3, defect ≥2 for all
non-anchor rows, θ-realization in the same chart, the clump hypothesis.
CONSUMER: not yet wired; a subdomain capacity theorem.  Upstream the
chart data comes from `saturated_chord_corridor` (θ ∈ [0,δλ]).
FALSIFIER: none — proved.  The tight (O,P,Q,R) equality family is a
member with w₀ = λ/3 (row Q: directions 9λ/8, 5λ/4 ∈ [λ, 4λ/3);
w₀ = λ/8 or λ/4 is WRONG — 5λ/4 is the excluded right endpoint).
That family is independently closed by the s ≤ 4 theorem.
SUCCESS_CRITERION: met — the mechanism is exactly the AVERAGED_BIN_PACKING
slack: a_i = 1 gives cube 2^{n−1} vs weight 2^{n−2} = quarter-cube slack.

Infrastructure: `directionRow_anchor_cons` and
`anchored_rowScore_eq_linear` generalized θ ≤ λ/2 → θ ≤ λ
(needed: residual θ up to δλ > λ/2).  All callers updated; axioms
[propext, Classical.choice, Quot.sound].

Residual after this closure (Lead-corrected): only rows with all
chords in the BOTTOM PREFIX [λ, λ+w₀), w₀ < (π−λ)/n = λ(1−(1−δ)/n),
are excluded.  A narrow row seated mid-corridor is NOT excluded —
the interval's left endpoint is fixed at λ.

## 2026-10-14 — Endpoint-refined chord window (PROVED, kernel-clean)

STATEMENT (ConeCorridor.lean):
`chord_in_endpoint_window` — under the two endpoint angle caps
`∠AXY, ∠AYX ≤ π−λ` and anchor rays `tx, ty ∈ [0, β]`, the projective
chord representative satisfies the DISJUNCTION
  phi ∈ [tx+λ, π−λ+ty]  ∨  phi ∈ [ty+λ, π−λ+tx].
Derivation: `∠AXY ≤ π−λ` rewrites to `|phi − tx| ≥ λ` (start-point
lower bound `phi ≥ tx+λ`, since `phi ≥ 0 > tx−λ`); `∠AYX ≤ π−λ`
rewrites to `|phi − ty| ≤ π−λ` (end-point upper bound).  The private
`directed_chord_in_corridor` conclusion was strengthened accordingly;
`chord_in_corridor` re-derives the crude `[λ, π−λ+β]` bound via
Icc-subset.
CONSUMER: `saturated_chord_endpoint_window` (row-level form on the
saturated corridor data), `saturated_chord_minmax_window`
(`dir ∈ [λ+min θ, π−λ+max θ]`), `saturated_chord_top_sliver` /
`saturated_chord_bot_sliver` — formalizing the previously
"derived, unformalized" extreme-sliver exclusivity: a chord with
dir > π−λ+t (resp. < λ+t) has an endpoint with θ > t (resp. < t).
FALSIFIER: none — proved.  NOTE: the per-row narrowing conjecture
"row i ⊆ [λ+θ_i, π−λ+θ_i]" is FALSE — the disjunctive case flips per
chord; the correct per-chord envelope is `[λ+min θ_ij, π−λ+max θ_ij]`.
SUCCESS_CRITERION: met as infrastructure.  The quarter-cube aggregate
`H + Σ S_v ≥ 2^{n−2}` still needs a packing argument consuming these
windows — sliver bins are reachable only through extreme-θ endpoints,
so an occupied extreme bin charges against few rows' window reach.

### Single-point deletion reduction (PROVED, axioms clean)

`potential_le_high_of_saturated_delete_narrow`: the Lead's proposed
chain F(c) ≤ 2^{n−2} + F(c\{q}) ≤ 2^{n−2} + 2^n is now kernel-checked.
Key step: after `Section4Legality.erase` + `eraseIdx_directionRow`, the
anchor's reduced score is ≥ its old score `n−1` (`rowScore_eraseIdx'`,
gain a natural number) and ≤ n−1 (`one_le_rowDefect`), hence the anchor
remains saturated and `potential_le_two_pow_of_saturated_narrow` applies
to the sub-configuration — which requires neither removability of q nor
uniqueness of saturation.  The per-surviving-row comparison uses the
same eraseIdx identity: `rowScore(c; sA i) ≤ rowScore(c'; i)`.

`potential_le_high_of_saturated_one_outlier`: if every anchor ray but
one is < α in the corridor chart, take q = the outlier endpoint; the
surviving θ's attain their max M < α (`Finset.exists_mem_eq_sup'`) and
`angle_eq_abs_of_half_plane_chart` turns pairwise angle bounds into
|θ_i − θ_j| ≤ M.  Residual consequence: θ_{s−2} ≥ α is now REQUIRED —
the residual needs at least two high anchor rays.

Implementation notes: `Finset.sup'_lt_iff` does not exist — used
`exists_mem_eq_sup'`; `Nat.pow_le_pow_right (by omega) h` inside an
un-annotated `have` leaves the base as a free metavariable (omega then
fails on `0 < ?b`) — annotate the have's type or the base; tactic-mode
`calc` absorbs a following `omega` as a bogus step — end the block with
`exact` or `have`+`exact` instead.

### Slack-certificate family (PROVED, axioms clean)

`potential_le_high_of_saturated_slack_family`: generalizes the clump
mechanism to the full certificate family — T rows with occupancy ≤ r
bins and defect ≥ r+1 each give slack 2^{n−r−1}; |T| ≥ 2^{r−1} sums to
2^{n−2}.  Requires the extra cover bound n·width < π−λ (clump's hnwlt)
as an explicit hypothesis; consumers pick width ∈ [W/n, B).
Implementation notes: `Finset.sum_sdiff` orders complement first;
`Finset.sum_const` produces nsmul needing `nsmul_eq_mul` — matching
`T.card * 2^k` forms across hypotheses avoids omega atom mismatch;
`let`-bound config aliases break atom matching against hypotheses —
prefer literal `(c ∘ v.succAbove)` in shared statements.

Phase-shift analysis (NEGATIVE): `uniformBin` supports a start offset,
but the feasible phase window is n·width − W < α < width for m = n and
< nB − W = α for m = n+1 — middle-seated clumps CANNOT be captured by
re-phasing a uniform cover.  The bottom-prefix restriction of the clump
theorem is intrinsic to uniform covers, not an artifact.

### Double-end residual + end-bin obstruction (PROVED, axioms clean)

`potential_le_high_of_saturated_delete_span` (Goal task A): deleting
ANY single non-anchor ray q leaves the anchor saturated; if the
surviving rays have span < (n+1)λ−π, the cap holds.  Instantiating q
at argmin/argmax θ gives the Lead's double-end residual: on the
contradiction domain both θ_{m−1}−θ_1 ≥ α and θ_m−θ_2 ≥ α must hold.
No sorting framework needed — sup'/inf' over erase suffices.

`first_bin_straddles` / `last_bin_straddles` (Goal task B, pure
arithmetic, IntervalPacking.lean): when a full corridor of length
L = π−2λ+θ_m−θ_1 is covered by n bins of width < λ, and the
non-sliver remainder L−lB (resp. L−lT) exceeds (n−1)·width, the first
(resp. last) bin straddles the sliver threshold.

`sliver_threshold_lt_width`: the geometric instantiation — in the
residual regime θ_m−θ₂ ≥ α the first bin's threshold condition gives
θ₂ < width.  Consequence recorded honestly: NO bin is sliver-exclusive
— both slivers live inside boundary bins shared with middle-corridor
chords.  Sliver charging cannot bill a whole bin; it must bill
fractional occupancy.  This closes the "sliver exclusivity → bin
occupancy" route as stated and redirects to fractional/shared-bin
accounting.

`defect_two_rows_le_three` + `four_defect_two_tiling` (volume
rigidity): each defect-2 row with occupancy ≤ 2 contributes cube
volume ≥ 2^{n−2}; ≥ 4 such rows saturate the 2^n budget, so at most
3 can coexist with a fifth non-anchor row.  Equality (4 defect-2 rows)
is a hole-free perfect tiling — the abstract negative control
(1,2,2,2,3) profile is exactly this boundary; Sendov requires a
geometric reason it cannot occur.  This is a precise attack target,
NOT yet a contradiction.

### 2026-09-24b — 五点残余：紧性结构与失败候选记录

**已证（Lean，公理干净）**：
- `potential_le_high_of_saturated_four_eq`：m=4、defect≥2、R≤2 ⟹ cap。
  五点残余 ⟺ R≤2。
- `three_defect_two_rows_tight`：s≥4、|T|=3 defect-2 ⟹ 每行 occ=2（S_i=0 紧性）。
  R≥3 ⟹ 至少三行处此刚性态。

**几何候选评估**：
1. ~~"单侧窗钉扎"~~（已否定）：曾以为 `d_{ij} ∈ [θ_i+π/2, θ_j+π/2]`，
   推导用了 `∠ ≥ λ` 单角下界——但 Section4Legality 只有 `∠ ≤ π−λ`
   （facing_lower 是两角和 ≥λ）。数值复核确认该钉扎为假。
2. 端点窗第二析取为空（正确但无新增量）：对 ty<λ，linRep 取向 2
   （oangle = phi+π）要求 phi ≤ ty−λ < 0，不可实现；取向 1 的低枝
   （phi ≤ tx）需要 Δ=0。故 `d_{ij} ∈ [λ+θ_min, π−λ+θ_max]`——
   与 corridor 全局界等价，不给新约束。
3. **defect-2 行的间隙结构（核心新事实，待形式化）**：
   score = Σ_{g≥λ}(⌊g/λ⌋−1)，Σfloor ≤ n（Σg = π < (n+1)λ）。
   defect=2 ⟺ score = n−2 ⟺ **恰好 2 个间隙 ≥λ 且 ⌊g1/λ⌋+⌊g4/λ⌋=n**
   （或一个内部间隙替代一个端隙）。端隙 g1,g4 ≥λ 恒真
   （方向 ∈ [λ+θ_i·low, π−λ+θ_i·high] 端窗），故内部间隙 < λ。
   剩余和恒等式 g2+g3 = δλ − r1 − r4 < δλ（r = 端隙小数部分）——
   **tight 行的方向跨度 < δλ**。
   推论：δ < (n−2)/(n−1) 时跨度 < w ⟹ occ=1 ⟹ 单行体积 2^{n−1}，
   两行即破预算 → **δ < (n−2)/(n−1) 时 R ≤ 1**（对 n=3 该区间为空，
   n=4 覆盖 δ∈[1/2,2/3)，n→∞ 覆盖几乎全部 δ 域）。
4. 剩余硬核：δ ≥ (n−2)/(n−1)（含 n=3 全域）时 occ=2 可跨一箱界，
   需要针对 (2,2,2,k) 与 (2,2,2,2) 剖面的真实几何排除——
   候选：共享弦 d_{ij} 在两行中的双重紧性、极端行端隙的 floor 钉扎。
