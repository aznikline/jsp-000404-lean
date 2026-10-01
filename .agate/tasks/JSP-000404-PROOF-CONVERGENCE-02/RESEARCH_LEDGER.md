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
3. ~~defect-2 行的间隙结构 → 小 δ 闭合~~（**已撤回**，2026-09-24c）：
   原推导含三处错误，由 Lead 精确反例否定：
   (a) defect=2 有**两支**：Type I（rowBig=1, rowCells=n−1）与
       Type II（rowBig=2, rowCells=n）；Type I 不能省略。
       反例：n=4, δ=3/5, gaps=(3/5,2/5,2/5,16/5)λ → floors=(0,0,0,3)，
       score=2=n−2 但只有一条大间隙。
   (b) "端隙 g1,g4 ≥λ 恒真"为假——端点窗只给 min/max 界，不保证
       首尾 gap 达 λ；端隙 ≥λ 只能作为假设，不能由端窗推出。
   (c) "跨度 < w ⟹ occ=1"为假：跨度 < 箱宽仍可跨一箱界。
       反例：n=4, δ=3/5, w=41λ/50, θ=λ/5, dirs=(51/20,13/5,11/4)λ，
       gaps=(2.35,0.05,0.15,2.05)λ，floors=(2,0,0,2)，span=0.2λ<w
       但 uniform grid 分到 (1,1,2) 三方向占两箱。
   另外跨度上界本身只有 ≤ δλ（两端余数可同时为 0，等号可达：
   gaps=(2,3/10,3/10,2)λ, n=4, δ=3/5 → span=δλ）。
   **δ < (n−2)/(n−1) 子域并未关闭，全部 δ∈[1/2,1) 仍在目标域。**
4. 剩余硬核：需要针对 (2,2,2,k) 与 (2,2,2,2) 剖面的真实几何排除——
   候选：共享弦 d_{ij} 在两行中的双重紧性、极端行端隙的 floor 钉扎。
   → 见 2026-09-24c：共享弦路线已部分实现（排除了"三行全两端大
   间隙"形态），Type I 与内部大间隙 Type II 仍 OPEN。

### 2026-09-24c — 共享弦几何排除：三行全两端大间隙不可能

**新定理（Lean，全部公理干净 `[propext, Classical.choice, Quot.sound]`）**：
- `linearBigCount` / `linearFloorSum` / `linearGapScore_add_bigCount` /
  `linearFloorSum_le_floor` / `linearFloorSum_eq_last_of_bigCount_le_one`
  （IntervalPacking.lean）：linearGapScore 的 floor 分解机制，
  score + bigCount = floorSum ≤ ⌊(right−left)/λ⌋₊。
- **`linearGapScore_span_le_of_big_ends`**：有序非空列表两端 gap 均 ≥λ、
  ⌊(right−left)/λ⌋₊=n、score+2=n ⟹ **跨度 ≤ (right−left) − nλ**
  （非严格——端隙 floor 和恰为 n，余数和 ≥0）。
- **`row_span_le_delta_of_defect_two_ends`**：defect-2 非锚行两端 gap
  ≥λ ⟹ 方向跨度 ≤ δλ = π−nλ。接 `anchored_rowScore_eq_linear`
  （left=θ_i, right=θ_i+π）+ `rowScore_eq_sub_defect`。
- **`three_defect_two_rows_big_ends_impossible`**（Lead 的共享弦论证）：
  三个互异 defect-2 行若各自两端 gap 均 ≥λ，则各行跨度 ≤δλ，
  三条共享弦 a=d_ij、b=d_ik、c=d_jk（dirRep_comm）两两差 ≤δλ，
  全落 [U−δλ, U]（U=max）。对 **Fin 3 子构型** p'=c∘succAbove∘ix
  用 `directionBinGraph_row_weighted_bound` 取 numBins=1、
  width=δλ、start=U−δλ（前提：U≥λ 来自 corridor 下界、
  U<π 来自 corridor 上界、δλ>0 是 hdelta、δλ<λ 由 ⌊π/λ⌋=n≥3），
  得 ∑ 2^{1−occ} ≤ 2，但每项 ≥1 ⟹ 3≤2 矛盾。
  **这是真实几何排除，不是条件包装**；不依赖 δ 阈值或原 n-bin 对齐。
- **`exists_short_end_of_three_defect_two`**（消费）：三个 defect-2 行中
  至少一行首 gap < λ 或尾 gap < λ（push_neg + 上定理）。
- **`short_first_gap_gives_lower`** / **`short_last_gap_gives_higher`**：
  短端 witness 顶点抽取——短首 gap ⟹ head 是到更低 θ 顶点的弦
  （`saturated_row_bot_sliver_forces_low`，t:=θ_r）；短尾 gap ⟹
  getLast 是到更高 θ 顶点的弦（`_top_sliver_forces_high`，u:=θ_r）。
- **`exists_crossing_witness_of_three_defect_two`**：合并版本——
  ∃ r ∈ {i,j,k}, ∃ u ≠ r, θ_u < θ_r ∨ θ_r < θ_u。
- **`first_gap_ge_of_theta_min`** / **`last_gap_ge_of_theta_max`**：
  全局 θ-min 行首 gap ≥λ；全局 θ-max 行尾 gap ≥λ。
  即极值行的短端必指向内侧。

**残余分析（下一轮攻击面，未证）**：
- 短端行 r ∈ {i,j,k}：若短首，witness u 满足 θ_u < θ_r——u 可能是
  第四行 l（则 θ_l < θ_r）或另一 defect-2 行；若短尾对称。
- s=4 子结构：θ-min 行短首 ⟹ θ_l < θ_min（l 沉底）；θ-max 行短尾
  ⟹ θ_max < θ_l（l 置顶）；二者不能同真（θ_l < θ_min ≤ θ_max < θ_l）。
  但 exists_short_end 只保证**至少一行**短端，不能指定极值行。
- 真正缺口仍是 Type I（rowBig=1, rowCells=n−1）与内部大间隙
  Type II 行的几何排除；以及短端 witness 的共享弦兼容性
  （u 行中同一 dirRep 的位置/剩余结构）。

**仍 OPEN（不得声称为已闭合）**：
- Type I（rowBig=1, rowCells=n−1）defect-2 行完全未排除——其唯一
  大间隙可在任意位置，span ≤δλ 论证不适用（floor 和为 n−1，余数
  可大到 δλ 量级之外）。
- Type II 中两大间隙含内部间隙的情形未排除。
- 短端 witness 的下一步消费（端点窗 card≤1 引理）尚未接线：
  短首 gap ⟹ 该行有弦通向更低 θ 顶点；短尾 gap ⟹ 更高 θ 顶点。
- 五点容量最终仍需 R≤2：当前只排除了"三行全两端大间隙"形态。

### 2026-09-24d — 接收弧二分 + 双端接收排除（4055052）

**新定理（Lean，全部公理干净 `[propext, Classical.choice, Quot.sound]`）**：

K3bGeometry.lean（~1968–2246）：
- **`rowDefect_eq_two_type`**：defect=2 完整算术分类（cells≤n, n≥3 域内）——
  Type I: `rowBig=1, rowCells=n−1`；Type II: `rowBig=2, rowCells=n`。
  （Lead 上一轮指出的缺失分支已补上：`B=1,C=n−1` 不可省略。）
- **`rowBig_eq_sum_indicator`**：`rowBig = Σ_{t∈univ} ite(lam≤gapAfter t) 1 0`。
- **`gapAfter_sum_Ici` / `arc_cells_le_arc_wrap`**：环绕弧 `Ici b` 的
  gap 和 = `cyclicDiff l[b] l[0]`；其 floor 加权和 ≤ 弧长。
- **`floor_gap_index_eq_of_cells`**：两个 floor ≥n−1 的 gap 必同索引
  （cells≤n, n≥3 ⟹ 2(n−1)>n）。
- **`defect_two_big_gap_avoids_arc`**（接收弧二分核心）：
  若弧 T 的 floor 和 ≤1 且几何长度 ≥λ，则 Tᶜ 中存在 floor ≥n−1 的
  原语 gap。Type I 直接（唯一大 gap 不能入弧，A<2λ<G≥2λ）；
  Type II 用 `π<(n+1)λ` 反证弧内 floor 和恰为 1。

OneSaturatedHigh.lean：
- **`short_first_arc_floor` / `short_last_arc_floor`**：Lead 的 0→1
  弧关系落地——短首 witness j：源 gap `floor((φ−θ_r)/λ)=0`，目标行
  前缀弧 `φ−θ_j ∈ [λ,2λ)`，`floor=1`，余数预算
  `(λ−g)+(A−λ)=θ_r−θ_j`；短尾对称（`(λ−g)+(A−λ)=θ_j−θ_r`）。
  目标弧是 aggregate（多个原语 gap 之和），未假设为单个 gap。
  下界 `λ≤A` 由 sliver 引理反设给出（`saturated_row_bot/top_sliver`
  contrapositive，不是单独假设）。
- **`defect_two_row_not_receive_both`**：defect-2 行 j 不能同时接收
  ——来自更高 θ 源的短首 witness（θ_j<θ_{i₁}，`φ₁−θ_{i₁}<λ`）与
  来自更低 θ 源的短尾 witness（θ_{i₂}<θ_j，`θ_{i₂}+π−φ₂<λ`）。
  机制：两接收弧（`Ico ⟨0⟩ b₁` 前缀、`Ici b₂` 后缀，端点为实际列表
  元素）各 cells≤1、长度≥λ ⟹ 唯一 floor≥n−1 gap 在两弧补集之交
  `Ico b₁ b₂` 中 ⟹ `b₁<b₂`；三段不交弧总长 ≥λ+(n−1)λ+λ=(n+1)λ>π。
  相交/相接情形不可能（否则 `Ico b₁ b₂` 为空）。

**残余分析（诚实标注，未证）**：
- Type I 本身可出现在真实配置（Lead 五点例 P3 饱和、P4 Type I，
  δ=3/4, K=1, R=1）——本轮排除的是**双端接收组合**，不是 Type I 行。
- R=3：短端 witness 目标可能是第四条高缺陷行（例中短尾指向
  defect=4 行）——双端排除只在目标也是 defect-2 时触发。
- R=4：≥2 短端行（`exists_two_short_end_rows_of_four`），但两行的
  短端类型可相同、目标可不同——双端排除需要"相反类型短端指向同一
  defect-2 目标"才触发。lower/higher 链可交替，有限链论证不能
  直接闭合。
- Type II 内部大间隙模式仍未排除（span 论证不适用）。
- 五点最终目标仍是 R≤2；当前获得的是接收端结构性约束。

### [2025-xx] Type I 传播引理 + 链终结（commit 8e0b7eb + 本轮）

OneSaturatedHigh.lean（全部公理 [propext, Classical.choice, Quot.sound]）：
- **`type_I_first_receiver_is_first_short`**：Type I defect-2 行
  （rowBig=1）接收来自更高 θ 源的短首 witness ⟹ 自身首 gap <λ。
  机制：接收前缀弧 `Ico ⟨0⟩ b₁` cells≤1 且长度≥λ ⟹ 唯一
  floor≥n−1 大 gap 在弧外（`defect_two_big_gap_avoids_arc`）；
  Type I 只允许一个大 gap（rowBig=1 的 indicator 计数），故
  索引 0 的 gap 非大 ⟹ `gapAfter l ⟨0⟩ <λ`；经
  `List.get_of_eq`/`get_cons_succ`/`get_mk_zero` 传输到
  子行 `head`。
- **`type_I_last_receiver_is_last_short`**：对称短尾版——接收
  环绕后缀弧 `Ici b₂` 中，末索引 `⟨len−1⟩` 的 wrap gap 非大
  ⟹ `θ_j+π−sub.getLast <λ`。`getLast` 跨 `hcons` 传输用
  `List.getLast?_cons_of_ne_nil` + `getLast?_eq_getLast`
  （Option API 无依赖索引，绕开 rw motive 问题）。
- **`type_I_first_witness_leaves_type_I`**：Type-I-defect-2 短首行
  集合中取 θ 最小者，其短首 witness 必**不**是 Type-I-defect-2
  ——否则传播给目标短首端，与极小性矛盾。即 Type I 短首链
  必然离开 Type-I-defect-2 集合（落到 Type II defect-2 或
  高缺陷行）。
- **`type_I_last_witness_leaves_type_I`**：对称——θ 最大 Type-I
  defect-2 短尾行的短尾 witness 必离开 Type-I-defect-2。

工程记录：`List.get_of_eq`/`List.get_cons_succ`/`List.get_mk_zero`
是跨 `l = a::sub` 等式传输 `l.get` 的正规接口（`rw [hcons]` 对
依赖 Fin 索引会 motive 失败）；`List.getLast?_cons_of_ne_nil` 是
`getLast` 的 Option 版本，同样绕开依赖证明参数。

**残余（更新）**：链终结把"短首 witness 指向谁"二分成了
(Type II defect-2 / defect≥3)。R=3 剩余工作：
- Type I 短端链落到 **Type II** defect-2 目标——需 Type II 侧的
  接收预算（弧内恰一 q=1 大 gap、弧外 q=n−1 大 gap；
  `R_out/λ+ρ_G+ρ_arc=δ`）及其与 `defect_two_row_not_receive_both`
  的组合排除。
- 落到 **defect≥3 第四行**的情形——需要 defect≥3 行的
  接收弧结构（大 gap 计数≥2 时的广义版本）。
- R=4 情形未动：两短端行不共享目标、方向可同。

### [2025-xx] Type II 接收弧结构 + 外侧预算（本轮，K3bGeometry）

K3bGeometry.lean 尾部新块（全部公理 [propext, Classical.choice, Quot.sound]）：
- **`rowDefect_eq_two_type`**：defect-2 二分——`rowBig=1 ∧ cells=n−1`（Type I）
  或 `rowBig=2 ∧ cells=n`（Type II）。`rowScore = cells − rowBig` 直接给。
- **`rowBig_eq_sum_indicator`**：rowBig 的 `Fin l.length` indicator 求和形式，
  供 `Finset` 位置论证用。
- **`gapAfter_sum_Ici`**：`∑_{t ∈ Ici b} gapAfter l t = gapAfter 环绕段`，
  `Ico_union_Ico_eq_Ico` 拆分 `univ = Ico 0 b ∪ Ici b`。
- **`arc_cells_le_arc_wrap`**：环绕弧 `Ici b` 的 cell 界（`arc_cells_le_arc`
  的 `Ico`-wrap 对偶）。
- **`floor_gap_index_eq_of_cells`**：cells 总和 ≤ n 时，floor ≥ n−1 的
  gap 索引**唯一**（两个 n−1 段已占 2n−2 > n cells）。
- **`defect_two_big_gap_avoids_arc`**：defect-2 行 + 弧 T cells ≤1 且
  弧长 ≥λ ⟹ `Tᶜ` 中存在 floor ≥ n−1 的原语 gap。机制：若 Tᶜ 全
  floor ≤ n−2，则 Tᶜ cells ≤ (len−1)(n−2)+……⟹ 总长 < π 矛盾；
  精确预算走 `Σ_{Tᶜ} floor = cells − Σ_T floor`。
- **`defect_two_outer_budget`**（Lead 的 `R_out/λ + ρ_G + ρ_arc = δ`
  预算的 Lean 形式）：接收弧 cells≤1、弧长≥λ ⟹ ∃ `s_out ∈ Tᶜ`，
  `floor(s_out) ≥ n−1` 且 `∑_{t∈Tᶜ, t≠s_out} gapAfter ≤ π − nλ`。
  机制：`Σ_{Tᶜ} floor = n−1`（cells 精确分配），`s_out` 独占 n−1
  ⟹ `Tᶜ\{s_out}` floor 全 0 ⟹ 各 gap <λ；几何预算由
  `π = Σ_T + Σ_{Tᶜ}`、`Σ_T ≥ λ`、`s_out ≥ (n−1)λ` 拆出。
- **`defect_two_type_II_arc_structure`**：Type II（cells=n, rowBig=2）
  接收弧的**完整二分**——`Σ_T floor = 1`（否则 Tᶜ 含全部 n cells，
  弧外 nλ + 弧 λ > π），故 ∃ `s_in ∈ T` floor=1（弧内恰一大 gap）、
  `s_out ∈ Tᶜ` floor=n−1；且 T 内其余与 Tᶜ 内其余 gap **全部 <λ**。
  证明：`sum_sdiff` 把 `Σ_{T} = 1` 拆成 `{s_in}` + `T\{s_in}`，
  后者 =0 ⟹ `Nat.floor_eq_zero` + `div_lt_one` 逐点 <λ；Tᶜ 侧同理。

工程记录：`\` 非结合——`(univ \ T) \ {s}` 必须加括号；
`∑ t ∈ X, f = 0` 会把 `= 0` 吞进 sum 体（AddCommMonoid Prop 失败），
写 `(∑ t ∈ X, f) = 0`；`∑` 拆出单元素用
`Finset.sum_sdiff (s₁ := {x}) (s₂ := X)` + `sum_singleton`。

**残余（更新）**：Type II 接收结构现在与 Type I 传播
（`type_I_first/last_receiver_*`）对等——两条链都能把"接收短端"
推进成"目标行承担哪段弧/哪个大 gap"。下一消费点：
- R=3：Type I 短端链落到 Type II 目标 ⟹ 目标的 `s_in`/`s_out`
  结构 + `defect_two_row_not_receive_both` 是否给出第三条
  短端或共享大 gap 的强制重合；
- witness 落到 defect≥3 第四行的情形（高缺陷行接收结构未建立）；
- R=4：两短端行不共享目标/方向。

### [2025-xx] Type II 三分传播 + 全类型链分类（本轮）

OneSaturatedHigh.lean（全部公理 [propext, Classical.choice, Quot.sound]）：
- **`type_II_first_receiver_trichotomy`**：Type II defect-2 行
  （rowBig=2）接收来自更高 θ 源的短首 witness ⟹ 三分——
  (a) 自身短首（`sub.head − θ_j < λ`），或
  (b) 自身短尾（`θ_j + π − sub.getLast < λ`），或
  (c) 两端皆大：弧内 `s_in` 恰好落在索引 0（floor=1）且弧外
  `s_out` 恰好落在末索引（floor=n−1）。
  机制：`defect_two_type_II_arc_structure` 把接收前缀弧
  `Ico ⟨0⟩ b₁` 的结构展开——索引 0 必在弧内（≠s_in 即 <λ）、
  末索引 `⟨len−1⟩` 必在弧外（`b₁.val ≤ len−1`，≠s_out 即 <λ）。
- **`type_II_last_receiver_trichotomy`**：对称——接收环绕后缀弧
  `Ici b₂` 时末索引必在弧内、索引 0 必在弧外（`b₂>0`，否则
  `Ici 0 = univ` 与 `s_out` 存在矛盾）；两端大分支 floor 交换
  （首=n−1，尾=1）。
- **`defect_two_first_witness_classification`**：在**全部** defect-2
  短首行（不限 Type I/II）中取 θ 最小者 j——其短首 witness
  （`dirRep j w = sub.head`, θ_w < θ_j）若落到 defect-2 目标 w，
  则 w 必为 **Type II 且短尾或两端大**。证明：w 为 Type I ⟹
  传播回短首 ⟹ w∈T 与极小性矛盾；w 为 Type II 短首分支同理；
  只剩 Type II 的另两支。这把旧 `type_I_first_witness_leaves_type_I`
  （仅限 Type I 源）升级为全 defect-2 链分类。
- **`defect_two_last_witness_classification`**：对称——θ 最大
  defect-2 短尾行的 witness 落到 defect-2 ⟹ Type II 且
  短首或两端大（首=n−1，尾=1）。

**残余（更新）**：短端链在 defect-2 集合内的"出口"已完全分类：
- 短首链下降出 Type-I 后，若继续留在 defect-2，只能进入
  Type II 的短尾行或两端大行——即链**转向**（短首⟶短尾/两端大），
  或离开 defect-2 集合（第四行 defect≥3 / 锚）。
- 两端大行有 `row_span_le_delta_of_defect_two_ends`（跨度≤δλ）
  与 `three_defect_two_rows_big_ends_impossible`（至多两行）。
- 尚缺：短尾行再发 witness 时的下一跳约束（短尾 witness 指向
  更高 θ——其目标的 Type II 结构是 `Ici` 弧版本，三分已备）；
  Type-II-出口行的短尾 witness 是否又必须回到短首行——若形成
  强制交替，R=3 的五行计数矛盾就闭合。
- witness 落到 defect≥3 第四行的情形仍未排除；R=4 未动。


## Type II no-return lemmas (immediate witness 2-cycles excluded)

- `type_II_short_last_witness_ne_source`: a Type II defect-2 row j
  receiving a short-first witness from a higher-θ source i₁ and itself
  short-last cannot have `dirRep j i₁` as its last row element. If the
  last element were φ₁, the receiving arc complement collapses to
  `{lastIdx}`, forcing `s_out = lastIdx` with floor n−1 ≥ 2λ gap
  length — against the short-last hypothesis (<λ).
- `type_II_short_first_witness_ne_source` (mirror): a Type II row
  receiving a short-last witness from a lower-θ source and itself
  short-first cannot have `dirRep j i₂` as its first element (arc
  `Ici ⟨1⟩` complement = {⟨0⟩}).
- Consequence: the witness relation restricted to defect-2 rows has no
  2-cycles through the SAME short end of the Type II receiver. A Type II
  short-last receiver that is itself short-last points its witness at a
  third vertex, not back at the source.
- Both proved: `[propext, Classical.choice, Quot.sound]`, no sorryAx.
- Remaining: assemble R=3 contradiction (chain alternation lower/higher
  still needs a real descent or closure argument; R=4 target-sharing
  and higher-defect target analysis open).


## Generalized no-return + packaged 2-cycle + extremal exit (this round)

- `defect_two_short_last/first_witness_ne_source`: the Type II
  no-return lemmas generalized to ALL defect-2 receivers (Type I+II) —
  `defect_two_big_gap_avoids_arc` needs only `rowDefect = 2`, no
  `rowBig` hypothesis. Type-I-specific hypothesis dropped.
- `defect_two_witness_no_two_cycle`: packaged exclusion — rows a<b
  (theta-order) cannot be mutual short-end witnesses (a last-witnesses
  b AND b first-witnesses a). Direct consumer of no-return.
- `first_witness_of_min_defect_two_high` / `last_witness_of_max_defect_two_high`:
  extremal exit — the theta-min defect-2 row's short-first witness
  (resp. theta-max's short-last witness) has defect >= 3 (leaves the
  defect-2 set, global defect >= 2 hypothesis). In five-point R=3 the
  witness is the unique high-defect row.
- All proved: [propext, Classical.choice, Quot.sound], no sorryAx.


## Zigzag ordering lemmas (direction preservation in alternating chains)

- `defect_two_last_recv_head_lt`: defect-2 row j receiving a short-last
  witness from lower-theta i2 and itself short-first satisfies
  `head_j < dirRep j i2` — the outgoing first-witness chord sits
  strictly below the incoming shared chord. Proof: phi2 sits at index
  b2 >= 1 (index 0 is theta_j); sortedness gives l[1] <= l[b2] = phi2;
  strictness by defect_two_short_first_witness_ne_source.
- `defect_two_first_recv_getLast_gt` (mirror): receiving short-first
  from higher i1 and itself short-last gives dirRep j i1 < getLast.
- CORRECTED SCOPE (2026-09-25, Lead review): the two lemmas are
  single-step chord orderings with OPPOSITE directions
  (last-recv->first-send: out < in; first-recv->last-send: in < out).
  They are NOT a chain-wide monotone quantity (1<4>2<5>1 is consistent).
  Long-cycle exclusion is supplied instead by projection descent below.
- Both proved: [propext, Classical.choice, Quot.sound], no sorryAx.
- Remaining: R=3 assembly still needs (i) defect>=3 receiving-arc
  budget for the fourth row, (ii) three-defect tightness (occ=2)
  consumption to kill the remaining alternating-cycle / pass-through
  patterns, (iii) R=4 target-sharing.


## Float probe: R>=3 in real five-point R-HIGH1 (EMPIRICAL, not a proof)

- tools/rhigh1_R3_probe.py: random + perturbation of the packet example
  (P0..P4, lam=4pi/23), hill-climb maximizing R, lam scanned over
  n in 3..7, delta in [0.5, 0.98] step 0.02, lam <= pi - max triangle
  angle; near-threshold gaps rejected.
- seed 1, 300 restarts: {-1:277, 0:10, 1:11, 2:2}.
- seed 7, 200 restarts (150-step climb): {-1:128, 0:14, 1:52, 2:6}.
- No R>=3 config found among 95 R-HIGH1 hits (restricted grid
  n=3..7, delta step 0.02, climb end-states; diagnostic only, no
  confidence quantification; same-type restarts STOPPED).  Consistent with the
  target R<=2; float only, so it is evidence, not a certificate.


## Projection descent (Jsp000404/ProjectionDescent.lean, 2026-09-25)

All `[propext, Classical.choice, Quot.sound]`; module build
`lake build Jsp000404.ProjectionDescent` PASS (8955 jobs, module, not
full-root).
- `acute_margin_of_floor`: n=floor(pi/lam)>=3 => beta+lam < pi/2
  (beta = pi - n lam), via pi < (n+1)lam <= 2(n-1)lam.
- `short_first_inner_neg` / `short_last_inner_neg`: pure geometry.  The
  lift branch is decided by the endpoint caps (`directed_chord_in_corridor'`,
  local copy of the private ConeCorridor lemma): short-first => direct
  branch would force phi >= t_X + lam, so oangle e (Y-X) = phi - pi and
  cos phi > 0 (phi < beta+lam < pi/2); short-last => reversed branch would
  force phi <= pi - lam + t_X, so oangle = phi with phi in (pi/2, pi).
  Either way <e, Y - X> < 0.  Nonzero vectors from legality injectivity.
- `ShortWitness` (any chord in the short first/last window of the source
  row, no defect hypothesis) and `shortWitness_projection_lt`:
  Psi j < Psi i, Psi i = <e, P_i - A>.
- `shortWitness_no_cycle`: TransGen ShortWitness is irreflexive —
  short-end witness cycles of every length excluded.
- `psi_min_row_ends_big`: the Psi-minimal non-anchor row has both end
  gaps >= lam.
- LIMITS: acyclicity alone does not give R<=2; chains may terminate at a
  defect-2 row with both end gaps big.  n=2 not covered (hn3).


## Full-in star receivers (Jsp000404/StarReceiver.lean, 2026-09-25)

All `[propext, Classical.choice, Quot.sound]`; module build
`lake build Jsp000404.StarReceiver` PASS (8956 jobs, module, not full-root).
Exact regression: tools/star_receiver_regress.py (packet c=3 local
example + 7996 rational grid cases, local gap model only).
- `gapScore_eq_zero_of_lt` (g < 2lam), `gapScore_eq_of_mem`
  ([(k+1)lam, (k+2)lam) -> k).
- `star_chord_window`: an incoming short chord j -> h lies in row h in
  F = [theta_h + lam, beta + lam) with theta_h < theta_j (short-first
  source) or L = (pi - lam, pi - lam + theta_h] with theta_j < theta_h
  (short-last source).  Proof by the two sliver bridges applied in rows
  j and h.
- `star_linear_score_one_sided` / `star_linear_score_mixed`: on the
  actual sorted row (linearGapScore theta_h (theta_h+pi)), in-window gaps
  score 0; one-sided -> n-2 (the single floor-(n-1) end gap); mixed ->
  n-3 (F->L gap is a genuine primitive gap of floor n-2, both ends floor
  1).  No whole-arc floor is charged as a primitive cell.
- `star_receiver_defect` (any s >= 2): if every other non-anchor vertex
  has a short chord into h, then c_h = 3 when both sides occur and
  c_h = 2 otherwise.
- `star_receiver_high_is_mixed`: a full-in star receiver with c_h >= 3
  is mixed and c_h = 3 (profile pinned to (1,2,2,2,3) at five points
  when the three sources are the defect-2 rows).
- NOT done this round: the general union-of-arcs budget
  c_h >= p + B_out for partial receivers (1 or 2 incoming, third chord
  unclassified) -- remains OPEN; star hypothesis is NOT assumed for
  general R=3 configurations.
- NEXT: exclude the mixed star using the three source rows' occ=2
  tightness and shared chords.


## JSP404-MIXED-STAR-EXCLUSION-01 (Jsp000404/MixedStarExclusion.lean)

CLOSED branch (five points, s = 4): a receiver H of defect >= 3 whose
three other non-anchor rows have defect 2 cannot receive short chords
from all three (`five_point_high_receiver_not_full_in`).  Full-root
build PASS (9003 jobs); see MIXED_STAR_BUILD.md, MIXED_STAR_AXIOMS.txt.

Geometry toolkit (general s):
- `Up a b`: actual edge P_b - P_a has oriented angle exactly phi_ab in
  [0, pi).  `up_or_up` (one orientation always), `up_corridor`
  (phi_ab in [theta_a + lam, pi - lam + theta_b]), `up_of_short_first`
  (short-first chord at a points down: Up b a), `up_of_short_last`
  (Up a b).  The lift is derived, never assumed.
- `oangle_add_between`: sum of two nonzero vectors with directions
  alpha < beta < alpha + pi has direction strictly between (sign of
  oangle via oangle_sign_add_left/right).
- `up_trans`: Up a b, Up b c => Up a c and phi_ac strictly between
  phi_ab and phi_bc (no wrap branch: all directions in (0, pi)).
- `up_cap`: source-triangle cap at the middle vertex:
  angle(a,b,c) = pi - |phi_bc - phi_ab| <= pi - lam.
- `row4_defect` (s = 4): three distinct sorted chords => rowDefect +
  sum of the four actual gap scores = n (row list identified exactly).

Cores (Lead route, all order facts derived from the toolkit):
- `mixed_star_2F1L_core` (P, Q short-first, R short-last, Up P Q):
  u < vv < z (wrap branch killed by the P-Q corridor), u < x < w,
  vv < y < w, y between x and z, |z - x| >= lam.
  Branch z < x: row P has 3 big gaps (last gap >= lam from the R-P
  corridor) => defect >= 3.  Branch x < z: row R forces x - theta_R >=
  2 lam; then row P forces its last gap < lam; then row Q pins its huge
  gap at z - y and the total exceeds (n+1) lam.
- `mixed_star_1F2L_core`: explicit mirror proof (not transported).
- `mixed_star_2F1L` / `mixed_star_1F2L`: orientation of P Q split by
  `up_or_up`, both cases proved.
- Note: the packet's separate lemma "opposite-side sources cannot
  exchange short chords" was not needed as a standalone theorem; the
  needed consequences (x - theta_P >= lam, theta_Q+pi-y >= lam) come
  from row R's defect-2 constraint inside the cores.  The standalone
  form remains NOT formalized.

Still OPEN: R=3 with 0/1/2 incoming edges at the high row; chains
ending at a low-defect row with both end gaps big; R=4 patterns; the
general union-of-arcs receiver budget c_h >= p + B_out; general m.

## 2026-09-26 (continued) — deletion rigidity + two-in normal form

Owner branch, commits 32869ea, 7ab157b, f5a271f, 0be7313 in
`Jsp000404/DeletionRigidity.lean` (wired into `Jsp000404.lean`).

Deletion rigidity (Lead packet DELETION-RIGIDITY-PARTIAL-RECEIVER):
- `deletion_rigidity`: saturated anchor + defect-2 row `i` + surviving
  defect-2 row `j`, delete any other non-anchor `q` (reduced config
  still `>= 4` points) -> `i` keeps score AND defect 2. Proof: if `i`
  became saturated, `rowScore_add_three_le_of_two_saturated` gives
  `k'_j + 3 <= n`, contradicting monotone `k'_j >= n-2`. Scoped: anchor
  not deleted, second defect-2 row required, no iteration to 3 points.
- Five-point consumers `five_point_merge_zero_{first,mid,last}`: merge
  gain at every non-anchor chord position is 0; `five_point_no_adjacent_big`
  -> no two linearly adjacent big gaps. Type II big-gap positions
  confined to {0,2},{0,3},{1,3}; Type I untouched.
- `five_point_delete_high_potential`: R=3, delete the high-defect row
  -> reduced potential exactly `5 * 2^(n-2)` (equality datum only).

Two-in receiver normal form (packet section 2):
- `linScore_split_{low,mid,high}`: exact one-insertion identity
  `score_full + mu = score_reduced` per gap slot.
- `two_in_{F,L,mixed}_row`: slot trichotomy; outer reduced gaps `< 2lam`
  give `mu = 0` via `mergeGain_eq_zero_of_lt`, so defect growth pins `z`
  into the unique long gap. `two_in_{F,L}_{above,below}` (defect <= 4),
  `two_in_mixed_between` (defect <= 5), `two_in_mixed_five` (mu=2,
  pieces >= lam, floor carry, n >= 5), `two_in_mixed_ge_three`.
- Caveat recorded: `dirRep h t` distinctness from the two received
  directions is an explicit hypothesis, not derived.

Axioms: all 22 decls `[propext, Classical.choice, Quot.sound]`; no
sorryAx. Module build PASS 8963 jobs. Full root `lake build` at tested
code SHA 0be7313 (evidence commit c5a8d28 docs-only on top): PASS,
9004 jobs, exit 0 -- raw output was not persisted to disk; the result
was recorded in-session only (see DELETION_RIGIDITY_BUILD.md).

Still OPEN (unchanged + new): the cross-row transport "mu_h >= 1 =>
some source row mergeGain > 0" (packet step 4) is NOT yet formalized;
also 0/1-in at the high row, low-defect chain endpoints, R=4,
union-budget consumer, general m, M3/M4. Air challenge PENDING.

## 2026-09-26 (continued-2) -- direction distinctness + zero-carry arithmetic

Owner branch, commits a611ba8 (central exclusion), 5cb8da6
(direction distinctness), plus FivePointZeroCarry module.

- `legal_dirRep_ne` (MixedTwoInCentral): equal outgoing `dirRep`
  values force the chord `oangle` to `0`/`pi`, hence collinearity,
  contradicting `Section4Legality.triAngle`. `SatChart.hleg_sub`
  restricts legality to `c . v.succAbove`.
- `two_in_mixed_central_exclusion` no longer takes `z != u`, `z != w`
  as hypotheses -- derived via `legal_dirRep_ne`. Net closed result:
  five-point R=3 mixed two-in at high row `H` forces `c_H = 3` and
  `z < u` or `w < z` (outer positions only).
- `mergeGain_eq_zero_iff_frac` / `_frac'` / `_frac_lt{,'}`
  (FivePointZeroCarry): for `x < lam <= y`, `mergeGain x y = 0` is
  exactly the no-carry condition `x + frac_lam(y) < lam`, i.e.
  `x + (y - floor(y/lam)*lam) < lam`. This upgrades deletion rigidity
  output from "not both big" to a per-direction remainder budget that
  can be summed across shared chords.

CLOSED (cbeef48): mixed outer `c_H = 3` exclusion -- both outer
positions proved impossible. `mixed_two_in_outer_low` / `_outer_high`
(MixedTwoInCentral): `Up(H,Q)` branches die to cap `|z - w| >= lam`
forcing `z > pi` (resp. `z < 0`); of the `Up(Q,H)` leaves, three kill
directly via `five_point_no_adjacent_big`; the two score leaves
(`y < x < t` / mirror) concentrate one defect-2 row's score on a
single gap (`(n-1)lam <= g`), which overflows a corridor bound after a
split on `floor((theta_P + pi - t)/lam)`. Note: the actual certificate
was score-concentration + corridor overflow, not the remainder-carry
summation; `mergeGain_eq_zero_iff_frac` remains available but was not
the sharp tool here. `mixed_two_in_excluded` combines central + both
outers: mixed two-in at a high row is IMPOSSIBLE in five points.

Still OPEN: same-side two-in; 0/1-in; low-defect endpoints; R=4;
general m. Air challenge PENDING.

## 2026-09-30 -- same-side two-in CLOSED + receiver indegree <= 1

Owner branch `agent/jsp404-air-emergency-owner-20260928` (worktree
`jsp-wt-air-owner`), commits `e550d69` (F/F), `323a036` (L/L),
`fcbd199` (aggregate).  `Jsp000404/SameSideTwoIn.lean`, module build
PASS (8965 jobs); all three head theorems axiom-clean
`[propext, Classical.choice, Quot.sound]`.

- `same_side_two_in_F`: two F-side short witnesses into a defect>=3
  receiver impossible.  16-chord-orientation enumeration reduces to
  the T-source leaf (`Up T H, T A, T B, A B`); that leaf splits on
  `theta_T <= theta_H` (defect-arithmetic kill) vs `theta_H < theta_T`
  (triangle (H,A,T) sine closure + two Robin Hood transfers).
- `same_side_two_in_L`: the mirror for two L-side (below-receiver)
  witnesses.  Residual is the A-source leaf (`Up A B, A H, A T, B H,
  B T, H T`): `theta_T <= theta_H` dies to the same sine-closure
  mechanism; `theta_H < theta_T` is a floor/defect kill -- `A->B->T`
  betweenness splits `p<x<y` (row B alone dies; when `w-y < lam` row
  T's last-gap floor collapses to 1 leaving defect-2 no witness) and
  `y<x<p` (row B alone).
- `five_point_receiver_indegree_le_one`: aggregate -- a defect>=3
  receiver in the R=3 five-point SatChart admits AT MOST ONE short
  witness (F/F, L/L, or mixed via `mixed_two_in_excluded`).  This
  upgrades `five_point_high_receiver_not_full_in` (indeg <= 2 of 3)
  to indeg <= 1 outright.
- z3 branch-synthesis tool for L/L added at
  `tools/same_side_two_in_ll.py`; kill certificates for every dead
  leaf were machine-extracted before the Lean encoding.

Closes the "same-side two-in" and "2-in" items.  Still OPEN: 0/1-in
at the high row (receivers with zero or one short witness), low-defect
chain endpoints, R=4 patterns, general m, M3/M4.  Air challenge
PENDING.

## 2026-10-01 -- five-point defect-profile closure via theta-order pair-kill

Owner branch `agent/jsp404-air-emergency-owner-20260928`, commits
`06b9a3a` (pairkill x3), `549bed8` (R3), `b10c330` (R4), `2bd9f4d`
(R>=3 assembly).  New module `Jsp000404/R3WitnessDag.lean`
(~2900 lines); module + full-root build PASS (8966 jobs); all six head
theorems axiom-clean `[propext, Classical.choice, Quot.sound]`, no
sorry/admit.

- `up_theta_lt` (MixedStarExclusion): `Up a b` implies
  `theta a < theta b` via `oangle_add_between` -- `Up` IS the strict
  theta order, so the defect profile alone (no witness DAG) already
  over-determines each defect-2 row's fan.
- `pairkill_{outer,midtop,midbot}`: for a defect-2 pair `a <_theta b`
  with two outsiders `x,y`, each lemma enumerates the 16 `up_trans`
  worlds of its theta configuration
  (`x a b y` outer / `a x b y` midtop / `y a x b` midbot).
  Worlds die three ways: pure order cycles (`linarith`),
  `r3_fan_overflow` on three cap-forced big gaps, or
  `r3_fan_trich_{lo,t3,hi,t4}` signature cells closed by integer
  squeeze (real corridor bounds multiplied by lam, cast to Nat floor
  bounds, `omega`).  Kill certificates for all 48 x 12 signature
  cells were z3-extracted per beta/n parameter region before encoding.
- `five_point_R3_impossible`: `fin_cases` on the defect>=3 row plus a
  6-comparison theta decision tree (64 leaves, 24 consistent total
  orders) dispatches to the appropriate pairkill by the high row's
  rank.  Profile (2,2,2,>=3) is IMPOSSIBLE.
- `five_point_R4_impossible`: all four non-anchor rows defect-2 --
  the theta-middle pair always has extremes on opposite sides, so
  `pairkill_outer` suffices.
- `five_point_R_ge_three_impossible`: card(T_defect2) >= 3
  assembles both -- FIVE_POINT_CLOSED at the SatChart level.

This supersedes the planned DAG-witness enumeration route
(`tools/r3_witness_dag.py` artifacts retained for audit): the
theta-order kill needs no witness chains at all.

Still OPEN (per owner plan): consumption into `CertExists` for
t = 5 (SatChart bridge: saturated anchor + defect accounting),
arbitrary-m lift, M3/M4, `MainTheorem.sendov_lower`.  Air challenge
PENDING.

## 2026-09-30 (continued) — slack accounting + residual occupancy constraints

Owner branch, commits `606188e` (delete_pair), `4d240e5` (slack_sum /
strict_slack), `86e9ef3` (contrapositive occupancy constraints).
All in `Jsp000404/OneSaturatedHigh.lean`; every new declaration
axiom-clean `[propext, Classical.choice, Quot.sound]`, no sorryAx.

New capacity consumers (arbitrary s, saturated anchor):
- `potential_le_high_of_saturated_delete_pair`: delete two rows with
  combined weight `2^{k1}+2^{k2} <= 2^{n-2}`; if surviving anchor rays
  span < alpha = (n+1)lam - pi, cap holds.  Defect>=3 pairs meet the
  cost bound automatically; residual premise is only the post-deletion
  narrow window.
- `potential_le_high_of_saturated_slack_sum`: GENERAL slack form —
  over any valid uniform n-bin cover, S_i = 2^{n-a_i} - 2^{n-d_i} >= 0
  is additive; Sigma_T S_i >= Q over ANY family T closes the cap.
  Subsumes slack_family; partial margins accumulate.
- `potential_le_high_of_saturated_strict_slack`: corollary — family
  with occ_i+1 <= d_i and Sigma_T 2^{n-d_i} >= Q.  A single defect-2
  row at occ <= 1 already carries Q.

Residual-domain consequences (contrapositives, PROVED):
- `occupied_bins_le_rowDefect`: a_i <= d_i always.
- `slack_sum_lt_of_potential_gt`: violation => Sigma_T S_i < Q for
  every T in every valid cover.
- `defect_two_occupancy_eq_two_of_potential_gt`: violation => every
  defect-2 row perfectly packed (occ = 2).  Its directions lie in
  exactly 2 uniform bins — a new geometric restriction on the
  theta-extreme low-defect rows (consistent with Type I two-cluster
  form; makes Type II interior-big-gap instances even tighter).
- `defect_three_strict_pair_excluded_of_potential_gt`: violation =>
  at most one defect-3 row can have occ <= 2.

SHARPENED LIVE BLOCKER (r=2 tail, unchanged in substance): supply a
family T with strict occupancy margins summing Sigma_T 2^{n-d_i} >= Q,
or equivalently find two defect>=3 rows at occ <= 2 in the SAME cover.
What the residual domain now provably looks like: defect-2 rows
perfectly packed at occ = 2, at most one defect-3 row at occ <= 2,
total slack < Q in every uniform cover.  The geometric input must
either break perfect packing of an extreme defect-2 row or produce a
strict margin on a high-defect row — both remain OPEN.

## 2026-10-01 — R2: anchor deletion, extreme-receiver clump, BETWEEN collapse

Owner branch, commits `90b88c3` (anchor promotion + min clump),
`e98081f` (BETWEEN trichotomy), `9732709`/`aa2cd31` (strengthening +
axiom audit).  New capacity chain lives in `FivePointCapacity.lean`
(module direction: needs both `OneSaturatedHigh` and
`TwoSaturatedHigh`); the geometric promotion lemma
`rowDefect_succAbove_eq_one_of_big_ends` stays in `OneSaturatedHigh`.
All new declarations axiom-clean `[propext, Classical.choice,
Quot.sound]`; full root build 9010 jobs PASS.

What was proved (arbitrary s, saturated anchor v, defect-2 rows a<b
in theta):

- Anchor-deletion promotion: `rowDefect_succAbove_eq_one_of_big_ends`
  — if row i has both anchored end gaps >= lam, deleting v makes it
  saturated (defect 1 after deletion).  Mechanism: anchor chord is the
  row's FIRST element (`directionRow_anchor_cons`), so erasing it merges
  exactly the two end gaps; `mergeGain_pos_of_ge` + `rowGain` gives
  +1, and the defect-2 ceiling forces equality.
- Double promotion: `potential_le_high_of_saturated_two_low_big_ends`
  — both low rows double-big-ended => after deleting v both saturate =>
  `potential_le_high_of_two_saturated` closes.  Contrapositive used in
  emission: over-capacity => some anchored end bound fails.
- Min-receiver clump: `potential_le_high_of_saturated_min_receiver_clump`
  — theta-min defect-2 row + all elements <= theta+pi-lam (big last end)
  + some element < theta+2*lam => first floor 1, last floor n-1 (new
  pin lemma `linearGapScore_last_le_of_big_ends_floor_one` in
  IntervalPacking), whole row in [theta+lam, theta+lam+beta],
  beta < w0 = (pi-2*lam+beta)/n, occupancy 1 => slack_sum cap.
  Re-reference e' = P_h - A (theta'_h = 0) via reference_shift +
  projectiveShift; theta'_i = theta_i - theta_h stays in [0,beta]
  BECAUSE h is theta-min — the asymmetry that complicates the mirror.

- BETWEEN emission: `between_residual_emission` — four-end failure
  split; a-first/b-last contradicted by extremal-gap lemmas
  (`short_first_gap_gives_lower`/`short_last_gap_gives_higher` + theta
  extremality).  Remaining: tail emission (low -> defect>=3 interior
  row) or low-low short ends (a-last->b, b-first->a).

- BETWEEN strengthened: `between_residual_tail_or_top`.
  * b-first->a ELIMINATED: if a short-last, no-immediate-return
    (`defect_two_short_last_witness_ne_source`) forces a's last witness
    off {a,b} => tail; if a big-last, dirRep a b = dirRep b a <
    theta_b+lam <= theta_a+beta+lam < theta_a+2*lam feeds the
    min-receiver clump => cap contradiction.
  * a-last->b splits: b short-first => first witness exits {a,b}
    (`defect_two_short_first_witness_ne_source`) => tail; else explicit
    TOP-CLUMP DATUM: b theta-max, defect-2, all elements in
    [theta_b+lam, theta_b+pi-lam], shared chord dirRep b a >
    theta_b+pi-2*lam.

Residual analysis (NOT yet a theorem): the top-clump datum would pin
row b into [theta_b+(n-1)*lam, theta_b+pi-lam] (width beta, near the
corridor top).  Under any corridor-anchored uniform cover — bins
[s+k*w0, s+(k+1)*w0), k=0..n-1, with the slack_sum requirement that the
corridor [lam, pi-lam+beta] ⊆ [s, s+n*w0] — single-bin containment of
the top clump is feasible iff theta_b > 2*beta - lam (derivation: bin
n-1 needs s <= theta_b+(n-1)*(lam-w0) and s+n*w0 >= (n-1)*lam+2*beta;
with s <= lam the binding constraint becomes w0 >= 2*beta - theta_b,
forcing theta_b > 2*beta - lam for w0 < lam).  The complement regime
theta_b <= 2*beta - lam requires beta >= lam/2 (delta >= 1/2) and is a
genuine residual: neither left-aligned (start=lam) nor right-aligned
(end at theta_b+pi-lam) covers work there.  Options forward: (a)
generalize slack_sum to a free bin start + exploit the clamp bin;
(b) use the joint structure — in the residual, a itself is short-last
and defect-2, so a's row has a short END (occ contribution to think
about differently); (c) attack the shared chord's corridor position
more finely (dirRep b a > theta_b+pi-2*lam is only the coarse bound).

Also noted: ALL_ABOVE / ALL_BELOW position types still need real
distance bounds — ordering alone gives no narrow window (lead warning
heeded; delete_pair NOT applicable in BETWEEN since deleting interior
rows leaves span theta_b - theta_a >= alpha).

──────────────────────────────────────────────────────────────────────
2026-10-01 — TOP-CLUMP ACTUAL-MAX CORRIDOR (obstruction falsified)

- The previous "theta_b <= 2*beta - lam is a genuine residual" verdict
  is FALSIFIED.  It measured feasibility of covering the broad corridor
  [lam, pi-lam+beta]; but with b global theta-max,
  `saturated_chord_minmax_window` gives dirRep_ij <= pi-lam+max(theta_i,theta_j)
  <= U := theta_b + pi - lam for EVERY actual chord — the segment
  (U, pi-lam+beta] contains no directions and never needed covering.

- Free-start grid (same chart, same width, moved start):
  w0 = (pi-2lam+beta)/n,  S = lam + theta_b - beta.
  Exact arithmetic: w0-beta = (n-2)(lam-beta)/n > 0,
  lam-w0 = 2(lam-beta)/n > 0, so beta < w0 < lam;
  0 < S <= lam;  S + n*w0 = U < pi.
  Corridor [lam,U] ⊆ [S,S+n*w0]; clump [U-beta,U] ⊆ last bin
  (U-w0, U] — uniformBin's min(n-1,·) clamp keeps the endpoint x=U.
  Row budgets: S - theta_i <= lam (theta_i >= 0, S <= lam);
  theta_i + pi - U = lam + theta_i - theta_b <= lam (theta_max).
  NO theta_b > 2*beta - lam hypothesis anywhere — all-parameter closure.

- Formalized (all axiom-clean, [propext, Classical.choice, Quot.sound]):
  IntervalPacking.linearGapScore_first_ge_of_big_ends_floor_one
    mirror of the last-gap pin: tail floor 1 + both end gaps big +
    score+2 = n  =>  first floor = n-1  =>  head >= left + (n-1)lam.
  OneSaturatedHigh.potential_le_high_of_saturated_slack_sum_start
    slack_sum generalized to arbitrary start <= lam; corridor upper
    bound and per-row right budgets explicit; anchored-row left stays
    theta_i (lam <= dirRep still via chord_in_corridor, NOT via S <= dir).
  FivePointCapacity.potential_le_high_of_saturated_max_receiver_clump
    top row -> [U-beta,U] -> bin n-1 -> occ 1 -> slack Q -> cap <= 5Q.
  FivePointCapacity.between_residual_tail_emission (renamed from
    between_residual_tail_or_top): second disjunct consumed by the
    max-receiver clump against hover.  Pure low-source -> defect>=3
    tail emission; no top-clump residual.

- Independent exact-rational replay (Fraction grid, 1872 sets, 468 in
  the old "hard region" t <= 2beta-1, 504 boundary): 0 failures.
  Scalar cover check only — not a geometric proof.

- SCOPE BOUNDARY: closes the BETWEEN low-low residual ONLY.  Not
  BETWEEN total capacity, not EmissionDichotomy, not M3, not the full
  Sendov theorem.  One real short chord != sufficient tail-weight
  control.  ALL_ABOVE/ALL_BELOW still unrouted; general high-defect
  tail supply still open.
