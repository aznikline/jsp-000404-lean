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
