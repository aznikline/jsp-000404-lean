# JSP-000404 — Final theorem DAG audit (lane/d-integration)

Branch: `lane/d-integration`. Base: `ccc95c0`.
Integration layer: `Jsp000404/Integration.lean` (new, builds green, no `sorry`).

Status legend:

- `PROVED` — declaration compiles with no `sorry` anywhere in its
  dependency cone.
- `INTERFACE_READY` — compiles, but takes the missing ingredient as an
  explicit hypothesis (a `Prop` parameter or structure field), so it is
  `sorry`-free yet conditional.
- `BLOCKED_BY_SELECTION` — statement exists; proof is `sorry` pending
  gadget selection.
- `MISSING` — no statement/route yet.

## 1. The load-bearing chain

```
GadgetSelection  ──▶  staircaseBound_of_selection  ──▶  sendov_count_bound
       │                        (StaircaseBound n ks big)         │
       │                                                          ▼
       │                       count_bound_(trivial_)of_selection
       │                                                          │
       ▼                                                          ▼
  (lane/c gadgetSelection_low/high,         sendov_lower_of_selection
   adapter still needed)                                           │
                                                                   ▼
                                          sendov_of_hypotheses ◀── SendovUpper
                                                                   │
                                                                   ▼
                                            sendov_lower / sendov_upper (root)
```

## 2. Node-by-node inventory

### Selection input

| Node | Location | Status |
|---|---|---|
| `GadgetSelection` (structure, `low`/`high` fields) | `Integration.lean:70` | `INTERFACE_READY` — hypothesis bundle, *not* an axiom |
| `gadgetSelection_low` / `gadgetSelection_high` | lane/c `Gadget.lean` (not in this worktree); contract in `HANDOFF.md:62-68` | `BLOCKED_BY_SELECTION` — the P0 crux; also needs `Gadget.charge_total`/`Gadget.cap_total` (still `sorry` on lane/c) plus the skeleton↔`exponents` adapter documented at `Integration.lean:29-33` |

`GadgetSelection.low` : for a legal disjoint-circle `GCfg` in strip
`n = ⌊π/λ⌋`, `δ = π/λ − n < 1/2 ⇒ Σᵢ 2^{kᵢ} ≤ 2ⁿ`.
`GadgetSelection.high` : `δ < 1 ⇒ Σᵢ 2^{kᵢ} ≤ 2ⁿ + 2^{n−2}`.
These are the `W ≤ 2` / `W ≤ 5/2` skeleton capacities in exponent
coordinates (`W = Σ 2^{kᵢ}/2^{n−1}`).

### Arithmetic / staircase backend (all `PROVED`)

| Node | Location |
|---|---|
| `StaircaseBound` structure | `Staircase.lean:59` |
| `layerCake` (`∀k∈ks, k<n → Σ2^k ≤ 2^n + [big]·2^{n-2}`) | `Staircase.lean:88` |
| `staircase_apply` / `_low` / `_big` | `Staircase.lean:240/248/256` |
| `sendov_count_bound` | `Staircase.lean:267` |
| `exponents` | `Staircase.lean:40` |
| `total_points_bound` | `CircleBound.lean:988` |
| `exponent_le_floor` | `CircleBound.lean:585` |
| `legality_of_GC` (GC hypotheses → `Section4Legality` of centers) | `Section4Legality.lean:74` |
| `GCfg.trivial_GA` / `trivial_points` / `trivial_find` / `trivial_sepCenter` | `GC.lean` |

### Integration layer (new file, all compiled)

| Node | Location | Status |
|---|---|---|
| `exponents_lt_of_floor` | `Integration.lean:94` | `PROVED` — the `top` field, unconditional |
| `staircaseBound_of_selection` | `Integration.lean:114` | `INTERFACE_READY` — `tail` = `sel.low`/`sel.high` via `layerCake`; **replaces** `staircase_of_legality` |
| `count_bound_of_selection` | `Integration.lean:145` | `INTERFACE_READY` |
| `trivial_disjointCircles` … `trivial_GD_ne` | `Integration.lean:175-220` | `PROVED` — trivial-GC plumbing |
| `count_bound_trivial_of_selection` | `Integration.lean:223` | `INTERFACE_READY` — `|pts| ≤ 2^{n'} + [δ'≥1/2]·2^{n'-2}` |
| `alphaN_succ_add`, `alphaN_of_ge_four`, `alphaN_lt_pi` | `Integration.lean:261/271/281` | `PROVED` |
| `distinctTriples`, `mem_distinctTriples` | `Integration.lean:306/311` | `PROVED` |
| `sendov_lower_three` | `Integration.lean:324` | `PROVED` — **unconditional** `N = 3` lower bound (π/3) |
| `sendov_lower_of_selection` | `Integration.lean:366` | `INTERFACE_READY` — arbitrary-`N` lower bound conditional on `GadgetSelection` |
| `SendovUpper` (def) | `Integration.lean:563` | `INTERFACE_READY` — the sharpness hypothesis |
| `sendov_of_hypotheses` | `Integration.lean:571` | `INTERFACE_READY` — conditional root: `GadgetSelection + SendovUpper ⇒` both halves |

### Still open

| Node | Location | Status |
|---|---|---|
| `staircase_of_legality` — `tail` field | `Section4Legality.lean:139`, `sorry` at `:164` | `BLOCKED_BY_SELECTION` — superseded by `staircaseBound_of_selection`; left in place as the legality→staircase statement |
| `sendov_lower` | `MainTheorem.lean:54`, `sorry` at `:58` | `BLOCKED_BY_SELECTION` — one-line wiring to `sendov_lower_of_selection` once `GadgetSelection` lands |
| `sendov_upper` | `MainTheorem.lean:62`, `sorry` at `:66` | `MISSING` — needs the extremal constructions (recorded as `SendovUpper`) |

### Deprecated / non-load-bearing deletion route

| Node | Location | Status |
|---|---|---|
| `exists_removable_vertex` | `Deletion.lean:~1288`, `sorry` at `:1294` | deprecated route — not on the staircase path |
| `exists_removable_hull_vertex` | `Deletion.lean:~1298`, `sorry` at `:1304` | deprecated route |
| `maxGap_boundary_emission` | `GeometricDeletion.lean:~613`, `sorry` at `:629` | geometric-deletion route crux; non-load-bearing for integration |

## 3. Sorry inventory (all sites)

| File:line | Declaration | Route |
|---|---|---|
| `Section4Legality.lean:164` | `staircase_of_legality` (`tail`) | **load-bearing blocker** — the weighted-capacity / gadget-selection step |
| `MainTheorem.lean:58` | `sendov_lower` | root (blocked) |
| `MainTheorem.lean:66` | `sendov_upper` | root (blocked; also needs constructions) |
| `Deletion.lean:1294` | `exists_removable_vertex` | deprecated |
| `Deletion.lean:1304` | `exists_removable_hull_vertex` | deprecated |
| `GeometricDeletion.lean:629` | `maxGap_boundary_emission` | non-load-bearing geometric route |

`Integration.lean` contributes **zero** new `sorry`s.

## 4. Boundary audit

- **`δ = 1/2` boundary**: `staircaseBound_of_selection` sets
  `big := decide (1/2 ≤ π/λ − n)`. At `δ = 1/2` exactly the `if_pos`
  branch fires → `sel.high` → capacity `2ⁿ + 2^{n-2}`. Matches the
  checker spectrum (`δ_min = 1/2 ⇔ W ≤ 5/2`, M\*=1). At `δ < 1/2`,
  `sel.low` gives the tight `2ⁿ`. Boundary convention `≤` is consistent
  with `sendov_count_bound`'s `big`-bonus.
- **`N = 3`**: `alphaN 3 = π/3` (`rfl`); `sendov_lower_three` is
  unconditional — equilateral case via `angle_add_angle_add_angle_eq_pi`
  + pigeonhole on `π/3`.
- **Small `N`**: `N = 4` → `n = clog₂4 − 1 = 1`, `4 ≤ 2¹ + 2^{−1} = 2.5`
  fails → `alphaN 4 = π/2` (square). `N = 5` → `n = 2`,
  `5 ≤ 4 + 1` holds → `alphaN 5 = (1 − 2/5)π = 3π/5` — confirms the
  corrected numerator `2` (catalogue's `1` was wrong).
- **Dyadic `N = 2^k`, `k ≥ 3`**: `n = k − 1`,
  `2^k ≤ 2^{k-1} + 2^{k-3}` iff `8 ≤ 5` — false → else-branch
  `alphaN = (1 − 1/k)π`. E.g. `alphaN 8 = 2π/3`, `alphaN 16 = 3π/4`.
- **Constants/numerators**: `alphaN` branch A `(1 − 2/(2n+1))·π`,
  branch B `(1 − 1/(n+1))·π`; threshold `N ≤ 2ⁿ + 2^{n−2}` (real, zpow —
  safe at `n = 1` where `2^{−1} = 1/2`). `sendov_lower_of_selection`'s
  `n = 1` sub-case handled explicitly (`hNgt` via `norm_num`,
  `2¹ + 2⁰ = 3 < N`).
- **`n' = ⌊π/lam⌋` mechanism**: `lam = π − M > π − alphaN` forces
  `n' ≤ n`; branch A gives `π/lam < n + 1/2` (`δ' < 1/2` at `n' = n` →
  `N ≤ 2ⁿ`, contradicting `2ⁿ < N`); branch B at `n' = n` gives
  `N ≤ 2ⁿ + 2^{n−2}`, contradicting the else-condition `N > 2ⁿ + 2^{n−2}`.
  `n' < n` uniformly gives `≤ 2^{n'+1} ≤ 2ⁿ < N`.
- **Quantifier-by-quantifier**: `sendov_lower`'s statement is exactly the
  conclusion of `sendov_lower_of_selection` modulo the `sel` parameter:
  `∀ C : PtCfg, |C.pts| = N → ∃ p q r ∈ C.pts, distinct → alphaN N ≤ ∠pqr`.
  `sendov_of_hypotheses` returns the literal conjunction of the two root
  statements. `∠ p q r` is `EuclideanGeometry.angle` (unoriented,
  vertex at `q`) — matches the problem's "angle determined by three
  points".
- **`PtCfg.len : 3 ≤ pts.length`** is a structure field, so the `N = 3`
  split and `2 ≤ |pts|` facts are consistent with `C.pts.length = N`.

## 5. Exact blocker and next step

**Exact blocker**: `GadgetSelection` (`Integration.lean:70`) — two
weighted-exponent capacities `Σᵢ 2^{kᵢ} ≤ 2ⁿ` (δ<½) / `≤ 2ⁿ + 2^{n−2}`
(δ<1) for legal `GCfg` forests. On lane/c this is
`gadgetSelection_low`/`gadgetSelection_high` (`HANDOFF.md:62-68`),
still open, plus the adapter skeleton→`exponents` and lane/c's own
`Gadget.charge_total`/`Gadget.cap_total` sorries.

**Next step for the selection lane**: prove `gadgetSelection_low/high`
(contrapositive form `no score-1 gadget ⇒ W ≤ 2`, etc.), then write the
adapter `Gadget.lean → GadgetSelection` extracting the center skeleton
and converting `cap_total` into the `Σ 2^{kᵢ}` bounds. Downstream wiring
is then mechanical: `sendov_lower := sendov_lower_of_selection sel`;
`sendov_upper` additionally needs the extremal constructions
(`SendovUpper`).
