# JSP-000404 GOAL-01 — Owner status

Branch: `agent/jsp404-angle-cert-goal-01-owner`
North star: arbitrary-N Sendov count bound closed in Lean kernel, no sorry.

## Phase status

| Phase | Content | State |
|---|---|---|
| P0 | s=3 closed-form base (`Base3.lean`) | **DONE** — kernel-verified |
| P1 | `AngleSystem` + geometry→abstraction bridge | IN PROGRESS |
| P2 | erase/merge preserves `AngleSystem` | pending |
| P3 | potential deletion identity hookup | pending |
| P4 | **Kraft packing** (K3) — sole math crux | K3a residual layer DONE; K3b (first overfull → debt-chain) open |
| P5 | induction → `StaircaseBound` → `sendov_count_bound` | pending |

## P0 (DONE)

`Jsp000404/Base3.lean`:
- `Base3CellData n δ` — `ext`/`k` + L1 `ext_pos`, L2 `top_requires_sat`,
  L3 `ext_budget` (real form of `Σext ≤ ⌊2(n+δ)⌋`), `k_le`.
- `base3_low`: `δ < 1/2 → Σᵢ 2^{kᵢ} ≤ 2^n` (sharp).
- `base3_high`: `δ < 1 → Σᵢ 2^{kᵢ} ≤ 5·2^{n-2}` (= `2^n+2^{n-2}`).
- Axioms: `[propext, Classical.choice, Quot.sound]` only. No sorry.
- Note: high bound holds for ALL δ<1; the phase transition is entirely
  the sharper `2^n` at δ<1/2.

## Key falsified candidates (do not retry)

- global `Σ 2^{kᵢ}Eᵢ ≥ F` — fails (optimal wE = F−2 on feasible, 56/572)
- weak `wE ≥ F−s+1` — fails (deficit 8 > slack 3, δ=3/4)
- min-k cert, extremal(min∪max)-k cert — fail at δ=3/4
- max-gap vertex CertA∨CertC; boundary-emitter; ρ/σ terminal cycle;
  zero-emitter charge map; any pure k-level selection rule.
- Cert existence is incidence/carry-structural, 1600+/1600+ verified.

## Lead's parallel lane (origin/master, tools/+notes/HANDOFF.md)

ABCEDF/gadget route: dyadic `W = Σ2^{(n−1)−kᵢ}`; crux
`gadgetSelection_{low,high}` — complementary challenger to Cert Lemma.
Confirmed facts: δ_min ∈ {0,½,1,inf}; W>5/2 ⇒ δ_min≥1.

## P0-bridge (DONE) — geometry → `Base3CellData` at s=3

`Jsp000404/Base3Bridge.lean` (new, imported by root module):

- `linRep_oangle_eq_angle_or_pi_sub`: projective sweep between two
  direction reps at center `i` equals `∠` or `π−∠`. Uses the vector
  `Orientation.angle_eq_abs_oangle_toReal` (works for arbitrary
  `o : Orientation`, unlike the affine version which is pinned to
  `positiveOrientation` and needs `Module.Oriented`).
- `cycGaps_pair`: sorted 2-row has gaps `[b−a, π−(b−a)]`.
- `other1/other2`: the two non-self indices in `Fin 3`;
  `erase_finRange_eq` gives the row `[o1,o2]` after erase+sort.
- `rowScore_eq_gapScore_arcs`: `rowScore = g(∠ᵢ)+g(π−∠ᵢ)` — both
  cyclic gaps are genuine triangle arcs, so legality transfers.
- `base3CellData`: `ext i = ⌊(π−∠ᵢ)/λ⌋₊`, `k i = rowScore` satisfies
  all four fields from `Section4Legality` alone. `ext_pos` uses
  `∠ᵢ ≤ π−λ`; `top_requires_sat` uses `⌊∠/λ⌋+⌊(π−∠)/λ⌋ ≤ ⌊π/λ⌋ = n`;
  `ext_budget` uses `Σ∠ᵢ = π` (affine triangle sum) → `Σext ≤ 2(n+δ)`.
- `base3_potential_le` (δ<1/2 → `≤2^n`),
  `base3_potential_le_big` (`≤5·2^{n−2}` uniform).
- Axioms: `[propext, Classical.choice, Quot.sound]` only. No sorry.
- `lake build`: PASS (3262 jobs).

## Representation decision (P1)

Geometry rows ARE the closed angle system: `directionRow` keeps the
s−1 direction reps per center, `cycGaps` gives real consecutive arcs,
`erase_directionRow` already proves deletion = sub-configuration row.
No separate abstract `AngleSystem` class needed — the bridge is
`Section4Legality` directly. P2 = `erase_directionRow` (already
proved) + merge legality transfer; P3 = `sum_potential_erase` /
`removable_iff` (already proved in `Deletion.lean`).

Remaining sorry inventory (pre-existing, on prize path):
`Section4Legality.staircase_of_legality` (the optimization crux),
`Deletion.lean:1294,1304`, `GeometricDeletion.lean:629`,
`MainTheorem.lean:58,66`.

## P2/P3 assembly + dedup bridge (DONE, this commit)

`Jsp000404/GeometricDeletion.lean` §7:

- `Section4Legality.erase`: deletion `v` reindexes by `v.succAbove`;
  `inj`/`triAngle` hereditary via `Fin.succAbove_right_injective`.
  This is the full legality-preservation half of P2 — no extra
  legality field needed since merged gaps are existing triangle arcs.
- `potential_sub_config`: `potential lam (directionRows (c∘v.succAbove))
  = potentialErase lam (deleteIndex) v (directionRows c)` via
  `eraseIdx_directionRow` + `Fin.sum_univ_succAbove`.
- `potential_le_sub_config_iff`: geometric form of the deletion
  certificate — `potential ≤ potential(sub) ↔ charge v ≤ 0` via
  `removable_iff`.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.

`Jsp000404/Deletion.lean` — deduplication invariance block:

- `zip_dropLast_tail_cons`, `cycGaps_cons_cons_self`:
  adjacent duplicate contributes a `0` head gap.
- `head_dedup`, `getLast_dedup`: nonempty sorted `dedup` keeps both
  endpoints (needed for the wrap gap).
- `adjPairs_dedup_perm`, `cycGaps_dedup_perm`: dedup removes exactly
  zero gaps — surviving cyclic gaps are a permutation of
  `cycGaps dedup ++ zeros`.
- `rowScore_dedup`: `rowScore lam l.dedup = rowScore lam l` on sorted
  lists — bridges multiplicity-bearing `directionRow` with
  deduplicated `circleDirs` exponents.
- Axioms: `[propext, Classical.choice, Quot.sound]` only.

`lake build`: PASS (3262 jobs). Sorry inventory unchanged — all
pre-existing placeholders, none new.

State after this commit: P1 (geometry rows = angle system), P2
(erase preserves legality + row structure), P3 (potential deletion
identity + dedup bridge) all kernelized. Sole remaining math crux:
`Section4Legality.staircase_of_legality` tail / certificate
existence on high-potential systems (P4).

## P5 induction skeleton — DONE (conditional on the cert crux)

`Jsp000404/Induction.lean` (new, axiom-audited clean) closes the whole
assembly modulo a single packaged hypothesis:

- `sendovCap n big` — `2^n + if big then 2^{n-2} else 0`.
- `CertExists o e n big lam` — **the isolated P4 crux**: every legal
  `t ≥ 4` center configuration with `cap < potential` satisfies
  `EmissionDichotomy` on `(deleteIndex, directionRows)`. Nothing else
  remains unproved in the count-bound chain.
- `potential_le_sendovCap` — strong induction on `s ≥ 3`:
  `s = 3` → `base3_potential_le{,_big}`; `s ≥ 4` → if `F ≤ cap` done,
  else `CertExists` → `removable_of_dichotomy` → `Removable` →
  `potential ≤ potential(sub)` via `potential_sub_config` → legality via
  `Section4Legality.erase` → IH.
- Bridges `exponents` ↔ `potential`:
  `cycGaps_eq_ofFn_gapAfter` (sorted fans), `exponents_entry_eq_rowScore`,
  `circleDirs_eq_dedup_directionRow` (needs `forest.Nodup`),
  `exponents_map_pow_sum` (`Σ 2^{k'} = potential`).
- `staircase_of_cert` — `StaircaseBound n (exponents V o e lam) big`
  modulo `CertExists`, `2 ≤ n`, `he`, `hbig : big = false → δ < 1/2`.
  `s ≤ 2` handled by the unconditional `top` bound; `s ≥ 3` by the
  induction.

Remaining holes (unchanged, all pre-existing): the `tail` field of the
original `staircase_of_legality` (now subsumed by `staircase_of_cert` —
identical statement + `hcert`/`hn2`/`hbig` hypotheses), the two
`Deletion.lean` placeholder sorries, `GeometricDeletion.lean:629`
(old challenger crux), `MainTheorem` sendov_lower/upper.
The `n = 1` staircase case (`N ≤ 6` in the final theorem) is excluded
by `hn2 : 2 ≤ n` and needs a separate small-N argument.

## P4 — Kraft reformulation (round 2 progress)

The crux restated in its cleanest form (see CERT_LEMMA.md §Kraft):

`F ≤ 2^n (+2^{n−2})` ⟺ `Σᵢ 2^{−cᵢ} ≤ 1 (+1/4)` where
`cᵢ = Bᵢ + (n − Σ⌊g/λ⌋)` = #big gaps + unused cells, `kᵢ = n − cᵢ`.

Verified mechanism (0 violations over ~6000+ legal configs):
- ≤2 saturated vertices (`cᵢ=1`), ≤1 in low regime — triangle angle-sum.
- single-cluster (`B=1`) cone `< (cᵢ−1+δ)λ`; triple `Σc ≥ n+3/n+2`;
  convex r-tuple `Σc ≥ r(n+1)−2(n+δ)`; interior ⟹ `c ≥ ~n/2`.
- cap-saturating profiles `[1,2,2,2]`, `[1,1,3,3]`, `[2,2,2,2]`
  observed — the bound IS a prefix-code bound + 1/4 defect.
- The `δ≥1/2` phase transition = two saturated vertices exactly filling
  the Kraft budget.

Lead's wave-2 plan v2 designates THIS geometric-deletion route as the
arbitrary-s main line (P0-H); the gadget lane is auxiliary.
Remaining gap: multi-cluster Kraft bound + lens recursion (see
CERT_LEMMA.md "remaining mathematical gap").

### Kraft formalized in Lean (round 2+)

`Deletion.lean` §9 + `Induction.lean` now carry the full kernel-checked
restatement: `rowCells`/`rowBig`/`rowDefect`,
`rowScore_eq_cells_sub_big`, `rowScore_eq_sub_defect`,
`potential_eq_two_pow_mul_kraft`,
`potential_le_two_pow_iff_kraft`, `gapAfter_nonneg`,
`cycGaps_sum_eq_pi`, `rowCells_le_floor_pi`,
`rowCells_directionRow_le{,_of_floor_eq}`, and the capstone
`potential_le_sendovCap_iff_kraft`: for geometric rows with
`⌊π/λ⌋ = n`, `potential ≤ sendovCap n big ⟺ Σ(1/2)^{cᵢ} ≤ 1+(1/4)[big]`.
All axioms `[propext, Classical.choice, Quot.sound]`; no new sorries.
The P4 crux is now literally a Kraft packing bound on `{c_i}` inside
the repo — either route (emission dichotomy OR direct defect packing)
closes it.

## K1/K2 done (this round)

`rowDefect_eq_one` + `cyclicDiff_le_or_ge` +
`angle_le_pi_sub_of_saturation` + `not_two_saturated_of_delta_lt_half`
— all kernel-checked, axioms `[propext, Classical.choice, Quot.sound]`.
The `δ = 1/2` phase transition is now a theorem, not an observation.

## K3 scaffold landed (this round, all proved)

New kernel-checked pieces (axioms `[propext, Classical.choice,
Quot.sound]` only, no new `sorry`):

- `one_le_rowDefect` (Deletion.lean): `n ≥ 1, cells ≤ n ⟹ cᵢ ≥ 1`
  (`cells = n` forces a gap `≥ λ`).
- `not_three_saturated` (Induction.lean): three saturated centers give
  all three triangle angles `≤ π − nλ`, so `π ≤ 3(π−nλ)`, i.e.
  `3nλ ≤ 2π < 2(n+1)λ ⟹ n < 2`.  Saturated count ∈ {0,1,2} for `n ≥ 2`.
- `KraftPacking` (Induction.lean): hypothesis bundle with the open
  case bounds `no_sat_low`/`no_sat_high` (K3-C, split by regime),
  `one_sat_low` (K3-B), `one_sat_high` (K3-A1), `two_sat` (K3-A2),
  stated over an abstract `d : Fin s → ℕ`.  IMPORTANT CORRECTION:
  `∀ cᵢ ≥ 2 → K ≤ 1` is FALSE in the high regime — all-`c=2` at
  `s = 5` is LP-realizable at `δ = 1/2` (W = 5/2), giving `K = 5/4`;
  the tight no-saturated high bound is `K ≤ 5/4`.  `s = 6` all-`c=2`
  is infeasible (δ_min ≥ 1), consistent.
- `kraft_packing_of_legality`: the full case split — card of the
  saturated set is 0/1/2 (≥3 impossible; 2 impossible in low regime),
  each branch discharged by the corresponding bundle field.  PROVED.
- `potential_le_sendovCap_of_packing`: K3 bundle → `potential ≤
  sendovCap` via `potential_le_sendovCap_iff_kraft`.  PROVED —
  `CertExists` is no longer needed on the main route.

## ABCEDF cross-map (this round)

Exact coordinate correspondence verified against
`origin/lead/jsp404-wave2-integration-v2` (`GadgetSelection.lean`,
`Integration.lean`):

| ABCEDF skeleton | Kraft route |
|---|---|
| `d_v = (n−1) − kexp v` | `c_v − 1` (`kexp v = rowScore`) |
| `W = Σ 2^{−d_v}` | `2·K`, `K = Σ 2^{−c_i}` |
| `W ≤ 2` capacity | `K ≤ 1` (K3-C + K3-B, low regime) |
| `W ≤ 5/2` capacity | `K ≤ 5/4` (K3-A1 + K3-A2, high) |
| deficit-0 vertex | saturated row (`c_i = 1`) |

Verdict: `GadgetSelectionLow/High` are *contrapositively equivalent*
to K3 (`sel.low` ⟺ `δ<1/2 → K≤1`), still open on that lane — no proved
S=0 packing theorem to import; the two lanes face the same obstruction
in dual form.  Their value: (a) ~1M-skeleton validation of the K3
shape (`δ_min ∈ {0,1/2,1}`), (b) the downstream `Integration.lean`
layer already consumes exactly `Σ2^{kᵢ} ≤ 2ⁿ+2^{n−2}`, i.e. our
`potential ≤ sendovCap`.

Remaining: the four `KraftPacking` fields are THE sole mathematical
crux; attack order K3-C first.

## K3a residual-capacity layer (this round, all proved, no sorry)

New file `Jsp000404/KraftResidual.lean` — pure `ℚ`-arithmetic,
axioms `[propext, Classical.choice, Quot.sound]` only.

Strategy change (lead): instead of proving the five `KraftPacking`
fields independently, K3 is now organized as a prefix-capacity
recurrence over the defect histogram `a_r = #{i | c_i = r}`:

    R_m = 2^m·B − Σ_{r ≤ m} a_r·2^{m−r}

with cap `B = 1` (low) / `B = 5/4` (high, i.e. `5·2^{m−2}` for m≥2).

Proved declarations:

- `defectCount`, `kraftSum`, `kraftResidual` — the basic objects.
- `univ_eq_biUnion_fiber`, `kraftSum_eq_hist` — histogram
  decomposition `K = Σ_{r≤M} a_r·2^{−r}`.
- `kraftResidual_eq_partial` — `R_m = 2^m·(B − Σ_{r≤m} a_r·2^{−r})`.
- `kraftResidual_succ` — **the recurrence `R_{m+1} = 2·R_m − a_{m+1}`**;
  the level capacity condition is `a_{m+1} ≤ 2·R_m`.
- `kraftResidual_eq` — capstone `R_M = 2^M·(B − K)` for `d ≤ M`.
- `kraft_le_iff_residual_nonneg` — `K ≤ B ↔ 0 ≤ R_M`.
- `kraftResidual_neg_mono`, `kraftResidual_neg_forall_add` —
  once negative, always negative.
- `kraft_le_iff_residual_forall_nonneg` — `K ≤ B ↔ ∀ m, 0 ≤ R_m`.
- `kraft_gt_iff_exists_residual_neg` — `K > B ↔ ∃ m, R_m < 0`.
- `kraftResidual_zero` — `R₀ = B` when all defects ≥ 1
  (`one_le_rowDefect` supplies the hypothesis).
- **`exists_min_overfull_level`** — the K3b entry point: `K > B`
  yields a minimal `m ≥ 1` with `R_{m−1} ≥ 0` but
  `a_m > 2·R_{m−1}` (first prefix-capacity overflow).
- Sanity `example`s: all observed tight profiles evaluate to
  `R = 0` (`[2]⁴`, `[1,2,3,3]` at `B=1`; `[2]⁵`, `[1,2,2,2]`,
  `[1,1,3,3]` at `B=5/4`) via the capstone.

K3 DAG is now:

    K3a residual algebra              DONE (this file)
    K3b first overfull level
        → DebtChain/ResidualWitness   OPEN — the sole math crux
    K3c witness → δ ≥ 1/2 (low) / 1 (high)
                                      DONE in gadget lane arithmetic
        → contradiction → KraftPacking fields → kraft_packing_of_legality

The five `KraftPacking` fields remain as the downstream
compatibility interface; they are no longer attacked separately.

## K3b first geometric layer (this round, all proved, no sorry)

New file `Jsp000404/K3bGeometry.lean` — the first place the residual
layer consumes real geometry.  Axioms `[propext, Classical.choice,
Quot.sound]` only.

Wiring convention (explicit, per lead boundary #2): the
`KraftResidual` defect function is `d i := rowDefect n lam
(directionRows o e c i)` — i.e. `c_i`, NOT the ABCEDF `c_i − 1`
(which would compute `W = 2K`).

Proved declarations:

- `geomDefectCount_one_le_two` — `a₁ ≤ 2` for `n ≥ 2`
  (`not_three_saturated` lifted to the histogram).
- `kraftResidual_one_eq` — `R₁ = 2B − a₁` when all `d_i ≥ 1`.
- `geom_kraftResidual_one_nonneg` — `R₁ ≥ 0` for `B ≥ 1`:
  level 1 can never be overfull.
- **`exists_first_overfull_level_ge_two`** — `K > B` (`B ≥ 1`,
  covers low `B=1` and high `B=5/4`) yields a first overfull level
  `m ∈ [2, n]` with `R_{m−1} ≥ 0`, `a_m > 2·R_{m−1}`.  The `m ≥ 2`
  improvement over `exists_min_overfull_level` is exactly
  `not_three_saturated` — first genuine geometry→residual theorem.
- `cycle_cert` / `cycle_cert_delta` — the polygon-shape certificate
  kernelized: `t ≥ 3` distinct centers whose cyclic interior angles
  `∠ vᵢ v_{i+1} v_{i+2}` sum to `(t−2)·π` (triangulation identity)
  satisfy `t·λ ≤ 2π`, i.e. `δ ≥ t/2 − n`.  At `n = 2`: a 5-cycle
  gives `δ ≥ 1/2` (`[2]⁵` tight profile), a 6-cycle gives `δ ≥ 1`.
  Consumes `Section4Legality.triAngle` + injectivity only.
  The hypothesis `hsum` (angle additivity along the vertex fans)
  is the remaining construction content.

Also `DebtChain.debt_residual_ge` — τ-parametric residual theorem
`τ·(c+u) ≤ K − B − C ⟹ δ ≥ τ` (fixes a `mul_comm` elaboration gap),
and `ChainWitness.ResidualWitness.ge_of` exposing the same
threshold at the witness level — the K3c backend now supports
`τ = 1` for the high regime.  `ResidualWitness.δ` binding to the
original geometric δ remains the caller's obligation.

## Corrected K3b experiment (tools/overfull_cert.py)

Methodology fix per lead: fix an OVERFULL integer skeleton first,
then let the exact-Fraction remainder LP produce the Farkas
certificate — never count "feasible samples all satisfy K ≤ B".

**Verifier rewritten after lead review** (`verify_cert`): the old
check only required nonneg weights on inequalities and printed
`−cst/dcoef` as the bound — which accepts the pure `δ ≤ 1`
constraint as a forged `δ ≥ 1` certificate.  The strict verifier
now requires the recombined form, after explicit residual
elimination (`rnn` for `+r` coefficients, `rle` for `−r`, with the
`−γ` constant adjustment), to be exactly `C − α·δ ≤ 0` with
`α > 0` and `C ≥ α·τ`.  It verifies every bounded leaf
independently, never overwrites a recorded bounded minimum with an
infeasible result, does not call the LP solver, and labels
`r ≤ 1` / `δ ≤ 1` as closed relaxations (not realizable floor/
remainder solutions).  Negative controls all reject:
`δ≤1` alone, flipped δ direction, negative weight on an
inequality, insufficient constant, tampered τ; the residual
elimination path verifies correctly (`selftest` subcommand).
Per-leaf evidence (order / bits / qs, full original constraint
forms, exact rational multipliers including elimination weights,
eliminated form, τ, verdict, closed-relaxation flag) is dumped
with `--save DIR` (JSON per leaf).

Overfull skeleton `n=2, s=5, c=[2]⁵` (K = 5/4 > B = 1):
leaf-1 certificate is a **pentagon** — five `∠i(i−1)(i+1) ≤ π−λ`
(weight 1/2) + three triangles `Δ012, Δ023, Δ034` (−1/2) —
`5λ ≤ 2π ⟹ δ ≥ 1/2`; this is `cycle_cert`.  Other leaves are
fan/remainder/signed-triangle combinations.

Overfull skeleton `n=2, s=6, c=[2]⁶` (K = 3/2 > B = 5/4):
every bounded leaf strictly verifies `1 − δ ≤ 0` (δ ≥ 1 = τ_high);
103 leaf evidence files saved under `certs_s6/`.  Polygon leaves
(6 `ang` + 4 `tri`) coexist with non-polygon ones, e.g. leaf 7:
4 `ang` + 2 signed `tri` + 3 `rnn` eliminations.  Both are
closed-relaxation certificates only.

## K3b second layer: the fat-arc certificate, fully wired (this
## round, all proved, no sorry)

A complete NON-polygon certificate chain from real geometry —
`K3bGeometry.lean`, axioms `[propext, Classical.choice,
Quot.sound]` only:

- `floor_mul_le_gap` — `λ·⌊g/λ⌋ ≤ g` for `g ≥ 0`: the per-gap
  remainder bound (the model's `rnn` layer).
- `cyclicDiff_eq_Ico_sum_gapAfter` — the forward arc between
  sorted positions `a ≤ b` is the consecutive `gapAfter` sum over
  `Finset.Ico a b` (proved by telescoping via `sum_Ico_eq_sum_range`
  + `sum_range_sub`, not assumed).
- `arc_cells_le_arc` — `(Σ⌊g/λ⌋)·λ ≤ arc` along the arc.
- `dirRep_arc_eq_angle` — discharges the arc↔angle identity:
  `cyclicDiff (dirRep i u) (dirRep i v) = linRep(oangle)`
  (`cyclicDiff_dirRep`), and on the branch
  `0 ≤ (oangle (cu−ci) (cv−ci)).toReal` (the model's same-bit
  selector) `linRep = ∠uiv`; the `toReal = π` edge would give
  `∠uiv = π`, excluded by `triAngle` + `λ > 0`.  A locally
  checkable orientation sign replaces `cycle_cert`'s global
  unproved `hsum`.
- **`arc_overflow_geometric_of_cells`** — hypotheses are exactly
  certificate data: an arc `p ≤ q` of the actual sorted
  `directionRow i` with endpoints `dirRep u`, `dirRep v` carrying
  `≥ n` integer cells, plus the orientation bit and legality;
  conclusion `(n+1)·λ ≤ π`, i.e. `δ ≥ 1` (high threshold).  No
  `hsum`-type premise, no free δ.
- `arc_overflow_geometric_absurd` — under `⌊π/λ⌋ = n` the same
  hypotheses give `False`: the infeasibility-witness form.

Honest residual gap (unchanged): these theorems consume certificate
data; *why* a first overfull level produces a fat arc (or a polygon
or another family) — the selection implication
`a_m > 2R_{m−1} ⟹ ∃ certificate` — remains the open mathematical
core of K3b.  The polygon template alone cannot suffice in general
(`n=4, c=[1,2,2,3]` is overfull at level 3 but any cycle gives only
`δ ≥ −2`); fan/remainder families like the one just wired are
required.  `MainTheorem.lean`'s `sendov_lower`/`sendov_upper` are
still `sorry`.

## Verifier control-flow + offline replay (this round)

`run` now classifies every leaf and exits accordingly:
`0` = all leaves certified `δ ≥ τ`; `2` = no failures but some leaf
only solver-infeasible (no infeasibility certificate — *not* a
certified bound); `1` = failures (rejected cert, bound below τ,
solver anomaly).  Selftest's positive control (`rle+rnn`
elimination, `α=1, C=−1`) is now asserted, not just printed.

New `tools/replay_cert.py`: offline replay of saved evidence — no
LP.  Rebuilds each leaf's skeleton from `order/bits/qs`, regenerates
ORIG, integrity-checks every saved `form`/`is_eq` against the
rebuilt constraint, re-verifies the saved multipliers through
`verify_cert`, then cross-checks the saved derived fields
(`elim_weight`, `proven_bound`, `eliminated_form`) against the
recomputation, and classifies:

- `FAT_ARC_CERTIFIED` — ∃ vertex i, same-bit pair (u,v), fan arc
  with `Σq ≥ n`; the mini-certificate `{ang(i,u,v): 1}` is re-run
  through the strict verifier, so the match is proved end-to-end.
- `POLYGON_SUPPORT_MATCH` — the saved `ang` support is a full
  s-cycle.  Support-shape recognition only: the `(t−2)π` angle sum
  (`cycle_cert`'s `hsum`) is still an unproved premise.
- `UNCLASSIFIED_SIGNED_CERT` — anything else.  This label is an
  *unclassified* fallback, NOT a DebtChain/signed-chain
  certification: the recognizers simply failed to match.  A
  non-match also says nothing about whether a simpler certificate
  exists for the same skeleton (leaf 7 showed LP support need not
  be minimal).

Exit status: `0` iff ≥1 record replayed and all passed
integrity + verification + derived-field checks; `2` for a missing
directory or zero matched records; `1` if any
VERIFY-FAIL / INTEGRITY-FAIL / DERIVED-MISMATCH occurred.

**Leaf 7 correspondence confirmed mechanically**: replay identifies
`V5 arc 0→4, cells = 2 = n` — exactly the lead's independent
recomputation.  The nine-constraint LP certificate simplifies to
`{∠504 ≤ π−λ} + {rnn r50..r53}` giving `1 − δ ≤ 0`: leaf 7 *is* the
fat-arc template.  LP support need not reflect the simplest proof —
simplification beats inventing new families from solver output.

## Coverage boundary measured (the important negative result)

| skeleton | regime | τ | leaves | FAT_ARC | POLYGON | UNCLASSIFIED | fails |
|---|---|---|---|---|---|---|---|
| `n=2, c=[2]⁶`, K=3/2 | high | 1 | 101 | 35 | 5 | 61 | 0 |
| `n=4, c=[1,2,2,3]`, K=9/8 | low | 1/2 | 401 | 44 | **0** | 357 | 0 |
| `n=4, c=[1,2,2,2,3]`, K=11/8 | high | 1 | 519 | 65 | **0** | 454 | 0 |

All 1021 replayed leaves: `VERIFY-FAIL = 0`, `INTEGRITY-FAIL = 0`,
`DERIVED-MISMATCH = 0`.  Counts note: `certs_s6` numbers reach
`leaf_0103` but holds 101 records (`leaf_0080`, `leaf_0096` absent —
cause not inferred); saved certified records and
solver-reported-infeasible leaves remain separate counts.

At mixed-defect skeletons with first overfull level `m = 3`
(`R₂ = 0, R₃ = −1`), the polygon recognizer matches **nothing** and
fat-arc only ~11–13%.  The remaining 82–89% are signed
fan/triangle/remainder combinations — worth studying for signed-chain
structure, but NOT shown to be DebtChain certificates, and not shown
to be the unique mechanism: the measurements bound only what the two
current recognizers see.

## K3b third layer: leaf-0001 signed residual wired (this round)

The concrete mixed-high certificate `certs_n4_high/leaf_0001.json`
is now fully wired in `K3bGeometry.lean`, axioms
`[propext, Classical.choice, Quot.sound]`:

```
dirRep arcs + cyclic-order data + orientation bits + cell bounds
      → fan eqs (cyclicDiff_chain4) + signed triangle eqs
        (angle_add_angle_add_angle_eq_pi + arc/complement branches)
      → P = r02+r03+r33+r10+r21+r32 satisfies P = 1+2δ, P ≥ 3
      → ResidualWitness.ge_of at τ = 1  →  5λ ≤ π  (δ ≥ 1)
```

- `leaf_0001_cert` — concludes `(5:ℝ)·λ ≤ π`, i.e. `δ ≥ 1` with
  `w.δ` literally bound to the system's `π/λ − 4`.  Hypotheses are
  exactly the certificate's `order`/`bits`/`qs` data on the actual
  `dirRep` values: two cyclic-order chains (rows 0, 3), one arc
  decomposition (row 2), eight `oangle.toReal` sign bits, and two
  cell lower bounds `4λ ≤ arc`, `3λ ≤ arc` (the `q03=4`, `q33=3`
  skeleton cells; the six `q = 0` remainders need no bound beyond
  `arc ≥ 0`).
- `leaf_0001_absurd` — under `⌊π/λ⌋ = 4` the same bundle gives
  `False`: the skeleton is infeasible in the `n = 4` regime, matching
  the LP picture (the closed relaxation only meets feasibility at
  the `δ = 1` boundary, where `r < λ` is relaxed to `r ≤ λ`).
- Supporting: `dirArc`, `dirRep_arc_eq_pi_sub_angle` (the
  `toReal < 0` complement branch — the model's differing `bits`),
  `cyclicDiff_eq_add_of_le` (intermediate direction on an arc splits
  it), `cyclicDiff_add_rev`, `cyclicDiff_chain4` (the fan chain
  `cd₁₂+cd₂₃+cd₃₄+cd₄₁ = π` from cyclic-order comparisons),
  `cyclicDiff_eq_zero_of_Ico`.
- The saved `order` is a *cyclic* fan order; here it enters as
  forward-arc comparisons between `dirRep`s — no `directionRow`
  positions or rotations are needed, since `cyclicDiff` between
  consecutive cyclic neighbors is already the model's gap.  The
  earlier `Ico p q` caveat applies only to the sorted-row
  `arc_overflow_geometric_of_cells` family, not this form.

This is one signed-residual leaf fully sourced from geometry —
not yet a reusable extension rule or a selection principle.  Next:
study which internal remainders cancel when a triangle piece is
added to this shape (the local extension rule question), before
proposing any signed-chain family.

## K3b fourth layer: the signed-chain family, arbitrary L (this
## round)

`leaf_0001_cert` is now an *instance* of a general kernel-checked
theorem, not a standalone proof.  For a chain of distinct centers
`x 0, x 1, …, x (L+1)` (`L ≥ 2`), with

```
A_j = dirArc (x0)(x_j)(x_{j+1})   D_j = dirArc (x_j)(x_{j-1})(x_{j+1})
S_j = dirArc (x_j)(x0)(x_{j-1})   H_0 = dirArc (x0)(x_{L+1})(x_1)
                                  H_L = dirArc (x_L)(x_{L+1})(x_0)
```

`tri_piece_rel` derives each triangle relation
`A_j + S_{j+1} = S_j + D_j` from the actual `dirArc` split + the
three `oangle` orientation bits (arc vs complement); the telescoped
sum plus the two boundary fan closures gives the master identity

    2π = A_L + H_0 + H_L + Σ_{j=1}^{L} D_j                      (★)

and `triAngle` through the `hbD` complement bits gives `D_j ≥ λ`.
With cell bounds `a·λ ≤ H_0`, `b·λ ≤ H_L`, `A_L ≥ 0`, the
parameterized backend `ResidualWitness.ge_of` yields

    δ = π/λ − n ≥ (a + b + L − 2n)/2.                          (†)

`leaf_0001_cert` is now the L=3, a=4, b=3, n=4 instance
(`(4+3+3−8)/2 = 1`, giving `5λ ≤ π` as before); its proof body is a
thin instantiation of `signed_chain_cert`.  All new declarations
axiom-clean `[propext, Classical.choice, Quot.sound]`.

**Coverage scan** (`tools/chain_scan.py`, offline, no LP —
skeleton-driven since the fix below): every fan/triangle/angle
constraint exists in ORIG for every index, so a chain is certified
iff the skeleton's `order/bits/qs` satisfy the theorem's hypotheses,
regardless of which constraints the saved LP certificate used.
Current recognizer output: **3487 valid chains across 1021 leaves**
— n4_high: 2076 (189 leaves have one reaching σ ≥ 2), n4_low: 401
(43 leaves reaching σ ≥ 1), s6: 1010 (none reach σ ≥ 2 — fat arcs
carry that sample).  The earlier "13 chains, all saturated, no
extension" reading was an artifact of scanning only the LP support:
prefix chains (e.g. `[0,1,2,3]` inside `leaf_0001`) were invisible.

**Extension boundary formula** (corrected): adding the piece
`△(x_0, x_L, x_{L+1})` (NOT `△(x_0, x_{L+1}, x_{L+2})` — the new
interior triangle uses the old `x_L`), a new demand
`∠(x_L, x_{L+1}, x_{L+2})` at apex `x_{L+1}`, and a new right fan at
`x_{L+1}` with cyclic order `x_0, x_L, x_{L+2}`, absorbs the
`x_{L+1}→x_{L+2}` gap of `order[i0]` into the chain, so
`a′ = a − q` (`q` = that gap's cell count) and the right boundary
moves to `x_{L+1}` with `b′ = Σ qs[x_{L+1}]` over the
`x_{L+2}→x_0` wrap.  Hence

    σ′ − σ = 1 + (a′+b′) − (a+b) = 1 + b′ − b − q

— the **old `b` is replaced, not kept**.  Nondecreasing iff
`b′ + 1 ≥ b + q`; strict gain iff `b′ ≥ b + q`.  Over the 923 real
extensions found in evidence: Δσ ∈ {−3:58, −2:133, −1:88, 0:118,
+1:378, +2:148} — about a third of one-piece extensions lose score.

`signed_chain_extend` (K3bGeometry) packages exactly this: old
length-`L` data + the new piece (wrap split `hext`, new triangle
bits, new demand bit, new right-fan closure, fresh `a′ b′` bounds)
→ `σ/2 ≤ δ ∧ σ′/2 ≤ δ`.  Regression `leaf_0001_extend_cert`: the
leaf-0001 skeleton certifies the L=2 prefix `[0,1,2,3]` (fans 0,2;
σ = 1, `δ ≥ 1/2`) and the extension to `[0,1,2,3,4]` (σ′ = 2,
`δ ≥ 1`), with `q = qs[0][3→4] = 0`, `b′ = b = 3` — matching the
hand-verified `Δσ = +1`.  The prefix needs row-2 fan-chain data
(`h2034 h204`), the wrap splits `h031 h230`, and the row-2 boundary
bound `hq20`, all sourced from the same skeleton's order/qs.

Chains are now a *third* recognized family (fat-arc, polygon
support-shape, signed chain) among the previously unclassified
leaves.  189/519 n4_high leaves are covered by a τ-meeting chain;
this does not show chains exhaust the rest, and selection
(`K > B ⟹ some valid certificate exists`) remains unproved.

### Template synthesis (`tools/template_cert.py`)

A stronger diagnostic: instead of matching the *saved* multiplier
support, synthesize the canonical multipliers of each chain shape
(fan +1, triangle −1, demand/arc-cap +1) directly from the skeleton
and pass the candidate through `verify_cert`'s exact-rational
elimination.  Three closure shapes are recognized:

- **A** (`signed_chain_cert`): left fan at `x_0`, right fan at
  `x_L`, triangulation `j = 1 … L−1`, demands `D_1 … D_L`.
- **B** (`signed_chain_certB`, proved this round): left fan at
  `x_0`, RIGHT closure at the endpoint `x_{L+1}` via the complement
  identity `S_{L+1} + H'_L = π`, triangulation runs through
  `j = L`.  Master identity `2π = H_0 + H'_L + Σ_{j≤L} D_j`; each
  residual arc may carry an arbitrary cell bound `m_j·λ` (the
  model's `r_{ij} = gap/λ − q_{ij}` normalization means a demand
  bound contributes `q+1` cells, an unused arc keeps `q`).
- **C**: like A but the right end is closed by an angle-cap
  inequality (`∠ ≤ π − λ` on the last triangulation vertex) instead
  of a right fan.  **C is geometrically subsumed by B**: the cap
  `S_{L+1} ≤ π − λ` is equivalent to `H'_L = π − S_{L+1} ≥ λ`, i.e.
  it supplies the right boundary bound `b' ≥ 1` in the same master
  identity `2π = H_0 + H'_L + ΣD_j`.

Coverage after verifier-checked synthesis (target `δ ≥ τ`):
n4_high 448/519 (A 270, B 246, C 309), n4_low 341/401 (A 271,
B 206, C 243), s6 0/101 (chains exist — A 3130/B 1706/C 1357 valid
candidates — but none reach the high target; fat-arc dominates
there).  Union with fat-arc: n4_high 452/519, n4_low 381/401,
s6 40/101.

### Skeleton-driven certB coverage (`tools/certb_scan.py`)

The LP-synthesizer numbers above undercount: they require a *saved*
cap/angle constraint in a narrow position and never use the qs
baselines.  A skeleton-driven recognizer that computes certB's
actual hypothesis bundle — per-piece bit branches and order splits,
demand arcs with `m_j = max(q_j, 1)` (demand `∠ ≤ π−λ` gives
`arc ≥ λ`; the qs baseline `q_j·λ` combines by max), left boundary
`a = max(q_wrap, 1)` when the cap `∠(x1,x0,x_{L+1}) ≤ π−λ` is on the
arc branch, right boundary `b' = max(q'_wrap, 1)` likewise — finds:

- **s6: 101/101** leaves admit a certB hypothesis bundle with
  `σ ≥ 2` (`δ ≥ 1`) — the endpoint-closure family completely
  explains that regime's certificates (e.g. `leaf_0002`: anchor row
  0 triangulation through `L = 4`, `a = 1` from the cap
  `∠015 ≤ π−λ`, `b' = 1` from `q54 = 1`, `m = (1,1,1,1)`).
- n4_high: 387/519 with `σ ≥ 2`; residual best-σ dist
  `{0: 6, 1: 126, 2: 387}`.
- n4_low: 285/401 with `σ ≥ 1`; residual best-σ dist
  `{-1: 16, 0: 100, 1: 203, 2: 82}`.

This is a hypothesis-availability diagnostic (does the skeleton
admit certB data), not a produced certificate — but it shows the
endpoint-closure family is far broader than the LP-support scan
suggested.  The residual n4 leaves (e.g. `leaf_0177`'s mixed-sign
two-row combination, `dirArc(1,3,4)+dirArc(2,3,4) ≤ 2π−4λ`) are
genuinely different supports; variant A (`signed_chain_cert`,
right fan at `x_L`) and fat-arc/polygon shapes cover additional
mass — the families are complementary, not nested.

`signed_chain_certB` (K3bGeometry) is the kernel-checked form of B:
same `tri_piece_rel` telescoping, endpoint complement `hcomp`,
per-demand `m : ℕ → ℕ` bounds, score `σ = a + b′ + Σ m − 2n` giving
`δ ≥ σ/2`.  Regression `leaf_0046_certB`: the leaf-0046 skeleton
(`order[0]=[1,2,3,4]`, `order[4]=[0,1,2,3]`, `q03=4`, `q43=2`,
`q32=2`) gives `m = (1,1,2)`, `σ = 2`, `δ ≥ 1` — `5λ ≤ π`.
Axioms clean `[propext, Classical.choice, Quot.sound]`.
