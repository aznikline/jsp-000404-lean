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
| P4 | **Kraft packing** (K3) — sole math crux | open; K1/K2 kernelized |
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
