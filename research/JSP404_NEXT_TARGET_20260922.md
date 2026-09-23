# JSP-000404 — next-target analysis (cheapest path to the prize)

Reconnaissance: two read-only passes over `jsp-000404-lean` (master),
the owner worktree, and the merged trunk worktree `jsp-wt-merge`
(branch `lane/integration`, head `0ceac4d`).

## State of the prize in the merge tree

The merge trunk is far ahead of the lane branches.  Verified sorry
inventory there:

| sorry | file:line | content |
|---|---|---|
| `sendov_lower` | MainTheorem.lean:20 | **ROOT lower bound, N ≥ 9 branch only** (N = 3…8 fully proved) |
| `staircase_of_legality` tail | Section4Legality.lean:165 | superseded by conditional `staircase_of_cert` |
| `exists_removable_vertex` | Deletion.lean:1294 | deprecated route; **statement is false as written** (no sortedness/Io-bounds hypotheses — countermodel: `lam=1, s=4, row=[5], del=0`) |
| `exists_removable_hull_vertex` | Deletion.lean:1304 | same, plus `Q` unconstrained vs `row`/`del` |
| `maxGap_boundary_emission` | GeometricDeletion.lean:629 | the deletion-route geometric leaf |
| `sendov_upper` | UpperBound.lean:104 | **PROVED** (sharpness, `ε`-threshold form, third-party constructions + new local proofs) |

**The whole remaining gap for `sendov_lower` is one mathematical
node**: `CertExists` (`Induction.lean:41`) — on every legal `t ≥ 4`
configuration with `potential > sendovCap n big`, the emission
dichotomy holds (≡ a removable vertex exists).  Downstream is proved:
`potential_le_sendovCap → staircase_of_cert →
sendov_alpha_eq_of_geometricCertificates / sendov_lower_of_selection`.

## What the other lanes already closed (do NOT re-prove)

- per-triple weighted bound (candidate A): `TriangleRestriction`
  `selected_triple_weights_le_{low,high}` — parity with competitor
  `triple_capacity_low/high`, via `rowScore_le_of_sublist` +
  `gapScore_merge`.
- S=1 propagation (candidate B): `OneSaturatedLow.
  potential_le_two_pow_of_saturated` — entire LOW cap `≤ 2^n` at
  arbitrary s with one saturated centre.
- two-saturated ⇒ remaining deficits ≥ 2 (candidate C):
  `TwoSaturatedDeficit.rowDefect_ge_three_of_two_saturated`
  (`rowDefect = d+1`, so defect ≥ 3 = d ≥ 2) — **already sharper than
  the competitor's `K_c ≤ n−2`** — plus `TwoSaturatedHigh.
  potential_le_high_of_two_saturated` (complete HIGH cap, real
  geometry).
- geometric saturation family: `SaturationPacking.not_three_saturated`,
  `saturatedCenters_card_le_{one_low,two}`, `Induction.
  angle_le_pi_sub_of_saturation` (geometric L2-min),
  `not_two_saturated_of_delta_lt_half` (geometric L3),
  `rowDefect_eq_one` (geometric B1).  The owner `SaturatedStructure`
  chain is the skeleton-level twin of these — redundant unless the
  gadget route is revived.
- bridge wiring (candidate E): `Induction.exponents_map_pow_sum`,
  `circleDirs_eq_dedup_directionRow`, `cycGaps_sum_eq_pi`,
  `rowScore_dedup`.

## What is still open (the real math)

`CertExists` case-splits by saturated count using proved lemmas:

- LOW + S≥1: closed (`OneSaturatedLow` gives `potential ≤ 2^n`
  directly, no dichotomy needed).
- HIGH + S≥2: closed (`TwoSaturatedHigh` gives `potential ≤
  2^n+2^{n-2}`).
- **LOW + S=0** — the Kraft packing crux.  Documented falsifications:
  "S=0 ⇒ K≤1" is false in the high band
  (`PentagonPacking.strict_no_saturation_counterexample`, kernel-checked
  skeleton, geometric origin = regular pentagon); a floating-point
  n=3 nine-point counterexample also exists.  Surviving reduction:
  the O+D cut-selection accounting (`GLOBAL_PACKING_RESEARCH.md`).
- **HIGH + S∈{0,1}** — the two-cover criterion
  (`ONE_SATURATED_HIGH_GEOMETRY.md`): partition G/H with interval
  covers, `k_v ≤ m − a_X(v)` ⇒ `Σ2^k ≤ 2^{m_G}+2^{m_H}`;
  probe-validated (1188+434 configs, no failure); sufficiency is
  mechanical, existence of the split is the open part.

## Ranked next targets (cost vs prize value)

1. **`CertExists` case-split reduction** (~100–200 lines bookkeeping).
   Prove `CertExists` from its two open restrictions using the
   saturated-case lemmas above.  Contracts the prize blocker to
   exactly LOW-S=0 and HIGH-S≤1 — the cheapest load-bearing step.
2. **Two-cover sufficiency for HIGH-S=1** (~300–500 lines, mechanical
   over `IntervalPacking.weighted_interval_packing` +
   `JSP404.sum_free_binary_coordinates_le`).  Turns HIGH-S=1 into an
   existence statement with a validated search target.
3. **`maxGap_boundary_emission`** (geometric leaf; medium-hard angle
   chase, emission lemmas already proved).  Independent of routes 1–2;
   closes the deletion-route input.
4. **LOW-S=0 Kraft/O+D packing** — the actual crux, highest cost and
   highest value; no cheap shortcut survives (all documented
   falsified).
5. **FanSystem parity items** (`three_saturated_impossible`,
   `k_v ≤ n−1`, ~50–90 lines total): near-free but redundant with the
   geometric versions already merged; only worth it to complete the
   skeleton layer.
6. Housekeeping: restate or retire `exists_removable_vertex{,_hull}`
   — false as stated; nothing on the live route depends on them.

## Bottom line

The cheapest prize-advancing unit is **#1 (CertExists case-split)** —
it isolates the two open mathematical cores using only proved lemmas.
The cheapest *new math* is **#2 (HIGH-S=1 two-cover sufficiency)**.
The decisive open math is **#4 (LOW-S=0)** — the same wall the
competitor's 09-22 snapshot admits ("the exponent-count bound does not
control the total of all smaller weights").
