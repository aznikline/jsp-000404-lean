# Lane E — adversarial challenger report

Mission: **break** the open gadget-selection claims, not prove them.

- `T_low`  : mode-A consistent skeleton with `W > 2` has a gadget of
  level ≥ 1  (operationally: LP/gadget bound `δ ≥ 1/2`).
- `T_high` : mode-A consistent skeleton with `W > 5/2` has a gadget of
  level ≥ 2  (operationally: bound `δ ≥ 1`).

Base SHA: `ccc95c0`.  Worktree branch: `lane/e-challenger`.

## Verdict

**No counterexample found under stated search envelope.**

This does **not** mean the theorems are true.  The s=6 combinatorial
skeleton space is essentially unexplored (see coverage gaps), and a
real semantic discrepancy was found in what "consistent" means.

## Search envelope

### s = 4 (n = 4) — near-exhaustive

- Variant space = all (order, bits, qs) per profile via
  `generic_enum.build_VV`; capped LP (`0 ≤ δ < 1`, exact Fraction
  simplex `residual_map.glp_min_delta`) over the full space in the
  bands `W ≤ 2`, `2 < W ≤ 5/2`, `W > 5/2`.
- Fresh re-verification: 40 skeletons/profile × all 35 profiles
  (`tools/e_reverify_s4.py`) — spectra only `{0, 1/2, 1, inf}`;
  hi-band feasible ⇒ `δ_min = 1`, mid-band ⇒ `δ_min ∈ {1/2, 1}`,
  lo-band includes `0`.  **0 violations.**
- link_graph vs LP fresh sample: **43/43 match** (all `δ_min = 1/2`
  cases, bound achieved exactly).
- Evaluator stress (`tools/e_evalstress.py 4 10 0`): tested = 350,
  match = 334, **over = 0**, under = 16 — every under is a gadget
  bound equal to the *free*-δ LP minimum below 0 (see semantics
  below); the enumerator is LP-optimal, never unsound.
- Free-δ sweep: 140,000 variant tuples (≤4000 sampled per profile),
  1,572 free-feasible; **0 skeletons with W > 2 and free-min < 1/2**.
  Negative-δ feasibility observed only in `W ≤ 2` profiles (442
  samples, free-min ∈ {−1/2, −1}).
- Relaxed scan on capped-**infeasible** skeletons in W > 2 profiles:
  19,388 tested, **0 with relaxed-min below the band threshold**
  (all infeasible-under-cap cases are either truly inconsistent or
  need `δ ≥` the required bound anyway).

### s = 5 — degenerate-geometry batch only

- 262 feasible skeletons (34 unique profile/δ rows) from degenerate
  configs (equal-spaced collinear, near-duplicate points, lattice
  subsets, exact regular polygon, semicircle) × δ ∈ {0,…,0.95}.
  **0 violations**; W > 2 rows all have min-δ ∈ {1/2, 1}, free-min
  identical.

### s = 6 (n = 6) — geometry-seeded, combinatorially thin

- Pure combinatorial sampler (`tools/e_scan_s6.py`): signature-pair
  consistency rate ≈ 6.6%; for a *fixed* consistent signature tuple
  only ~3/3000 random q-assignments pass the triangle prefilter and
  ~0 pass the LP.  Most sampled profiles yielded **zero** feasible
  skeletons in ~3.5k attempts — the combinatorial feasible region is
  effectively unsampled.
- Geometric generator (`tools/e_geom.py`, families collinear /
  collinear2 / circle / cluster / twoarc / random, δ-grid):
  997/1500 configs feasible.  Hi-band rows all `δ_min = 1`,
  mid-band `δ_min ∈ {1/2, 1}` — **0 violations**.
- Degenerate-geometry batch (equal spacing, duplicates, lattice):
  201 feasible / 27 unique, **0 violations**.
- Seed library (`tools/e_seeds.py` → `lane_e_seeds_s6n6.json`):
  2,335 feasible skeletons over 199 distinct profiles (23 hi-band,
  20 mid-band).  All 143 W > 2 seeds re-checked under **free-δ**:
  free-min ∈ {1/2, 1}, none < 1/2.
- Profile-preserving mutation climb (`tools/e_climb.py`), hi-band:
  128 profiles, **viol = 0** (371 s); mid-band climbs bottomed at
  relaxed-min 1/2, never below.
- Boundary profile `d = (0,1,2,2,2,2)`, `W = 5/2`: capped-min 1
  observed combinatorially, 1/2 observed geometrically — consistent
  with theorems (W = 5/2 not > 5/2; ≥ 1/2 needed for T_low).

### s = 7 — thin

- One geometric run (`lane_e_geom7.log`): hi-band `δ_min = 1`,
  no violation; very limited coverage.

### n ≠ s — nearly untested

- s=5,n=4: 28 feasible; s=4,n=5: 26; s=5,n=6: 25; s=6,n=5: 27;
  s=6,n=7: 1 in 508 s; s=7,n=6: 16 in 153 s.  No violation seen;
  coverage negligible.

## Concrete findings

### 1. `inf` does NOT always mean structural inconsistency

The handoff's reading — capped-LP `inf` ⇒ skeleton inconsistent for
all δ — is **wrong**.  Removing only the `δ < 1` cap turns some `inf`
skeletons into high-debt feasible ones:

- Repro: `python3 tools/e_inf_semantics.py`
- `d = (1,1,1,1)` (W = 2), ks = [2,2,2,2], idxs `(0,43,16,1)`:
  capped LP infeasible; relaxed LP min δ = **2** (exact);
  `enumerate_max` bound = **2** (level M = 4) — the gadget family
  certifies the full debt.
- Relaxed-min distribution over sampled `inf` skeletons at s=4:
  9 cases at `3/2`, 21 cases at `2` (profiles (0,0,0,1), (0,0,1,1),
  (0,1,1,1), (0,0,1,2), (1,1,1,1), …).

This does not violate T_low/T_high (such skeletons carry *more*
debt), but any "inf ⇒ inconsistent" reasoning in the pipeline is
invalid, and `inf` skeletons in W > 5/2 profiles are the natural
place to look for `δ ≥ 1` gadgets.

### 2. Three different "consistent" semantics diverge

`Jsp000404/Gadget.lean` `ModeA` has **no** `0 ≤ δ < 1` hypothesis;
the checker adds them.  Measured on s=4:

- capped (`0 ≤ δ < 1`): the operational model.
- relaxed (`δ ≥ 0` only): `inf` splits into "needs δ ≥ 1" vs truly
  inconsistent — all 19,388 sampled W > 2 cases that are feasible at
  all satisfy their band threshold anyway.
- free (δ ∈ ℝ): 1,572/140,000 sampled tuples feasible; negative-min
  skeletons exist (min −1/2, −1) but **only in W ≤ 2 profiles**.
  Repro: `python3 tools/e_free_delta.py` —
  `d = (1,2,2,2)`, idxs `(0,36,12,0)`: capped min 0, free min **−1/2**,
  and `enumerate_max` bound = **−1/2** exactly (the enumerator proves
  the tight bound the capped LP cannot even see).

So far every W > 2 skeleton tested satisfies its threshold under
**all three** semantics, but the Lean statements quantify over
whichever consistency they actually use — worth pinning down.

### 3. Tooling bug found and worked around

`generic_cegis.lp_min_delta_f` passes `bounds = [(0,1)]` per variable
to `seidel_lp.lp_max`, silently clamping δ to [0,1] even when the
`'δ<1'`/`'δ≥0'` constraints are skipped — all earlier "relaxed" and
"free" float runs through that path were secretly capped.
`lane_e_util.lp_min_delta_free` (bounds = None) is the corrected
version; all free/relaxed numbers in this report use it or the exact
`residual_map.glp_min_delta`.

### 4. Budgeted-enumerator undercounts at s=6 (provisional only)

`enumerate_max` is infeasible to run at s=6, so a budgeted variant
(`e_evalstress.enumerate_budgeted`, max path length, fan cap) was
used.  It undercounts the capped LP, e.g. `d = (0,1,2,2,2,2)`,
W = 5/2, capped-min = 1 (= free-min): bound = 1/3 (small budget),
2/5 at max_len=3/fan_cap=80 (758 s), 1/2 at max_len=4/fan_cap=150
(25,229 s) — monotone convergence toward the LP value but still
short of 1.  These are **budget artifacts**, not confirmed
evaluator bugs: at s=4 the full enumerator matched the free LP on
all 350 tested skeletons including negative bounds.

## Confidence-limiting coverage gaps

1. **s=6 combinatorial feasible region nearly unsampled.**  Random
   consistent skeletons are ~1e-3–1e-4 of signature space; searches
   effectively covered only geometry-reachable skeletons and their
   mutation neighborhoods.  Exotic non-geometric consistent
   skeletons — if any exist — are the blind spot.
2. **Full `enumerate_max` unverified at s ≥ 6.**  Only budgeted
   enumeration run; undercounts expected from truncation.  No
   overcounts observed anywhere.
3. **Free-δ sweep sampled, not exhaustive** (≤4000 of up to ~7e9
   variant tuples per s=4 profile).
4. **n ≠ s** essentially untested (a few dozen samples total).
5. **Structured signatures** (all-equal bits, zero-q cells, q_arc =
   n−1/n boundaries, symmetric orders) are covered exhaustively at
   s=4 only via full enumeration; at s ≥ 5 only via degenerate
   geometry families.
6. **Boundary δ values** are exact Fractions where checked (minima
   1/2 and 1 occur and are tight), but no systematic
   just-below-threshold grid was run at s ≥ 5.

## Next attack suggestion

The promising blind spot is the s=6 *non-geometric* consistent
skeleton space.  Build a guided constructor: incremental signature
DFS with LP pruning on partial assignments (or a SAT/SMT encoding of
edge-consistency + triangle-interval + q-choice) targeted at the
hi-band profiles that currently have **no** seed — e.g.
`d = (0,0,1,4,4,5)` W = 85/32, `(0,1,1,1,4,5)` W = 83/32,
`(0,0,2,2,2,x)` family.  Second: settle the consistency semantics in
Lean — if `SkeletonConsistent` is free-δ ModeA, the negative-δ region
(currently seen only at W ≤ 2) deserves a targeted hunt at W > 2.

## Artifacts

- `tools/lane_e_util.py` — shared helpers incl. corrected free/relaxed
  LP (`lp_min_delta_free`, `lp_f_free`, `lp_f_relaxed`).
- `tools/e_inf_semantics.py`, `tools/e_free_delta.py` — repro scripts.
- `tools/e_reverify_s4.py`, `tools/e_scan_s6.py`, `tools/e_geom.py`,
  `tools/e_seeds.py`, `tools/e_mutate.py`, `tools/e_climb.py`,
  `tools/e_evalstress.py` — search machinery.
- Data: `lane_e_seeds_s6n6.json`, `lane_e_geom_s6.json`,
  `lane_e_climb_s6.json`, `lane_e_mutate_s6.json`,
  `lane_e_evalstress_s4.json`, `lane_e_d012222_sols.json`,
  logs `lane_e_*.log`.
