# Lane E2 (wave 2) — adversarial challenger report

Mission: **break** the open gadget-selection claims, closing the
wave-1 coverage gaps.

- `T_low`  : Lean-consistent skeleton (`∃ r δ, 0 ≤ δ < 1 ∧ ModeA`)
  with `W > 2` admits a gadget of bound `≥ 1/2`.
- `T_high` : same with `W > 5/2` ⇒ bound `≥ 1`.

Base SHA: `b69e915` (`lane/integration`).  Branch: `lane/e2-challenger`.

## Verdict

**No theorem counterexample and no evaluator overcertification
found under the stated search envelope.**

This does **not** mean the theorems are true.  In fact the wave-2
data reframes the attack surface sharply (see "the vacuum
observation"): every consistent `W > 2` skeleton found anywhere
sits at `free_min = 1/2` exactly, and no consistent `W > 5/2`
skeleton was found at all — `T_high` may be vacuous, `T_low`
exactly tight.

One tooling bug **was** confirmed: `lane_a6._CAP_CACHE` is keyed
by `id(ctx)` and produces wrong bounds on warm-cache skeleton
streams (3 diffs/80 skeletons; all on LP-infeasible skeletons so
far — a real correctness hazard, not yet a soundness exploit).

## Operational semantics (pinned down this wave)

- `Skeleton.Consistent n` in `Jsp000404/GadgetSelection.lean` is
  `∃ r δ, 0 ≤ δ < 1 ∧ ModeA` — i.e. **capped** feasibility.
  Operational test: exact relaxed LP (δ ≥ 0, no cap) `min < 1`.
  (Capped-LP `min = 1` = phantom: needs δ ≥ 1.)
- Any `Valid` gadget bound `≤ free_min` (min δ over the *unclamped*
  ModeA system) — because `gadget_ge` is proved.  Therefore the
  clean kill certificates are pure LP facts, no evaluator needed:

      consistent ∧ W > 2   ∧ free_min < 1/2   ⇒  T_low dead
      consistent ∧ W > 5/2 ∧ free_min < 1     ⇒  T_high dead

## New machinery (this wave)

- `tools/e2_util.py`
  * `float_cons` — mode-A constraints of a *partial* skeleton
    directly in float form (no Fraction substitution);
  * `lp_min_f` — HiGHS (`scipy.optimize.linprog`) min-δ.  NOTE:
    `seidel_lp.lp_max` is effectively unusable at ~30 vars with
    equality pairs (>2 min vs ~3 ms per LP at s = 6) — all wave-2
    float LPs use HiGHS;
  * `guided` — interleaved (signature, q) DFS per vertex with
    monotone LP pruning: partial constraints are a subset of the
    full system, so partial relaxed-min ≥ 1 (or infeasible) prunes
    the whole subtree; `mode='cex'` additionally prunes
    free-min ≥ threshold (keeps only counterexample-viable
    branches); `qrestrict` allows targeted q-subfamilies;
  * exact wrappers `capped/relaxed/free_exact` via
    `residual_map.glp_min_delta` (Fraction simplex).
- `tools/e2_campaign.py` — parallel per-profile scan
  (feas + cex passes, exact verification of flagged leaves).
- `tools/e2_freedelta.py` — gen_cases enumeration with float
  relaxed/free screen per skeleton.
- `tools/e2_overcert.py` — extended evaluator (`lane_a6`,
  `CapKind.low` signed caps + vertex floors) vs exact LP;
  budgeted variant for s ≥ 5.
- `tools/e2_poison.py` — `lane_a6._CAP_CACHE` `id(ctx)` poisoning
  test (see hazards).
- `tools/e2_hunt_d0.py` — targeted δ = 0-forcing-vertex hunt.
- `tools/e2_exactver.py` — exact Fraction-LP re-verification of
  all consistent skeletons found by a campaign.
- `tools/e2_deep_target.py` — long-deadline single-profile hunt
  (used on `(0,0,1,4,4,5)`, `(0,1,1,1,4,5)`).
- `tools/e2_repro.py` — compact repro of the headline facts.

## Search envelope

### s = 3, n ∈ {3,4,6} — exhaustive

Same pattern: hi profile `(0,0,0)` (W = 3) has 0 consistent
skeletons (48–56 enumerated); mid `(0,0,1)` (W = 5/2) has
consistent skeletons, all `free_min = 1/2`.

### n ≠ s campaigns

`e2_campaign` full `W > 2` profile sweeps (20 s feas + 30 s cex):

| (s,n)    | profiles | consistent | max W cons | free-min set | viol |
|----------|----------|-----------|------------|--------------|------|
| (4,5)    | 19       | 6         | 5/2        | {1/2}        | 0    |
| (5,6)    | 80       | 17        | 5/2        | {1/2}        | 0    |
| (6,5)    | 114      | 27        | 5/2        | {1/2}        | 0    |

Spot-guided `(7,6)` on `(0,0,0,1,2,2,3)` W = 33/8 and
`(0,0,2,2,2,2,2)` W = 13/4: 0 consistent within ~55 s each.

### s = 6, n = 6 — guided LP-pruned DFS (the wave-1 gap)

`e2_campaign` over **all 197** `W > 2` deficit profiles
(feas pass 25 s + cex pass 40 s per profile, 8 workers,
1541 s wall):

- Guided DFS explores ~0.1–2.3 M signature nodes/profile vs
  wave-1's ~3.5 k blind random attempts.
- **43 profiles yielded consistent skeletons; max W = 5/2.**
- Every consistent leaf found (≤ 20/profile) has float
  `free_min = 1/2`; `cex` pass (free_min < thr pruning,
  thr = 1 for W > 5/2 else 1/2) found **0 leaves, 0 violations**
  in all 197 profiles.
- **All 23 wave-1 hi-band "seeds" exact-verified as PHANTOMS**
  (`relaxed_min = 1`, not consistent under Lean semantics — the
  wave-1 capped float LP counted `δ ≤ 1` boundary minima as
  feasible).  Wave-1's s=6 hi-band coverage was therefore
  phantom-only.
- `e2_exactver` re-verified every consistent profile exactly
  (Fraction LP): 43 profiles, free-min set `{1/2}`, viol = 0.
- Deep single-profile hunts: `(0,0,1,4,4,5)` 300 s / 137,890
  nodes → 0 found; `(0,1,1,1,4,5)` 300 s / 126,149 nodes →
  0 found (incomplete — deadline, not proof of inconsistency).

### s = 5, n = 5 — guided campaign (all 52 `W > 2` profiles)

`e2_campaign 5 5 all` (20 s feas + 30 s cex, 1050 s wall):

- 12 profiles yielded consistent skeletons; **max W = 5/2**
  (`(0,1,1,2,2)`, `(1,1,1,1,1)`); all consistent leaves have
  float `free_min = 1/2`; 0 cex leaves, 0 violations.

### s = 4, n = 4 — full census (COMPLETE)

Every `gen_cases` skeleton in all 13 `W > 2` profiles enumerated
(float relaxed screen; consistent leaves get float free screen;
`e2_census_s4.json`, 8,021 s wall):

| profile       | W    | skeletons | consistent | flo |
|---------------|------|-----------|------------|-----|
| (0,0,0,0)     | 4    | 8,646     | 0          | —   |
| (0,0,0,1)     | 7/2  | 40,662    | 0          | —   |
| (0,0,0,2)     | 13/4 | 45,240    | 0          | —   |
| (0,0,0,3)     | 25/8 | 33,024    | 0          | —   |
| (0,0,1,1)     | 3    | 197,752   | 0          | —   |
| (0,0,1,2)     | 11/4 | 223,974   | 0          | —   |
| (0,0,1,3)     | 21/8 | 153,228   | 0          | —   |
| (0,0,2,2)     | 5/2  | 249,568   | 10,368     | 1/2 |
| (0,0,2,3)     | 19/8 | 172,048   | 2,592      | 1/2 |
| (0,0,3,3)     | 9/4  | 121,152   | 1,296      | 1/2 |
| (0,1,1,1)     | 5/2  | 963,396   | 25,272     | 1/2 |
| (0,1,1,2)     | 9/4  | 1,078,566 | 39,528     | 1/2 |
| (0,1,1,3)     | 17/8 | 714,204   | 6,480      | 1/2 |

**Total: 4,001,460 skeletons; 85,536 consistent — all at
W ≤ 5/2, all with float free_min = 1/2.**

Since `gen_cases` enumerates every signature-consistent
completion (a superset of the Lean-consistent skeletons — an
inconsistent signature cannot be completed consistently), this
is an *exhaustive* s = 4 result: at s = 4 there is **no**
consistent skeleton at `W > 5/2` at all (`T_high` vacuous), and
every consistent `W > 2` skeleton has free-min exactly `1/2`
(`T_low` exactly tight, and the evaluator attains it — see
overcert table).

### δ = 0-forcing-vertex hunt (the sharpest T_low attack)

A vertex with `Σq = n−s+1` forces `Σr = m`, all `r = 1`, `δ = 0`
(fan equality alone).  Any *consistent* skeleton containing one
has `free_min ≤ 0 < 1/2` → instant T_low counterexample.
`e2_hunt_d0` restricted every `k = 0` vertex to `Σq = n−s+1`:
83 `W > 2` s = 6 profiles ending in 5, ~180 k nodes each —
**0 consistent skeletons contain a δ = 0-forcing vertex**.
(Note: wave-2 v1 `q_prefilter` wrongly excluded exactly these
`Σq = n−s+1` variants — off-by-one, fixed before the campaign.)

## The vacuum observation (main finding)

Across every `(s,n)` probed, Lean-consistent skeletons appear to
exist only at `W ≤ 5/2`, and every consistent `W > 2` skeleton
found has `free_min = 1/2` exactly.  Concretely:

- consistent skeletons DO exist (s = 4: 85,536 of them in the
  full census; s = 5: 12 profiles; s = 6: 43 profiles; n ≠ s:
  (4,5) 6, (5,6) 17, (6,5) 27 consistent profiles);
- consistent skeletons with `W > 5/2` found NOWHERE — at s = 4
  this is **exhaustive** (4,001,460 skeletons, 701,902 in
  `W > 5/2` profiles, zero consistent); at s = 5,6 and n ≠ s it
  covers ~460 `W > 2` profiles via guided DFS;
- consistent skeletons with `free_min < 1/2` found NOWHERE
  (float screens + exact re-verification of all 43 consistent
  s = 6 profile families: free-min set `{1/2}`);
- consistent skeletons with `free_min < 0` at `W > 2` found
  NOWHERE (negative-δ remains a `W ≤ 2` phenomenon);
- the free-min spectrum at `W > 2` appears to be
  `{1/2, 1, 3/2, 2, ...}` — matching the gadget-level spectrum.

If "consistent ⇒ W ≤ 5/2" holds, `T_high` is vacuous and `T_low`
is exactly tight — worth stating explicitly as a challenger-side
conjecture for the prover lanes.

## Extended-evaluator soundness (overcert hunt)

`lane_a6.enumerate_max_ext` bound vs exact `free_min`:

- s = 4: **280 skeletons scanned, 0 overcertifications**
  (`e2_overcert_s4.json`).  On the 11 consistent `W > 2` rows the
  bound equals `free_min = 1/2` exactly (the `T_low` bound is
  reached, never exceeded); the 55 consistent rows with
  `free_min < 1/2` are all at `W ≤ 2` — no `T_low` violation.
  Bounds `> free_min` occur only on LP-**infeasible** skeletons
  (vacuous — gadget bounds constrain nothing there).
- ext bound `= free_min` exactly on sampled rows, consistent
  and phantom alike (e.g. phantom `(0,0,2,2)` rows bound 1 =
  free 1; consistent `(0,1,1,1)` rows bound 1/2 = free 1/2);
  bound `< free_min` also occurs (undercertification — e.g.
  ext 0 or −1/2 on free-0 skeletons), never `>`.

### Hazard CONFIRMED: `lane_a6._CAP_CACHE` keyed by `id(ctx)`

`cap_options_ext` caches under `(id(ctx), v, negblk, maxsz)`;
freed `Ctx` ids are recycled by CPython.  `e2_poison.py` streams
skeletons through the evaluator without clearing the cache, then
re-runs each with a cleared cache:

- **3 bound mismatches in 80 skeletons** (maxsz = 3):
  `d = (0,0,1,3)` warm `4` vs cold `3`; `d = (0,0,0,2)`
  warm `4` vs cold `3` and warm `5` vs cold `4` — the poisoned
  bound keeps inflating across the stream
  (`e2_poison_s4.json` consolidated; logs `e2_poison_s4{,b}.log`).
- All diffs observed so far land on **LP-infeasible**
  skeletons, so no *soundness* violation demonstrated — but the
  mechanism is real: warm-cache runs of `lane_a6` are not
  deterministic across skeleton streams.  Any tooling using
  `lane_a6` on multiple skeletons must clear `_CAP_CACHE`
  (or key it by skeleton content) before trusting a bound.

## Tooling notes / bugs

1. `seidel_lp.lp_max` exponential-blowup at ~30 vars — replaced by
   HiGHS in all wave-2 code (`e2_util.lp_min_f`); keep
   `lane_e_util.lp_min_delta_free` for small cases only.
2. `q_prefilter` off-by-one (fixed): fan feasibility allows
   `Σq = n−s+1` (δ = 0 boundary), not `n−s+2`.
3. `lane_a6._CAP_CACHE` `id(ctx)` reuse hazard — CONFIRMED:
   warm-cache bounds differ from cold-cache bounds (3/80
   skeletons; all diffs on infeasible skeletons so far, hence no
   soundness violation yet, but the evaluator is nondeterministic
   under warm-cache use).
4. Wave-1 s = 6 seed library: all hi-band rows are phantoms under
   strict Lean consistency (re-verified exactly) — the "seeded
   hi-band coverage" was phantom-only.

## Coverage gaps remaining

1. s = 6/5 guided DFS is depth-first with deadlines — explored
   prefixes are large but not certified-complete per profile;
   `max_sols = 20` caps leaves per profile, so a counterexample
   skeleton could hide in an unexplored subtree of a profile that
   already yielded 20 consistent leaves.
2. s = 7 thin (2 spot profiles only); s ≥ 7 essentially open.
3. n ≠ s covered at (4,5),(5,6),(6,5) fully and (3,4),(3,6),
   (4,6),(7,6) sampled; larger |n−s| untouched.
4. Extended evaluator verified at s = 4 (280 skeletons) only;
   no s ≥ 5 gadget enumeration (LP-level analysis only) — the
   s = 5 budgeted evaluator pass did not run.
5. The "consistent ⇒ W ≤ 5/2" conjecture is challenger-side
   empirical — if a consistent hi skeleton exists anywhere it was
   not found.  At s = 4 it is exhaustive (full census); at
   s = 5,6 it rests on deadline-bounded DFS.
6. Exact free_min verification covers all consistent s = 6
   profile *families* (43 profiles, sampled skeletons) but the
   s = 4 census and s = 5/s = 6 campaigns used float LP screens —
   a free_min = 0.5−ε would have been flagged, and none was.

## Next attack suggestion

- Settle the vacuum question: either a proof attempt at
  "consistent ⇒ W ≤ 5/2" (which would vacuate `T_high`) or a
  deeper existence hunt for consistent `W > 5/2` skeletons at
  larger `s` / `n` (constraint-programming formulation rather than
  DFS).
- For `T_low`: the interesting region is `2 < W ≤ 5/2` consistent
  skeletons — all found sit at free_min = 1/2; a counterexample
  needs a *new* consistency structure, e.g. asymmetric/mixed-sign
  link cycles only reachable at s ≥ 6, or n ≠ s.
- Negative-δ remains confined to `W ≤ 2` — a `W > 2` skeleton
  feasible at δ < 0 AND at δ ∈ [0,1) simultaneously is the clean
  kill; target mid-band profiles with zero-`B_v` vertices.

## Artifacts

- `tools/e2_util.py`, `e2_campaign.py`, `e2_freedelta.py`,
  `e2_overcert.py`, `e2_poison.py`, `e2_hunt_d0.py`,
  `e2_exactver.py`, `e2_deep_target.py`, `e2_repro.py`
  (`e2_repro.py` reproduces the headline facts in ~3 min).
- Data: `e2_campaign_{s4n5,s5n5,s5n6,s6n5,s6n6}_all.json`,
  `e2_census_s4.json`, `e2_exactver_s6n6.json`,
  `e2_freedelta_s4n4_all.json`, `e2_overcert_s4.json`,
  `e2_poison_s4.json`, `e2_hunt_d0_s6n6.json`,
  `e2_verify_first.json`, logs `e2_*.log`.
