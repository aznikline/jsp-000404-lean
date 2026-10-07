# Devin F17 selector lane, 2026-10-08: boundary-event reduction (selector NOT proved)

Branch `agent/devin-f17-selector-20261008`, base `c152f27739f3e1b5c6001c57b60956419fe0890e`
(`agent/devin-f17-hull-gap-20261008`). New module `Jsp000404/DevinF17Selector.lean`.
`DevinF17HullGap.lean` and every older file are unchanged byte-for-byte.

**Status: the F17 hull-zero selector is NOT proved. The all-N lower bound for
`N >= 17` remains OPEN.** Nothing here claims a selector is impossible either.

## Setting (no extra premises)

Every theorem takes the actual
`H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam` (n4 LOW,
cap 16), `3 <= s`, an original zero pair `p`, `p.succAbove q` (both original row score
0), and uses only the Model's own proper-subset capacity through the existing
`ActualZeroPairDeletionBudget.actual_zero_pair_deletion_budget` and
`DevinF17HullGap.actual_zero_pair_outside_gap_plateau`. No capacity, cover,
partition, forbidden-growth, selector, restricted-Model or fractional-floor premise
is added. Windows `W`, `W'` are actual `ActualHullRayWindow.Window`s of the original
and the twice-restricted configuration; `hull_observer_windows` builds both from
`IsHullVertex c (p.succAbove (q.succAbove a))` alone (via `isHullVertex_restrict`,
original hull -> restricted hull only; the converse is NOT used and is false).

Write `t = gapScore lam (pi - W.width)` and the *boundary event* of observer `a`:
`EV(a) := (t + 2) * lam <= pi - W'.width`.

## Proved (Lean, trust 0, axioms only propext / Classical.choice / Quot.sound)

| declaration | statement (informal) |
|---|---|
| `gapScore_wrapGap_le_rowScore` | `gapScore lam (wrapGap l) <= rowScore lam l` |
| `outside_score_le_rowScore` | for an actual window and any nonzero reference `e`, `gapScore lam (pi - W.width) <= rowScore lam (directionRow o e c a)` |
| `restricted_score_eq` | twice-restricted row score = original score + second-deletion `rowGain` (first deletion is gain-free because `p` is a zero target) |
| `zero_observer_outside_lt_three` | retained original zero observer: `pi - W'.width < 3 lam` |
| `two_zero_observers_not_both_wide` | two DISTINCT retained zero observers cannot both have `2 lam <= pi - W'.width` |
| `boundary_event_zero` | `EV(a)` forces: `a` is an original ZERO observer, `t = 0`, and `pi - W'.width < 3 lam` |
| `boundary_event_unique` | `EV(a)` and `EV(b)` for the same zero pair imply `a = b` |
| `hull_observer_windows` | original hull vertex retained -> actual original and restricted windows exist |

Mechanism: an observer whose restricted outside gap reaches `(t+2) lam` has restricted
row score at least `t + 1`; positive observers are excluded by the plateau
(`E < (t+2) lam`), so the observer is zero with gain >= 1, which costs >= 1 of the
pair budget 1; two such observers cost 2 > 1; a zero observer reaching `3 lam` would
cost 3 > 1.

**Next usable consumer.** Any argument that exhibits, for some original zero pair of
the actual Model, TWO distinct retained original hull observers satisfying `EV`
(or one observer with restricted outside gap `>= 3 lam`) now gets `False` from
`boundary_event_unique` / `boundary_event_zero`. Exact missing bridge:

> **(SEL)** From `H` alone (potential 17, cap 16, n4 LOW), produce original zero
> targets `p`, `p.succAbove q` and two distinct retained original hull vertices
> `a != b` with `EV(a)` and `EV(b)` (or one with `3 lam <= pi - W'.width`).

## Paper analysis of why SEL is hard (paper only, not formalized)

Turning identity (checked numerically below, residual < 1e-50): if both deleted
points are hull vertices and their removal exposes no new vertex, the two deleted
exterior angles are redistributed onto the surviving neighbours' exterior angles.
Each deleted exterior angle is `> lam` (LOW legality: every hull angle `< pi - lam`),
so the neighbours together gain `> 2 lam` of exterior angle. That alone does NOT
cross an integer threshold: a neighbour with exterior angle `x` crosses
`(t+2) lam` only if its gain exceeds `(t+2) lam - x`, which can be close to `lam`
or close to `2 lam`, and the two gains can concentrate on one neighbour. Moreover,
when the removal exposes an original interior point, that point absorbs turning and
is not an original hull observer (outside the scope of `EV` and of the plateau).

## Falsified / insufficient subclaims (controls; `verification/.../controls/`)

All replayed at 50 digits by `controls/verify_controls.py`; output
`controls/controls_output.txt` (floor margins printed so no floor is near a tie).

1. *"The local zero-deletion ledgers alone (every single zero deletion expense 0,
   every zero-pair expense <= 1) force two boundary events for some pair."*
   FALSE. Control **C8** (8 points, all hull, all scores 0, `lam = 0.764683`,
   legal with slack 0.0040): every single expense 0, every zero-pair expense <= 1,
   every pair has at most one event. Control **C6** (6 points, all hull, scores
   `[0,1,1,0,0,0]`, `lam = 0.709937`): same, and the events occur only at zero
   observers (consistent with `boundary_event_zero`). Both are low-potential
   (8 and 8), so they are NOT F17 Models; they only show SEL must use the
   potential-17 / minimality data, not the local ledgers.
2. *"Adjacent hull zero deletions always produce two events."* FALSE as a
   ledger-free statement in C8 (adjacent pairs give exactly one event). Regular 7 at
   `pi/4` does give two events for adjacent pairs, but it violates the pair budget
   (expense 2), so it is only a low-potential control, not an F17 Model.
3. F16 five-point control at `7 pi/30` (scores `[3,1,1,1,1]`, potential 16): no
   original zero target, so SEL's hypotheses are vacuous there; consistent.
4. *"An all-hull configuration suffices."* In an F17 Model with potential 17 and
   all scores 0 one needs 17 points, while LOW legality bounds the hull size
   (each exterior angle `> lam > 2 pi / 9`, so at most 8 hull vertices). Hence an
   F17 Model must have original interior points or positive scores; SEL must handle
   exposure of interior points, which the plateau and `EV` do not see.
   (Search for ledger-satisfying controls WITH interior points: see
   `controls/interior_search.txt`.)

Known traps respected: no global projective gap `>= lam/2`, no LOW gap
`>= pi - n lam`, no pure-interior 3-lam selector, no assumption that the new hull is
the old hull minus deletions, no incoming-zero transfer to positive targets, no
summing slack of distinct covers, no FixedCard whole-band bound, no fractional
floors.

## Verification

See `verification/devin-f17-selector-20261008/RECEIPT.md`.
