# Lane A — LOW gadget selection (`W > 2 ⇒ score ≥ 1`)

Status: **the selection step remains OPEN** (it is the documented
project crux).  This lane (i) found and fixed a real *gap in the
gadget certificate language* — complementary lower-bound cap entries
("extended caps" / vertex floors) — without which the gadget grammar
cannot certify several skeletons at all; (ii) ported and extended the
frozen Lean gadget semantics (`Gadget.lean`) accordingly; (iii) pinned
the exact missing proposition in compiling Lean
(`GadgetSelection.lean`) with the full soundness reduction proved; and
(iv) validated the extended evaluator on the whole `s = 4` corpus
sample.  No `sorry` anywhere.

## What was proved in Lean (PROVED)

Files added/changed on this branch:

* `Jsp000404/Gadget.lean` — ported from `lane/c-gadget` (base
  `ccc95c0`) and **extended**:
  * new `CapKind.low`: complementary `∠ ≤ π−λ` used as a *lower*
    bound `Σ_arc r ≥ 1 − q_arc`, i.e. the signed cap
    `−Σ_arc r ≤ q_arc − 1` (`sgn = −1`, `B = q_arc − 1`, `u = 0`);
  * `CapEntry.sgn : ℤ` (`±1`); coverage in `Gadget.Valid` is now the
    *signed* per-gap condition `max (−coef) 0 ≤ Σ m·sgn` (required on
    every gap, which also legalises *floor* caps on empty negative
    blocks — see below);
  * `cap_bound` reproved for the signed statement
    `sgn·Σ_range r ≤ B + u·δ`; `cap_total` generalised to signed
    coverage (`U ≤ Bcap + u·δ` still holds);
  * level theorems unchanged in form: `gadget_ge`,
    `gadget_ge_half`, `gadget_ge_one`.  `#print axioms`:
    `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
* `Jsp000404/GadgetFixtures.lean` — new; the checker-discovered
  **vertex-floor certificate** replayed in Lean: the phantom
  skeleton `(0,93,75,50)` (`k = (3,2,2,1)`, `W = 9/4`) plus its
  two-entry signed cap gadget; `phantomFloor_valid`,
  `phantomFloor_bound : bound = 1`, `phantomFloor_score` all closed
  by `decide`/`native_decide`.  This is a complete end-to-end check
  that the `CapKind.low` extension is both necessary and
  sufficient to express the certificate the old grammar missed.
* `Jsp000404/GadgetSelection.lean` — new; all proved:
  * `VertexData.kexp`, `Skeleton.d`, `Skeleton.W` (`ℚ`-valued
    `Σ_v 2^{−d_v}`, `d_v = (n−1) − Σ_g max(q−1,0)`);
  * `Skeleton.Consistent n` — `∃ r δ, 0 ≤ δ < 1 ∧ ModeA n sk r δ`;
  * `GadgetSelectionLow s n`, `GadgetSelectionHigh s n` — the exact
    missing propositions (as `Prop`s, not sorried theorems);
  * `bound_half_unfold`, `bound_one_unfold` — rational bound
    `≥ t` ⇒ capacity inequality used by `gadget_ge`;
  * **`selection_low_sound`**: `GadgetSelectionLow s n` ⇒ every
    consistent `W > 2` skeleton has `δ ≥ 1/2` — the complete LOW
    theorem modulo the single open combinatorial step;
  * `selection_high_sound` — the lane-B analogue (`δ ≥ 1`).
* `Jsp000404/DebtChain.lean` — one-line repair: `debt_residual_ge`
  had a latent `le_trans`/`mul_comm` mismatch (the file was outside
  the import tree at `ccc95c0` and never compiled); fixed with the
  same patch used on `lane/c-gadget`.

## The extended-cap discovery (the lane's mathematical content)

The frozen evaluator (`tools/link_graph.py`) reported "no gadget"
(`best = 0`) on skeletons such as `idxs = (0,93,75,50)` for which the
LP proves `δ_min = 1`.  These are *phantom* skeletons — mode-A
infeasible for `δ < 1` — so `SkeletonConsistent` excludes them, but
the gap still mattered for two reasons:

1. it showed the gadget grammar was **incomplete**, not just
   unproven — a selection theorem stated over the old grammar would
   have a strictly larger "no-gadget" class than the LP-optimal one;
2. the missing mechanism is real certificate structure: e.g. at one
   vertex, a direct cap `r₀ + r₁ ≤ δ` combined with a complementary
   lower bound `r₀ ≥ 1` (from `∠ ≤ π−λ` on a complementary arc with
   `q_arc = 0`) and `r₁ ≥ 0` yields `δ ≥ 1` — a **vertex floor**, a
   gadget with *zero equalities* whose cap combination on the empty
   negative block certifies `0 ≤ −1 + δ`.

`tools/lane_a6.py` implements the generalised per-vertex cap step:
a cap is any subset of primitive entries `{r ≤ 1, arc-uppers,
comp-lowers}` whose combined coefficient vector `α` satisfies
`α_g ≥ κ_g` on the negative block `N` (possibly empty) and `α_g ≥ 0`
off `N`; cost `(Σ const, Σ δcoef)`; `N = ∅` yields floor options.
This exactly matches the `CapKind.low` + signed-coverage semantics
now in `Gadget.lean`.

## Empirical validation (CHECKER-VALIDATED, not proofs)

* All **72** previously-failing "hard" skeletons (LP `δ_min = 1`,
  old evaluator `best = 0`) certify `δ ≥ 1` under the extended
  evaluator — matching LP exactly (`lane_a4_out.txt` targets
  re-run: `72/72` covered, all bounds `≥ 1`, one `= 2`).
* Broad run `tools/lane_a7.py`: `780` skeletons sampled across all
  **13** `W > 2` profiles of `s = n = 4` (60 per profile), computing
  LP `δ_min` and the extended gadget bound (early-exit at the LP
  target): **0 failures** — `tools/lane_a7_out.txt`:
  `482` infeasible (phantom) skeletons all certified `≥ 1`,
  `36` skeletons at LP `δ_min = 1/2` all certified `≥ 1/2`,
  `262` at LP `δ_min = 1` all certified `≥ 1`.  Notably **no
  sampled `W > 2` skeleton had `δ_min = 0`** — consistent with the
  selection conjecture.
* Earlier runs (`lane_a2_out.txt`): `499,472` skeletons lacking a
  level-1 *fan* gadget all admitted level-1 gadgets through links —
  link gadgets are essential, fans alone do not suffice.
* `lane_a_par_out.txt`: `5000` sampled skeletons, all covered.

## Structural facts discovered (CHECKER-VALIDATED / CONJECTURED)

* `k_v = Σ_g max(q_{v,g} − 1, 0)` and `Σ_g q_{v,g} ≤ n` give the
  exact budget identity
  `B_v = n − Σq_v = d_v + z_v − (s−2)`
  where `z_v = #{g : q_{v,g} = 0}` and `d_v = (n−1) − k_v`.
  This is the direct link between the deficit profile `W(d)` and
  the fan budgets that enter gadget bounds — the candidate
  **capacity lemma** channel.  (CONJECTURED as the mechanism of the
  missing step; the identity itself is a proved computation.)
* Consistency forces `B_v ≥ 0` (i.e. `d_v ≥ (s−2) − z_v`) and:
  direct arcs need `q_arc ≤ n−1`, complementary arcs `q_arc ≤ n`
  (else `pure_gadget`/floor certificates fire).
* A `k_v = n−1` vertex (`q = (n,0,…,0)`, `B_v = 0`, `Σr = δ`) forces
  every arc containing the big cell to be complementary; each such
  complementary arc yields `Σ_arc r ≤ δ` — a rigid local structure.
* `W = 2` boundary skeletons (e.g. deficit `(0,1,2,2)`) exhibit
  "comb" structures saturating a Kraft-type equality — supporting
  the layer-cake/capacity reading of the contrapositive.
* The generalisation `W > 2 + m/2 ⇒ score ≥ m+1` is FALSIFIED at
  `m = 2` (profile `(0,0,0,0)`, `W = 4`, `δ_min = 1`) — known, not
  re-litigated.
* Complementary-angle count per vertex is *not* fixed (observed
  distribution 7832 vs 4168 for 1 vs 2 comp angles at `s = 4`).

## The open step — precise statement

```lean
def GadgetSelectionLow (s n : ℕ) : Prop :=
  ∀ sk : Skeleton s, sk.Consistent n → 2 < sk.W n →
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) / 2 ≤ g.bound n sk
```

(`Jsp000404/GadgetSelection.lean`.)  Equivalent contrapositive:
*no valid gadget of bound `≥ 1/2` ⇒ `W ≤ 2`.*

### Decomposition

1. `GadgetSelectionLow` — the whole missing step.  Empirically the
   *extended* gadget language reaches the LP bound on every
   `W > 2` skeleton examined (consistent or phantom); whether
   consistency is needed at all in the statement is unknown —
   `inf` skeletons (infeasible for all `δ`) may still lack gadgets,
   so `Consistent` is kept.
2. Candidate route (user-suggested, still the best): forbid each
   gadget family in turn — vertex floors, single-fan strips,
   endpoint-capped link paths, closed cycles — and aggregate the
   resulting local constraints into `Σ_v 2^{k_v} ≤ 2^n`
   (i.e. `W ≤ 2`) via the identity `B_v = d_v + z_v − (s−2)`
   and a Kraft/layer-cake argument over link components.
3. Alternative route: prove **evaluator completeness**
   (best gadget bound = LP `δ_min` whenever bounded — empirically
   exact on the corpus), then the theorem reduces to the pure
   feasibility statement *feasible at `δ < 1/2` ⇒ `W ≤ 2`*, which
   needs no gadget language at all.  Completeness itself is
   unproven but checkable per-instance.

### Minimal unresolved step (honest)

A general (arbitrary `s`, `n`) combinatorial proof that the
forbidden-gadget constraints bound `Σ_v 2^{k_v} ≤ 2^n`.  All
supporting machinery (gadget semantics, soundness, the `δ`-bound
reduction) is proved; the gap is exactly the existence/counting
argument.

## Files

* `Jsp000404/Gadget.lean` — extended gadget semantics (signed caps,
  `CapKind.low`), fully proved soundness.
* `Jsp000404/GadgetSelection.lean` — `Consistent`, `W`,
  `GadgetSelectionLow/High`, proved `selection_low/high_sound`.
* `Jsp000404/GadgetFixtures.lean` — phantom floor-certificate
  fixture, machine-checked (`bound = 1`).
* `tools/lane_a6.py` — extended-cap evaluator (floor certificates).
* `tools/lane_a7.py` — broad profile×LP×gadget validation.
* `tools/lane_a*.py`, `lane_a*_out.txt` — exploratory evidence.

## Recommended next step

Prove `GadgetSelectionLow` along route 2: formalise "no score-1
gadget" as simultaneous constraints on `(order, bits, q)` per vertex
and per triangle link, then aggregate via `B_v = d_v + z_v − (s−2)`
into `W ≤ 2`.  The `s = 4, n = 4` finite corpus can drive case
discovery; the proof must lift to arbitrary `(s, n)` — the
`W = 2`-boundary comb skeletons are the canonical extremal family
to match.
