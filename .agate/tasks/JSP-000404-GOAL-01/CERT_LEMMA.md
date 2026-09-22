# Cert Lemma — the sole mathematical crux

## Statement (target)

```
feasible(A) ∧ F(A) > cap  ⟹  ∃t : Σ_{i≠t} 2^{k_i}(2^{g_{it}}−1) ≥ 2^{k_t}
```

with `g_{it} = auto_{it} + carry_{it}` (auto = both flank cells ≥1;
carry requires remainder `r_a+r_b ≥ 1`, LP-feasible in the system).

## Verified (empirical, exact-rational, NOT theorems)

- s=4 n=3 δ=1/4: 572/572 LP-feasible F≥7 have joint cert+merge-feasible.
- s=4 n=4 δ=1/4: 512/512 F≥15.  δ=3/4: 296+4/300 (cert at higher k).
- s=4 n=4 δ=3/4 full: 302/302 hard-feasible.
- s=5 n=4: all 14 F=17 debt-survivors LP-infeasible; δ=3/4 maxF(+debt)=20=cap.
- Abstract maxF = uniform cap in every tested regime.

## Falsified (counterexamples on file)

- `Σ 2^{k_i}E_i ≥ F`: best wE = F−2 (56/572 top-F).
- `Σ 2^{k_i}E_i ≥ F−s+1`: deficit 8 > slack 3 at δ=3/4
  (assignment `[(0,0,4),(0,1,3),(0,3,1),(3,0,1)]`, ks=[3,2,2,2]).
- min-k cert: 4/300 δ=3/4 only at k=2.
- extremal (min∪max)-k cert: 12/400 δ=3/4 cert only at middle k=2.
- zero-emitter charge map; max-gap vertex CertA∨CertC; boundary
  emitter; ρ/σ terminal cycle; every min-k receives gain (29% fail on
  random); universal per-vertex emission; min-k deletion rule.

## Structural facts (proved on the model, empirical for assignments)

- zero-emitter ⟺ saturated (C_z = n, budget B_z = δ < 1 ⇒ no carry
  possible) AND active cells pairwise non-adjacent (no auto pair).
- Emission edges strictly ascend in k when no cert exists (else the
  single edge gives cert).
- Cert locations observed at min-k, max-k, and middle k — genuinely
  incidence-structural.
- The merge at angle level preserves ALL constraints trivially
  (merged gap = previously-existing triangle arc). The earlier
  non-closure was an artifact of the cell-only abstraction.

## Layer-cake form

`cert(t) ⟺ Σ_{j≥1} 2^{j−1}·A_j(t) ≥ 2^{k_t}` where `A_j(t)` counts
emitters whose gain reaches across level j.  The top level j = k_t
alone needs `2^{k_t−1}` of coverage — half the demand at one level.

## Connection to Lead's gadget lane

`gadgetSelection` (W-form, `W = Σ 2^{(n−1)−k_i}`) is the dual-weight
version of the same crux.  If their Hall/Kraft gadget machinery
closes first, it should transfer to this statement — and vice versa.

## Geometric-level falsification (emission_digraph.py, this round)

Real point configs (uniform / gon / cocircular-with-gap samplers),
legality = all triangle angles <= pi-lam (exact Section4Legality
contract).  ~1450 legal configs over (n,delta,s) in
{3,4,5}x{0.25,0.75}x{4..8}:

- EmissionDichotomy (non-ascending arc OR >=2 jump-1 emitters into one
  receiver): **0 failures** on all legal+nonflat configs.
- All dichotomy failures are flat configs (F = s <= cap) — vacuous.
- **0 configs with F > cap found by random sampling** — the over-cap
  region is unreachable by sampling, consistent with the bound being
  the theorem's content.  Abstract assignment-level coverage stands
  (302/302, 572/572, 512/512 hard-feasible all have certs).

## Mechanism map (sharpened)

Negating the dichotomy gives a rigid structure:

- Every positive-gain arc strictly ascends (k_i < k_v).
- At most one emitter into each v sits at level k_v - 1.
- A max-exponent vertex M emitting *anything* yields a non-ascending
  arc (k_v <= k_M everywhere) = CertA.  So **no-cert forces every
  max-k vertex to be a zero emitter** (all big gaps isolated AND all
  flanks non-carrying) — same saturated+nonadjacent structure as the
  zero-emitter characterization.
- Crux restated: a legal nonflat config cannot have its emission
  digraph be strictly-ascending with silent top layer and <=1
  jump-1 in-degree.

Component facts (empirical status):

- `nonflat => exists arc` : 0 violations (~1450).  First provable
  stepping stone — equivalent to "all-silent => flat".
- `every big gap emits to an endpoint`: FALSIFIED (1755 silent big
  gaps at s=5 n=3 alone).  Emissions come from run-interior positions
  and carry pairs, not gap endpoints.
- All sampled emission arcs are emitted/received at hull vertices
  (1946/1946 receivers on hull at s=4; interior arcs essentially 0).
- Big gap g > pi-lam at i between (a,b)  <=>  angle a i b = pi-g < lam:
  an antipodal pair.  Triangle sum then forces angle iab + iba >
  pi-lam — big gaps propagate medium arcs at the paired vertices.
  This propagation is the most promising unproved mechanism.

## Sharpest remaining statement

EmissionDichotomy instantiated on (directionRows, deleteIndex) under
Section4Legality + F > cap.  No simpler special-vertex rule survives;
the proof must use the remainder/carry structure of the fan budgets
(`sum_g r_g = n + delta - sum_g q_g`) against the legality constraints
— the same object Lead's W-lane attacks as gadgetSelection.

## Additional falsification data (same round)

- `all-silent => flat` is FALSE at the abstract fan level: gaps
  `[2lam, eps, lam, delta']` with eps+delta' = lam/4 give a silent
  vertex with k = 1 (mergeGain 0 at every position).  So
  `nonflat => exists arc` needs cross-vertex geometry, not per-fan
  combinatorics.
- Silent NONFLAT vertices exist geometrically too: 6 found over 9573
  legal samples (e.g. ks=[0,0,0,0,1], vertex 4 silent with k=1).
  The dichotomy survives because the OTHER vertices emit — and arcs
  between equal-k vertices are jump-0 = CertA.
- Consequence: **no-cert => no arcs within any level** (jump-0 arcs
  are CertA).  Under no-cert the emission digraph is not merely
  ascending but has empty intra-level restriction.  Jump-0 arcs were
  the dominant type in samples (1375/1946 at s=4 n=3) — the typical
  certificate witness.

## P5 closure — the crux is now a single packaged hypothesis

`Jsp000404/Induction.lean` defines

```lean
def CertExists (n : ℕ) (big : Bool) (lam : ℝ) : Prop :=
  ∀ {t : ℕ} {c : Fin t → Plane₂}, 4 ≤ t →
    Section4Legality c lam →
    sendovCap n big < potential lam (directionRows o e c) →
    EmissionDichotomy lam
      (fun v i => deleteIndex o e c v i) (directionRows o e c)
```

and proves (kernel-checked, axioms = [propext, choice, Quot.sound]):

    CertExists  ⇒  potential_le_sendovCap   (strong induction, s ≥ 3)
                ⇒  staircase_of_cert       (StaircaseBound.tail)
                ⇒  sendov_count_bound      (existing machinery)

So `CertExists` is *the* remaining mathematical content.  Its
contrapositive form may be easier to attack:

    ¬ EmissionDichotomy  ⇒  potential ≤ cap

### Structural consequences of no-certificate (verified, not proved)

Under `¬ EmissionDichotomy`:
1. every positive-gain arc strictly ascends in exponent
   (a level or descending arc is CertA);
2. every vertex has at most one jump-1 emitter, with gain exactly 1,
   and all other incoming charges sum < 2^{k_v - 1};
3. every maximal-exponent vertex is silent (`no_gain_from_max_exponent`
   is *proved* in Deletion.lean — max-k vertices emit nothing under
   no-cert, since their arcs would be CertA);
4. silent non-flat vertices *do* exist geometrically (6 samples), so
   "all silent ⇒ flat" is false — the global argument cannot be a
   per-vertex emission claim;
5. no-certificate configurations appear to have **no same-level arcs at
   all** — the incidence digraph is a strict upward DAG on the k-levels.

### Arithmetic free bound (proved-level facts)

`Σ_j ⌊g_j/λ⌋ ≤ ⌊π/λ⌋ = n` over any fan ⇒ `k_i ≤ n − B_i` where `B_i`
is the number of gaps ≥ λ (gapScore truncates: small gaps contribute
0, not −1).  This is exactly the `top` bound `k_i ≤ n − 1` for nonflat
rows; the interesting content is the *weighted* budget, which is the
crux.

### Falsified this session

- `Σq ≤ n ⟹ k_i ≤ n − s + 1` — FALSE reasoning (gapScore truncates;
  small gaps cost nothing).  Correct form: `k_i ≤ n − B_i`.
- All previous falsifications (max-gap, boundary emitter, min/max-k
  vertex, global charge maps, all-silent⇒flat) stand.

### Receiver in-arc profile under no-certificate (sharpened)

`Removable ⟺ 2^{k_v} ≤ C_v`, so `∀v ¬removable` gives `C_v ≤ 2^{k_v}-1`
per vertex — hence `wE ≤ F - s` globally.  Per receiver `v`:

- at most one jump-1 arc, necessarily of gain **exactly 1**
  (a gain-2 jump-1 arc alone contributes `3·2^{k_v-1} ≥ 2^{k_v}`);
- **no gain-2 arc from level `k_v - 2`** (contributes
  `3·2^{k_v-2} ≥ 2^{k_v-1}`, exceeding the residual budget once a
  jump-1 arc is present — and alone it is still `< 2^{k_v}` only if no
  other arc arrives);
- total charge from emitters at `≤ k_v - 2` is `< 2^{k_v-1}`;
- min-exponent vertices receive **zero** arcs (all arcs ascend).

Together: the charge digraph is a strict upward DAG whose per-receiver
in-profile is sparse and tightly budgeted.  `CertExists` ⟺ this DAG
cannot carry `F > cap`; the missing step is the geometric bound on
per-emitter out-degree/carry capacity forced by `Section4Legality`.

## Kraft reformulation (round 2 — the cleanest crux statement)

Define the **defect** of vertex `i`:

    c_i = B_i + (n − Σ_g ⌊g/λ⌋)  =  (number of gaps ≥ λ at i)
                                   + (unused λ-cells at i)

Since `k_i = Σ_g (⌊g/λ⌋−1)⁺ = Σq − B_i = n − c_i`,

    F = Σ_i 2^{k_i} = 2^n · Σ_i 2^{−c_i}

so the Sendov bound is EXACTLY a Kraft inequality:

    F ≤ 2^n          ⟺   Σ_i 2^{−c_i} ≤ 1        (low regime)
    F ≤ 2^n + 2^{n−2} ⟺  Σ_i 2^{−c_i} ≤ 5/4      (high regime)

with `c_i ≥ 1` integers (`c_i = 0` needs `B = Σq = 0`, forcing `n = 0`).

Empirical: 0 violations over ~6000 legal configs; max Kraft sums
0.75 (low) / 1.25 (high — cap achieved exactly).  Saturating profiles
observed: `c = [1,2,2,2]` (n=3 δ=3/4), `[1,1,3,3]` (n=5 δ=3/4),
`[2,2,2,2]` (low) — i.e. the cap is a *prefix-code* bound plus a 1/4
defect allowance in the high regime.  The staircase profile
`c = [1,2,3,…,s]` is the comma code, Kraft-equality for low.

This explains the phase transition: `c_i = 1` ⟺ saturated vertex
(single `q = n` gap ⟺ sees all points in a cone `< δλ`).  Two saturated
vertices already fill the Kraft budget `1/2 + 1/2 = 1`; the +1/4 in the
high regime is the room left for everything else.

## Verified geometric mechanism (round 2, 0 violations)

1. **Saturation bound**: `c_i = 1` (i.e. `k_i = n−1`, single `q=n` gap,
   sees all others in cone `< δλ`).  Any 3 saturated vertices give a
   triangle with all angles `< δλ`, sum `< 3δλ < π` since `2δ < n`
   (n ≥ 2) — so **at most 2 saturated vertices**.  For `δ < 1/2` two
   saturated + any third point `k` give `∠ikj > π − 2δλ > π − λ` —
   so **at most 1 saturated in the low regime**.  (Verified: max
   simultaneous saturated = 2 at δ = 3/4, 0 configs with ≥ 2 at
   δ = 1/4.)

2. **Single-cluster cone**: `B_i = 1` ⟹ all directions at `i` lie in an
   arc of width `< (c_i − 1 + δ)λ` (the complement of the big gap).
   More generally directions at `i` lie in ≤ `B_i` clusters of total
   width `< (c_i − B_i + δ)λ` (small gaps total `≤ (budget+δ)λ`).

3. **Triple deficit bound**: any 3 single-cluster (`B=1`) vertices have
   `Σc ≥ n+3` (low) / `n+2` (high), since the triangle's angles are
   bounded by the cone widths.  Verified on every triple over ~6000
   configs.

4. **Convex r-gon deficit bound**: `r` hull single-cluster vertices in
   convex position have `Σc ≥ r(n+1) − 2(n+δ)` (interior-angle sum
   `≥ (r−2)π` vs cone widths).  Verified for `r = 4` over 45k quads.

5. **Interior vertices are cheap**: a single-cluster vertex inside the
   triangle of 3 others has direction spread `≥ π/2`, hence
   `c_i ≥ ~n/2` — negligible Kraft mass `≤ 2^{−n/2}`.

6. **Rest-Kraft after saturation** (empirical): with 1 saturated vertex
   the remaining vertices' Kraft sum stays `≤ 0.75` — consistent with
   the lens-recursion conjecture below.

## The recursion conjecture (unproved — the likely proof skeleton)

The Kraft inequality should recurse on saturated vertices:

- If vertex `v` is saturated, **every** other vertex sees `v` inside a
  `δλ`-cone — and at every other fan the direction `→v` is isolated in
  a clearing of radius `≥ (1−δ)λ` (from `∠vab + ∠vba > π − δλ` applied
  to the saturated vertex's narrow view).
- If deleting `v` decreased every other defect `c_j` by ≥ 1
  (`c'_j ≤ c_j − 1`), then `Σ_rest 2^{−c} ≤ (1/2)·Σ_rest 2^{−c'} ≤ 1/2`
  and the low-regime bound follows by induction on `s`.
- Gap in this argument: the clearing radius `(1−δ)λ < λ` does NOT force
  both flanking gaps `≥ λ`; `c'` can stay equal or increase by 1.
  The honest defect change is `c' − c ∈ {−2,−1,0,+1}`.

- **Two saturated ⟹ lens**: all other points lie in the intersection of
  two `< δλ`-cones along segment `ij` — a thin lens.  Conjecture: the
  lens sub-configuration behaves like an `(n−2)`-sized problem, giving
  `Σ_rest 2^{k} ≤ 2^{n−2}` — exactly the high-regime bonus.

## Remaining mathematical gap (sharp)

To close `Σ 2^{−c_i} ≤ 1 + (1/4)[big]` the missing pieces are:

- a Kraft-capacity bound for **multi-cluster** vertices (`B_i ≥ 2`,
  which evade the cone argument), and
- the **lens recursion** — a proof that vertices forced into a thin
  sector by 1–2 saturated vertices carry a halved/quartered budget, or
  equivalently a cardinality bound `#low-defect ≤ 2^{n−1}` in the
  presence of saturated vertices.

These are strictly weaker than `EmissionDichotomy` and may admit a
direct packing proof that bypasses the deletion induction entirely —
if `Σ2^{−c} ≤ cap` is proved directly, `potential_le_sendovCap` follows
without any removable-vertex argument.

## Lean status (kernel-checked, round 2+)

The Kraft restatement is now formalized and kernel-verified:

- `rowCells`, `rowBig`, `rowDefect` (`Deletion.lean` §9):
  `cells = Σ_t ⌊g_t/λ⌋₊`, `B = #{g ≥ λ}`, `c = B + (n − cells)`.
- `rowScore_eq_cells_sub_big`: `k = cells − B`.
- `rowScore_eq_sub_defect`: `cells ≤ n ⟹ k = n − c`.
- `potential_eq_two_pow_mul_kraft`: `potential = 2^n · Σᵢ (1/2)^{cᵢ}` in ℚ.
- `potential_le_two_pow_iff_kraft`: `potential ≤ 2^n ⟺ Σ(1/2)^c ≤ 1`.
- `gapAfter_nonneg`, `cycGaps_sum_eq_pi`, `rowCells_eq_sum_floor`,
  `rowCells_le_floor_pi`, `rowCells_directionRow_le`,
  `rowCells_directionRow_le_of_floor_eq` (`Induction.lean`):
  geometric rows satisfy `cells ≤ ⌊π/λ⌋ = n` — the `cells ≤ n`
  hypothesis is discharged for real configurations.
- `potential_le_sendovCap_iff_kraft`: for geometric direction rows,
  `potential ≤ sendovCap n big ⟺ Σᵢ (1/2)^{cᵢ} ≤ 1 + (1/4)[big]`.

All axioms `[propext, Classical.choice, Quot.sound]`.  The remaining
crux is now literally a Kraft/prefix-code inequality on the defect
multiset `{c_i}` — with `c_i ≥ 1` derivable from
`exponent_le_floor` (`k_i ≤ n−1` on deduplicated rows) composed with
`rowScore_dedup`.  What is missing is exactly the packing argument
sketched in the sections above.

## Regime-separated recursion invariant (round 3 — sharp, empirical)

IMPORTANT: legality is `triAngle : ∠ ≤ π − λ` (NOT `≤ nλ`); all numbers
below use the correct constraint.  Tight = observed profile attaining
the bound.

- **C (no saturated vertex)**: `K ≤ 1` in BOTH regimes.
  Tight: `[2,2,2,2]` (s=4), `[2,2,2,3,3]` (s=5).
- **B-low (exactly 1 saturated, δ<1/2)**: `K_rest ≤ 1/2`, so `K ≤ 1`.
  Tight: `[1,2,3,3]`.  1-saturated low-regime configs exist but are rare.
- **A-high-1 (1 saturated, δ≥1/2)**: `K_rest ≤ 3/4`, so `K ≤ 5/4`.
  Tight: `[1,2,2,2]`.
- **A-high-2 (2 saturated)**: `K_rest ≤ 1/4`, so `K ≤ 5/4`.
  Tight: `[1,1,3,3]`.

**Phase transition explained**: two saturated vertices `i,j` force
`∠jik + ∠ijk < 2δλ` (each sees the other inside its `< δλ` cone), but
legality gives `∠jik + ∠ijk ≥ λ` — hence `2δλ ≥ λ ⟺ δ ≥ 1/2`.
Exactly the regime boundary; the +1/4 bonus is the "two-saturation"
slack.

**Recursion skeleton**: if deleting a saturated vertex dropped every
other defect by ≥1, `K_rest ≤ (1/2)·cap` would close both regimes —
but `c'−c ∈ {−2,−1,0,+1}` individually; the needed statement is the
WEAKER aggregate `Σ_rest 2^{−c(A)} ≤ (1/2)·Σ_rest 2^{−c(A−v)}` in low
regime (rest ≤ 1/2 while cap_rest = 1) — i.e., defect drop only needs
to hold in Kraft-average, not pointwise.

## K1/K2 kernelized (round 4 — the phase transition is now a theorem)

The saturation structure and the `δ = 1/2` phase transition are now
**proved in Lean**, not just observed:

- `rowDefect_eq_one` (`Deletion.lean`, pure row arithmetic):
  `c_i = 1` (with `2 ≤ n`, `cells ≤ n`, gaps ≥ 0, `Σgaps = π`)
  ⟹ `∃ G ∈ cycGaps, n·λ ≤ G ∧ (∀ g ≥ λ, g = G) ∧
      (∀ g ≠ G, g < λ) ∧ Σgaps − G ≤ π − n·λ`.
  Proof: `B = 0 ⇒ cells = 0 ⇒ c = n ≥ 2`, so `B = 1, cells = n`; the
  unique big gap has `⌊G/λ⌋ = n` hence `G ≥ nλ`.
- `cyclicDiff_le_or_ge` (`Induction.lean`): the forward arc between
  two row elements either misses `G` (`≤ π − G`) or contains it
  (`≥ G`) — telescoping `gapAfter` ranges over `Finset.Ico`.
- `angle_le_pi_sub_of_saturation` (`Induction.lean`):
  `c_i = 1 ⟹ ∠jik ≤ π − n·λ` for `j,k ≠ i` — via
  `cyclicDiff_dirRep` + `linRep_oangle_eq_angle_or_pi_sub` + legality
  (`∠ ≤ π − λ < n·λ` kills the "contains the big gap" branch).
- `not_two_saturated_of_delta_lt_half` (`Induction.lean`):
  `s ≥ 3`, two saturated `i,j`, `π < (n + 1/2)λ` ⟹ `False`
  (`λ ≤ ∠jik + ∠ijk ≤ 2(π − nλ) < λ`).

All four depend only on `[propext, Classical.choice, Quot.sound]`.
The `δ = 1/2` Sendov boundary is now kernel-derived from the full
geometric system (`Section4Legality.facing_lower`), closing K1 and
K2 of the DAG.  **The sole remaining crux is K3 Kraft packing.**

## K3 — formal four-case split (this round, glue proved)

`Induction.lean` now carries the complete case-split skeleton:

- `one_le_rowDefect` (Deletion.lean): `n ≥ 1, cells ≤ n ⟹ cᵢ ≥ 1`.
- `not_three_saturated`: three saturated centers force `n < 2`
  (`π ≤ 3(π−nλ)` + `π < (n+1)λ`), so saturated count ≤ 2 for `n ≥ 2`.
- `KraftPacking` structure — the four open case bounds over an
  abstract defect function `d : Fin s → ℕ`:

  | case | hypothesis | bound |
  |---|---|---|
  | K3-C-low `no_sat_low` | `π < (n+½)λ`, `∀ i, d i ≥ 2` | `K ≤ 1` |
  | K3-C-high `no_sat_high` | `∀ i, d i ≥ 2` | `K ≤ 5/4` |
  | K3-B `one_sat_low` | `π < (n+½)λ`, `d v = 1` | `rest ≤ 1/2` |
  | K3-A1 `one_sat_high` | `d v = 1` | `rest ≤ 3/4` |
  | K3-A2 `two_sat` | `d u = d v = 1`, `u ≠ v` | `rest ≤ 1/4` |

  **Correction vs. the original four-case table**: the unconditional
  `∀ cᵢ ≥ 2 → K ≤ 1` is FALSE — `tools/generic_enum` +
  `lp_min_delta_f` show all-`c=2` profiles at `s = 5` (`d = 1`,
  `W = 5/2`) are LP-realizable at `δ = 1/2` (106/200 sampled), while
  `s = 6` all-`c=2` is infeasible (`δ_min ≥ 1`) and `s = 6`
  `[2,2,2,2,2,3]` likewise — the tight no-saturated bound in the high
  regime is exactly `K = 5/4`, realized by `[2]^5`.

- `kraft_packing_of_legality`: **proved** case-split assembly —
  `KraftPacking + Section4Legality + ⌊π/λ⌋ = n ≥ 2 + s ≥ 3 ⟹
  K ≤ 1 + ¼[big]`.  The ≥3-saturated and low-2-saturated branches are
  discharged by `not_three_saturated` /
  `not_two_saturated_of_delta_lt_half`, not by the bundle.
- `potential_le_sendovCap_of_packing`: **proved** — `KraftPacking`
  closes `potential ≤ sendovCap` via `potential_le_sendovCap_iff_kraft`,
  bypassing `CertExists`/`EmissionDichotomy`/deletion entirely.

## ABCEDF cross-map verdict (this round)

`Skeleton.d v = (n−1) − kexp v = c_v − 1`, so `W = 2·K` exactly;
`W ≤ 2 ⟺ K ≤ 1`, `W ≤ 5/2 ⟺ K ≤ 5/4`.  The gadget lane's open
`GadgetSelectionLow/High` are *contrapositively the same theorem* as
K3 (`sel.low` ⟺ `δ<1/2 → K≤1`), not a supplier for it — there is no
proved S=0 packing theorem to import.  See STATUS.md for the full
correspondence table.

**Remaining mathematical crux = the four `KraftPacking` fields**
(equivalently, one `gadgetSelection`-style capacity proof).
Attack order: K3-C (`∀ cᵢ ≥ 2 ⟹ K ≤ 1`) first — δ-free.
