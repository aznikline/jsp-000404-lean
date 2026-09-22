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
