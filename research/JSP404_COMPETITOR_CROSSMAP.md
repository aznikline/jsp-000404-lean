# JSP-000404 — Competitor Cross-Map Report (Challenger)

Audited repo: `jerrylijize1224-star/jsp404-lean-partial` @ `a6a363f96cf617fa6227c7300a4a318fde86244a`
(latest extracted snapshot `jsp404-finite-clusters-20260921`; the repo ships source as zip archives).
Main repo: `aznikline/jsp-000404-lean` @ `ccc95c0` (all five lanes at same commit).

Status discipline: every claim is tagged `PROVED` (in someone's Lean), `CHECKER-VALIDATED`
(our LP/enumeration), `INFERRED` (from source structure), `CONJECTURED`, or `FALSIFIED`.
The competitor snapshot is self-described as AI-assisted and unreviewed; none of its
results are reused as proof dependencies.

**No RACE_ALERT.** `Target.lean` defines `SendovClaim` only as a `Prop`; the README
states the arbitrary-s sharp bound and the arbitrary-N reduction are missing.
`grep` over the snapshot confirms `SendovClaim` is never proved. [PROVED by inspection]

---

## 1. Executive verdict

**A. SAME_CORE_DIFFERENT_COORDINATES** — with a twist: the coordinate systems are not
merely parallel, they are literally the same gadget.

- `sectorCapacity t x = (⌊t·x⌋ − 1).toNat` (competitor, `SectorCapacity.lean:14`)
  is *definitionaly identical* to our `gapScore lam x = ⌊x/λ⌋₊ − 1`
  (`Deletion.lean:31`) once `t = π/λ` and `x = g/π` are substituted:
  `t·(g/π) = g/λ`. [PROVED — both are Lean defs; the equality is `ring` + `congr`]
- `gapIndex t = Σ_i sectorCapacity t (gap_i/π)` ≡ our `rowScore`/`exponentAt` = `k_i`.
  [PROVED — same def shape]
- `Σ_i 2^{gapIndex_i}` (their `capacity`, `fourCentreCapacity`) ≡ our
  `potential = Σ_i 2^{exponentAt_i} = 2^{n−1}·W`. [PROVED — algebra]
- Hence their s=4 theorems `fourCentreCapacity_low` (`≤ 2^n`, for `t < n+1/2`) and
  `fourCentreCapacity_high` (`≤ 2^n + 2^{n−2}`, for `t < n+1`) are *exactly* the
  contrapositives of our `gadgetSelection_low`/`gadgetSelection_high` restricted to
  `s = 4` real gap data: `W ≤ 2 ⟺ Σ2^{k_i} ≤ 2^n`, `W ≤ 5/2 ⟺ Σ2^{k_i} ≤ 2^n+2^{n−2}`.
  [PROVED — arithmetic equivalence]
- Experiment B (§3) shows the constraint systems coincide exactly: dropping fan sums,
  triangle sums, or angle caps each collapses `δ_min` from `1/2` to `0`, while dropping
  `r ≤ 1` or `∠ ≥ 0` changes nothing. Their `InteriorAngleData`/`ConvexFourAngleData`
  axioms are our mode-A system repackaged. [CHECKER-VALIDATED]
- The wall is identical on both sides: they lack the sharp bound for `s ≥ 5`; we lack
  `GadgetSelection` — the same inequality in different coordinates.

What transfers is therefore not their *theorems* (which we already have equivalents of
at s=4, checker-side) but their *proof strategy*: a saturated-exponent case split with
deficit propagation, which translates directly into a gadget-construction recipe (§4, §5).

---

## 2. Object correspondence table

| Competitor object | Main-project object | Class | Formula-level correspondence |
|---|---|---|---|
| `sectorCapacity t x = (⌊tx⌋−1)⁺` | `gapScore λ g = ⌊g/λ⌋₊−1` | EXACT_EQUIVALENT | `t = π/λ`, `x = g/π` ⇒ `tx = g/λ` |
| `gap i` (cyclic gap, `>0`, `Σ = π`) | `cyclicDiff`/`cycGaps`; skeleton gap `g = q+r` | EXACT_EQUIVALENT | both partition the projective circle `Σ g = π` |
| `gapIndex t = Σ (⌊t·g/π⌋−1)⁺` | `rowScore λ row` = `exponentAt` = `k_i` | EXACT_EQUIVALENT | `k_i = Σ_g (⌊g/λ⌋−1)⁺ = Σ(q_g −1)⁺` with `q_g = ⌊g/λ⌋` |
| `Σ_i 2^{gapIndex_i}` | `potential = Σ 2^{k_i}`; `W = Σ 2^{k_i−(n−1)}` | EXACT_EQUIVALENT | `potential = 2^{n−1}·W` |
| `SortedDirectionChart` (`theta`,`length`,`ray`; strict-mono `θ∈[0,π)`) | skeleton row `(order, bits)` + real gaps | DIFFERENT_COORDINATIZATION | their `θ` = absolute projective positions; ours = relative cyclic order + ray bits. `length` is inert (directions only). Chart ⇒ our row by sorting; converse needs gap values |
| `theta_unique`, `gap_unique`, `gapIndex_unique` | — (skeleton already canonical) | EXACT_EQUIVALENT | their invariance theorem = our `order`/`bits`/`q` being determined by geometry + gauge `bits[order[0]]=0`; `rowScore_rotate` is our cyclic-gauge invariance |
| `allowed coordinates` / `exists_allowed_gap`, `cluster_card_le_gapIndex` | (leaf-point layer, deleted in our model) | NO_ANALOGUE | they count points per sector by binary labels; our skeleton quotients leaves away and keeps only `k_i` |
| `InteriorAngleData` {`a1,a2,b1,b2,c1,c2,ab,ac,bc`, `total`, `comp_*`, nonneg} | mode-A constraint set {fan `Σgap−δ=n`, triangle `Σ∠−δ=n`, caps `∠≤n−1+δ`, `r≥0`, `r≤1`} | EXACT_EQUIVALENT (s=4) | `total` = Σ split parts `= t` = fan sum; `comp_*` = `1 ≤ t·(1−x)` = cap on complementary arc; `ab,ac,bc` = triangle-sum cells. Verified by constraint-deletion experiment (§3/Exp B) |
| `ConvexFourAngleData` (same, plus `gap_*` identities) | same | EXACT_EQUIVALENT (s=4) | `gap_*` = quadrilateral diagonal-split identities = triangle sums in our system |
| `splitVertexBits t x y = gapBits x + gapBits y + gapBits (t−x−y)` | per-vertex `k_i` restricted to 3 gaps | DIFFERENT_COORDINATIZATION | at s=4 each vertex has 3 gaps; they name them by triangle angles `x,y` and remainder `t−x−y`; our `q`/`r` split is the same data discretized |
| `fourCentreCapacity`, `FiniteClusterModel`, `card_le_sum_gap_capacity` | `potential`; `W`; skeleton | WEAKER ↔ | their cluster model still carries leaf points; bound `N ≤ Σ 2^{gapIndex}` corresponds to our `N ≤ potential`; our `W` form is the same thing normalized |
| `exists_capacity_bound` (unsharp, ∃ bound) | `GadgetSelection` (sharp, contrapositive) | WEAKER | theirs asserts *some* bound exists; ours asserts the sharp dyadic bound — the missing piece on both sides |
| `SendovClaim` bands `N ≤ 2^k+2^{k−2}` @ `(1−2/(2k+1))π`; `N ≤ 2^{k+1}` @ `(1−1/(k+1))π` | `u = 2k+1` (δ=1/2, `t=k+1/2`) and `u = 2k+2` (δ=0, `t=k+1`) | EXACT_EQUIVALENT | their two bands are our low/high regimes with the parity split made explicit: low band = odd `u`, high band = even `u` |
| `card_le_two_pow_of_*` (binary-label counting, `Counting.lean`) | — | NO_ANALOGUE | we never count points; the skeleton starts after this quotient. Harmless: it is the reduction side, not the crux |

---

## 3. Four-centre proof decomposition

Chain in their code (all `PROVED` in their repo):

```
four_centre_geometry_cases              (Radon: interior ⊎ convex-quadrilateral)
  → InteriorAngleData / ConvexFourAngleData   (six scaled angle parts, nonneg,
        total = t, complement bounds, triangle cells ab/ac/bc)
  → K_v := splitVertexBits t x y            (= our k_v, real-coordinate form)
  → case split on K_v = n−1                 (saturated vertices)
  → drop lemmas bound the other K's
  → pow_* closes the arithmetic
```

The sharp bound comes from exactly two ingredients:

**(I) Saturation ⇒ shallowness.** `splitVertexBits_control`
(`FourCentreInterior.lean:33`): `K_v ≤ n−1`, and `K_v = n−1 ⇒ x+y ≤ t−n = δ`.
A saturated centre sees the whole configuration inside a wedge of scaled width `δ`.
In our skeleton terms: `k_v = n−1` forces `q_v = (n,0,…,0)`, threshold bits, and every
incident angle `≤ δ`. [PROVED their side; CHECKER-VALIDATED ours — see §5/L2]

**(II) Deficit propagation.** In the low band (`δ < 1/2`):
- interior case `low_drop` (`:222`): one saturated vertex pushes the other two outer
  exponents to `≤ n−2` and at least one to `≤ n−3`; `interior_le` (`:195`) gives the
  interior vertex `K_D ≤ n−3` unconditionally;
- convex case `low_drop` (`:113`): saturated `A` ⇒ `K_C ≤ n−3` and (`K_B ≤ n−3` or
  `K_D ≤ n−3`), while `drop_of_A_high` (`:95`) rules out a second saturated vertex
  in the *whole* band.

Then `pow_low_pattern`: `2^{n−1} + 2^{n−2} + 2^{n−3} + 2^{n−3} = 2^n`, and
`pow_four_mid` (no saturated vertex): `4·2^{n−2} = 2^n`. This is exactly deficit
profile `(0,1,2,2)` saturating `W = 1 + 1/2 + 1/4 + 1/4 = 2`. **The exclusion of
`W > 2` at `δ < 1/2` is precisely the statement "saturated + any shallow vertex is
impossible"**, i.e. their `low_drop` ↔ our fan-strip gadget.

High band (`δ < 1`): interior case allows *two* saturated vertices, but
`third_le_of_two_high` (`:208`) forces the third outer vertex `≤ n−3`;
`pow_two_high`: `2·2^{n−1} + 2·2^{n−3} = 2^n + 2^{n−2}` — deficit profile
`(0,0,2,2)`, `W = 5/2`. Convex case never allows two saturated. **The exclusion of
`W > 5/2` is "two saturated ⇒ all others have d ≥ 2".**

Hidden structure worth noting: every `pow_*` identity is `s/2` against the target —
`4·2^{n−2} = 2^n` works *because* `s = 4` (§5). The mechanism is: count saturated
vertices; each saturated vertex propagates deficit to its neighbours through the
triangle sums (their `total`, `comp_*`, `ab/ac/bc`); close by dyadic arithmetic.
That is precisely our fan-strip gadget: fan equations at saturated vertices +
triangle links + endpoint caps.

**Experiment B — minimal core** (LP on a `ks=(3,2,2,1)`, `δ_min=1/2` skeleton,
`tools/generic_model.py`, `mode='A'`):

| constraints dropped | `δ_min` |
|---|---|
| none | 1/2 |
| angle caps (`∠ ≤ π−λ`) | 0 |
| triangle sums | 0 |
| fan sums | 0 |
| `r ≤ 1` | 1/2 |
| `∠ ≥ 0` | 1/2 |

[CHECKER-VALIDATED] The essential system = fan sums + triangle sums + caps —
identical to the fields of `InteriorAngleData` (`total` = fan, `comp_*`/`ab` etc. =
caps + triangle cells). Nonnegativity and `r≤1` are inessential *for this bound*.

---

## 4. Gadget correspondence (Experiment A)

Method: `tools/link_graph.py` pure evaluator + `chain_dump_s4.json` (43 skeletons of
profile `ks=(3,2,2,1)`) + `gc_*_n5s5.json` gadget certs. Competitor "active
inequality" column = the lemma excluding that profile below the stated `δ`.

| # | profile `ks` | deficits `d` | `W` | regime | gadget found (ours) | bound | competitor exclusion |
|---|---|---|---|---|---|---|---|
| 1 | (3,2,2,1) | (0,1,1,2) | 9/4 | low breach | fan-strip: fans{0,2} + link (1,2,−1), MUS = 1 fan + 2 tri + 2 caps | δ ≥ 1/2 | `low_drop`: sat A forces one of B,C ≤ n−3; here both are n−2 |
| 2 | (3,3,2,1) | (0,0,1,2) | 11/4 | high breach | fan-only: fan{1} alone | δ ≥ 1 | `third_le_of_two_high`: two sat ⇒ third ≤ n−3; here third is n−2 |
| 3 | (3,3,1,1) | (0,0,2,2) | 5/2 | high boundary | fan-strip: fan{0} + link (1,2,−1) | δ ≥ 1/2 | `pow_two_high` is *tight* here — boundary feasible at δ=1/2 (their capacity-10 example needs δ ≥ 1/2) |
| 4 | (3,2,1,1) | (0,1,2,2) | 2 | low boundary | none needed | δ = 0 | `pow_low_pattern` tight — boundary feasible at δ=0 |
| 5 | s=5 `gc_0_1_2_2_2` | (0,1,2,2,2) | 9/4 | low breach | MUS: 2 fans + 3 tri + 3 caps, K=3/2, C=1 | δ ≥ 1/2 | (their code has no s=5 sharp bound; same mechanism) |
| 6 | s=5 `gc_1_1_1_1_2` | (1,1,1,1,2) | 9/4 | low breach | MUS: 2 fans + 3–5 tri + caps | δ ≥ 1/2 | same |

[Instances 1–4: CHECKER-VALIDATED (link_graph, matches LP level on 75/75 corpus +
240 sampled skeletons per HANDOFF); 5–6: CHECKER-VALIDATED via `residual_map_s5.json` verdicts `mapped`.]

Correspondence summary:
- competitor `controls`/`drop_of_A_high` (saturation propagation) ↔ our **fan-only /
  pure-cap** gadgets (saturated fan + caps).
- competitor `low_drop`/`third_le_of_two_high` (propagation through triangle cells)
  ↔ our **fan-strip** gadgets (fan + signed link chain + endpoint caps).
- competitor `pow_*` dyadic closings ↔ our `SaturationDebt`/`DebtChain` telescoping
  arithmetic. [INFERRED — semantic match of mechanisms, not a theorem yet]

Their s=4 case split is *finite* (4 exponents, 3 levels); ours must cover arbitrary `s`.
But the gadget families already found by `link_graph.py` are exactly the propagation
patterns their proof uses.

---

## 5. Generalizable lemma candidates

Sorted by usefulness for `GadgetSelection`. `B_v = n − Σq` (fan budget),
`m_v = #{g : q_g ≥ 1}`, `d_v = B_v + m_v − 1` [the identity is PROVED-trivial].

**L1 — deficit identity.** `d_v = B_v + m_v − 1` (i.e. `k_v = Σq − m_v` restated).
- SOURCE: our own algebra. WHY: makes "deficit = free budget + large-gap count"
  visible; `m_v` is skeleton-visible. CHECKER: definitional. LEAN: immediate.

**L2 — saturated structure.** `d_v = 0` (saturated) ⟺ `q_v = (n,0,…,0)`; then
`Σr = δ` (fan), every pair crossing the big gap must be complementary (bits differ),
and every incident angle `≤ δ` when `δ < 1` (strict; `r ≤ 1` boundary artifacts excepted).
- SOURCE: competitor `splitVertexBits_control` + our derivation.
- CHECKER-VALIDATED: bit-threshold pattern held on all tested skeletons
  (68/68, 21/21, 10/10 in earlier scans); consistent with corpus.
- LEAN: provable inside mode-A semantics (fan equality + caps); medium effort.

**L3 — saturated counting (the key transfer).**
`#{v : d_v = 0} ≥ 2 ⇒ δ ≥ 1/2` (score ≥ 1 gadget exists);
`#{v : d_v = 0} ≥ 3 ⇒ δ ≥ 1` (score ≥ 2 gadget).
Mechanism (INFERRED, and essentially the competitor's `third_le_of_two_high`):
two saturated vertices `u,v` force `∠u v w ≤ δ` and `∠v u w ≤ δ` for every `w`,
so the triangle sum gives `∠u w v ≥ t − 2δ = n − δ`; the cap needs `n−δ ≤ n−1+δ`,
i.e. `δ ≥ 1/2`. Sharper: feasibility at `δ = 1/2` requires all other vertices `d ≥ 2`
(their `pow_two_high` profile `(0,0,2,2)`).
- CHECKER-VALIDATED: s=4 full spectrum — every profile with ≥2 zeros has
  `δ_min ∈ {1/2, 1, inf}` and `δ_min = 1/2` occurs only in `(0,0,2,2)`,
  `(0,0,2,3)`, `(0,0,3,3)`; all `(0,0,1,*)` and `(0,0,0,*)` are `{1, inf}`.
  s=5 samples `(4,4,3,3,3)`, `(4,4,4,3,3)` → `{1, inf}`. s=6 adversarial
  (hand-built consistent signatures, `ks=(5,5,5,3,3,3)`, `(5,5,5,5,5,5)`):
  14/15 infeasible, 1 at `δ_min=1`; 6-saturated all infeasible. No counterexample.
- LEAN feasibility: two saturated fans + triangle sum + one cap = a concrete
  `DebtChain`/`ResidualWitness` pattern; provable given L2.

**L4 — interior vertex depth.** If every gap at `v` is complementary-type (bit
transition at each adjacency — geometrically: `v` inside conv hull of the others),
then `m_v = s−1`, hence `d_v ≥ s−2`.
- SOURCE: competitor `interior_le` (`K_D ≤ n−3` at s=4 ⟺ `d ≥ 2 = s−2`).
- STATUS: CONJECTURED for us (the skeleton predicate "all-comp" needs care at odd
  `s−1`: bits cannot alternate around an odd cycle, so at even `s` an interior
  vertex must have ≥1 direct-type gap — refine before formalizing).

**L5 — `m_v ≥ #bit-transitions at v`.** Adjacent directions with different bits
force that gap `≥ λ` (complement cap), hence `q ≥ 1` (strictly, `r < 1`).
- SOURCE: our own derivation; implicit in their `gap_b`-style hypotheses.
- STATUS: CHECKER-VALIDATED modulo `r=1` boundary; LEAN: provable from cap semantics.

**L6 — Kraft/prefix reformulation (proof-route candidate, not a lemma).**
`W ≤ 2 ⟺ Σ_i 2^{−(d_i+1)} ≤ 1` — a prefix-free (Kraft) condition with codeword
lengths `ℓ_i = d_i + 1`. Sendov's original argument and the competitor's
`Counting.lean` (`card_le_two_pow_of_*`) are exactly binary-label packings; the
per-centre refinement trees nested by gaps are a geometric realization of the
code tree. A proof of GadgetSelection via *explicit binary-tree packing* of the
centres is a plausible alternative mechanism. CONJECTURED — no counterexample
possible (it is a restatement), but no new inequality either; its value is the
proof idiom.

**FALSIFIED candidates** (recorded so nobody retries):
- "Three saturated vertices ⇒ infeasible at δ<1" — FALSIFIED as stated for the LP
  model: `(3,3,3,2)` has 21/40 sampled skeletons at `δ_min = 1`, not `inf`
  (boundary `r=1` artifacts). The correct form is `δ_min ≥ 1` (L3).
- Broad level law `W > 2 + m/2 ⇒ M* ≥ m+1` — already FALSIFIED at `m=2` in HANDOFF.

---

## 6. Skeleton quotient proposal (Q4)

Competitor's `theta_unique`/`gap_unique`/`gapIndex_unique` prove the sorted chart is
a *canonical form* of the geometry. Translating:

- `order` at each vertex = the sorted projective order — already canonical, not a
  gauge choice. `bits` = ray orientations — canonical up to the fixed gauge
  `bits[order[0]] = 0`. `q` = `⌊ĝ⌋` of the real gaps — canonical given the gaps.
- So our skeleton state is already essentially quotient-free; the only honest
  redundancy is *which* geometric configurations share a skeleton — which is the
  intended abstraction, not waste.

The one place a quotient would genuinely help is the **(q, r) split itself**:
competitor works on real gaps `ĝ` directly; our `r ≤ 1` relaxation manufactures
boundary skeletons (`r = 1`, `δ_min` reporting `1` instead of `inf` — observed in
`(3,3,3,2)`). [CHECKER-VALIDATED] A `q`-cells + open-intervals semantics
(`0 ≤ r < 1`) or a `2`-adic refinement would remove these artifacts; for Lean the
real-gap form `ĝ` with `q = ⌊ĝ⌋`, `r = ĝ − q ∈ [0,1)` is cleaner anyway.
Impact on `GadgetSelection`: cosmetic — recommend keeping skeletons, treating
`r = 1` cases as limit cases in proofs. [SMALL_SIMPLIFICATION at most]

---

## 7. Impact on GadgetSelection

**SMALL_SIMPLIFICATION** (candidate: MAJOR if L3-style counting is extended).

Why not ALTERNATIVE_PROOF_ROUTE: the competitor's route is the same mechanism in
real coordinates and hits the identical wall at `s ≥ 5` — `pow_four_mid` is
`4·2^{n−2} = 2^n` *because* `s = 4`; at `s = 5` "no saturated" only gives
`W ≤ 5/2` for free, and at `s ≥ 6` even the high bound needs real propagation.
There is no hidden arbitrary-s Kraft argument in their code — their arbitrary-s
chain stops at `exists_capacity_bound` (unsharp). [PROVED by inspection: their
README + theorem inventory]

What concretely transfers:

1. **Case split by saturated count.** `W > 2` with `S = #saturated`:
   `W ≤ S + (s−S)/2` unconditionally, so `W > 2` needs `S ≥ 1` or `s ≥ 5`-type tails.
   Each `S`-level is a finite family of deficit profiles; the corpus shows every
   such profile carries a gadget. This is exactly their `by_cases` on `K_v = n−1`,
   and it is an *organizing principle* our gadget enumeration can follow: build
   gadgets by induction on saturation depth (saturated → its d=1 neighbours → …).
   [INFERRED; consistent with all corpus data]
2. **The propagation lemmas are gadget templates.** `low_drop`/`third_le_of_two_high`
   say *which* fans and links to pick: fans at saturated vertices, triangle links to
   their shallowest neighbours, endpoint caps. `link_graph.py` already finds these;
   L2/L3 turn the s=4 observation into Lean-provable skeleton lemmas.
3. **Free bounds:** at `s = 5`, `S = 0 ⇒ W ≤ 5/2` discharges `gadgetSelection_high`
   on unsaturated skeletons trivially; generally `W ≤ S + (s−S)/2` prunes cases.

Why not NO_ACTIONABLE_TRANSFER: items 1–3 are actionable.

---

## 8. Recommended Lead action (≤3)

1. **Formalize L2 + L3 in Lean** (`SkeletonConsistent` level): saturated structure
   lemma, then `≥2 saturated ⇒ score ≥ 1 gadget` and `≥3 saturated ⇒ score ≥ 2`
   gadget as explicit `ResidualWitness`/`DebtChain` instances. This discharges the
   extreme end of `GadgetSelection` and is the piece the competitor proof makes
   most concrete. Effort: moderate; all ingredients exist (`SaturationDebt`,
   `ChainWitness`).
2. **Adopt the saturation-depth case split for `GadgetSelection`**: prove
   `W ≤ S + (s−S)/2` counting lemma, then handle `S = 0` (needs the real work:
   a Hall/Kraft-type bound over the link graph — see L6), `S = 1` (deficit
   propagation to neighbours = fan-strip family), `S ≥ 2` (L3). This mirrors the
   competitor's proof shape without importing their code.
3. **Optional hygiene:** switch checker semantics to strict `r < 1` (or record
   `r = 1` solutions as boundary) to kill the `δ_min=1`-vs-`inf` reporting
   artifact; and note their `SendovClaim` band split = odd/even `u` parity, which
   matches our `δ < 1/2` / `δ < 1` regimes exactly.

---

## Appendix — experiment log

- **Exp B** (constraint deletion, `generic_model.py`, mode A, skeleton `ks=(3,2,2,1)`
  at `δ_min=1/2`): table in §3. Core = {fan, tri, caps}.
- **Exp A**: §4 table; sources `chain_dump_s4.json`, `fan_pairs_s4.json`,
  `residual_map_s5.json`, `gc_*_n5s5.json`.
- **Exp C**: candidate L3 falsified nowhere — s=4 full spectrum
  (`level_scan_s4.json`, 35 profiles × ≤30001 leaves), s=5 samples, s=6 adversarial
  (hand-built consistent signatures from real point configs `flat`, `two-cluster`;
  `ks=(5,5,5,3,3,3)` → 14/15 infeasible + 1×δ=1; `(5⁶)` → all infeasible).
- **Boundary artifact found**: `(3,3,3,2)` reports `δ_min=1` in 21/40 sampled
  skeletons rather than `inf`; traced to the `r ≤ 1` relaxation admitting `r = 1`
  (strict model would be infeasible). Same class of artifact as L5's `q=0, r=1` edge.
- **s=4 spectrum confirms** both target theorems over the whole corpus: every
  profile with `W > 2` has no `0` in its spectrum; every profile with `W > 5/2`
  has spectrum ⊆ `{1, inf}`. [CHECKER-VALIDATED]

## Appendix — file index

Competitor (snapshot `jsp404-finite-clusters-20260921`): `Target.lean`
(SendovClaim, unproved), `SectorCapacity.lean`, `FourCentreInterior.lean`
(`splitVertexBits_control`, `three_gapBits_le`, `low_drop`,
`third_le_of_two_high`, `pow_*`, `capacity_low/high`),
`FourCentreConvex.lean` (`controls`, `drop_of_A_high`, `low_drop`, `capacity_*`),
`FourCentreLocalIndex.lean` (`threeRayIndex`, `labelled_capacity_eq`),
`FourCentreCapacity.lean` (`fourCentreCapacity_low/high`),
`FourCentreClassification.lean` (`four_centre_geometry_cases*`),
`FourCentreProjectiveGaps.lean` (`gap_pos/sum`, `index_eq_gapIndex`,
`projective_gapIndex_independent`, `fourCentreCapacity_eq_projectiveGaps`),
`FiniteDirectionChart.lean`, `FiniteDirectionInvariance.lean`
(`theta/gap/gapIndex_unique`), `ThreeGapAllowed.lean`, `GapSectorCounting.lean`,
`GeneralizedDirectionCover.lean`, `FiniteClusterCounting.lean`
(`cluster_card_le_gapIndex`, `card_le_sum_gap_capacity`, `exists_capacity_bound`),
`Counting.lean` (`card_le_two_pow_of_*`), `ThreeCentreCapacity.lean` (s=3 analog).

Main project: `Jsp000404/Deletion.lean` (`gapScore`, `cycGaps`, `rowScore`,
`exponentAt`, `potential`, `potentialErase` — the deletion-route mirror of the
competitor's capacity), `SaturationDebt.lean`, `DebtChain.lean`,
`ChainWitness.lean` (`ResidualWitness`), `Section4Legality.lean`,
`Staircase.lean` (`staircase_of_legality`, `sorry`), `tools/generic_model.py`,
`generic_enum.py`, `residual_map.py`, `link_graph.py`, `level_scan_s4.json`,
`notes/HANDOFF.md`.

## Attribution notes

- Competitor snapshot is self-described AI-assisted work, not externally reviewed,
  and not an award claim. Their `ThreeGapAllowed`/`FiniteDirectionChart` cite
  Sendov (1995) Lemma 4.4/4.6 as source.
- No competitor Lean code was copied; all correspondences were re-derived at the
  formula level and checked against our checker.
- Ideas genuinely originating from their proof shape: the saturated-depth case
  split (L3 usage) and the interior-vertex depth bound (L4). If either enters the
  Lean proof, cite `jsp404-lean-partial @ a6a363f` as the idea source.
