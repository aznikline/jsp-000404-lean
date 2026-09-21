# JSP-000404 (Erdős #504 / Blumenthal–Sendov) — lead handoff

Status: CHECKER-VALIDATED gadget semantics; Lean arithmetic backend proved;
GadgetSelection theorems OPEN (the only mathematical blocker).

## Model (mode A, remainder variables)

- `λ = 2π/u`, `π/λ = n + δ`, `0 ≤ δ < 1`, `n = ⌊π/λ⌋`.
- Each gap: `gap/λ = q + r`, `0 ≤ r ≤ 1` (checker uses `r ≤ 1` for strict `< 1`).
- Fan equality at vertex `v` (sum over gaps at `v`):
  `Σ_g r_{v,g} − δ = n − Σ_g q_{v,g}`   (`B_v = n − Σq` = fan budget)
- Triangle equality for each 3-subset `{a,b,h}`:
  `∠a{b,h} + ∠b{a,h} + ∠h{a,b} = n + δ`
- Angle at `x` between others `u,w`:
  `arc = Σ_{g ∈ rng(u,w)} (q_g + r_g)` where `rng` = gaps strictly
  between `u` and `w` in the cyclic fan order at `x`.
  - direct (bits equal):     `∠ = arc`,          bound `∠≤π−λ` ⟹ `Σr ≤ (n−1−q_arc) + δ`
  - complementary (bits diff): `∠ = n+δ−arc`,     bound `∠≤π−λ` ⟹ `Σr ≥ 1−q_arc`; `∠≥0` ⟹ `Σr ≤ (n−q_arc)+δ`
- Dyadic weight: `W(d) = Σ_i 2^{−d_i}`, `d_i = (n−1) − k_i`.

## Residual form (the checker contract)

Accumulate `Σ coef·r + dco·δ + con = 0` from a weighted combination of
fan/triangle equalities.  Then `P − U − c·δ = C` with
`c = −dco`, `C = −con`, `P = Σ coef⁺·r`, `U = Σ coef⁻·r`.
Positive leftover blocks may be *charged* by complementary angles
whose arc ⊆ block (gain `min coef · (1 − q_arc)`, arcs disjoint).
Negative leftover blocks must be *covered* by cap entries
(`r≤1`, direct `∠≤π−λ`, or comp `∠≥0`; multiplicity `m` supplies `m`
units to every gap in range; a gap with coefficient `κ` needs
`Σ_{entries ∋ g} m ≥ κ`).
Bound: `δ ≥ (K − Bcap − C)/(c + u)`; gadget score `= 2·bound` levels.

## Confirmed facts (CHECKER-VALIDATED, not proofs)

- `δ_min` over ~1M skeletons takes only `{0, 1/2, 1, inf}`.
- `W ≤ 2`  ⇒ a realizable skeleton with `δ_min = 0` exists.
- `2 < W ≤ 5/2` ⇒ every realizable skeleton has `δ_min = 1/2` (M*=1).
- `W > 5/2` ⇒ every realizable skeleton has `δ_min ≥ 1` (M*=2).
- `inf` = structural inconsistency of mode A, NOT a higher debt level;
  DebtSelection must only range over consistent/realizable skeletons.
- The generalization `W > 2+m/2 ⇒ M*≥m+1` FAILS at m=2 (counterexample:
  `(0,0,0,0)`, W=4, `δ_min=1`).  Only m ∈ {0,1} holds — exactly what
  JSP-000404 needs.
- `link_graph.py` pure skeleton evaluator (no LP/MUS): 75/75 corpus +
  240 sampled realizable skeletons match LP level exactly (0 mismatch).

## Gadget families observed

1. **fan-strip**: fans + σ=−1 pivot-shared triangle path; endpoint
   caps; interior telescoping via nested arcs (comp ⊋ dir).
2. **fan-only**: single fan positive block + complement-angle charges
   (often enough for level 2).
3. **pure-cap**: direct angle with `q_arc ≥ n` forces `r ≤ δ−(q−n+1)`,
   contradicting `r ≥ 0` — zero equalities needed.
4. Rare: negative fans/links, mixed signs, closed cycles — all
   captured by the evaluator's signed fan/link support.

## Remaining crux (P0)

```lean
theorem gadgetSelection_low
    (hconsistent : SkeletonConsistent sk)
    (hW : 2 < W sk) : ∃ g : Gadget sk, g.Valid ∧ 1 ≤ g.score

theorem gadgetSelection_high
    (hconsistent : SkeletonConsistent sk)
    (hW : 5/2 < W sk) : ∃ g : Gadget sk, g.Valid ∧ 2 ≤ g.score
```

Preferred direction: contrapositive
`no score≥1 gadget → W ≤ 2` / `no score≥2 gadget → W ≤ 5/2`
(Kraft/Hall-style capacity aggregation over link components).

## Key files

- `tools/remainder_check.py` — LP model + exact semantics
- `tools/link_graph.py` — pure gadget enumerator (eval_chain etc.)
- `tools/skeleton_enum.py` — `gen_cases` yields consistent skeletons
  (MUTATES `sol` in place — copy before storing!)
- `tools/level_scan.py` — δ_min spectrum scanner
- `tools/level_scan_s4.json` — full s=4 spectrum
- `Jsp000404/SaturationDebt.lean`, `DebtChain.lean`,
  `ChainWitness.lean` — proved arithmetic backend
- `Jsp000404/Gadget.lean` (lane/c branch) — WIP gadget semantics

## Downstream DAG (after selection)

gadget → ResidualWitness → δ lower bound → weighted capacity →
sendov_count_bound → arbitrary-N lower → existing upper → root
theorem → COMPLETION SHA.
