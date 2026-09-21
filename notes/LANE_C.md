# Lane C — gadget semantics frozen in Lean

`Jsp000404/Gadget.lean` freezes the skeleton-local gadget semantics of
`tools/link_graph.py` (which replays `tools/remainder_check.py` mode-A
constraints) into a compiling, sorry-free Lean theory.  It does **not**
prove `W ⇒ gadget existence`; `gadgetSelection_low`/`gadgetSelection_high`
remain open (see `notes/HANDOFF.md`).

## Correspondence map (Lean ↔ checker)

| Lean (`Jsp404.Gadget`)                  | checker (`link_graph.py`)                |
|-----------------------------------------|------------------------------------------|
| `VertexData.pos/bits/q`                 | `v['order']`/`v['bits']`/`v['qs']`       |
| `VertexData.arc a b` = `Ico lo hi`      | `arc_rng`: `range(min pos, max pos)`     |
| `VertexData.comp a b` = `bits a ≠ b`    | `bits[u] != bits[v]`                     |
| `angleExpr` (direct `arc`, comp `n+δ−arc`)| `angles[frozenset(u,v)]`               |
| `fanForm n sk v`                        | `ctx.fan[(v,fw)]` residual (`coef=fw`, `con=fw(Σq−n)`, `dco=−fw`) |
| `linkForm n sk a b h`                   | `ctx.link[(a,b,h,σ)]` (3 angle terms + `⟨0,−1,−n⟩`) |
| `Gadget.form` = `formSum (fans ++ links)`| `R`,`con`,`dc` accumulation in `eval_chain` |
| `coef`/`cc`/`CC`                        | `R`, `c = −dc`, `C = −con`               |
| `chargeGain = min'_arc coef · (1−arcQ)` | `gain = min(posblk[g]) · (1−q)`          |
| `K = Σ chargeGain`                      | `K += gain` (greedy disjoint arcs)       |
| `CapEntry.range/B/u`                    | cap options in `eval_chain`/`pure_gadget`|
| `Bcap = Σ m·B`, `uu = Σ m·u`            | `Bcap`, `u` of chosen combo              |
| `bound = (K−Bcap−CC)/(cc+uu)` (0 if denom ≤ 0) | `bound = (K−Bcap−C)/(c+u)`  |
| `score = 2·bound`                       | `M = 2·bound`                            |
| `Valid`                                 | per-vertex cover conditions + `c+u>0`    |

Cap kinds: `rle` (`r≤1`), `piLam` (direct `∠≤π−λ`), `nn`
(complementary `∠≥0`).  The checker only ever emits `rle`/`piLam`;
`nn` is in the Lean API for completeness (it is a valid mode-A bound)
but no fixture exercises it — noted as a coverage gap.

## Theorems

* `gadget_ge`      — `Valid` gadget + `t·(cc+uu) ≤ K−Bcap−CC` ⇒ `t ≤ δ`.
* `gadget_ge_half` — score ≥ 1 case: `t = 1/2`.
* `gadget_ge_one`  — score ≥ 2 case: `t = 1`.
* supporting: `residual_eval` (form evaluates to 0 under `ModeA`),
  `pos_neg_eval`, `charge_total` (`K ≤ P`), `cap_total`
  (`U ≤ Bcap + uu·δ`), `gadget_fields` (packaged
  `ResidualWitness.Valid`-style field verification), `cap_bound`,
  `charge_bound`.

`#print axioms` for both level theorems:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## Proof notes

* `charge_total`: each charge `(v,a,b)` is a complementary angle, so
  `ang_le` gives `Σ_arc r ≥ 1 − q_arc` (`charge_bound`); multiplying
  by `min_arc coef ≥ 0` bounds `chargeGain ≤ Σ_arc (coef⁺·r)`.  Charge
  arcs are pairwise disjoint after embedding `(v,g)` as product pairs
  (`hdj` hypothesis), so the gains pack inside `P`.
* `cap_total`: pointwise `coef⁻·r ≤ (coverage)·r` from the `hcov`
  condition, summed and regrouped into per-cap
  `m·Σ_range r ≤ m·(B + u·δ)` (`cap_bound`), giving `U ≤ Bcap + uu·δ`.

## Fixtures / regression

* `tools/gadget_fixtures.py` regenerates `tools/gadget_fixtures.json`
  (28 gadgets): per record of `chain_dump_s4.json` it runs
  `eval_chain`/`pure_gadget` with identical selection logic but also
  records the explicit `charges`/`caps`/`coef` that link_graph only
  keeps implicitly.  Two synthetic all-direct skeletons
  (`syn-purecap`, `syn-purecap2`) supply pure-cap and score-2
  coverage (no `q_arc ≥ n` skeleton exists in the s4 dump).
* `tools/gadget_check.py` recomputes `coef`, `dco`, `con`, `K`,
  `Bcap`, `u`, `bound`, `score` from `(skel, fans, links, charges,
  caps)` using the Lean formulas and checks every `Valid` side
  condition.  Result: `28 ok, 0 bad`.
* Coverage: pure-cap 2, fan-only 3, fan-strip 23, mixed-sign 17,
  score0 6, score1 20, score2 2 (tags overlap).

## Commands

```sh
cd tools && python3 gadget_fixtures.py   # regenerate fixtures
cd tools && python3 gadget_check.py      # verify (exit 0)
lake build Jsp000404.Gadget              # Lean side
```

## Discrepancies vs the WIP

None semantic.  The WIP compiled fixes were: `Finset.Ico`/`Fintype`
imports, `LinForm` evaluation lemmas, `CapEntry`/`Gadget` signature
parameters, `max` orientation in `pos_neg_eval`, and the two `sorry`s
(`charge_total`, `cap_total`) which are now proved.  A pre-existing
multiplication-order type error in `DebtChain.lean` (`hcap`) was also
fixed (`rw [mul_comm]`).

## Limitations

* `nn`-kind caps are not exercised by any fixture (checker never emits
  them).
* Fixture `pos`/`bits` are only defined at `u ≠ v` (as in the checker);
  Lean's `VertexData.pos/bits` are total functions but only ever
  evaluated at distinct `u ≠ v`.
* Lean `bound` is a `ℚ` guard (`cc+uu ≤ 0 → 0`); the checker only
  produces gadgets with `c+u > 0`, where the two agree exactly.
* `gadgetSelection_low`/`gadgetSelection_high` remain OPEN — this file
  does not address gadget existence.
