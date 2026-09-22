# JSP-000404 — Consolidated Status (auto-maintained by Lead)

Integration head: see `lane/integration`. All lane branches pushed to
`github.com/aznikline/jsp-000404-lean`.

## Branch map

| Branch | Purpose | Status |
|---|---|---|
| `master` | baseline: arithmetic engine + tools + handoff notes | stable |
| `lane/integration` | merged integration trunk (build green, 8945 jobs) | ACTIVE TRUNK |
| `lane/c-gadget` | `Gadget.lean` — checker-faithful semantics, 0 sorry | merged |
| `lane/a-low` | selection Props + `CapKind.low` + soundness lemmas | merged |
| `lane/b-high` | `HighDebt.lean` level-2 arithmetic + `dyadic_two_zeros` | merged |
| `lane/d-integration` | `Integration.lean` conditional pipeline + `FINAL_DAG.md` | merged |
| `lane/e-challenger` | falsification wave 1 + inf-semantics correction | merged |
| `lane/a2-lowclose` | ghost-vertex counterexample + `Skeleton.Proper` repair | merged |
| `lane/b2-highmech` | `HighSelection.lean` mechanical stack (all PROVED) | merged |
| `lane/b3-allbad` | `AllBad.lean` alignment invariant PROVED + 8-branch spec | merged |
| `lane/e2-challenger` | s=4 exhaustive census + vacuum observation + cache-bug report | merged |
| `lane/l1-lowp` | W3: `GadgetSelectionLowP` attack | RUNNING |
| `lane/v1-vacuum` | W3: vacuum lemma `Consistent ⇒ W ≤ 5/2` | RUNNING |
| `agent/*` | older session worktrees (crossmap, l2-l3) | archived |

## PROVED (Lean, 0 sorry, standard axioms only)

- `Gadget/Valid/bound` + `charge_total`/`cap_total`/`gadget_ge_half`/`gadget_ge_one`
- `CapKind.low` signature-cap extension; 28/28 Python↔Lean fixture parity
- `debt_residual_ge(t)`, `ResidualWitness.ge_half/ge_one`, `charge_cap_ge`, `pure_cap_ge`
- `dyadic_two_zeros` (general s), `dyadic_two_zeros4`
- `weight_ge_two_sat`, `saturated_iff`, `saturated_dichotomy`,
  `good_saturated_gadget`, `three_sat_has_good`
- `bad_pair_slots` alignment invariant ((L,R)/(R,L)/(O,O) only)
- `selection_low_soundP` / `selection_high_soundP`
- `gadgetSelection_high` reduced to single `AllBadStrip` hypothesis
- `sendov_lower_three` (unconditional N=3), `sendov_of_hypotheses` (conditional)

## OPEN (the only remaining blockers)

1. `GadgetSelectionLowP` — proper skeletons, W>2 ⇒ ∃ gadget bound ≥ 1/2 (Lane L1)
2. Vacuum lemma `Consistent ⇒ W ≤ 5/2` — if proved, `GadgetSelectionHighP` is
   vacuous and `all_bad_strip` is unnecessary (Lane V1)
3. `all_bad_strip` — contingency only; 8-branch spec in `notes/LANE_B3.md`,
   checker coverage 100% on all W>5/2 profiles

## FALSIFIED / corrected

- Loose `GadgetSelectionLow/High` without `Proper`: ghost-vertex counterexample
  at (s,n)=(3,2) — `not_gadgetSelectionLow_3_2` etc. (uses `native_decide`;
  kept off the root path)
- `inf` from capped LP ≠ structural inconsistency (δ-clamp bug fixed; free-δ
  tooling added)
- `lane_a6._CAP_CACHE` keyed by `id(ctx)` — warm-cache bounds wrong; cold
  recomputation confirmed no soundness violation in affected rows

## Completion gate (unchanged)

arbitrary-N root theorem, both regimes closed, no sorry/admit/custom axiom /
unproved-parameter substitution, fresh `lake build`, root `#print axioms`
standard-only, quantifier-correspondence audit, public immutable commit.
