# Lane B2 — HIGH-MECHANICAL status

Base: `lane/integration` @ `b69e915`. Branch: `lane/b2-highmech`.
New file: `Jsp000404/HighSelection.lean` (imported from the root
`Jsp000404.lean`).

Everything below labelled PROVED is a Lean theorem in a green build
(`lake build`, 8946 jobs), axiom-checked to depend only on
`[propext, Classical.choice, Quot.sound]` — no `sorry`/`sorryAx`.

## Required lemma stack — status

| Lemma | Status | Location / notes |
|---|---|---|
| `weight_ge_two_sat` | **PROVED** | `Jsp000404/HighSelection.lean:322`. For `s = 4`, `d_v ≥ 0`, `(5:ℚ)/2 < sk.W n`, concludes `2 ≤ #{v ∣ saturated n v}`. Route: `Rat.cast` of `Skeleton.W` to ℝ (`Rat.cast_sum`, `Rat.cast_zpow`), `Int.toNat` deficits via `d ≥ 0`, `dyadic_two_zeros4`, `d = 0 ↔ saturated` (`Skeleton.d_eq_zero_iff_saturated`), pair-subset cardinality. Packaged variants: `weight_ge_two_sat'` (checker `q`-bounds, `:374`), `weight_ge_two_sat_of_consistent` (`Σ q ≤ n` from mode A, `:383`). |
| `saturated_iff` | **PROVED** | `:150`. For `2 ≤ n`, `0 ≤ q`, `Σ q ≤ n`: `k_v = n − 1 ↔ ∃ t, q_t = n ∧ (∀ g ≠ t, q_g = 0)`. Pure algebra: split the `kexp`/`q` sums at the unique heavy cell, slack `q_g − max(q_g−1,0)` vanishes. |
| `saturated_dichotomy` | **PROVED** | `:270`. Sat vertex ⇒ heavy cell `t` via `saturated_iff`, then `VertexData.badAt_or` (`:251`) gives: same-bit arc `∋ t` ∨ complementary arc `∌ t` ∨ `badAt t`; the third disjunct + heavy-cell data packages to `v.bad n`. |
| `good_saturated_gadget` | **PROVED** | `:904` (raw form) + `good_saturated_gadget'` (`:937`, takes `saturated ∧ ¬bad` + checker bounds). Pure-cap branch: `pureCapGadget` (single `piLam` cap, `:607`), valid via `pureCapGadget_valid` (`:623`), bound `= 1` via `pureCapGadget_bound` (`:683`) since `arcQ = n`. Fan+charge branch: `fanChargeGadget` (unit fan + one complementary charge, `:617`), valid via `fanChargeGadget_valid` (`:733`, uses `Gadget.charge_bound` to force arc nonempty), bound `= 1` via `fanChargeGadget_bound` (`:822`). |
| `three_sat_has_good` | **PROVED** | `:451` (explicit triple) + `three_sat_has_good'` (`:490`, cardinal form). Key input `bad_saturated_angle_le` (`:399`): at a bad saturated vertex every angle `≤ δ` (fan equality gives `Σ r_v = δ`; `arcQ ∈ {0, n}` at a heavy cell). Three bad saturated vertices force `n + δ ≤ 3δ` in the mode-A triangle equality, i.e. `n ≤ 2δ < 2`, contradicting `2 ≤ n`. |
| `all_bad_strip` | **OPEN — Lane B3** | Stated (not proved) as `Jsp404.AllBadStrip` (`:955`): consistent `W > 5/2` skeleton, every saturated vertex bad ⇒ `∃` valid gadget bound `≥ 1`. CHECKER-VALIDATED only; `gadgetSelection_high` takes it as an explicit hypothesis. |

## Assembled reduction

`gadgetSelection_high` (`:964`): for `2 ≤ n`, `s = 4`, checker-style
`0 ≤ q`, `sk.Consistent n`, `(5:ℚ)/2 < sk.W n`, and `AllBadStrip 4 n`,
produces `∃ g, g.Valid n sk ∧ (1:ℚ) ≤ g.bound n sk`. Case split:
`≥ 3` saturated ⇒ `three_sat_has_good'` + `good_saturated_gadget'`;
exactly `2` saturated ⇒ either all bad (`AllBadStrip`, lane B3) or a
good one (`good_saturated_gadget'`).

Supporting gadget algebra proved in-file: `LinForm.coef_formSum` /
`dco_formSum` / `con_formSum`, `Gadget.coef_eq_fans` /
`dco_eq_neg_fans` / `con_eq_fans` (no-link gadgets), `finRange_map_sum`.

## Remaining gap (exact)

The **only** open node is `Jsp404.AllBadStrip` — the two-saturated
all-bad strip. It is consumed as a hypothesis by
`gadgetSelection_high`; discharging it is Lane B3's node (LANE_B.md
§6 H4). No other gap: every mechanical lemma in the B2 stack is
proved.

Note also the repo-wide caveats (pre-existing, not from this file):
`sk.Consistent n` includes `δ < 1` but the `0 ≤ δ` field is named
`hδ0`/`hδ1` in `gadgetSelection_high` via the `Consistent` structure;
the full `GadgetSelectionHigh` in `GadgetSelection.lean` still needs
`AllBadStrip` plus the ambient `0 ≤ q` checker hypothesis threading.

## Build / sorry status

- `lake build` — **green**, 8946 jobs (warnings only: deprecation +
  linter noise, all pre-existing style).
- `sorry` count in `Jsp000404/HighSelection.lean` — **0**
  (`grep -n 'sorry\|admit\|axiom'` clean).
- `#print axioms` on every stack theorem —
  `[propext, Classical.choice, Quot.sound]` only.
