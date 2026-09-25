# JSP-000404 — Pentagon result → `GadgetSelectionHighP` bridge

Date: 2026-09-24.  Source: opponent snapshot `jsp404-pentagon-order-20260923.zip`.

## What the opponent proved

For a `FiniteClusterModel V 3` (five occupied centres) and parameter `t` with `1 ≤ t < 3`:

- `card_eq_five_of_lt_three` — if the angle bound `(1 - 1/t)·π` holds, the total label count is exactly 5.
- `not_angleBound_of_five_centres_low` — if `1 ≤ t < 5/2`, the angle bound cannot hold.

The proof uses `ConvexIndependent` + strict separation + slope sorting + Radon classification to construct a `PentagonFan` for any relabelled convex-independent 5 points, then uses the exterior-angle budget (`exterior_sum = 2`) and `FiniteExteriorBound` to get `card ≤ 2·t`.

## Mapping to our language

In our `GeomSkeleton` setup:

- `t = π / λ` (the parameter in the opponent's angle cap).
- `n = ⌊π / λ⌋₊` is the same `n` that indexes `GadgetSelectionHighP`.
- `δ = π/λ - n = t - n`, with `0 ≤ δ < 1`.
- `W = potential / 2^{n-1}` by `bridgeSkeleton_W`.
- For five points (`s = 5`), the opponent's total label count 5 translates to `potential = 5` labels in the finite-cluster model.

The Sendov high cap for the corresponding band is `2^n + 2^{n-2}`.  For `n = 2` this is `4 + 1 = 5`, i.e. the same as the opponent's "exactly 5" count.  Hence in the geometric range `2.5 ≤ t < 3` (which is `n = 2` with `δ ≥ 1/2`, the HIGH regime), the opponent has shown that a 5-point configuration cannot exceed the high cap; it saturates it exactly when the angle bound is satisfied.

## Target for the gadget pipeline

`GadgetSelectionHighP 5 2` says:

```lean
∀ sk : Skeleton 5, sk.Proper → sk.Consistent 2 → (5 : ℚ) / 2 < sk.W 2 →
  ∃ g : Gadget 5, g.Valid 2 sk ∧ (1 : ℚ) ≤ g.bound 2 sk
```

The **geometric subcase** (skeletons that arise from a legal 5-point configuration via `bridgeSkeleton`) is handled as follows:

1. `GeomSkeleton` gives `sk.Proper`, `sk.Consistent 2`, and `sk.W 2 = potential / 2`.
2. The opponent's `card_eq_five_of_lt_three` for `2.5 ≤ t < 3` gives `potential ≤ 5`.
3. Therefore `sk.W 2 ≤ 5/2`, contradicting the hypothesis `(5 : ℚ) / 2 < sk.W 2`.
4. So the implication is vacuously true for all geometric `Skeleton 5` with `n = 2`.

## What remains to close

`GadgetSelectionHighP` is quantified over **all** proper consistent `Skeleton 5`, not only geometric ones.  To use the opponent's result for the full proposition, we need one of:

(A) Show every proper consistent `Skeleton 5` with `n = 2` is geometric, i.e. realizable by a legal planar 5-point configuration.  This is the inverse of the bridge and is not proved.

(B) Lift the opponent's exterior-angle / pentagon argument to abstract `Skeleton`/`ModeA` without referring to actual Euclidean points.  The bridge gives `angleExpr = ∠/λ` and `bridgeSkeleton_W`, but the combinatorial structure of `PentagonFan` (convex independence, strict crossings, exterior sum = 2) needs a purely skeleton-level analogue.

(C) Construct an explicit `Gadget 5` from the `PentagonFan` data.  The opponent's three crossing diagonals (`AC/BD`, `AD/CE`, `AC/BE`) are natural signed triangle links that can be turned into `Gadget.links` with weights; the exterior-sum `2` gives the residual constant; the angle cap gives the cap entries.  This is the most direct route.

## Recommended next step

Pursue (C): for any proper `Skeleton 5` that is geometrically induced by a convex pentagon (or can be relabelled to one), use the three diagonal crossings as triangle links, the five fan equalities, and the exterior-angle budget to build a `Gadget` with `bound ≥ 1`.  The gadget construction can be done in `Jsp000404/PentagonGadgetBridge.lean` and then integrated into `gadgetSelection_of_selectionP`.

## Axiom note

No new axioms are needed for the bridge theorems; the open step is the construction/proof of the gadget, which will use only `propext`, `Classical.choice`, `Quot.sound` if it stays inside the existing framework.
