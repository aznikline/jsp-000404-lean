# JSP-000404 — Opponent lower-bound bridge (2026-09-30)

Source: `jerrylijize1224-star/jsp404-lean-partial` @ `3182c9b1d2b4e3f1ab2a98a64cfaabba2d72cda7`
Snapshot: `jsp404-deficit-obstruction-20260930.zip`

Previous snapshots in this lineage:
- `jsp404-edge-lower-20260929.zip`
- `jsp404-quantitative-lower-20260928.zip`
- `jsp404-strict-lower-20260927.zip`
- `jsp404-uniform-lower-20260927.zip`

## Latest: dyadic sharp values + deficit/rotating obstruction (2026-09-30)

### 1. Sharp dyadic values

File: `Prize/JSP404/DyadicSharp.lean`

```lean
theorem alpha_dyadic {k : ℕ} (hk : 2 ≤ k) :
    alpha (2 ^ k) = (1 - 1 / (k : ℝ)) * Real.pi

theorem dyadic_isSharpBound {k : ℕ} (hk : 2 ≤ k) :
    IsSharpBound (2 ^ k) ((1 - 1 / (k : ℝ)) * Real.pi)

theorem alpha_sixteen : alpha 16 = (3 / 4 : ℝ) * Real.pi
theorem alpha_thirty_two : alpha 32 = (4 / 5 : ℝ) * Real.pi
```

This proves Sendov's value for every dyadic cardinality `N = 2^k` (`k ≥ 2`), i.e. `N = 4, 8, 16, 32, 64, ...`. It uses `RotatingSectorCover` for the lower bound and `EquallySpacedBinaryAxes` for the upper bound.

### 2. Rotating deficit obstruction

File: `Prize/JSP404/RotatingSectorDeficit.lean` / `RotatingCoverDeficit.lean`

The 9.30 work also introduces a **free-slot budget**: for a rotating sector cover, the total budget is `N + ∑_v f(v) ≤ 2^k`, where `f(v)` counts unused relations at vertex `v`. When `N + 1 = 2^k`, at most one free pair is allowed at any rotation. This rules out an unrestricted quantifier exchange in the binary-cover argument.

A concrete 6-pair obstruction from an equilateral triangle shows the budget is tight.

### 3. Earlier lower bounds preserved

The 9.29 edge-lower and 9.28 quantitative/strict lower bounds are still in the project but are now superseded for dyadic `N` by the exact values.

## Relevance to our `lane/integration`

Our `Jsp404.alphaN` is the Sendov piecewise formula. For dyadic `N = 2^k`:

```lean
alphaN (2 ^ k) = (1 - 1 / (k : ℝ)) * Real.pi
```

So the opponent's `alpha_dyadic` gives the equality `JSP404.alpha (2^k) = alphaN (2^k)`.

We already have the general upper bound:

```lean
theorem alpha_le_alphaN (N : ℕ) (hN : 3 ≤ N) : JSP404.alpha N ≤ alphaN N
```

The remaining `MainTheorem.sendov_lower` needs `alphaN N ≤ JSP404.alpha N` for **all** `N ≥ 9`.

### What is useful to borrow

1. **Dyadic equality already matches our formula** for `N = 2^k`. This is the first infinite family where the opponent has closed `IsSharpBound`.
2. **Rotating sector cover / free-slot budget** may be reusable for non-dyadic `N` if our gadget/selection route stalls.
3. **The non-dyadic bands remain open** in the opponent's project, same as ours.

### Mapping to our notation

For our `alphaN` and `JSP404.alpha`, the dyadic result becomes:

```lean
-- Opponent's dyadic sharp result (borrowable as an interface theorem; proof not ported)
theorem opponent_alpha_dyadic (k : ℕ) (hk : 2 ≤ k) :
    JSP404.alpha (2 ^ k) = alphaN (2 ^ k) := sorry
```

Full Lean port would require copying `Prize/JSP404/DyadicSharp.lean`, `RotatingSectorCover.lean`, `RotatingSectorDeficit.lean`, `CompactDirectionSpace.lean`, `EquallySpacedBinaryAxes.lean`, etc., or reproving within our `PtCfg`/angle framework.

## Status

- Opponent's `SendovClaim` remains unproved (it requires all `N`, not just dyadic).
- Our `MainTheorem.sendov_lower` N ≥ 9 remains `sorry`.
- The race is still open for non-dyadic cardinalities.
