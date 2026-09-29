# JSP-000404 — Opponent lower-bound bridge (2026-09-29)

Source: `jerrylijize1224-star/jsp404-lean-partial` @ `d7f1b623e2b763d0dbce1ba63ed65d112c32d952`
Snapshot: `jsp404-edge-lower-20260929.zip`

Previous source: `ad96b5e65b87d305ea7606d6ac97675aacda61e1` (`jsp404-quantitative-lower-20260928.zip`)

## Latest: unordered-edge lower bound (2026-09-29)

### 1. Edge-based explicit lower bound

File: `Prize/JSP404/EdgeDirectionLowerBound.lean`

```lean
def edgeAngle k N :=
  (1 - 1/k) * Real.pi + Real.pi / (k * (N.choose 2 + 1))

theorem edge_alpha_lower {k N : ℕ} (hk : 0 < k) (hN : 2^k < N) :
    edgeAngle k N ≤ alpha N
```

Idea: instead of using one representative for every ordered pair including dummy diagonals, count exactly one representative for each **unordered edge**. This reduces the number of directions from `N²` to `N.choose 2`, giving a larger explicit margin.

### 2. Comparison to the 9.28 quantitative bound

9.28 margin: `π / (k * (N² + 1))`  
9.29 margin: `π / (k * (N·(N-1)/2 + 1))` — approximately twice as large for large `N`.

```lean
theorem quantitativeAngle_lt_edgeAngle {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    quantitativeAngle k N < edgeAngle k N
```

### 3. Example: alpha 17

9.27 strict: `3π/4 < alpha 17 ≤ 7π/9`  
9.28 quantitative: `871π/1160 ≤ alpha 17 ≤ 7π/9` ≈ `135.155° ≤ alpha 17 ≤ 140°`  
9.29 edge: `103π/137 ≤ alpha 17 ≤ 7π/9` ≈ `135.328° ≤ alpha 17 ≤ 140°`

## Earlier: quantitative and strict uniform lower bounds (2026-09-28)

File: `Prize/JSP404/QuantitativeLowerBound.lean`

```lean
def quantitativeAngle k N := Real.pi - (Real.pi / k) * (1 - 1 / (N^2 + 1))
-- equivalent to: (1 - 1/k) * pi + pi / (k * (N^2 + 1))

theorem quantitative_alpha_lower {k N : ℕ} (hk : 0 < k) (hN : 2^k < N) :
    quantitativeAngle k N ≤ alpha N
```

File: `Prize/JSP404/StrictUniformLowerBound.lean`

```lean
theorem uniform_alpha_strict_lower {k N : ℕ} (hk : 0 < k) (hN : 2^k < N) :
    (1 - 1/k) * Real.pi < alpha N

theorem exists_uniform_alpha_gap {k : ℕ} (hk : 0 < k) :
    ∃ ε > 0, ∀ N, 2^k < N → (1 - 1/k) * Real.pi + ε ≤ alpha N
```

The ε is existential (derived from compactness of the unit direction assignment space), not the sharp Sendov gap.

## Relevance to our `lane/integration`

Our `Jsp404.alphaN` is the Sendov piecewise formula. We already have the upper bound:

```lean
theorem alpha_le_alphaN (N : ℕ) (hN : 3 ≤ N) : JSP404.alpha N ≤ alphaN N
```

in `Jsp000404/UpperBound.lean`. The remaining `MainTheorem.sendov_lower` needs:

```lean
alphaN N ≤ JSP404.alpha N  -- for N ≥ 9
```

### What is useful to borrow

1. **Not the upper bounds**: we already have our own sharp upper bands.
2. **The lower-bound techniques may be useful if our gadget/selection route stalls**:
   - Empty-bin/short-sector counting (`QuantitativeSectorCover`)
   - Compactness-based uniform margin (`CompactDirectionSpace`, `UnitDirectionAssignments`)
   - Binary counting transfer to ordinary configurations
   - Unordered-edge representative selection (`EdgeDirectionLowerBound`)
3. **The edge formula is still weaker than `alphaN`** in both bands, so it cannot directly replace `sendov_lower`. It does show `alpha` is strictly above the uniform bound.

### Mapping to our notation

For our `alphaN` and `JSP404.alpha`, the opponent's latest statement becomes:

```lean
-- Edge lower (borrowable as an interface theorem; proof not ported)
theorem opponent_edge_lower (k N : ℕ) (hk : 0 < k) (hN : 2^k < N) :
    (1 - 1/(k : ℝ)) * Real.pi
      + Real.pi / ((k : ℝ) * ((N.choose 2 : ℝ) + 1)) ≤ JSP404.alpha N := sorry
```

Full Lean port would require copying `Prize/JSP404/EdgeDirectionLowerBound.lean`, `QuantitativeSectorCover.lean`, `CompactDirectionSpace.lean`, `GeneralAngleBounds.lean`, etc., or reproving within our `PtCfg`/angle framework.

## Status

- Opponent's `SendovClaim` remains unproved.
- Our `MainTheorem.sendov_lower` N ≥ 9 remains `sorry`.
- The race is still open: whichever side first proves `alphaN N ≤ JSP404.alpha N` for all N ≥ 9 closes the theorem.
