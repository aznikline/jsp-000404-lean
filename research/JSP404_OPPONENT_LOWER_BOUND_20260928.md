# JSP-000404 — Opponent lower-bound bridge (2026-09-28)

Source: `jerrylijize1224-star/jsp404-lean-partial` @ `ad96b5e65b87d305ea7606d6ac97675aacda61e1`
Snapshot: `jsp404-quantitative-lower-20260928.zip`

## What the opponent proved

### 1. Quantitative explicit lower bound

File: `Prize/JSP404/QuantitativeLowerBound.lean`

```lean
def quantitativeAngle k N := Real.pi - (Real.pi / k) * (1 - 1 / (N^2 + 1))
-- equivalent to: (1 - 1/k) * pi + pi / (k * (N^2 + 1))

theorem quantitative_alpha_lower {k N : ℕ} (hk : 0 < k) (hN : 2^k < N) :
    quantitativeAngle k N ≤ alpha N
```

This improves the uniform bound `alpha N ≥ (1 - 1/k)π` by an explicit margin `π / (k(N^2+1))`.

### 2. Strict uniform lower bound (existential margin)

File: `Prize/JSP404/StrictUniformLowerBound.lean`

```lean
theorem uniform_alpha_strict_lower {k N : ℕ} (hk : 0 < k) (hN : 2^k < N) :
    (1 - 1/k) * Real.pi < alpha N

theorem exists_uniform_alpha_gap {k : ℕ} (hk : 0 < k) :
    ∃ ε > 0, ∀ N, 2^k < N → (1 - 1/k) * Real.pi + ε ≤ alpha N
```

The ε is existential (derived from compactness of the unit direction assignment space), not the sharp Sendov gap.

### 3. Band-wise intervals

```lean
theorem low_band_alpha_strict_bounds {k N : ℕ} (hk : 2 ≤ k)
    (hlo : 2^k < N) (hhi : N ≤ 2^k + 2^(k-2)) :
    (1 - 1/k) * Real.pi < alpha N ∧ alpha N ≤ (1 - 2/(2k+1)) * Real.pi

theorem high_band_alpha_strict_bounds {k N : ℕ} (hk : 2 ≤ k)
    (hlo : 2^k + 2^(k-2) < N) (hhi : N ≤ 2^(k+1)) :
    (1 - 1/k) * Real.pi < alpha N ∧ alpha N ≤ (1 - 1/(k+1)) * Real.pi
```

### 4. Example: alpha 17

Old: `3π/4 < alpha 17 ≤ 7π/9`  
New: `871π/1160 ≤ alpha 17 ≤ 7π/9`  
Numerically: `135.155° ≤ alpha 17 ≤ 140°`.

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
3. **The quantitative formula is weaker than `alphaN`** in both bands, so it cannot directly replace `sendov_lower`. It does show `alpha` is strictly above the uniform bound.

### Mapping to our notation

For our `alphaN` and `JSP404.alpha`, the opponent's statements become:

```lean
-- Quantitative (borrowable as an interface theorem; proof not ported)
theorem opponent_quantitative_lower (k N : ℕ) (hk : 0 < k) (hN : 2^k < N) :
    (1 - 1/(k : ℝ)) * Real.pi + Real.pi / ((k : ℝ) * ((N : ℝ)^2 + 1)) ≤ JSP404.alpha N := sorry

-- Strict (borrowable as an interface theorem; proof not ported)
theorem opponent_strict_lower (k N : ℕ) (hk : 0 < k) (hN : 2^k < N) :
    (1 - 1/(k : ℝ)) * Real.pi < JSP404.alpha N := sorry
```

These are currently documented here; full Lean port would require copying `Prize/JSP404/QuantitativeSectorCover.lean`, `CompactDirectionSpace.lean`, `GeneralAngleBounds.lean`, etc., or reproving within our `PtCfg`/angle framework.

## Status

- Opponent's `SendovClaim` remains unproved.
- Our `MainTheorem.sendov_lower` N ≥ 9 remains `sorry`.
- The race is still open: whichever side first proves `alphaN N ≤ JSP404.alpha N` for all N ≥ 9 closes the theorem.
