# M3 target — R-HIGH1 (transcribed from source)

Scope: `n ≥ 3`, `δ = π/λ − n ∈ [1/2, 1)`, `S = 1` (exactly one center
with `rowDefect = 1`).  Goal: `potential ≤ sendovCap n true`, i.e.

```text
potential lam (directionRows o e c) ≤ 2^n + 2^(n-2)     (= 5·2^{n-2})
```

equivalently `K = Σᵢ 2^{−cᵢ} ≤ 5/4`.

## Actual declarations (as read from source)

`Jsp000404/Induction.lean`:

```lean
def sendovCap (n : ℕ) (big : Bool) : ℕ :=
  2 ^ n + if big then 2 ^ (n - 2) else 0

def CertExists (n : ℕ) (big : Bool) (lam : ℝ) : Prop :=
  ∀ {t : ℕ} {c : Fin t → Plane₂}, 4 ≤ t →
    Section4Legality c lam →
    sendovCap n big < potential lam (directionRows o e c) →
    EmissionDichotomy lam
      (fun v i => deleteIndex o e c v i) (directionRows o e c)

theorem potential_le_sendovCap {n : ℕ} (hn2 : 2 ≤ n) (big : Bool)
    {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (hn : Nat.floor (Real.pi / lam) = n)
    (hbig : big = false → Real.pi / lam - n < 1 / 2)   -- one-way only
    (hcert : CertExists o e n big lam) (he : e ≠ 0) :
    ∀ {s : ℕ}, 3 ≤ s → ∀ {c : Fin s → Plane₂},
      Section4Legality c lam →
      potential lam (directionRows o e c) ≤ sendovCap n big
```

Consumer chain: `potential_le_sendovCap` → `staircase_of_cert`
(Induction.lean) → `CertificateIntegration` → `MainTheorem.sendov_lower`.
`CertExists` is the sole mathematical opening on that path.

Note the one-way `hbig`: `big = true` is consistent with any δ; the
regime `δ ≥ 1/2` is what *forces* `big = true` upstream, and
`δ < 1/2` forces `big = false`.  The R-HIGH1 scope therefore uses
`big = true` together with the explicit hypothesis
`1/2 ≤ π/λ − n` (`hδ`).

## What is proved so far (this phase)

`Jsp000404/OneSaturatedHigh.lean` (new):

```lean
theorem one_saturated_capacity_of_narrow_window {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (_he : e ≠ 0)
    (hs : 1 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (_hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    {beta : ℝ} (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin s,
      InnerProductGeometry.angle (c (v.succAbove i) - c v)
        (c (v.succAbove j) - c v) ≤ beta) :
    ∃ e' : Plane₂, e' ≠ 0 ∧
      potential lam (directionRows o e' c) ≤ 2 ^ n

theorem potential_le_two_pow_of_saturated_narrow {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin s) (_hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    {beta : ℝ} (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin s, i ≠ v → j ≠ v →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ beta) :
    potential lam (directionRows o e c) ≤ 2 ^ n
```

Axioms: `[propext, Classical.choice, Quot.sound]` (both, kernel
`#print axioms`).  The bound `2^n` is strictly stronger than the cap
`2^n + 2^{n-2}`.

Mechanism: `exists_ray_window` (new chart `e'` in the middle of the
anchor-ray spread) → `chord_in_corridor` puts every chord
representative in `[λ, π−λ+β]`; `β < α = (n+1)λ − π` makes the
corridor width `< (n−1)λ`, so `n−1` uniform bins of width `< λ`
suffice.  `δ ≥ 1/2` gives `α ≤ λ/2`, so `β < λ/2` and the anchor
offsets satisfy the `theta ≤ λ/2` premise of
`anchored_rowScore_eq_linear`.  Then `directionBinGraph_row_weighted_bound`
+ `linearGapScore_le_empty_of_interval` bound the non-anchor rows by
`2^{n−1}` and the anchor row by `2^{n−1}` (`rowScore ≤ n−1`).

## The precise residual obligation (live blocker)

The complementary case inside R-HIGH1:

```text
saturated center v,  δ ≥ 1/2,  and there is NO beta < α = (n+1)λ − π
bounding all pairwise angles of the rays c w − c v  (w ≠ v),
i.e. the anchor-ray spread is ≥ α.
```

By `saturated_ray_window` the spread is always `< δλ < λ`, so the
residual window is `α ≤ spread < δλ` — nonempty exactly when
`δ > 1/2`.  The exact four-point example in
`notes/ONE_SATURATED_HIGH_GEOMETRY.md` (spread ≈ 29°, α ≈ 4.3°) shows
this subdomain is nonempty, so the corridor argument alone cannot
finish R-HIGH1; a genuinely different argument (or a split into
subdomains each reachable by existing machinery) is required there.

What remains after this reduction: prove that in the residual case
`potential ≤ 2^n + 2^{n-2}` — or more precisely that the
over-capacity assumption yields `EmissionDichotomy`, matching the
`CertExists` consumer.

## Defect/remainder identities (verified from source)

- `rowDefect = rowBig + (n − rowCells)`,
  `rowScore = rowCells − rowBig = n − rowDefect` when `rowCells ≤ n`
  (`Deletion.lean`: `rowScore_eq_cells_sub_big`,
  `rowScore_eq_sub_defect`, `one_le_rowDefect`).
- `Σ_j r_ij = c_i − big_i + δ` follows from `Σ g = π = (n+δ)λ`.
- `SaturatedStructure.saturated_cells_unique`: defect-1 row ⇒ exactly
  one cell of size `n`, all other cells `0`, remainder sum `δ`.
  The `big = 0` defect-1 branch is impossible (would need `cells = n`
  with every gap `< λ`, contradicting `Σ g = π`).
