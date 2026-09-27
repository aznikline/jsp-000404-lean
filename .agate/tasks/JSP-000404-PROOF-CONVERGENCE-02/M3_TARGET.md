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

Also proved, a pure counting closure (no geometry needed beyond
`rowCells ≤ n` and defect bookkeeping):

```lean
theorem potential_le_high_of_saturated_small {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (hs : 2 ≤ s) (hs4 : s ≤ 4) (hn2 : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin s → Plane₂} (_hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (huniq : ∀ w : Fin s, w ≠ v →
      2 ≤ rowDefect n lam (directionRow o e c w)) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2)
```

i.e. R-HIGH1 is closed whenever `s ≤ 4` total centers: the anchor row
contributes `2^{n−1}` and each of the `≤ 3` remaining rows has defect
`≥ 2` (since `S = 1`), hence exponent `≤ n−2`, giving
`2^{n−1} + 3·2^{n−2} = 5·2^{n−2}` exactly.  This subdomain is *tight*:
the `AVERAGED_BIN_PACKING.md` family `(O,P,Q,R)` attains equality at
`s = 4` for every `n ≥ 3`, with anchor spread `7λ/10 > α` — it lives
inside the residual window subdomain.

**Bottom-clump closure** (proved): if some non-anchor row's chord
directions all lie in `[λ, λ+w₀)` with `w₀·n < π−λ`, an adaptive
uniform cover of width `max((π−(n+1)λ+δλ)/n, (w₀+B)/2)` (`B = (π−λ)/n`)
puts all of that row's chords in bin `0`.  Its encoding cube then has
volume `2^{n−1}` while its defect `≥ 2` bounds the actual weight by
`2^{n−2}` — a `2^{n−2}` slack equal to the whole quarter-cube needed:

```lean
theorem potential_le_high_of_saturated_clump {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 1 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin (s + 1))
    (_hsat : rowDefect n lam (directionRow o e c v) = 1)
    (huniq : ∀ i : Fin s,
      2 ≤ rowDefect n lam (directionRow o e c (v.succAbove i)))
    {theta : Fin s → ℝ}
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    {w0 : ℝ} (hw0 : w0 * (n : ℝ) < Real.pi - lam)
    (istar : Fin s)
    (hclump : ∀ j : Fin s, j ≠ istar →
      dirRep o e (c ∘ v.succAbove) istar j ∈ Set.Ico lam (lam + w0)) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2)
```

Axioms: `[propext, Classical.choice, Quot.sound]` (kernel
`#print axioms`; module + root build pass).  The hypothesis is
chart-relative: `dirRep` values are taken in the same chart `e` in
which `theta` realizes the anchor rays — upstream the chart is
supplied by `saturated_chord_corridor` (θ ∈ `[0, δλ]`).  This
required generalizing `AnchoredRows.directionRow_anchor_cons` and
`anchored_rowScore_eq_linear` from `theta ≤ λ/2` to `theta ≤ λ`
(the residual window has `θ` up to `δλ`).

This also covers the tight equality family of
`notes/AVERAGED_BIN_PACKING.md`: its slack row `Q` has both chord
directions at `9λ/8` and `5λ/4`, which lie in `[λ, λ + λ/3)`, so
`w₀ = λ/3` and `w₀·n = λn/3 < π − λ` iff `n/3 < n + δ − 1`, true for
`n ≥ 3`.  (Independent coverage: the same family is already closed by
`potential_le_high_of_saturated_small` since it has only 4 centers.
Corrected per Lead review: `w₀ = λ/8` was wrong — `5λ/4` is the
excluded right endpoint of `[λ, λ+λ/8)`; and `λ/4` likewise fails.)

IMPORTANT SCOPE NOTE (Lead correction): the clump premise fixes the
interval's LEFT endpoint at `λ` — it only excludes rows whose chords
sit in the bottom prefix `[λ, λ+w₀)`.  A row can be narrow yet sit in
the middle of the corridor; such rows are NOT excluded from the
residual.

**Single-outlier deletion closure** (proved, this round): if deleting
one non-anchor center `q` leaves every pair of surviving anchor rays
within `β < α`, then `potential ≤ 2^n + 2^{n−2}` — the deleted row's
weight `≤ 2^{n−2}` (defect `≥ 2`) is paid explicitly and the reduced
configuration `c ∘ q.succAbove` satisfies the `≤ 2^n` narrow-window
bound.  The anchor stays saturated after deletion because
`rowScore_eraseIdx'` shows deletion never lowers a row score while
`one_le_rowDefect` caps every score at `n−1`; no removability of `q`
and no uniqueness of saturation in the sub-configuration is required:

```lean
theorem potential_le_high_of_saturated_delete_narrow {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (v q : Fin (s + 1)) (hvq : v ≠ q)
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hq : 2 ≤ rowDefect n lam (directionRow o e c q))
    (hδ : (1 / 2 : ℝ) ≤ Real.pi / lam - n)
    {beta : ℝ} (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin (s + 1), i ≠ v → j ≠ v → i ≠ q → j ≠ q →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ beta) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2)

theorem potential_le_high_of_saturated_one_outlier {s n : ℕ}
    ... (iqr : Fin s)
    (hlow : ∀ i : Fin s, i ≠ iqr →
      theta i < ((n : ℝ) + 1) * lam - Real.pi) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2)
```

Corollary `one_outlier`: in the saturated-corridor chart, if all anchor
rays except possibly one (`iqr`) lie strictly below `α`, the cap
follows — the surviving rays' finite maximum `M < α` supplies the
pairwise bound via `angle_eq_abs_of_half_plane_chart`.  Residual
consequence: **at least two anchor rays must reach `α`** — writing
`0 = θ_1 ≤ … ≤ θ_{s−1} = σ`, the residual now requires
`θ_{s−2} ≥ α`, i.e. `σ ≥ θ_{s−2} ≥ α` (previously only `σ ≥ α`).

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

After all reductions so far, the residual inside R-HIGH1 is:

```text
s ≥ 5 total centers,  unique saturated center v,  δ ≥ 1/2,
anchor-ray spread σ ∈ [α, δλ]   where α = (n+1)λ − π = (1−δ)λ
(σ ≤ δλ is non-strict — no strictness lemma exists),
AT LEAST TWO anchor rays reach α:  σ = θ_{s−1} ≥ θ_{s−2} ≥ α
(else one_outlier closes it — only one ray at height ≥ α suffices),
the defect profile satisfies  Σ_{w≠v} 2^{2−c_w} > 3,
and NO non-anchor row has all chord directions in the bottom prefix
[λ, λ+w₀) with w₀·n < π−λ   (else the clump theorem closes it).
NOTE: narrow rows seated in the MIDDLE of the corridor are still in
the residual — the clump theorem only covers the λ-anchored prefix.
```

(the `Σ 2^{2−c} > 3` condition is exactly `rest > 3·2^{n−2}`; the
bounded corpus's minimal over-capacity profile is `(1,2,2,2,3)`,
K = 11/8.  Whether every realized `(1,2,2,2,3)` skeleton has a
bottom-prefix-clumped row is NOT known — and per Lead review the
four-point equality family cannot serve as a residual witness anyway,
since it has s = 4 and is covered by `potential_le_high_of_saturated_small`.)

Clump threshold arithmetic (corrected): `w₀·n < π−λ` with
`B = (π−λ)/n = λ(1 − (1−δ)/n) < λ`, so the excluded prefix width is
any `w₀ < B` — a width *below* `λ`, not `≈ λ(1+1/n)`.

In this residual the corridor `[λ, π−λ+σ]` has width in
`[(n−1)λ, (n+2δ−2)λ)`, so `n` bins of width `< λ` always exist
(`σ < (2−δ)λ`).  With `m = n` bins the bin graph gives only
`Σ 2^{n−a_v} ≤ 2^n`; the required `3·2^{n−2}` is exactly a
**quarter-cube saving**.  In terms of `H = 2^n − Σ 2^{n−a_v}` (holes)
and `S_v = 2^{n−a_v} − 2^{k_v} ≥ 0` (per-row slack, valid since
`k_v ≤ n − a_v`):

```text
residual target  ⇔  H + Σ_v S_v ≥ 2^{n−2}
```

Known structural constraints on the residual — now FORMALIZED in
`ConeCorridor.lean` (axioms clean): `saturated_chord_endpoint_window`
gives the per-chord disjunction
`dir ∈ [θ_i+λ, π−λ+θ_j] ∨ dir ∈ [θ_j+λ, π−λ+θ_i]`, hence
`saturated_chord_minmax_window` (`dir ∈ [λ+min θ, π−λ+max θ]`) and
`saturated_chord_{top,bot}_sliver`: a chord above `π−λ+t` (resp. below
`λ+t`) needs an endpoint ray above `t` (resp. below `t`).  Writing
anchor rays `0 = θ_1 < … < θ_{s−1} = σ`, the top sliver
`(π−λ+θ_{s−2}, π−λ+σ]` can only contain chords incident to
`Q = θ_{s−1}`, and the bottom sliver `[λ, λ+θ_2)` only chords incident
to `P = θ_1` — moreover each such bin is occupied by a row only through
its single dedicated chord to P / from Q, respectively.  Each non-anchor
row additionally carries its anchor direction `θ_W ∈ [0,σ]` strictly
below the corridor start `λ`.  (Correction to the earlier note: per-row
narrowing `row i ⊆ [λ+θ_i, π−λ+θ_i]` is FALSE — the disjunctive case
flips per chord; only the min/max envelope holds.)

The four-point example in `notes/ONE_SATURATED_HIGH_GEOMETRY.md`
(spread ≈ 29°, α ≈ 4.3°) and the equality family in
`notes/AVERAGED_BIN_PACKING.md` both live in the *wide-window regime*
(`σ ≥ α`) — but have `s = 4` and are therefore closed by
`potential_le_high_of_saturated_small`, NOT part of the residual.
Whether the `s ≥ 5` residual contains tight configurations is open:
the corpus's `(1,2,2,2,3)` skeleton at `s = 5` has K = 11/8 > 5/4
but was never realized geometrically.  No slack-heavy estimate can
be assumed to suffice until a non-clumped residual instance is
certified to exist.

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
