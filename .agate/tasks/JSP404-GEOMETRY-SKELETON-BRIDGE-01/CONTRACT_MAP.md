# G0 — Geometry→Skeleton contract map

Task: JSP404-GEOMETRY-SKELETON-BRIDGE-01.  Base: lane/integration @
`9945ee8bd25ed3520aa89a063493cf3398e6f884`.

## Source (geometry) — exact signatures

| object | type / statement | file:line |
|---|---|---|
| `Section4Legality c lam` | `lam_pos : 0 < lam`; `inj : Injective c`; `triAngle : ∀ i j k, i≠j → j≠k → i≠k → ∠(c i)(c j)(c k) ≤ π−λ` | Section4Legality.lean:44 |
| `dirRep o e c i j` | `linRep (o.oangle e (c j − c i)) : ℝ`, value in `[0,π)` | GeometricDeletion.lean:41 |
| `directionRow o e c i` | `((finRange s).erase i).map (dirRep …) |> insertionSort (·≤·)`; sorted, length `s−1`, entries in `[0,π)`, *with multiplicities* | GeometricDeletion.lean:46 |
| `gapAfter ds i` | `ds[i+1] − ds[i]` if `i+1 < len`, else `ds[0] + π − ds[i]` (wrap gap) | CircleBound.lean:254 |
| `cycGaps l` | consecutive `cyclicDiff`s + `wrapGap`; `cycGaps_eq_ofFn_gapAfter` (sorted) | Deletion.lean:77, Induction.lean:122 |
| `gapAfter_sum` | `l ≠ [] → Σ_{Fin l.length} gapAfter l = π` | CircleBound.lean:549 |
| `rowScore lam l` | `Σ (⌊g/λ⌋₊ − 1)` over `cycGaps`; `= Σ_{Fin l.length} (⌊gapAfter/λ⌋₊−1)` via `exponents_entry_eq_rowScore` | Deletion.lean:82, Induction.lean:197 |
| `rowCells/rowBig/rowDefect` | `rowDefect n lam l = rowBig + (n − rowCells)`; `rowScore = n − rowDefect` when `rowCells ≤ n` | Deletion.lean:1593–1707 |
| `exponentAt/potential` | `potential lam row = Σ_i 2^{rowScore (row i)}`; `= 2^n·Σ(1/2)^{c_i}` (Kraft) | Deletion.lean:836,842,1711 |
| `dirRep_comm` | `dirRep i j = dirRep j i` (needs `e≠0`, `c i ≠ c j`) | GeometricDeletion.lean:260 |
| `linRep_oangle_eq_angle_or_pi_sub` | sweep `linRep(oangle(a−i)(b−i)) = ∠a i b ∨ π − ∠` | Base3Bridge.lean:33 |
| `o.angle_eq_abs_oangle_toReal` | `angle u v = |(o.oangle u v).toReal|` (`u,v≠0`) | Mathlib |
| `o.oangle_sub_left` | `o.oangle u v = o.oangle e v − o.oangle e u` (`e,u,v≠0`) | Mathlib |
| `linRep_class` | `↑(linRep d) = d ∨ ↑(linRep d) = d + π` | CircleBound.lean:41 |
| `cycGaps_sum_eq_pi`, `cycGaps_nonneg` | sorted `[0,π)`-lists: gaps sum to π, each `≥0` | Induction.lean:225,231 |
| `exponents_map_pow_sum` | `(exponents V o e lam).map (2^·) | .sum = potential lam (directionRows o e centers)` | Induction.lean:574 |
| `rowCells_directionRow_le_of_floor_eq` | `rowCells lam (directionRow i) ≤ n` when `⌊π/λ⌋₊ = n`, `2≤s` | Induction.lean:276 |

## Target (skeleton) — exact signatures

| field | type | file:line |
|---|---|---|
| `VertexData s` | `pos : Fin s → Fin (s−1)`; `bits : Fin s → Bool`; `q : Fin (s−1) → ℤ` | Gadget.lean:63 |
| `Skeleton s` | `vtx : Fin s → VertexData s` | Gadget.lean:69 |
| `arc a b` | `Finset.Ico (pos a ⊓ pos b) (pos a ⊔ pos b)` on `Fin (s−1)` — symmetric, **never contains wrap gap `s−2`** | Gadget.lean:77 |
| `comp a b` | `bits a ≠ bits b` | Gadget.lean:85 |
| `angleExpr n sk r δ x a b` | `bits a = bits b → Σ_arc (q+r)`; else `n + δ − Σ_arc(q+r)` | Gadget.lean:90 |
| `ModeA n sk r δ` | `r_nn`, `r_le : r ≤ 1`; `fan : Σr − δ = n − Σq`; `tri : ∀ a b h pairwise ≠ → ∠a{b,h}+∠b{a,h}+∠h{a,b} = n+δ`; `ang_le/ang_nn : ∀ x a b, a≠b → 0 ≤ expr ≤ n−1+δ` | Gadget.lean:98 |
| `Skeleton.Proper` | `pos` injective on `{a : a ≠ v}` | GadgetCounterexample.lean:185 |
| `Skeleton.Consistent n` | `∃ r δ, 0 ≤ δ < 1 ∧ ModeA n sk r δ` | GadgetSelection.lean:59 |
| `kexp` | `Σ_g max (q_g − 1) 0 : ℤ` | GadgetSelection.lean:43 |
| `Skeleton.d n v` | `(n−1) − kexp v : ℤ` | GadgetSelection.lean:49 |
| `Skeleton.W n` | `Σ_v (2:ℚ)^{−d_v} : ℚ` | GadgetSelection.lean:53 |
| `GadgetSelectionLowP/HighP` | proper+consistent+`W>2`(`5/2`) → valid gadget bound `≥1/2`(`1`). **OPEN — not ours.** | GadgetCounterexample.lean:341,346 |
| `GadgetSelection` (bundle) | `low: δ<1/2 → Σ2^{kᵢ} ≤ 2^n`; `high: δ<1 → Σ2^{kᵢ} ≤ 2^n+2^{n−2}` on `exponents` | Integration.lean:70 |

## Field-by-field mapping (construction plan)

Notation: `l_x := directionRow o e c x`, `d_j := dirRep o e c x j`,
`Θ_j := o.oangle e (c j − c x) : Real.Angle` (so `d_j = linRep Θ_j`,
`Θ_b − Θ_a = o.oangle (c a − c x) (c b − c x)`, and
`∠(c a)(c x)(c b) = |(Θ_b − Θ_a).toReal|`).

| # | target field | quantifier domain | geometric source | construction | proof status |
|---|---|---|---|---|---|
| 1 | `pos x : Fin s → Fin (s−1)` non-self | `a ≠ x` | sorted order of `dirRep x ·` | `pos x a = ⟨(J_x).idxOf a, _⟩` where `J_x = ((finRange s).erase x).insertionSort (dirLe x)`, `dirLe` = lex `(dirRep, index)` — **index tie-break keeps injectivity under duplicate directions** | needs `J_x.Nodup` (erase+perm), `idxOf_lt_length` |
| 2 | `pos` injectivity (Proper) | `a b ≠ x` | — | `idxOf_inj` on members of nodup `J_x` | provable (Mathlib `List.idxOf_inj`) |
| 3 | `bits x a`, `a ≠ x` | non-self | lift/fold of `Θ_a` vs `d_a` | `rawBit x a := decide (↑(d_a) = Θ_a + π)`; `bits x a := rawBit x (selfA x a)` where `selfA x a = if a = x then other x else a` | new: `Θ_a = ↑d_a − rawBit·π` from `linRep_class` |
| 4 | `q x g` | `g : Fin (s−1)` | canonical cell `⌊G_{x,g}/λ⌋₊` | `q x g = ↑⌊gapAfter l_x ⟨g,_⟩ / lam⌋₊` | direct; `q ≥ 0`, `Σq ≤ n` via `rowCells_le_floor_pi` |
| 5 | `r x g` | same | remainder `G/λ − ⌊G/λ⌋₊` | `r x g = gapAfter … / lam − q x g` | `0 ≤ r < 1` (STRICT) via `Nat.floor_le`, `Nat.lt_floor_add_one`; `q+r = G/λ` |
| 6 | `fan v` | `v` | `Σ gaps = π` | `Σ(q+r) = π/λ = n + δ` via `gapAfter_sum` + length transport | provable |
| 7 | `tri a b h` | pairwise distinct | triangle angle sum `= π` | `angleExpr x a b = ∠(c a)(c x)(c b)/λ` (non-self endpoints) + `angle_add_angle_add_angle_eq_pi` | needs the bits↔angle lemma (#9) |
| 8 | `ang_le`/`ang_nn`, non-self | `a b ≠ x`, `a≠b` | `triAngle` + `angle_nonneg` | `∠/λ ≤ (π−λ)/λ = n−1+δ`; `∠/λ ≥ 0` | same lemma |
| 9 | **bits↔angle** | `a b ≠ x` | `∠ = \|(Θ_b−Θ_a).toReal\|` | `Θ_b − Θ_a = ↑(d_b − d_a) − (bit_b − bit_a)·π`; case split on bit pair ⇒ `∠ = \|d_b−d_a\|` (equal) or `π−\|d_b−d_a\|` (differ). Arc sum `Σ_Ico gapAfter = \|d_b−d_a\|` by telescoping (`sum_Ico_eq_sum_range`+`sum_range_sub`, pattern at Induction.lean:336) | new lemma ~toReal/toIocMod case work |
| 10 | **self slots** `x=a` or `x=b` in `ang_le/ang_nn` | `x=a`, `b` arbitrary `≠x` | `pos x x := pos x a₀`, `bits x x := bits x a₀` (`a₀ = x.succAbove 0`, needs `2≤s`) | `angleExpr x x b = angleExpr x a₀ b` **definitionally** (arc/comp see only pos/bits values); `b = a₀` ⇒ expr `= 0`; else real angle bound. Needs `1 ≤ n` for `0 ≤ n−1+δ`. Symmetric for `x=b` (`arc`/`comp` symmetric). | construction choice — see audit below |
| 11 | `kexp v` | `v` | `rowScore lam l_v` | `max(↑⌊G/λ⌋₊−1,0) = ↑(⌊G/λ⌋₊−1)`; `Σ` over `Fin(s−1)` = `Fin l.length` sum = `rowScore` via `exponents_entry_eq_rowScore` | provable |
| 12 | `Skeleton.d` | `v` | `rowDefect c` | `d_v = (n−1) − kexp = (n−1) − (n − c_v) = c_v − 1` (ℤ; needs `rowCells ≤ n` for `rowScore_eq_sub_defect`) | provable |
| 13 | `Skeleton.W n` | — | `potential` | `W = Σ_v 2^{kexp−(n−1)} = 2^{−(n−1)}·Σ 2^{rowScore} = potential/2^{n−1}` (ℚ zpow; no sign hypothesis needed) | provable |
| 14 | `Consistent n` | — | `δ = π/λ − n` | `0≤δ` from `Nat.floor_le`; `δ<1` from `Nat.lt_floor_add_one` | provable |
| 15 | binding `n, δ, lam, regime` | — | `⌊π/λ⌋₊ = n` same λ everywhere; `δ = π/λ − n` | all fields share `(lam, n)`; no weakening | definitional |
| 16 | consumer packaging | `∀ V o e` | `GadgetSelection.low/high` | `GadgetSelectionLowP`/`HighP` at `(s,n)` + bridge ⇒ `potential ≤ cap` ⇒ `Σ2^{kᵢ} ≤ 2^n (+2^{n−2})` via `exponents_map_pow_sum` | provable conditional |

## Self-slot audit (task-mandated)

`ModeA.ang_le x a b` / `ang_nn x a b` quantify over `a ≠ b` **with `x`
free** — so `x = a` and `x = b` are live cases.  `angleExpr x x b`
uses `pos x x` and `bits x x` which have no geometric meaning.

* **Construction**: `selfA x a = if a = x then other x else a` with
  `other x := x.succAbove ⟨0, hs : 0 < s−1⟩` (needs `2 ≤ s`).  Both
  `pos` and `bits` are functions of `selfA` alone, so
  `angleExpr n sk r δ x x b = angleExpr n sk r δ x (other x) b` and
  `angleExpr n sk r δ x a x = angleExpr n sk r δ x a (other x)`
  are definitional equalities (`arc` symmetric, `comp` symmetric).
* **Obligations discharged**:
  - `b = other x`: `arc (other x) (other x) = Ico(p,p) = ∅`, bits equal
    ⇒ `expr = 0`; bounds `0 ≤ 0 ≤ n−1+δ` need `1 ≤ n` (domain gives
    `n ≥ 3`, and `n ≥ 1` follows from `lam ≤ π` in any case).
  - `b ∉ {x, other x}`: reduces to the genuine angle
    `∠(c a₀)(c x)(c b)/λ ∈ [0, (π−λ)/λ]` by `triAngle`.
* **Not weakened**: no constraint on `pos`/`bits` self values was
  removed; `Proper` only quantifies `a,b ≠ v`, unchanged.
* The checker's `bits` is `fold_j XOR fold_{b0}` (a global flip of ours
  per vertex, see `tools/e_geom.py:48-52`); `comp` is flip-invariant,
  so the semantics coincide on every predicate the model consumes.

## Domain

Primary: `4 ≤ s`, `3 ≤ n`, `0 < lam`, `⌊π/λ⌋₊ = n`, `e ≠ 0`,
`Section4Legality c lam`.  The construction itself only needs
`2 ≤ s`, `1 ≤ n`; we keep it at `2 ≤ s` / `1 ≤ n` when free, and note
`s ∈ {0,1}` is vacuous downstream (`Skeleton 1` uninhabited since
`pos : Fin 1 → Fin 0`; `Skeleton 0` trivial).

## Explicitly NOT claimed

* `GadgetSelectionLowP/HighP` remain open (main-owner/proof-convergence
  scope).  The bridge is stated as the *conditional* reduction
  `(∀ s n, …P s n) → GadgetSelection`.
* No `GadgetSelection`/`CertExists`/`KraftPacking` hypothesis is used
  to build the bridge.
* No positivity/strictness is assumed beyond `Section4Legality`:
  collinear triples (`∠ = 0`, duplicate `dirRep`) are handled by the
  index tie-break, not excluded.
