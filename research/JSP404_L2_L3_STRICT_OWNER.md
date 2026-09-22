# JSP404-L2L3-STRICT-01 — Lane A Owner Report

Base: `b3342399d49e50a7778b1834eb0ee88877025baf` (strict-remainder
challenger head).  Branch: `agent/jsp404-l2-l3-strict-01-owner`.

All Lean work lives in **`Jsp000404/SaturatedStructure.lean`** (new,
registered in `Jsp000404.lean`).  Kernel-checked, `autoImplicit=false`,
no `sorry`/`admit`/custom axioms/`native_decide` anywhere in the file.

---

## 1. What was delivered

The minimal chain requested, plus the second-layer strengthening and
the `gapScore` bridge — all at **arbitrary fan size / arbitrary `s`**:

```text
saturated_cells_unique            (B1, pure arithmetic)
        ↓
saturated_angle_le                (L2-min)
saturated_bits_iff                (full L2, crossing iff)
saturated_bits_all_eq_last        (full L2, wrap corollary)
        ↓
FanSystem.two_saturated_ge_half   (L3)
FanSystem.two_saturated_lt_half_impossible  (L3 contrapositive)

saturated_cells_unique_of_gaps    (bridge to gapScore/exponents)
```

Supporting local cap lemmas (`arc_ge_one_of_bit_ne`,
`arc_le_of_bit_eq`, `bit_eq_of_arc_lt_one`) formalize the exact
2-constraint strict MUS the challenger found on every `(0,0,1,*)`
skeleton: a small arc (`arc < 1`) under different bits would exceed
the cap `∠ ≤ T−1`.

---

## 2. Semantics contract (strict, no closed-box leftovers)

- `T = n + δ`, `0 ≤ δ < 1` encoded as `(n:ℝ) ≤ T` and `T < n+1`.
- `gap j = q j + r j`, `q j : ℕ`, `0 ≤ r j`.  (`r < 1` is carried in
  `FanSystem.hr1` where needed; B1/B2 only need `r ≥ 0`, which is the
  honest weaker hypothesis — strictness enters through `T < n+1`.)
- Exponent `k = ∑ j, (q j - 1)` — **natural subtraction**, identical
  to `gapScore lam x = ⌊x/lam⌋₊ - 1` (`Deletion.lean:31`) and the
  summand of `exponents` (`Staircase.lean:40-44`, summing
  `Nat.floor (gapAfter ... / lam) - 1` over `circleDirs`).
- Saturated `:= k = n - 1` (deficit `d = 0`).

---

## 3. Theorem inventory (exact statements)

### B1 — `Jsp404.saturated_cells_unique`

```lean
theorem saturated_cells_unique {q : Fin m → ℕ} {r : Fin m → ℝ}
    {n : ℕ} {T : ℝ} (hn : 2 ≤ n) (_hnT : (n : ℝ) ≤ T) (hT : T < n + 1)
    (hr : ∀ j, 0 ≤ r j)
    (hfan : ∑ j : Fin m, ((q j : ℝ) + r j) = T)
    (hsat : ∑ j : Fin m, (q j - 1) = n - 1) :
    ∃ b : Fin m, q b = n ∧ (∀ j, j ≠ b → q j = 0)
      ∧ (∀ b', 0 < q b' → b' = b)
      ∧ ∑ j : Fin m, r j = T - n
```

Mechanism (exposed, not buried in `omega`): positive cells
`P = {j : q j > 0}`; `∑(q−1) = ∑q − |P| = n−1`; `∑q ≤ T < n+1` gives
`∑q ≤ n`; hence `|P| = 1`, `∑q = n`, and `∑r = T−n`.  The `n ≤ T`
hypothesis is part of the `δ ≥ 0` contract but the proof does not use
it (marked `_hnT`); saturation + `T < n+1` + `r ≥ 0` suffice.

### L2-min — `Jsp404.ProjFan.saturated_angle_le`

```lean
theorem ProjFan.saturated_angle_le {n : ℕ}
    (hn : 2 ≤ n) (hnT : (n : ℝ) ≤ T) (hT : T < n + 1)
    (hr : ∀ j, 0 ≤ f.r j)
    (hfan : ∑ j : Fin m, f.gap j = T)
    (hsat : ∑ j : Fin m, (f.q j - 1) = n - 1)
    (hcap : ∀ i j : Fin m, i ≠ j → f.angle T i j ≤ T - 1)
    {i j : Fin m} (hij : i ≠ j) :
    f.angle T i j ≤ T - n    -- T - n = δ
```

`ProjFan` is the local model of `vertex_variants`: `arc i j` is the
non-wrapping linear sum `∑ t ∈ Ico (min i j) (max i j), gap t` and
`angle = arc` when `bit i = bit j`, else `T - arc` — exactly the
checker's convention after `order`/`pos` is absorbed into `Fin m`.

Mechanism: if the linear arc contains the big cell `b`, `arc ≥ n`,
so equal bits would put `angle > T−1` — cap forces different bits and
`angle = T − arc ≤ T − n`.  If the arc avoids `b`, every cell in it
vanishes, `arc ≤ ∑ r = δ`; different bits would give `angle ≥ n > T−1`
— cap forces equal bits and `angle = arc ≤ δ`.

### Full L2 — `Jsp404.ProjFan.saturated_bits_iff` + wrap corollary

```lean
theorem ProjFan.saturated_bits_iff ... :
    (f.bit i ≠ f.bit j) ↔
      ∃ t ∈ Finset.Ico (min i j) (max i j), 0 < f.q t
```

— the exact strict-checker predicate (crossing ⟺ arc contains a
positive cell ⟺ contains `b`).  `saturated_bits_all_eq_last` handles
the wrap case: if the only positive cell is the last position, no
linear arc contains it, hence all bits are equal.

### L3 — `Jsp404.FanSystem.two_saturated_ge_half`

```lean
theorem FanSystem.two_saturated_ge_half (hn : 2 ≤ n) {u v w : Fin (s + 3)}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : F.Saturated u) (hv : F.Saturated v) :
    (1 : ℝ) / 2 ≤ δ
```

`FanSystem s n δ` packages `s+3` vertices (`s ≥ 3` automatic), each
with a `ProjFan` over the `s+2` other directions, `dir` (the checker's
`order`), `fan_sum`, `cap` (`∠ ≤ n+δ−1`, the `triAngle` contract),
and `tri` (triangle sums `= n+δ`).  `posOf` is the order-inverse.

Proof is exactly the advertised chain: L2-min at `u,v` gives
`∠u{v,w}, ∠v{u,w} ≤ δ`; `tri` gives `∠w{u,v} ≥ n−δ`; `cap` gives
`∠w{u,v} ≤ n+δ−1`; `linarith` closes `n−δ ≤ n+δ−1`.

Corollary `two_saturated_lt_half_impossible`: the same hypotheses
with `δ < 1/2` yield `False` — the strict disappearance of
`(0,0,·,·)` profiles.

### Bridge — `Jsp404.saturated_cells_unique_of_gaps`

```lean
theorem saturated_cells_unique_of_gaps {g : Fin m → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hg : ∀ j, 0 < g j) {n : ℕ}
    (hn : 2 ≤ n) (hnf : Nat.floor (Real.pi / lam) = n)
    (hsum : ∑ j : Fin m, g j = Real.pi)
    (hsat : ∑ j : Fin m, (Nat.floor (g j / lam) - 1) = n - 1) :
    ∃ b : Fin m, Nat.floor (g b / lam) = n
      ∧ (∀ j, j ≠ b → Nat.floor (g j / lam) = 0)
      ∧ (∀ b', 0 < Nat.floor (g b' / lam) → b' = b)
```

The fractional decomposition `g j / λ = ⌊g j/λ⌋₊ + (g j/λ − ⌊·⌋₊)`
instantiates B1 directly: `T = π/λ`, `δ = π/λ − n ∈ [0,1)` from
`⌊π/λ⌋₊ = n`.  A saturated row of `exponents` therefore has exactly
one cell `⌊g_b/λ⌋₊ = n` — this is the `d = 0 ⇒ q = (n,0,…,0)` lemma
at the repository's own exponent, not a parallel notion.

What remains for full integration: `Staircase.exponents` sums
`gapScore` over the actual `circleDirs`/`gapAfter` cyclic gaps; the
bridge currently takes `g : Fin m → ℝ` abstractly (any positive gaps
summing to `π`).  Wiring it into `circleDirs` requires the geometric
step that `gapAfter` gaps are positive and sum to `π` — deferred to
the integration lane, no unproved assumption introduced here.

---

## 4. Axiom check

`#print axioms` (file end):

```text
saturated_cells_unique            : [propext, Classical.choice, Quot.sound]
ProjFan.saturated_angle_le        : [propext, Classical.choice, Quot.sound]
ProjFan.saturated_bits_iff        : [propext, Classical.choice, Quot.sound]
ProjFan.saturated_bits_all_eq_last: [propext, Classical.choice, Quot.sound]
FanSystem.two_saturated_ge_half   : [propext, Classical.choice, Quot.sound]
FanSystem.two_saturated_lt_half_impossible
                                  : [propext, Classical.choice, Quot.sound]
saturated_cells_unique_of_gaps    : [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no custom axioms.

---

## 5. Tests

```text
lake build                                    → success (2528 jobs)
lake build Jsp000404.SaturatedStructure       → success
```

Sanity examples in-file (`section Sanity`):

- saturated fan `q=[0,0,4]`, `r=1/6`, `T=9/2` (`δ=1/2`, boundary
  admissible) → B1 returns `b=2` (wrap position);
- `q=[0,4,0]` → `b=1` (non-wrap);
- `two_saturated_lt_half_impossible` covers `δ<1/2` + two saturated
  ⟹ impossible; `two_saturated_ge_half` itself asserts `δ ≥ 1/2` with
  equality permitted (boundary stays allowed by the strict bound
  `1/2 ≤ δ`, consistent with checker strict-1/2 skeletons).

---

## 6. Status against the task

```text
L2_MIN_STATUS=PROVED     (saturated_angle_le)
L2_FULL_STATUS=PROVED    (saturated_bits_iff + saturated_bits_all_eq_last)
L3_STATUS=PROVED         (two_saturated_ge_half + contrapositive)
HIGH_STRICT_STATUS=NOT_ATTEMPTED  (see §7)
BRIDGE_TO_MAIN_PROOF=PROVED at the exponent level
                     (saturated_cells_unique_of_gaps); circleDirs
                     wiring deferred, no unproved assumptions
```

## 7. High-strict: honest blocker note

`deficit_one_impossible_of_two_saturated` (two saturated ⇒ all
remaining deficits ≥ 2) was **not** claimed, deliberately.  The
strict-MUS analysis on `(0,0,1,*)` skeletons showed each
infeasibility certificate is a **local 2-constraint violation** (one
`r ≤ M` bound + one angle cap), i.e. a side-consistency
(bit/arc/order) obstruction — not a fan-internal arithmetic fact.
The local half *is* proved here: `arc_ge_one_of_bit_ne` /
`bit_eq_of_arc_lt_one` is precisely that 2-constraint MUS in Lean.
A profile-level theorem needs the side-consistency layer (the
oriented-matroid conditions linking `dir`, `bit`, `q` across
vertices) which `FanSystem` deliberately does not assert; adding
those hypotheses just to force the theorem through would violate the
"no silent strengthening" rule.  Recommended owner: the high-regime
lane, building the signature-consistency predicate first, then
lifting `bit_eq_of_arc_lt_one` vertex-locally.

## 8. Remainders / non-issues

- `hnT` (`n ≤ T`, i.e. `δ ≥ 0`) is carried in B1's interface but
  unused by the proof (`_hnT`) — kept for contract honesty.
- `ProjFan` assumes nothing about geometry: positions are `Fin m`,
  arcs are linear (never wrap), the checker's `order`/`pos`
  relabeling is absorbed by reindexing.  `posOf`/`dir` supply the
  cross-vertex identification for L3 only.
- Escalation criteria from the task spec did not trigger: B1 needs
  nothing beyond `r ≥ 0` + fan sum + `T < n+1`; L2-min needs nothing
  beyond the `angle ≤ T−1` cap; L3 needs no convexity, no `s=4`, no
  lower angle bounds.
