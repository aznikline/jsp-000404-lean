# Lane A2 — LOW-CLOSER: `GadgetSelectionLow` is FALSE as stated

**Headline result.** The wave-1 target

```lean
def GadgetSelectionLow (s n : ℕ) : Prop :=
  ∀ sk : Skeleton s, sk.Consistent n → 2 < sk.W n →
    ∃ g : Gadget s, g.Valid n sk ∧ (1 : ℚ) / 2 ≤ g.bound n sk
```

is **disproved**, in compiling Lean with no `sorry`, at `(s, n) = (3, 2)`
— and the same instance disproves `GadgetSelectionHigh 3 2`
(`W = 3 > 5/2`).  The failure is a *model-looseness* gap in
`VertexData`, not a mathematical counterexample to the intended
statement: `pos : Fin s → Fin (s - 1)` is not required to be injective
on the other vertices (the checker's `order` is always a permutation),
and `q : Fin (s-1) → ℤ` is signed (the checker uses `0 ≤ q ≤ n`).

## The ghost-vertex mechanism

Collapse all of `v`'s positions to `0`.  Every arc `Ico(p,p)` at `v`
is empty, so every angle `∠v{a,b}` is the empty direct arc `0` — the
angle axioms at `v` are vacuously satisfied — while `v`'s `q`-vector
never appears in any angle bound (it is seen only by the fan sum).
Taking `q = (M, -M + c)` keeps `Σq` feasible but makes
`k_v = Σ_g max (q_g - 1) 0` arbitrarily large, inflating
`W = Σ 2^{-(n-1-k_v)}` without bound.  Since `∠v{·,·} = 0`, each
triangle containing `v` pushes its entire `n + δ` onto the other two
vertices — feasible iff `2(n-1+δ) ≥ n+δ`, i.e. `n ≥ 2` (for `s = 3`).

Then the *proved* soundness theorem `gadget_ge_half`
(`Valid` gadget with `bound ≥ 1/2` ⇒ `δ ≥ 1/2` on **every** mode-A
solution) kills all gadgets: a `δ = 0` solution exists, so no valid
gadget can have `bound ≥ 1/2`.  No gadget enumeration is needed — the
soundness direction alone suffices.

## The counterexample (`ghostSk`, verified in Lean)

`s = 3, n = 2, δ = 0`, `r = ((½,½),(1,1),(1,1))`:

| v | pos | bits | q | k | W-contribution |
|---|-----|------|---|---|----------------|
| 0 | (0,0,0) | fff | (3,-2) | 2 | 2 |
| 1 | (0,0,1) | fft | (0,0) | 0 | 1/2 |
| 2 | (0,1,0) | ftf | (0,0) | 0 | 1/2 |

`W = 3 > 2`.  `∠0{·,·} = 0`; `∠1{0,2}=∠1{1,2}=∠1{2,0}=∠1{2,1} = 1`
and `∠2{0,1}=∠2{1,0}=∠2{1,2}=∠2{2,1} = 1` (complementary `{0}`-arcs);
`∠1{0,1} = ∠2{0,2} = 0`.  Triangle: `0+1+1 = 2 = n+δ`.  All ModeA
fields verified by `fin_cases` + computation.

## PROVED in Lean (`Jsp000404/GadgetCounterexample.lean`)

* `ghostSk_modeA`, `ghostSk_consistent`, `ghostSk_W : 2 < W 2` —
  the witness.
* `not_gadgetSelectionLow_3_2 : ¬ GadgetSelectionLow 3 2`.
* `not_gadgetSelectionHigh_3_2 : ¬ GadgetSelectionHigh 3 2`.
* `not_gadgetSelectionLow_all / not_gadgetSelectionHigh_all :
   ¬ ∀ s n, …` — the universal statement is false.
* Boundary (the counterexample is minimal on both axes):
  * `not_consistent_zero : 2 ≤ s → ¬ sk.Consistent 0` —
    `0 ≤ ∠ ≤ δ - 1` impossible.  ⇒ `GadgetSelectionLow/High s 0`
    vacuously true for `s ≥ 2`.
  * `gadgetSelectionLow_s0`, `W_le_two_s1`, `gadgetSelectionLow_s1`,
    `W_le_two_s2`, `gadgetSelectionLow_s2` (and High analogues) —
    `s ≤ 2` is vacuous (`s = 2` uses `q ≤ n` per vertex from the fan).
  * The same vacuous instances for the repaired `…P` propositions.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` plus
  `native_decide` trust axioms (same profile as `GadgetFixtures.lean`).
  **No `sorryAx` anywhere.**

## The repair (stated, still OPEN)

```lean
def Skeleton.Proper (sk : Skeleton s) : Prop :=
  ∀ v a b, a ≠ v → b ≠ v → (sk.vtx v).pos a = (sk.vtx v).pos b → a = b

def GadgetSelectionLowP s n :=
  ∀ sk, sk.Proper → sk.Consistent n → 2 < sk.W n → ∃ g, …
```

`Proper` is exactly the checker's `order = permutation` condition and
kills the ghost (`ghostSk_not_proper` proved).  Under `Proper`, every
non-wrap gap lies in a singleton arc, so its `q` is pinned to
`[-1, n]`; only the wrap gap (in no arc) is unconstrained, and it
contributes `0` to `k`.  Signed `q` then cannot inflate `W` — the
loophole closes.  All checker evidence (which only ever sees proper
skeletons) supports `GadgetSelectionLowP`.

`selection_low_soundP / selection_high_soundP` are proved — the
reduction `GadgetSelectionLowP ⇒ δ ≥ 1/2` is unchanged.

## Status of the remaining nodes (PROVED / OPEN)

| Node | Status |
|---|---|
| `GadgetSelectionLow s n` (original) | **FALSE** at (3,2); true (vacuous) for `s ≤ 2`, all `n`, and for `n = 0`, all `s` |
| `GadgetSelectionHigh s n` (original) | **FALSE** at (3,2); same vacuous boundary |
| `GadgetSelectionLowP s n` (proper) | **OPEN** — the surviving crux |
| `GadgetSelectionHighP s n` | **OPEN** |
| `GadgetSelectionLow 3 1` | **OPEN** — ghosts are inconsistent at `n = 1` (`2δ < 1+δ`), so the statement may hold; needs gadget existence on proper s=3 skeletons, unproved |
| `GadgetSelectionLowP 3 n`, `n ≥ 2` | **OPEN** — not vacuous: e.g. vertices `q=(n,0)`-comp + `q=(0,n)`-direct give `k=(n-1,·)`, `W>2`, but consistency forces `δ ≥ 1/2` exactly — a gadget should exist but is unproved |

## Notes for downstream

1. `notes/LANE_A.md`'s decomposition remains correct *for the
   repaired statement*.  The Kraft/aggregation route now needs
   `Proper` as an explicit hypothesis — under it, the `q`-vectors are
   effectively bounded (`[-1,n]` on arc gaps; wrap gap harmless),
   which may also simplify the combinatorial case analysis.
2. `Skeleton.Consistent` need not change; the ghost is consistent
   (it *is* mode-A feasible) — the defect is that `Skeleton` admits
   degenerate fans at all, i.e. `Proper` belongs in the selection
   proposition (or in a `Skeleton.WF` predicate reused everywhere).
3. Wave-3 suggestion: restate `GadgetSelectionLow/High` with the
   `Proper` hypothesis (one-line change to the `Prop`s in
   `GadgetSelection.lean`) — all soundness proofs carry over verbatim
   (`selection_low_soundP` is already written).
4. `GadgetSelectionLow 3 1` is the cheapest possibly-true open
   instance of the *unrepaired* statement.
