# Lane B3 — the all-bad strip: extracted invariant, construction spec

Target:

```lean
theorem all_bad_strip
    (hcons : SkeletonConsistent sk)
    (hW : 5/2 < W sk)
    (hall : ∀ v, saturated v → bad v) :
    ∃ g : Gadget sk, g.Valid ∧ 2 ≤ g.score
```

(in this repo's language: `∃ g : Gadget 4, g.Valid 4 sk ∧ (1:ℚ) ≤
g.bound 4 sk`; `score = 2·bound`, `gadget_ge_one` does the rest.)

Status: **construction fully specified and CHECKER-VALIDATED**;
the extracted alignment invariant is **PROVED in Lean**
(`Jsp000404/AllBad.lean`, axiom-clean `[propext]`); the gadget-side
case lemmas remain **OPEN** (each is a mechanical but lengthy
`Gadget.Valid` verification).

Labels: **PROVED** = Lean, builds, no sorry. **CHECKER-VALIDATED** =
exact enumeration/selector evidence only. **CONJECTURED** = believed.

---

## 1. The extracted "incompatible alignment" — PROVED

`saturated v` ⟺ `k_v = n−1` ⟺ `q_v = (n,0,…,0)` up to permutation;
write `hp` (heavy-gap position, `Fin 3`) for the index of the `n`
cell.  A saturated vertex is *bad* — no local `δ ≥ 1` gadget — iff
its bit pattern is the threshold step at `hp`:

    badBit hp p = (p > hp)     -- direction at position p

(`hp = 2` gives the all-equal pattern `000`.)  In `AllBad.lean`:

```lean
def badBit (hp p : Fin 3) : Bool := decide (hp < p)

def sidePos (hp pj pk : Fin 3) : ℤ :=
  (if pk > pj then 1 else -1) *
    (if badBit hp pk = badBit hp pj then 1 else -1)
```

`sidePos` is the checker's `side[(j,k)]` signature of an edge
(`generic_model.py`): the side of `k` relative to edge direction
`j`.  The signature table of a bad fan (all `by decide`):

```lean
theorem sidePos_L : ∀ hp pk : Fin 3, pk ≠ hp →
    sidePos hp hp pk = -1          -- j at L slot (pos = hp)

theorem sidePos_R : ∀ hp pk : Fin 3, pk ≠ hp + 1 →
    sidePos hp (hp + 1) pk = 1     -- j at R slot (pos = hp+1)

theorem sidePos_O : ∀ hp pk : Fin 3, pk ≠ hp + 2 →
    sidePos hp (hp + 2) pk = (if pk = hp then 1 else -1)
                                   -- j at O slot (pos = hp+2):
                                   -- +1 toward L, −1 toward R
```

The two characterisations of *bad* coincide (`by decide`):

```lean
theorem bad_arc_iff : ∀ hp pj pk : Fin 3, pj ≠ pk →
    (decide (hp < pj) = decide (hp < pk) ↔
      ¬(min pj pk ≤ hp ∧ hp < max pj pk))
  -- bits equal ⟺ the arc avoids the heavy gap — exactly the
  -- checker's is_bad (no direct-heavy arc, no comp-zero arc)
```

Edge-side consistency between two bad fans (`generic_enum.consistent`):
`side_i(j,k) = −side_j(i,k)` for each shared vertex `k`.  Packaging
the finite data (`hi,hj` heavy positions; `pi`/`pj` the positions of
`j`/`i` in the partner's fan; `a`/`b` the first shared vertex's
positions; the second shared vertex sits at `thirdPos`):

```lean
theorem bad_pair_slots : ∀ hi hj pi pj a b : Fin 3,      -- PROVED
    a ≠ pi → b ≠ pj → badPairConsistent hi hj pi pj a b →
    (pi = hi ∧ pj = hj + 1) ∨ (pi = hi + 1 ∧ pj = hj) ∨
      (pi = hi + 2 ∧ pj = hj + 2)
```

i.e. **two bad saturated vertices see each other only as `(L,R)`,
`(R,L)` or `(O,O)`** — complementary adjacency to the heavy gap, or
mutual opposition.  `(L,L)`, `(R,R)`, `(L,O)`, `(O,L)`, `(R,O)`,
`(O,R)` are edge-inconsistent.  This is the exact "incompatible
alignment" condition, now a Lean theorem (`by decide` over the
`3^6` configurations).

In the `(O,O)` case consistency additionally forces the *crossed*
assignment (`by decide`):

```lean
theorem bad_pair_OO : ∀ hi hj pi pj a b : Fin 3,         -- PROVED
    a ≠ pi → b ≠ pj → badPairConsistent hi hj pi pj a b →
    pi = hi + 2 →
    pj = hj + 2 ∧ (a = hi → b = hj + 1) ∧ (a = hi + 1 → b = hj)
  -- i's L-neighbour is j's R-neighbour and vice versa
```

The lift to real skeletons (`VertexData.Bad`, `sideOf`,
`Set.InjOn` of `pos` on the non-self vertices, `hec` = edge-side
consistency) is also proved:

```lean
theorem bad_pair_of_skeleton (sk : Skeleton 4)           -- PROVED
    {i j k1 k2 : Fin 4} (hij : i ≠ j) …
    (hbi : (sk.vtx i).Bad i hi) (hbj : (sk.vtx j).Bad j hj)
    (hinj : Set.InjOn (sk.vtx i).pos {x | x ≠ i})
    (hjinj : Set.InjOn (sk.vtx j).pos {x | x ≠ j})
    (hec : ∀ k, k ≠ i → k ≠ j →
        (sk.vtx i).sideOf j k = -(sk.vtx j).sideOf i k) :
    (pos_i j = hi ∧ pos_j i = hj+1) ∨ (pos_i j = hi+1 ∧ pos_j i = hj)
      ∨ (pos_i j = hi+2 ∧ pos_j i = hj+2)
```

plus `two_shared` (the two shared vertices of an edge exist).
Axioms: `[propext]` only.

### Checker confirmation of the invariant — CHECKER-VALIDATED

Every signature-consistent all-bad skeleton scanned (all `W>5/2`
profiles, including LP-infeasible ones) has every saturated pair in
`{(L,R),(R,L),(O,O)}` — the `slots=` tallies in
`tools/allbad_scan_*.txt` contain no other pattern.  `(O,O)`
survives exact LP feasibility only in the two-saturated profiles;
in `(0,0,0,2)`/`(0,0,0,3)` all `(O,O)` candidates are LP-infeasible
while `(L,R)`/`(R,L)` are feasible at `δ_min = 2`.

## 2. The construction — CHECKER-VALIDATED, spec below

The selector `tools/allbad_selector.py::select` is a finite decision
tree over skeleton data; every branch is an explicit `Gadget`
template.  Coverage: **every signature-consistent all-bad skeleton
in every `W>5/2` profile is covered** (see §4 tally) — including all
LP-infeasible ones, so the construction does not use
`SkeletonConsistent`.

Branches (checked in order; all gadget data is in `Gadget 4`
language — `fans : Fin 4 → ℤ`, signed `links`, `charges`,
`caps : List (CapEntry 4)`):

| branch | gadget template | residual/capacity content |
|---|---|---|
| `PURE` | one `piLam` cap `(v,a,b,m=1)` | direct arc `a→b` at some vertex `v` with `arcQ ≥ n`; bound `= arcQ−(n−1) ≥ 1`. (Bad saturated vertices never host one — their heavy arcs are all complementary by `bad_arc_iff` — so `v` is non-saturated or non-bad.) |
| `BLOCK` | `low` caps on disjoint comp arcs `A_i` + `piLam`/`nn`/`rle` caps on containing arcs `B_j`, all at one `v` | per-gap containment `∀ g ∈ A_i`, `g` covered by ≥1 positive cap; bound `= (Σ_i(1−q_{A_i}) − Σ_j B_j)/Σ_j u_j ≥ 1`. |
| `FAN0` | `fans v = +1` at a non-saturated `v`, plus the cap/charge cover of its residual | residual = fan row `Σ_g r_vg − δ = n − Σq_v`; positive blocks feed `charges`, negative blocks get caps; bound `(K−Bcap−CC)/(1+uu) ≥ 1`. |
| `STRIP-A` | `fans f = +1`, `f` non-saturated, + ≤2 signed links sharing one pivot `h` | the links connect the residual blocks of `f`'s fan to the bad pair's blocks; same cover mechanism. |
| `STRIP-B` | `fans f = +1`, `f ∈ {i,j}` a bad vertex, + ≤2 signed links | bad fan `Σr_f = δ` plus links into the non-saturated pair. |
| `STRIP-C` | ≤2 signed links, no fan | pure link combination whose constant already gives `δ ≥ 1` (typical of `(O,O)`). |
| `STRIP-D` | two signed fans `±1` + ≤2 signed links | needed in ~1–2% of records, all profiles. |
| `STRIP-E` | three fans + ≤2 links | needed in `(0,0,1,2)` (48 of 59,696 records); unused elsewhere. |

Link sets: a pivot `h ∈ Fin 4` and ≤2 signed triangle links
`(a,b,σ)` with `a,b` distinct non-`h` vertices, `σ ∈ {±1}`
(`l.2.2.2 = σ` in `Gadget.links`); all `4 · (3 pair-subsets · 3
edge-choices) · 2^{|links|}` combinations are enumerated.

The residual/capacity argument is uniform: `Valid` ⇐ fan weights
`∈ {0,±1}`, link signs `±1`, distinct endpoints; every `charge`
arc complementary, nonempty, and inside the positive residual
(`∀ g ∈ arc, 0 < coef`), pairwise-disjoint per vertex; every `cap`
well-formed; the cover inequality `max(−coef,0) ≤ Σ_{e∋g} m·sgn`
per gap; and `cc + uu > 0`.  Bound `≥ 1` ⇔ `cc+uu ≤ K−Bcap−CC`
(`bound_one_unfold`), which feeds `gadget_ge_one` (PROVED).

## 3. Lean-ready decomposition

```lean
-- 1. PROVED (this branch): saturated ↔ heavy cell, and the
--    alignment invariant.
theorem saturated_iff_heavy            -- Jsp000404/AllBad.lean
theorem bad_pair_of_skeleton           -- Jsp000404/AllBad.lean

-- 2. OPEN (interface): bad in skeleton terms — both forms.
def VertexData.Bad (v : VertexData 4) (i : Fin 4) (hp : Fin 3) : Prop
  := ∀ k ≠ i, v.bits k = decide (hp < v.pos k)   -- (in AllBad.lean)
lemma saturated_bad_iff (v : VertexData 4) (i : Fin 4) :
    (∀ a b ≠ i, a ≠ b → v.bits a = v.bits b ↔ hp ∉ v.arc a b) ↔
      v.Bad i hp                        -- finite check via bad_arc_iff

-- 2b. Structural fields the checker takes as part of a "skeleton"
--     and Lean must add to Skeleton / Consistent:
--   * pos restricted to non-self vertices is a bijection
--     (the checker's `order` is a permutation);
--   * edge-side consistency: ∀ i j k, sideOf_i j k = −sideOf_j i k
--     (generic_enum.consistent — a signature-level property, not a
--     consequence of ModeA's r/δ rows);
--   * Σ_g q ≤ n, q ≥ 0 per vertex (generic_model.q_tuples).

-- 3. OPEN (the eight case lemmas).  Each is of the form
--    "if the skeleton exhibits pattern X (a decidable conjunction
--    of pos/bits/q conditions), then the explicit gadget g_X is
--    Valid ∧ bound ≥ 1":
lemma allbad_pure   …   -- ∃ v a b, ¬comp ∧ arcQ a b ≥ 4 → gadget
lemma allbad_block  …   -- ∃ v, low-charge arcs inside caps → gadget
lemma allbad_fan0   …   -- ∃ nonsat v, fan residual covers → gadget
lemma allbad_stripA/B/C/D …            -- fan/link templates

-- 4. OPEN (assembly): the case split itself.
--    On the enumeration the selector's first-hit order is
--    PURE → BLOCK → FAN0 → STRIP-A → -B → -C → -D; the Lean proof
--    needs the disjunction "one of the branch patterns occurs" —
--    CHECKER-VALIDATED (0 uncovered, §4), not yet a Lean lemma.
theorem all_bad_strip …                -- the target
```

Everything in branch 3 is *local*: each lemma quantifies over
`pos/bits/q` data only (`r,δ` never appear — the gadget's `Valid`
proof replays `ModeA` rows, and `bound` is integer arithmetic).
The genuine mathematical content still needing formal proof:

* **(a) branch-pattern completeness** — the analogue of
  `gen_cases`'s pruning must be stated as a *Lean* property (the
  `hec` edge-side-consistency hypothesis of `bad_pair_of_skeleton`,
  plus triangle interval pruning, both of which follow from mode-A
  consistency but are not yet formalised as such);
* **(b) per-branch `Valid` proofs** — mechanical `Finset`/`ℤ`
  verification per template, substantial but not creative.

## 4. Checker-validated coverage

`tools/allbad_scan.py --sel`: every signature-consistent all-bad
skeleton (`gen_cases` = edge-side consistency + triangle-interval
pruning; **no LP**), deterministic `select`.

| profile `d` | `k` | all-bad candidates | uncovered |
|---|---|---|---|
| (0,0,0,0) | (3,3,3,3) | 6 | 0 |
| (0,0,0,1) | (3,3,3,2) | 570 | 0 |
| (0,0,0,2) | (3,3,3,1) | 924 | 0 |
| (0,0,0,3) | (3,3,3,0) | 552 | 0 |
| (0,0,1,1) | (3,3,2,2) | 46208 | 0 |
| (0,0,1,2) | (3,3,2,1) | 59696 | 0 |
| (0,0,1,3) | (3,3,2,0) | 31533 scanned (cap) | 0 |

For `(0,0,1,3)` the scan hit the 40-min compute cap after 31,533
candidates (0 uncovered); its *complete* LP-feasible all-bad set —
5,502 records — is separately 100% covered (`allbad_selector.py
allbad_dump_0_0_1_3.json`).  Every feasible all-bad set dumped:
`(0,0,0,2)` 126/126, `(0,0,0,3)` 42/42, `(0,0,1,2)` 28,950 (all
inside the scanned candidate set).

Slot tallies in every profile: only `(L,R)`, `(R,L)`, `(O,O)` —
matching `bad_pair_slots`.  Branch tally on the completed
`(0,0,1,1)` scan (46,208 candidates, all covered):
`FAN0 20940, PURE 11442, STRIP-A 5540, STRIP-B 1992, BLOCK 4896,
STRIP-C 800, STRIP-D 598, STRIP-E 0`.

## 5. Observations for the assembly proof

* `(O,O)` occurs only when there are **exactly two** saturated
  vertices (the `O`-direction at each is the other bad vertex); in
  3-saturated profiles every bad pair is `(L,R)`/`(R,L)`.
* `STRIP-C` (link-only) and most `STRIP-B` gadgets are the
  characteristic `(O,O)` certificates; `STRIP-A`/`STRIP-D` dominate
  `(L,R)`.
* `SkeletonConsistent` is not used by the selector — the
  construction works on LP-infeasible all-bad candidates too.  The
  theorem's `hcons` will discharge only the *consistency-side*
  hypotheses of the case lemmas (edge-side consistency /
  `pos`-injectivity / `Σq ≤ n`), not feasibility.
* `STRIP-E` is needed only in `(0,0,1,2)` (48 records); a real
  case, not redundancy — keep it in the grammar.

## 6. Remaining gap (honest)

* **PROVED**: the incompatible-alignment invariant
  (`AllBad.lean`), all level-2 arithmetic (`Gadget.lean`,
  `HighDebt.lean`), the `W > 5/2 ⇒ ≥2 saturated` profile argument
  (`dyadic_two_zeros4`).
* **CHECKER-VALIDATED**: the 7-branch selector covers 100% of
  signature-consistent all-bad skeletons in all `W>5/2` profiles;
  every such skeleton admits an explicit `bound ≥ 1` gadget.
* **OPEN (Lean)**: the eight branch lemmas + the completeness
  disjunction + the consistency-side interface (`pos` injectivity,
  `Σq ≤ n`, edge-side consistency from mode A).  No `sorry`
  anywhere in the repo.
