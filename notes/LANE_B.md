# Lane B — HIGH selection theorem: status map and proof spec

Target (contrapositive form):

    no score≥2 gadget  ⇒  W ≤ 5/2

equivalently, over mode-A-consistent skeletons of the `s = n` model,

    theorem gadgetSelection_high
        (hconsistent : SkeletonConsistent sk)
        (hW : 5/2 < W sk) :
        ∃ g : Gadget sk, g.Valid ∧ 2 ≤ g.score

Status: **NOT PROVED** (the combinatorial selection step is open).
The arithmetic backend for level 2 *is* proved on this branch, and
the checker-side evidence is now substantially sharper than the
handoff: the gadget grammar needed for level 2 has been fully
isolated, and it is richer than `tools/link_graph.py` shipped.

Labels: **PROVED** = Lean theorem, `lake build` green, no sorry.
**CHECKER-VALIDATED** = exact-rational LP/enumeration evidence only.
**CONJECTURED** = believed, no proof. **FALSIFIED** = refuted.

---

## 1. What is proved (Lean, this branch)

`Jsp000404/HighDebt.lean` (new), all axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

```lean
theorem debt_residual_ge_one                       -- PROVED
    {P U C K c u B δ : ℝ}
    (hres : P - U - c * δ = C) (hP : K ≤ P)
    (hU : U ≤ B + u * δ) (hc : 0 < c + u)
    (hcap : c + u ≤ K - B - C) : (1 : ℝ) ≤ δ

theorem charge_cap_ge                              -- PROVED
    {A X B u δ K t : ℝ}
    (hK : K ≤ A) (hX : 0 ≤ X)
    (hcap : A + X ≤ B + u * δ) (hu : 0 < u)
    (ht : t * u ≤ K - B) : t ≤ δ

theorem pure_cap_ge                                -- PROVED
    {X B δ t : ℝ} (hX : 0 ≤ X)
    (hcap : X ≤ B + δ) (ht : t ≤ -B) : t ≤ δ

def ResidualWitness.High (w) :=                    -- PROVED def
  w.Valid ∧ w.c + w.u ≤ w.K - w.B - w.C

theorem ResidualWitness.ge_one (w) (h : w.High) :  -- PROVED
    (1 : ℝ) ≤ w.δ

theorem dyadic_two_zeros {s : ℕ} (d : Fin s → ℕ)   -- PROVED
    (h : 1 + ((s : ℝ) - 1) / 2 <
      ∑ i : Fin s, (2 : ℝ) ^ (-(d i : ℤ))) :
    ∃ i j : Fin s, i ≠ j ∧ d i = 0 ∧ d j = 0

theorem dyadic_two_zeros4 (d : Fin 4 → ℕ)          -- PROVED
    (h : (5 : ℝ) / 2 < ∑ i : Fin 4,
      (2 : ℝ) ^ (-(d i : ℤ))) :
    ∃ i j : Fin 4, i ≠ j ∧ d i = 0 ∧ d j = 0
```

`dyadic_two_zeros` is the profile-level half of the selection
argument, proved for **general `s`** (at `s = 4` the threshold
`1 + (s-1)/2` is exactly `5/2`): if fewer than two profile entries
are `0`, then `W ≤ 1 + (s-1)/2`, contradicting `W > 5/2`.  What
remains open is only the *lifting* of "two `d = 0` entries" to
"two saturated vertices of the skeleton" (needs the `Skeleton`
interface) plus the all-bad strip construction.

Also repaired a pre-existing toolchain-drift build failure in
`Jsp000404/DebtChain.lean:143` (`le_of_mul_le_mul_left` argument
order; one-line fix, statement unchanged).

### The key structural remark behind `charge_cap_ge`

The residual framework `P − U − c·δ = C` is only produced by fan /
triangle **equalities**, but `debt_residual_ge` does not require
`c > 0` or a nontrivial equality content: taking `P = U` (the *zero
form*) reduces the certificate to the pure inequality combination
`K ≤ A`, `A + X ≤ B + u·δ`, `0 ≤ X`.  This is exactly the family of
gadgets `link_graph.py`'s evaluator cannot express, and they are
*needed* — see §3.

So the gadget object (`Gadget` on lane/c) needs one more kind: a
**block gadget** whose residual form is identically zero and whose
bound is `(K − Bcap)/u` from a charge-arc-inside-cap-arc nesting.
In lane/c's `Valid` fields this is `form ≡ 0`, `dco = 0`, `con = 0`,
with the positive block taken to be the cap's range.

## 2. The level-2 gadget grammar (CHECKER-VALIDATED)

Exhaustive exact-rational check over **all** feasible skeletons of
**all** `W > 5/2` profiles at `s = n = 4`
(`tools/cover3.py`, `tools/eval_ext.py`, `tools/link_graph.py`,
`tools/generic_enum.py`; LP via `tools/generic_model.py` +
`residual_map.glp_min_delta`).

`W > 5/2` profiles (`d`-sorted, `k_v = n-1-d_v`, `W = Σ2^{-d}`):

| profile `d` | `k` | `W` | feasible skeletons | uncovered |
|---|---|---|---|---|
| (0,0,0,0) | (3,3,3,3) | 4 | 3888 (complete) | 0 |
| (0,0,0,1) | (3,3,3,2) | 7/2 | 9720 (complete) | 0 |
| (0,0,0,2) | (3,3,3,1) | 13/4 | 3888 (complete) | 0 |
| (0,0,0,3) | (3,3,3,0) | 25/8 | **0** (all `inf`) | — |
| (0,0,1,1) | (3,3,2,2) | 3 | 15344 (complete*) | 0 |
| (0,0,1,2) | (3,3,2,1) | 11/4 | ≥ 4086 (partial, 40 min cap) | 0 |
| (0,0,1,3) | (3,3,2,0) | 21/8 | ≥ 6804 (partial, 40 min cap) | 0 |

*`(0,0,1,1)` covered 100% already under the weaker
`|fans|≤2, |links|≤2` grammar (`tools/cover_all.py`, 15344 feasible,
0 uncovered); the enriched-grammar tally for that profile is
partial (3355 skeletons scanned before the time cap, 0 uncovered).
The `(0,0,1,2)` and `(0,0,1,3)` scans each hit the 40-minute cap
with **zero uncovered** skeletons (`tools/cov_*.txt`); completing
them is a compute-budget question, not a missing-gadget question —
no level-2 skeleton scanned so far lacks a gadget of bound ≥ 1.

The covering grammar (everything below is inside
`debt_residual_ge`/`charge_cap_ge` arithmetic):

1. **pure caps**: direct arc `q_arc ≥ n` ⇒ `δ ≥ q_arc − (n−1)`.
2. **block gadgets**: complementary arc `A` (`Σr_A ≥ 1−q_A`) nested
   in a cap arc `B ⊇ A` (`Σr_B ≤ (n−1−q_B)+δ` direct, or `n−q_B+δ`
   for the `∠≥0` "nn" cap) at a single vertex.  Zero equalities.
   Discovered this session via `tools/cert_high.py`; *invisible to
   the shipped evaluator* (see §3).
3. **fan/link gadgets**: one pivot `h`, signed triangle links
   forming open paths or closed cycles on subsets of the remaining
   vertices (`≤ 3` links suffice at `s = 4`), arbitrary signed fans
   (assignments `v ↦ {−1,0,+1}`), with the full cap menu per
   negative block: `r ≤ 1`, direct caps, `nn` caps (`comp ∠≥0`,
   `Σr ≤ (n−q)+δ`), and **charge-reduced caps**: a cap arc `B`
   containing a disjoint charge arc `A` covers `B∖A` with bound
   `B − (1−q_A)` — needed e.g. on `(0,0,1,2) idxs=(11,12,39,26)`
   where `r₃₁ = r₁₁+r₂₁+1 ≥ 1` follows from three links and the cap
   `r₃₀+r₃₁ ≤ 1+δ` is tightened to `r₃₁ ≤ δ` by the charge
   `r₃₀ ≥ 1`.  Also missing from the shipped evaluator.

Observed tally on the completed profiles: `block` and `pure` alone
cover most skeletons; fan-only `(0,1)` gadgets cover a constant
fraction; the `(≤3 links, ≤3 fans)` mixed family covers the rest —
including the two-saturated-vertex "strip" exceptions.

## 3. FALSIFIED / corrected claims

- **FALSIFIED**: "`link_graph.py` matches the LP level on all
  realizable skeletons" (handoff claim, verified only on the
  75+240 corpus).  Counterexample: profile `(3,3,2,1)`,
  `idxs=(0,23,75,50)`, LP `δ_min = 1`, shipped `enumerate_max`
  best bound `1/2`.  The needed certificate is the block gadget
  `r₂₁ ≥ 0`, `∠₂{0,1} ≤ π−λ` (cap `r₂₀+r₂₁ ≤ δ`), `∠₂{0,3} ≤ π−λ`
  (comp, charge `r₂₀ ≥ 1`) ⇒ `δ ≥ 1` — **no fan or triangle
  equality at all**.  After adding block gadgets + `nn` caps +
  charge-reduced caps (`tools/eval_ext.py`), all completed-profile
  skeletons are covered.
- **FALSIFIED**: "every consistent `W>5/2` skeleton has a local
  saturated-vertex gadget" — two-saturated "all-bad" cases need
  strips (already known); refined in §4.
- **FALSIFIED** (re-confirmed): `W > 2 + m/2 ⇒ M* ≥ m+1` fails at
  `m=2` (`(0,0,0,0)`, `W=4`, `δ_min=1`).
- `(0,0,0,3)` (`W=25/8`) has **zero** feasible skeletons: the high
  theorem is vacuous there; `inf` remains "inconsistent", not a
  level.

## 4. The saturated-vertex dichotomy (CHECKER-VALIDATED, exact)

`saturated v` ⟺ `k_v = n−1` ⟺ `q_v = (n,0,…,0)` (proof: `Σ(q−1)⁺ =
n−1` with `Σq ≤ n` forces exactly one positive cell, `q = n`).
Write `t*` = position of the heavy gap.  For a saturated vertex,
every angle arc has `q ∈ {0, n}`:

- a **direct** arc containing `t*` has `q = n` ⇒ pure cap `δ ≥ 1`;
- a **complementary** arc avoiding `t*` has `q = 0` ⇒ charge `1`
  inside the fan block `Σr_v = δ` ⇒ fan-alone gadget `δ ≥ 1`.

Hence `v` has **no local `δ≥1` gadget** iff the bits split exactly
at the heavy gap:

    bad(v) ⟺  ∀ u,w :  bits(u) ≠ bits(w) ⟺ t* ∈ arc(u,w)
           ⟺  bits = (threshold step at t*)  (up to global flip)

Verified: `tools/sat_dichotomy.py` — on all scanned feasible
skeletons every "good" saturated vertex's predicted gadget
(pure cap or `fan{v:+1}`) evaluates to bound `≥ 1`, zero
mismatches; "bad" vertices have `K = 0` under every fan sign and
cap menu, so no local gadget exists.

## 5. Remaining open case — the "all-bad" strip lemma

When every saturated vertex is bad (empirically this needs exactly
two saturated vertices in `F`-modes; ≥3 saturated always produces a
good one — CHECKER-VALIDATED, not proved), the level-2 gadget is a
strip: typically `fan{x:+1}` at one bad saturated vertex plus a
signed 2–3-link path/cycle through the non-saturated vertices,
terminated by a (possibly charge-reduced) cap; or a block/pure
gadget at a non-saturated vertex.

Representative exact certificate `(3,3,2,1) idxs=(0,23,75,50)`:
block gadget at the `k=2` vertex (see §3).

Representative strip `(3,3,2,2) idxs=(0,11,21,9)`:
`½·(fan₀ + r₀₂≥0 + r₁₀≥0 − Δ₀₁₂ − Δ₀₂₃ + ∠₂₁₃≤π−λ + ∠₃₀₂≤π−λ)`.

**Open**: a uniform non-enumerative construction.  Conjectured
shape: edge-side consistency between two bad saturated vertices
forces their bit cuts to be *incompatibly aligned* on the shared
edge, which forces a chargeable complementary arc to exist on one
of the two remaining vertices and a cap path back — the gadget is a
length-≤3 signed strip.  The exact statement is in §6 (H4).

## 6. Lean-ready proof decomposition

Interfaces needed (exist on lane/c as WIP `Gadget.lean`; NOT on
this branch):

```lean
-- skeleton data: per vertex v, cyclic order of the other s−1
-- vertices, bits : others → Fin 2, q : gaps → ℕ, Σq ≤ n.
structure Skeleton (s n : ℕ)

def SkeletonConsistent (sk : Skeleton s n) : Prop
  -- mode-A LP feasibility: fans + triangles + ∠≤π−λ + 0≤r≤1
  -- + δ ≤ 1 has a solution.  (NOT δ < 1: δ_min = 1 counts as
  -- consistent — see the (0,0,1,2)/(0,0,1,1) feasible-δ_min=1
  -- skeletons.)

def W (sk : Skeleton s n) : ℝ := Σ v, (2:ℝ) ^ (-(d v : ℤ))
  -- d v = (n-1) - k v,  k v = Σ_g max (q v g - 1) 0

structure Gadget (sk : Skeleton s n)   -- lane/c, needs extension:
  -- + BlockGadget kind: zero residual form, charge arc inside cap.
  -- + CapKind entries may carry internal charge arcs
  --   (charge-reduced caps).

def Gadget.score (g : Gadget sk) : ℝ := 2 * (K - Bcap - C)/(c + u)
```

Lemma stack (arithmetic parts PROVED here; combinatorial parts
stated exactly, proved-status marked):

```lean
-- W-side counting: PROVED at the profile level on this branch
-- (dyadic_two_zeros / dyadic_two_zeros4, general s + the s = 4
-- instance).  What remains is only the interface lift:
theorem weight_ge_two_sat                   -- OPEN (interface lift
    {s n : ℕ} {sk : Skeleton s n}           --  only; profile part
    (hW : 5/2 < W sk) (hs : s = 4) :        --  proved by
    2 ≤ #{v | saturated v}                  --  dyadic_two_zeros4)

theorem saturated_iff (v) :                 -- PROVED-in-text:
    saturated v ↔ ∀ g ≠ g*, q v g = 0 ∧ q v g* = n
  -- one-line algebra from k v = n-1, Σq ≤ n (see §4)

theorem saturated_dichotomy (v) (hsat : saturated v) :
    (∃ a b, directArc ∋ t* )                -- → pure cap
    ∨ (∃ a b, compArc ∌ t* )                -- → fan+charge
    ∨ bad v                                  -- OPEN (the hard
                                             --  direction is just
                                             --  unfolding §4)

theorem good_saturated_gadget (v)           -- OPEN, mechanical
    (hsat : saturated v) (h : ¬ bad v) :
    ∃ g : Gadget sk, g.Valid ∧ 2 ≤ g.score
  -- pure cap: charge_cap_ge/pure_cap_ge (PROVED arithmetics)
  -- comp charge: debt_residual_ge_one with P = Σr_v (fan form),
  --   K = 1, c = 1, U = 0, C = 0.

theorem three_sat_has_good                  -- OPEN (checker says
    (hW : 5/2 < W sk)                       --  true on all
    (h3 : 3 ≤ #{v | saturated v}) :         --  scanned skeletons)
    ∃ v, saturated v ∧ ¬ bad v
  -- OR direct gadget construction skipping the dichotomy.

theorem all_bad_strip                       -- OPEN (the crux)
    (hcons : SkeletonConsistent sk)
    (hW : 5/2 < W sk)
    (hall : ∀ v, saturated v → bad v) :
    ∃ g : Gadget sk, g.Valid ∧ 2 ≤ g.score
  -- CHECKER-VALIDATED: grammar {block | pure | fan+≤3 signed
  -- links, charge-reduced caps} covers 100% of completed profiles.
  -- Conjectured mechanism: §5.

theorem gadgetSelection_high                -- the target
    (hcons : SkeletonConsistent sk)
    (hW : 5/2 < W sk) :
    ∃ g : Gadget sk, g.Valid ∧ 2 ≤ g.score
  -- = weight_ge_two_sat + case split on #saturated + good vertex
  --   exists-or-not + all_bad_strip, then score ≥ 2 ⟺ bound ≥ 1
  --   via ResidualWitness.ge_one (PROVED).
```

## 7. Overlap with the LOW case (lane A)

Shared, already proved on this branch (usable by both lanes):
`debt_residual_ge`/`_ge_half`/`_ge_one`, `ResidualWitness`,
`debt_chain_*`, gadget bound arithmetic.

Low-specific (score ≥ 1 ⟺ `δ ≥ 1/2`): capacity `(c+u)/2 ≤ K−B−C` —
two-fan chains suffice; no block gadgets needed.

High-specific (score ≥ 2 ⟺ `δ ≥ 1`): needs the extended gadget
menu (block gadgets, nn caps, charge-reduced caps, 3-link closed
cycles, 3-fan+1-link "outer-fan" gadgets) and the saturated-vertex
dichotomy.  The arithmetic is the *same* `debt_residual_ge` at
`t = 1` — so the high theorem is **not** "low with stronger
capacity"; it has genuinely new certificate families, but no new
arithmetic lemma beyond the shared residual theorem.

## 8. Commands run / evidence

- `lake build` — green, 2527 jobs; `Jsp000404.HighDebt` builds with
  all six theorems (`debt_residual_ge_one`, `charge_cap_ge`,
  `pure_cap_ge`, `ResidualWitness.ge_one`, `dyadic_two_zeros`,
  `dyadic_two_zeros4`), `#print axioms` clean
  (`[propext, Classical.choice, Quot.sound]`), no `sorry`.
  (Note: the file currently does `import Mathlib`; a narrower
  import set would suffice — the Finset/power lemmas used live in
  `Mathlib.Data.Finset.*` and `Mathlib.Algebra.Order.*`.)
- `python3 tools/cover_all.py` — `(0,0,1,1)`: 15344 feasible,
  0 uncovered (`|fans|≤2,|links|≤2,pure` grammar).
- `python3 tools/cover3.py d0 d1 d2 d3` — enriched grammar
  (block + nn + charge-reduced caps + enumerate_max link/fan
  space): completed profiles `(0,0,0,0)` 3888/3888,
  `(0,0,0,1)` 9720/9720, `(0,0,0,2)` 3888/3888 covered;
  `(0,0,0,3)` no feasible skeletons; `(0,0,1,1)` partial
  3355/0-uncov (fully covered anyway by `cover_all.py`);
  `(0,0,1,2)` partial 4086/0-uncov; `(0,0,1,3)` partial
  6804/0-uncov (40-min cap each; raw tallies in
  `tools/cov_*.txt`).
- `python3 tools/cert_high.py k0..k3 i0..i3` — exact LP min-δ
  certificates (fractions), used to isolate block gadgets and
  charge-reduced caps.
- `python3 tools/sat_dichotomy.py` — saturated-vertex dichotomy,
  zero good-but-uncovered mismatches on scanned profiles.

New tools committed: `eval_ext.py` (extended evaluator),
`cover3.py`, `cover_all.py`, `cert_high.py`, `sat_dichotomy.py`,
plus earlier discovery scripts (`scan_*.py`, `pair_*.py`,
`dump_*.py`, `star_test.py`).

## 9. Next step

1. Prove `all_bad_strip` (§6 H4): extract the exact compatible
   signature condition between two bad saturated vertices from
   edge-side consistency, then construct the strip gadget; the
   needed certificate shapes are enumerated in §2.
2. Extend lane/c `Gadget` with the block-gadget kind and
   charge-reduced cap entries (spec in §1/§2), fill
   `charge_total`/`cap_total`.
3. Formalize `Skeleton`/`SkeletonConsistent` (LP-feasibility
   predicate over the order/bits/qs data) — shared dependency
   with lane A; coordinate to avoid duplicate definitions.
