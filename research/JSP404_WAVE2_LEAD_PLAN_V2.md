# JSP-000404 Wave-2 Lead Plan v2

Canonical base:

`lane/integration @ 85813185e92a54a36895edbf839814993c9f12c0`

Lead branch:

`lead/jsp404-wave2-integration-v2`

## 1. Current verified state

Merged and green:

- Wave-1 gadget semantics / selection interfaces / integration.
- B2 HIGH mechanical stack:
  - `weight_ge_two_sat`
  - `saturated_iff`
  - `saturated_dichotomy`
  - `good_saturated_gadget`
  - `three_sat_has_good`
  - `gadgetSelection_high` conditional on `AllBadStrip 4 n`
- A2 model-fidelity counterexample:
  - original `GadgetSelectionLow/High` are false;
  - `Skeleton.Proper` repairs the non-injective `pos` ghost;
  - `GadgetSelectionLowP/HighP` are the repaired open interfaces.

## 2. Two hard corrections to the project status

### Gate Q — `Proper` is not yet the full checker-faithful state

The checker has nonnegative floor cells `q >= 0`.
Lean currently has:

`VertexData.q : Fin (s-1) -> Int`

and `Skeleton.Proper` only constrains positions.

B2 already requires `0 <= q` explicitly.

Therefore `GadgetSelectionLowP/HighP` must NOT be treated as checker-faithful
until one of the following is proved:

1. `Proper + Consistent -> q >= 0`; or
2. introduce an explicit admissibility predicate carrying `q >= 0`; or
3. prove the stronger P statements even with signed q.

No silent use of checker nonnegativity is accepted.

### Gate S — B2 only closes the s=4 HIGH reduction

`HighSelection.gadgetSelection_high` is explicitly:

`Skeleton 4`

and uses `5/2 < W -> >=2 saturated`, which is special to s=4.

But `Integration.GadgetSelection.high` quantifies over arbitrary
`V.forest.length`.

So `AllBadStrip 4 n` is NOT the final arbitrary-s HIGH theorem.

Example of why the profile argument does not generalize:
for s=6, six deficit-1 terms have W=3>5/2 but no saturated vertex.

## 3. New route allocation

### P0-A: LOW / admissible gadget route

Branch: `lane/a3-low-admissible`

Goal:
- settle Gate Q;
- prove an arbitrary-(s,n) LOW selection theorem on the exact faithful state;
- keep closed `r <= 1` semantics if possible; only require strict remainders if a Lean counterexample forces it.

### P0-H: arbitrary-s HIGH via geometric deletion induction

Branch: `lane/h-general-high`

Reactivate the weighted-cell branch, but only the kernelized pieces:

- s=3 base:
  `ff4e73a`, `f5574fe6`
- deletion / legality / potential bridge:
  `94b6fd0`
- certificate research status:
  `5930acea`

Do not merge the old branch wholesale.

Target proof shape:

```
Section4Legality c lam
  -> if potential <= cap: DONE
  -> else exists v with potential <= potential(c erase v)
  -> legality hereditary
  -> induction to s=3
  -> low cap 2^n / high cap 2^n+2^(n-2)
```

This single route, if closed, proves BOTH uniform LOW and HIGH capacities
without needing the abstract Gadget->geometry adapter.

The remaining theorem should be stated as a progress-or-done lemma, not
as a stronger universal removable-vertex claim if sparse configurations
have no removable vertex.

### P1-B3: s=4 all-bad strip

Continue B3.

Its value:
- validates the strict bit-cut mechanism;
- may supply the missing certificate pattern to H-general;
- closes the s=4 HIGH local theorem.

But it is no longer considered the full HIGH blocker.

### P0-E2: challenger / over-cert gate

Continue E2 with highest priority on:

- proper skeletons with signed/negative q;
- s>=6 non-geometric admissible skeletons;
- signed `CapKind.low`;
- charge/cap overlap and repeated consumption;
- strict-vs-closed boundary.

A true over-certification bug blocks all gadget merges.

## 4. Integration decision tree

### If H-general closes first

Use geometry-level deletion induction directly to construct
`Integration.GadgetSelection.low/high` consequences or bypass that interface
with a direct `StaircaseBound` theorem.

Then LOW gadget selection becomes optional corroboration, not load-bearing.

### If A3 LOW + a future arbitrary-s HIGH gadget theorem close first

Open one adapter lane:

```
geometry rows
 -> proper/admissible Skeleton
 -> ModeA
 -> exponent correspondence
 -> W normalization
 -> Integration.GadgetSelection
```

### If B3 closes but H-general remains open

Record s=4 HIGH as proved, but do NOT mark global HIGH closed.

## 5. Root theorem status

Even after the lower bound closes, `SendovUpper` extremal constructions are
still separate and must be completed for the full minimax equality.

## 6. Lead state

Current state:

**CRUX-REDUCED / TWO GLOBAL OPTIONS**

- Gadget route: LOW still open, arbitrary-s HIGH still open.
- Deletion route: base + erase + potential identity all kernelized; sole general
  crux = high-potential certificate/progress lemma.

Do not label the project PROOF-INTEGRATION until one complete arbitrary-s
capacity route is closed.
