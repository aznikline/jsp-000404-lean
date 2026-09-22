# JSP404-A3-LOW-ADMISSIBLE — Owner Task

Base:
`85813185e92a54a36895edbf839814993c9f12c0`

Branch:
`lane/a3-low-admissible`

## Mission

Close the LOW theorem without repeating A2's model-fidelity mistake.

The current repaired statement

`GadgetSelectionLowP s n`

adds `Skeleton.Proper`, but checker skeletons also have nonnegative integer
cells `q >= 0`, while Lean still permits signed q.

First settle the theorem domain. Then prove the arbitrary-(s,n) LOW selection.

## Phase 0 — mandatory falsification

Try hard to falsify:

```
Proper sk
+ Consistent sk n
+ W sk n > 2
-> score>=1 gadget
```

with proper positions but signed negative q.

Search both checker-side and Lean-constructible small cases:
- s=3,4
- n=1..4
- exact Fraction LP
- structured q vectors with positive/negative cancellation.

If a proper negative-q counterexample exists, commit it as a Lean theorem.

## Phase 1 — faithful state

Preferred minimal predicate if needed:

```
def Skeleton.CellNonneg (sk) : Prop :=
  forall v g, 0 <= (sk.vtx v).q g

def Skeleton.Admissible (sk) : Prop :=
  sk.Proper &&/or CellNonneg
```

Use Prop conjunctions, not booleans, if that fits the codebase.

Do NOT add:
- convexity,
- geometry-only ordering facts not present in checker,
- extra angle lower bounds,
- finite-corpus assumptions.

Keep closed `r <= 1` semantics unless a concrete counterexample forces strict
`r < 1`. Proving over the closed relaxation is stronger and preferred.

## Phase 2 — theorem target

Preferred target:

```
GadgetSelectionLowA s n :
  forall sk,
    sk.Admissible ->
    sk.Consistent n ->
    2 < sk.W n ->
    exists g, g.Valid n sk /\ 1/2 <= g.bound n sk
```

Equivalent contrapositive is allowed:

```
no score-1 gadget -> W <= 2
```

Proof must be arbitrary `s,n`.

Finite enumeration is discovery/falsification only.

Candidate proof routes:
1. Kraft / prefix packing on deficits;
2. inclusion-minimal overfull block;
3. forbidden-gadget aggregation using
   `B_v = d_v + z_v - (s-2)`;
4. evaluator-completeness only if proved as an arbitrary finite LP dual theorem,
   not by corpus enumeration.

## Acceptance

- arbitrary s,n theorem;
- no sorry/admit/custom axioms;
- exact state predicate documented;
- if state is weakened/strengthened, prove why geometry/checker instantiates it;
- `lake build`;
- `#print axioms`.

## Lead-auditable delivery

All reports/evidence/tests must be committed and pushed.

Final report must include:

```
REMOTE_BRANCH=
REMOTE_EXACT_HEAD=
BASE_SHA=85813185e92a54a36895edbf839814993c9f12c0
TASK_PATH=
TREE_CLEAN=YES/NO

DOMAIN_VERDICT=
NEGATIVE_Q_COUNTEREXAMPLE=YES/NO
FINAL_SELECTION_STATEMENT=
THEOREMS_PROVED=
TEST_COMMANDS=
TEST_RESULTS=
AXIOM_OUTPUT=
UNPROVED_REMAINDER=
```
