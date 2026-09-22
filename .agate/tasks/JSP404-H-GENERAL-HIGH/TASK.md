# JSP404-H-GENERAL-HIGH — Owner Task

Base:
`85813185e92a54a36895edbf839814993c9f12c0`

Branch:
`lane/h-general-high`

## Mission

Close the arbitrary-s uniform capacity bound by geometric deletion induction.

Do NOT assume the s=4 HIGH proof generalizes.

The integration theorem needs, for arbitrary forest length:

- LOW: potential <= 2^n when delta < 1/2;
- HIGH: potential <= 2^n + 2^(n-2) when delta < 1.

The uniform caps are independent of s, so a non-increasing deletion step is
enough: reduce to the already-proved s=3 base.

## Proven source material to port selectively

From `agent/jsp404-angle-cert-goal-01-owner`:

- `ff4e73a620cf2e1bcee2b68971f71f6faa22c007`
  - Base3CellData, base3 low/high arithmetic.
- `f5574fe6c1542f6502d6074b3922f8db37c531f6`
  - geometry -> s=3 base bridge.
- `94b6fd07e47bf6b85fb442b49aafc64f1bfbd975`
  - `Section4Legality.erase`
  - `potential_sub_config`
  - `potential_le_sub_config_iff`
  - dedup / rowScore bridge.
- `5930acea648bd9ab64487a4e04edc3853cda73cd`
  - research/status only; do not treat empirical claims as proof.

Do not merge the old branch wholesale. Rebase/cherry-pick only kernelized pieces
needed on top of 8581318, resolving imports against the current gadget tree.

## Main theorem shape

Do NOT target the false/too-strong statement
"every legal configuration has a removable vertex".

Sparse low-potential configurations can lack one.

Target a progress-or-done lemma:

```
theorem potential_progress_or_bound
    (hlegal : Section4Legality c lam)
    (...) :
    potential lam (directionRows c) <= cap
    \/ exists v,
         potential lam (directionRows c)
           <= potential lam (directionRows (c erase v))
```

with cap selected by the delta regime.

Equivalent certificate form:

```
F > cap -> exists v, charge v <= 0
```

is preferred if it matches existing `potential_le_sub_config_iff`.

Then prove well-founded induction on s:
- s<=2: trivial / impossible as appropriate;
- s=3: Base3Bridge;
- s>=4 and F>cap: delete v;
- legality is hereditary;
- n, lam, delta regime unchanged;
- recurse.

## Cert-lemma evidence to use as discovery only

The old branch observed, under the exact legality contract:
- positive gain arcs that do not rise in exponent give immediate certificates;
- no-cert forces a strictly ascending emission graph;
- max-k layer becomes silent;
- at most one jump-1 incoming emitter;
- intra-level emission is forbidden;
- all geometric nonflat samples satisfied the proposed dichotomy.

These are hints, not assumptions.

Cross-fertilize with current gadget work:
- B2 saturated/bad structure;
- B3 shared-edge bit-cut incompatibility;
- A3 deficit/Kraft constraints.

A proof that converts any over-cap legal configuration into either:
- a non-ascending emission edge; or
- enough close incoming emitters;
is acceptable.

## Strong alternative

If the cert lemma remains hard, prove the uniform capacity bound directly from a
global LP/Kraft inequality and skip deletion. The result must still be arbitrary s.

## Acceptance

- full arbitrary-s LOW+HIGH capacity, or at minimum arbitrary-s HIGH if LOW A3
  is expected to close first;
- no reliance on s=4;
- no finite enumeration as proof;
- no new sorry/admit/custom axioms;
- exact connection to `Integration.GadgetSelection` or directly to
  `StaircaseBound`;
- `lake build` and `#print axioms`.

## Lead-auditable delivery

Every report/evidence/test must be committed and pushed.

Final report:

```
REMOTE_BRANCH=
REMOTE_EXACT_HEAD=
BASE_SHA=85813185e92a54a36895edbf839814993c9f12c0
TASK_PATH=
TREE_CLEAN=YES/NO

PORTED_KERNEL_COMMITS=
PROGRESS_LEMMA_STATUS=
LOW_CAP_STATUS=
HIGH_CAP_STATUS=
INDUCTION_STATUS=
INTEGRATION_HOOK=
TEST_COMMANDS=
TEST_RESULTS=
AXIOM_OUTPUT=
UNPROVED_REMAINDER=
COUNTEREXAMPLES_OR_FALSIFIED_SUBLEMMAS=
```
