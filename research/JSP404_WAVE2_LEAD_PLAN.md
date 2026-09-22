# JSP-000404 Wave-2 Lead Integration Plan

Canonical base: `lane/integration @ b69e9151cd593e7b60ac8233e79314416b9420f9`

Lead branch: `lead/jsp404-wave2-integration`

## 0. Canonical-state decision

- `lane/integration@b69e915` is the only canonical proof base.
- Legacy lane heads `lane/a-low`, `lane/b-high`, `lane/c-gadget`, `lane/d-integration`, `lane/e-challenger` are all ancestors of this base and are frozen.
- Do not merge those lane tips again.
- `agent/jsp404-angle-cert-goal-01-owner@f5574fe...` is an auxiliary weighted-cell/Base3 branch. Do not merge wholesale into the proof lane.
- `agent/jsp404-competitor-crossmap-01-challenger@b334239...` is a challenger/checker branch. Do not merge wholesale into the proof lane.

## 1. Mandatory semantic gate before accepting Wave-2 Selection proofs

`Gadget.lean` certificate soundness is frozen.

However, the current abstract Selection state space is broader than the checker state space:

- checker `pos`: a permutation of the other `s-1` vertices;
- Lean `VertexData.pos : Fin s -> Fin (s-1)`: currently unconstrained;
- checker `q`: nonnegative floor cells;
- Lean `VertexData.q : Fin (s-1) -> Int`: currently unconstrained;
- real/checker remainder semantics: `0 <= r < 1`;
- `ModeA`: only stores `r <= 1`.

This is not automatically unsound: proving Selection over the larger Lean class would be stronger.
But a Wave-2 proof must not silently rely on checker-only well-formedness absent from its theorem statement.

### Gate WF

A2/B3 results are acceptable by one of two routes:

1. **STRONGER route** — prove the existing `GadgetSelectionLow/High` statements exactly as currently stated, with no checker-only assumptions; or
2. **EXACT route** — introduce a proved checker-faithful predicate, e.g. `Skeleton.WellFormed` / `Skeleton.StrictConsistent`, containing only assumptions justified by the real geometry/checker:
   - positions of vertices distinct from `v` enumerate `Fin (s-1)`;
   - `0 <= q_g`;
   - `0 <= r_g < 1`;
   - `0 <= delta < 1`;
   - `ModeA`.
   Then prove the geometry/skeleton adapter constructs this predicate.

No other weakening is accepted.

## 2. Wave-2 merge order

### Stage H0 — B2 mechanical HIGH lemmas
Merge first once pushed and green.

Acceptance:
- no change to Selection theorem statements;
- no new axioms/sorries;
- all exported lemmas generic in `s` unless explicitly justified otherwise;
- full build + `#print axioms`.

Purpose: shrink HIGH to exactly `all_bad_strip`.

### Stage E0 — E2 challenger gate
E2 is a gate, not a proof dependency.

Required attacks:
- s>=6 non-geometric valid checker skeletons;
- malformed Lean skeletons (duplicate/non-surjective `pos`, negative `q`) to test whether current Selection state space is accidentally too broad;
- signed `CapKind.low`, link polarity, charge/cap overlap, repeated-consumption cases;
- strict-vs-closed boundary cases.

If E2 finds an over-certification bug, fix `Gadget.Valid` before merging A2/B3.
If E2 only finds under-certification or invalid abstract states, use Gate WF; do not patch the proof with ad-hoc assumptions.

### Stage H1 — B3 `all_bad_strip`
Merge only after H0 and E0 are satisfied.

Acceptance theorem shape:
```
consistent/wellFormed skeleton
+ W > 5/2
+ every saturated vertex bad
=> exists valid gadget with bound >= 1
```

Prefer structural proof from incompatible shared-edge bit cuts.
Finite enumeration/corpus completeness is not accepted as the theorem.

### Stage L1 — A2 `GadgetSelectionLow`
Independent of H1; may merge before or after B3.

Acceptance:
```
W > 2
=> exists valid gadget with bound >= 1/2
```
over either the existing stronger class or the exact checker-faithful class allowed by Gate WF.

The proof must be arbitrary `s,n`, not bounded enumeration.

## 3. After LOW/HIGH close: open one Adapter lane

This is currently an explicit missing edge in `notes/FINAL_DAG.md`.

Target:
```
Section4Legality / real direction rows
   -> Skeleton + remainders + delta
   -> ModeA (and WellFormed/StrictConsistent if Gate WF uses them)
   -> kexp = actual exponents
   -> Skeleton.W normalization = actual weighted exponent sum
```

Deliver the adapter from skeleton-level:
`GadgetSelectionLow/High`
to geometry-level:
`Integration.GadgetSelection.low/high`.

This lane must prove, not assume:
- cyclic order / position bijection;
- q = floor(gap/lambda) nonnegative;
- remainder bounds;
- fan sum;
- triangle sum;
- angle upper/nonnegative constraints;
- exponent correspondence.

Only after this adapter exists are LOW/HIGH Selection usable by `sendov_lower_of_selection`.

## 4. Root integration

Once Adapter supplies `Integration.GadgetSelection`:

1. replace conditional lower route by concrete Selection object;
2. discharge/retire `staircase_of_legality.tail` or prove it via Selection;
3. wire `sendov_lower`;
4. separately handle `SendovUpper` extremal constructions;
5. run full `lake build`, theorem inventory, `#print axioms`, exact theorem statement audit, and `lean-verify`;
6. then push the immutable priority commit.

## 5. Auxiliary branches policy

### Base3 / weighted-cell branch
`agent/jsp404-angle-cert-goal-01-owner@f5574fe...`

Keep as fallback/independent proof support.
Do not merge the branch wholesale because it diverged before Wave-1 and carries extensive experimental checker history.
If needed, cherry-pick only the proved `Base3Bridge.lean` layer after Selection closes.

### strict challenger branch
`agent/jsp404-competitor-crossmap-01-challenger@b334239...`

Keep as checker/challenger evidence.
Do not make its Python margin LP a proof dependency.
Its strict results determine theorem-domain choices under Gate WF.

## 6. Current Lead verdict

State = **CRUX-REDUCED, NOT YET PROOF-INTEGRATION**.

Upgrade to **PROOF-INTEGRATION** only when:
- LOW Selection proved;
- HIGH Selection proved;
- E2 over-cert gate passes;
- geometry->Skeleton adapter proved.

Wave-2 task SHAs previously reported as `c44f6abd`, `209e641d`, `6a866a6a`, `3ead6c0c` are not currently resolvable as GitHub commits and no corresponding new remote branches are visible. Treat them as issued task IDs/local state until pushed.
