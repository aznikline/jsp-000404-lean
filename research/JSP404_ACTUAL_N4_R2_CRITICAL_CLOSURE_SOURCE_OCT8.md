# Actual n4 HIGH exact-F21 R2 closure: source-only candidate

Status: **SOURCE_ONLY**. No Lean invocation, build, axiom check or new
actual closure PASS is claimed. The new outer terminal and exhaustive
outer data chain must be checked before this consumer can be verified.

Source: `Jsp000404/ActualN4R2CriticalClosure.lean`, 153 lines, one selected
public export, `actual_n4_high_critical21_impossible`. SHA-256:
`76297df83dc2b4ecc377403f0c2d8bf74906cceb3519de113195efe7b2290e0e`.

## Public target

The original actual configuration supplies only:

- `s ≥ 6`, a fixed orientation, and a nonzero reference;
- `Section4Legality c λ`, `floor (π/λ) = 4`, and natural HIGH condition
  `1/2 ≤ π/λ - 4`;
- three distinct original centers of scores `3`, `2`, and `2`;
- exact original potential `21`.

The candidate concludes `False`. The caller supplies no chart, ranks,
triangle word, low-row placement, tail-flatness assumption, defect
profile, finite-check acceptance, capacity, or counter-model property.

This is an exact-F21 theorem. It is not full R2 capacity: potential 22,
minimum-score-one cases, and six-point mixed-tail closure are separate
obligations. It does not complete the original all-N lower bound.

## Existing unconditional actual split and inflation

The narrow split API question has a positive answer when the legal
scale is allowed to decrease within the natural HIGH band.

`ActualSingleSplitScoreTable.exists_single_positive_split_score_table`
requires only actual legality, at least three points, a nonzero
reference, a chosen positive-score center, and `0 < τ < λ`. It constructs
the endpoint axis, safe references and positive perturbation internally.
Both children of the chosen center have old score minus one, and every
other original row retains its exact old score at the returned legal
scale. The original point positions also survive under the original
index injection. Thus a chosen score-one tail becomes two actual
score-zero points while the untouched anchor/low rows retain `3,2,2`.
No perturbation family or half-angle certificate is a caller premise.

The earlier generic `ActualScorePreservingExpansion` helper does require
axes and explicit continuous floor trajectories. Those weaker helper
premises are not needed by the completed single-split score-table API.

The existing
`R2N4PureTailInflation.exists_actual_n4_critical21_pure_tail_eight`
already performs the full selective iteration, protecting the three
original centers. It returns a genuine `Fin 8` configuration, a protected
injection preserving original points and scores, five actual zero-score
tails, potential 21, and a scale `π/5 < λFinal < λ` with floor four and
HIGH remainder in `[1/2,1)`. It does not claim fixed-scale splitting or
inheritance of original minimum-cardinality/deletion-criticality facts.

Existing immutable formal evidence was checked read-only:

- `research/JSP404_ACTUAL_PROTECTED_INFLATION_20261006.json`, SHA-256
  `e02bc962fd2816f4075bb19a2b15542795690f776bac38a231461fb2b6acbfb7`;
  seven single-split and thirteen protected-inflation standard-three-axiom
  exports, successful strict/normal records, and matching successful raw
  output hashes.
- `research/JSP404_R2_N4_PURE_TAIL_INFLATION_STRICT_20261006b.json`, SHA-256
  `2204cfdcc86ab62040d621c104bcf48e9b63c6fa48bd9ce3fd0d35b448213883`;
  seven standard-three-axiom exports, strict-final exit 0 and genuine
  normal exit 0, including the exact-F21 eight-point producer. Both
  successful raw hashes match. Current producer source hashes match the
  receipts; no new check was run.

## Internal actual closure chain

The new public consumer invokes the existing protected F21 producer.
Actual row-cell bounds and score/defect identities then derive final
anchor defect one and two low defects two. Every other final score is
zero; `rowDefect_le` is used explicitly to conclude defect four rather
than inferring it from truncated subtraction alone.

The private eight-point helper constructs the actual saturated ray
window and `SatChart` with its internally chosen nonzero reference.
Reference invariance transports every original final defect to that
chart. `ActualN4R2RankRegions.actual_chart_low_rank_regions` supplies the
actual sorted rank map and the two possible assignments of original low
points to `lo,hi`. Injectivity of the composed rank/`succAbove` map proves
that all other ranked rows are genuine tails.

The three actual rank regions are consumed in their public order:

1. `(5,6)`: the public exact model reflection transports both low rows
   and all five tails to `(0,1)`, then the new outer-left terminal applies.
2. `(0,6)`: the already checked between terminal applies directly.
3. `(0,1)`: the new outer-left terminal applies directly; its stronger
   interface needs only low row 1 and tail rows 2..6.

No classification of a bare scalar model is assumed. All rank regions
come from the actual saturated geometric chart. The reflected model is
the existing public `SatScalarModelReflection.reflect` construction.

## Pending verification and ownership

Uniform confirmed the outer terminal's fixed public API. The outer
soundness core remains frozen at source `e69febc9...f0b80630`, and the new
terminal remains unchanged at `b5fab574...4ff8d7a`. Uniform owns the new
193-shard data and all-check assembly. This task owns only this new
closure source and note; no dependency or shared document was edited.

Independent read-only review found no mathematical or apparent API
blocker in the protected score conversion, reference invariance, swapped
low assignments, rank injectivity, three region branches or reflection
consumer. The remaining let/definitional-equality and transparent-region
elaboration risks require the actual compiler check. The candidate still
needs root-authorized strict/genuine-normal checks after its pending
data/terminal dependencies are ready. No Git or Lean operation was
performed while preparing it.
