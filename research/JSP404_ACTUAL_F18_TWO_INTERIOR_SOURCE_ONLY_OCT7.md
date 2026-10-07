# All-light F18: two distinct original interior centers

Status: **SCOPED PASS**. `Jsp000404/ActualF18TwoInterior.lean` passed strict attempt 2 and a genuine normal target build at the same final source SHA `3f7c7e1e08d1f8485e03d69820b48d1510222eee595cfec1ef514c1ef8f02003`. The selected public theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`; both routes report zero own warnings. The initial SOURCE_ONLY note and the first genuine failed candidate remain preserved.

The single public consumer is

`ActualF18TwoInterior.actual_F18_all_light_two_interior_false`.

It takes the original actual n4 LOW minimal Model, original potential 18, original score one at every center, two distinct original interior centers `X,Y`. There is no assumption about the hull status of other centers. It accepts no partition, apex relation, nearest-neighbor information, cardinality, or deletion/gain budget.

## Actual producers and the nine-point count

The existing actual F18 Frame internally gives the original score/count facts. Since every original score is one, its heavy set is empty and the original cardinality is nine.

At each of `X,Y`, the actual original score-one partition is produced internally. All three classes have at least two members: every original target is light, so the original critical minimum form supplies zero incoming gain for its deletion, and an actual class singleton would emit positive gain.

All point classes used below are images of those produced subtype fibers in the original indexing set. Their sizes agree with the subtype-fiber sizes; classes at a given observer are pairwise disjoint and contain no observer itself. No original full-hull assertion is transferred to a subset.

## The other interior cannot be in the apex

Suppose `Y` belongs to the apex class at `X`. The two nonapex classes at `X` contain at least four distinct points in total. Each is different from both `X` and `Y`, because their actual class tags are 0 or 2 whereas `Y` has tag 1.

For each such point `q`, the actual apex bound gives

`angle(Y,X,q) ≥ 3λ`.

If `q` and `X` were in different classes at `Y`, the actual different-class bound would give

`angle(X,Y,q) ≥ 2λ`.

The actual triangle would then have two angles summing to at least `5λ > π`, which is impossible in this LOW band. Thus the four points are all in the same class as `X` at `Y`.

That class at `Y` contains at least five points, including `X`. Its other two classes contain at least two points each. The total would be at least `5+2+2=9` other centers, whereas the actual nine-point configuration has only eight. This proves that `Y` is nonapex at `X`. The same internal argument with the centers interchanged proves that `X` is nonapex at `Y`.

This argument does not require the other four points to be hull points. It uses only original actual partitions, their internally derived class sizes, actual triangle angles, and the derived nine-point count.

## Two disjoint hull-light apex blocks

The preceding no-apex-between argument applies to any two original interior centers, without an assumption on the other points. If a member `q` of an original interior center's apex were itself interior, its actual score-one partition and class sizes could be produced internally; applying that same argument to the center and `q` would say that `q` is nonapex there, a contradiction. Every apex member is therefore an original hull point.

Let `U,V` be the internally produced apex fibers of `X,Y`. They contain neither observer; the mutual nonapex conclusions also exclude the other interior center. The internally proved apex-hull conclusion makes every member of `U` and `V` an original hull light point, even when the original configuration has additional interior centers.

For every `u ∈ U` and every original `z ∉ U` with `z ≠ X`, the actual apex producer gives `angle(u,X,z) ≥ 3λ`. This is the full outside condition needed by `ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four`, including when the outside point is the other interior center. Therefore `|U| ≥ 4`. The symmetric call gives `|V| ≥ 4`.

If a point `r` belonged to both blocks, the mutual nonapex conclusions would give actual angles at both `X` and `Y` in the triangle `X,Y,r` at least `3λ`. Since `6λ > π`, the blocks are disjoint.

Their union belongs to the original set with `X,Y` removed, which has seven members. Its size is at least eight, a contradiction.

## Scope boundary

This checked consumer excludes any pair of distinct original interior centers in the original all-score-one F18 subdomain, so it covers all such configurations with at least two interior centers. It does not close the zero-interior or single-interior all-light cases by itself, configurations with heavy centers, the F17 residual, or the original arbitrary-cardinality theorem. It does not rely on the longer frozen two-interior nearest-neighbor paper route.

The source uses the already public actual partition, class-size, F18 Frame, and PureLightBlock interfaces. Its finite block helpers are local; it does not reference generated private declarations in other modules. Existing PASS files and the new verified PureInteriorZeroBlock and FiveTwoClassPairing sources were not changed.


## Verification record

Strict attempt 2 exited zero in 23.21 seconds; genuine normal attempt 1 exited zero in 23.85 seconds and actually built `Jsp000404.ActualF18TwoInterior`. The existing single-target 8 GiB/180-second guard did not fire. The first strict attempt failed only on the insertion-cardinality API name and dependent elimination of a local `Fin 3` label. The repairs use `Finset.card_insert_of_notMem` and an independent finite scalar sum lemma. No public premise, actual definition, or mathematical conclusion changed.

The machine-readable receipt is `research/JSP404_ACTUAL_F18_TWO_INTERIOR_RECEIPT_20261007.json`. Raw outputs, source-before snapshots, selected-name checks, and the five normal target artifacts are recorded there. All checks exited and the absence of active Lean/lake processes was confirmed before the sole window was formally passed to integration for AllLight assembly. No old PASS source or frozen PureInteriorZeroBlock file was changed, and no Git or whole-project build was run.

This receipt certifies the no-pair-of-interior-centers consumer only. The all-light assembly, the remaining F18 branches, and the F17 global selector each retain their own independent status.
