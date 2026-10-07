# Original F18 interior class weights

Status: **SOURCE_ONLY**. `Jsp000404/ActualF18ClassWeight.lean` has not been compiled or kernel checked. The source and its consumer API received independent read-only static review with no definite blocker. Existing PASS files were not modified.

## Public actual producer

`ActualF18ClassWeight.exists_actual_F18_interior_class_weight`

has inputs `o e he H hF p hnot` and returns

`Nonempty (ActualF18ClassWeight.Data o e c lam p)`.

Here `H` is the original actual n4 LOW minimal Model to cap 16, `hF` states original potential 18, and `hnot` states that `p` is not an original full-hull vertex. No original score for `p`, all-light profile, partition, class cardinality, mass budget, or weight certificate is supplied by the caller. The original F18 Frame internally proves that `p` has score one: score two would make it an original hull vertex.

The original physical three-class partition is then selected by `ActualInteriorOnePartition.actualPartition` at the original configuration and scale. All weights use the original row scores.

## Stable interface

`originalWeight o e c lam S` is `sum_{q∈S} 2^(rowScore lam (directionRow o e c q))`.

The public computed set `classMembers D k` is the image in the original `Fin t` indices of the corresponding noncentral subtype fiber of `D.classOf`. Public membership, nonempty, exclusion-of-center, disjointness, and cover lemmas are supplied for these sets.

The `Data` structure itself is generic in `c : Fin t → Plane₂`; only the actual Model producer uses the usual `Fin (s+1)` indexing. Its fields are:

- `partition`: the original actual `ActualInteriorOnePartition.Data`;
- `score_one`: the original score of the center equals one;
- `classMembers`: three plain original-index Finsets;
- `mem_iff`: for each noncentral original point, set membership is equivalent to its actual class tag;
- `ne_center`: no class contains its observer;
- `disjoint`: distinct classes are disjoint;
- `weight_ge_four`: each class has original weight at least four;
- `weight_sum`: the three original class weights sum to sixteen.

All fields are internally constructed by the producer; public consumers need no caller Data or desired mass premise.

## Lower weight proof

Every original F18 point has score one or two by the original Frame, hence weight at least two. Any class of at least two points therefore has weight at least four.

Each actual class is nonempty. If its cardinality is one, let its original target be `q`. When `q` is light, all other original rays at the observer belong to different actual classes and have angle at least `2λ` from `q`. The actual emission theorem therefore gives positive gain when `q` is deleted. The original F18 light-target minimum critical form gives zero incoming gain at every other original row, a contradiction.

If the singleton target is heavy, its original weight is four and the required bound already holds. Heavy singletons are not excluded. The zero-gain conclusion is used only for an original light **target**, not for arbitrary deletions from a light observer.

## Exact total weight

The three original-index classes are disjoint and cover exactly the original indices other than the observer. Their weights therefore sum to the original retained mass. The original potential is eighteen and the internally established center score is one, so the center has weight two and the remaining mass is exactly sixteen.

No restricted configuration or intermediate criticality is invoked. There is no transfer of a subset-hull fact to the original hull.

## Intended independent consumer

`ActualF18InteriorApex.lean`, independently owned by Sharp, consumes this Data to exclude one original interior point from another's apex. If `Q` lies in the apex at `P`, the two nonapex classes at `P` have total original weight at least eight. Their actual `3λ` angles place all their members in the same class as `P` at `Q`; together with the original weight two of `P`, that class weighs at least ten. Each other class at `Q` weighs at least four, contradicting the total sixteen.

This note does not declare that consumer or this producer kernel checked. An authorized verification window must preserve the candidate and actual failures, then run strict and genuine normal checks. No whole F18 or F17 capacity claim is made here.
