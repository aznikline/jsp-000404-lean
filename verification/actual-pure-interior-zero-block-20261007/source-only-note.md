# F17 actual deletion selection: a local six-point obstruction

The global F17 selector remains **UNKNOWN**. This note records a new local PAPER result, an implemented SOURCE_ONLY actual consumer, and the exact gap between that local result and a global deletion choice. It does not claim F17 capacity or the original arbitrary-cardinality theorem.

The pure combinatorial helper `Jsp000404/FiveTwoClassPairing.lean` has independently passed strict and genuine normal checks at source SHA `973e075526921bfa4726ca01815b38e89cc2ae2c082e7f712c7749642bb90635`, with only the three standard axioms and zero own warnings. The actual consumer `Jsp000404/ActualPureInteriorZeroBlock.lean` is still SOURCE_ONLY at the time this note is written.

## Original budgets and the closed boundary

Let the original actual n4 LOW configuration be a minimal counter to cap 16, with a zero-score point. Its original potential is 17. Every original zero **target** has zero incoming gain at every other original observer. This does not say that an arbitrary zero observer has zero outgoing gain when a positive target is deleted.

For any proper actual restriction retaining at least three points, the already proved original ledger is

`restrictionExpense + 1 ≤ removedWeight`.

Deleting `k` original zero points therefore allows total retained expense at most `k - 1`. In particular, deleting two zero points allows only one unit: a retained original score-one or score-two observer cannot grow at all, and at most one retained original zero observer can grow by one.

For the original fixed-cardinality F17 maximum, deleting one original zero target leaves every actual cyclic gap of a retained original zero observer at most

`2ρ = 4π/9`.

This inequality is closed. Equality is allowed, and at `ρ` itself that gap may score positively. Neither a row-zero conclusion at `ρ` nor a strict `< 2ρ` inequality follows. The new local result below does not strengthen or use this boundary statement.

## New local result

Assume `2π/9 < λ ≤ π/4`. Let `U` be a nonempty set of **original interior zero-score points**. Suppose an original point `P ∉ U` satisfies the actual separation condition

`angle(u,P,z) ≥ 3λ`

for every `u ∈ U` and every original `z ∉ U` with `z ≠ P`. Suppose also that the original zero targets in `U` have zero incoming actual gains, as the original minimal Model supplies. Then

**`|U| ≥ 6`.**

No original or restricted potential profile is supplied to the proof. No restricted configuration is asserted to be critical, minimum, maximal, flat, or to retain original row scores.

### First force five members

At each `u ∈ U`, the actual original interior-zero producer gives three nonempty physical classes. Equal-class angles are bounded by their spans, whose sum is at most `T = π - 3λ`; unequal-class angles are at least `2λ`.

The actual triangle `u,P,z` and the `3λ` separation at `P` imply that the angle between `P` and `z` at `u` is at most `T`. Since `T < 2λ`, every outside point lies in the same class as `P` at `u`. The case `z = P` is handled separately, without applying the cross-angle premise to a repeated center.

The other two classes consist entirely of members of `U`. Each has at least two members: a singleton would emit positive gain when that singleton original zero target is deleted, contrary to its original incoming-zero conclusion. Together with the observer `u`, this gives five distinct actual points in `U`.

### Exclude exactly five members

If `|U| = 5`, then at every `u ∈ U` its four other members fill the two classes in a `2+2` pattern. No other member of `U` is in the outside class.

There are exactly two unordered same-class pairs at each observer, hence ten same-class angle incidences over the five observers. There are exactly ten unordered actual triangles in `U`. Every triangle has at least one same-class angle, since three different-class angles would sum to at least `6λ > π`. Thus every triangle has exactly one same-class angle and two angles at least `2λ`.

Consequently, every same-class angle in this five-point restriction is at most

`R = π - 4λ < λ/2`.

Each of the five actual observers now has two physical clumps of size two, same-clump angles at most `R`, different-clump angles at least `2λ`, and a distinct same-clump companion for every target. Choosing three observers contradicts the already proved `SmallTwoClusterGeometry.no_three_small_two_clusters`.

The only inheritance step is actual legality from the original configuration to the injectively indexed five-point restriction. There is no original-hull/subset-hull transfer, and no invocation of minimum cardinality on an intermediate configuration.

## Implemented interfaces

`ActualPureInteriorZeroBlock.card_ge_six_of_original_zero_incoming` takes the original actual legality and LOW scale, the nonempty actual set `U`, the outside original point, original interior/zero assertions for `U`, original zero-target incoming gains, and the actual `3λ` separation. It internally produces all original partitions and the actual five-point restriction.

`ActualPureInteriorZeroBlock.actual_low_four_pure_interior_zero_block_card_ge_six` takes the original n4 LOW minimal Model and the same actual set/interior/zero/separation conditions. It internally derives incoming-zero gains for each target in `U` from the original critical form. A separate F17 hypothesis is unnecessary because the nonempty original zero set already forces F17 in that Model.

The private five-row construction uses actual partition tags and witness points. The independent public finite helper accepts abstract five-point Bool rows only for its pure counting lemma; that abstract helper is never presented as an actual geometric producer.

## Concrete use and remaining selector

An HO heavy observer already supplies two actual endpoint clumps with cross angles at least `3λ`. If one endpoint clump consists entirely of original interior zero points, it has at least six actual centers. In particular, an endpoint of original weight five made of five original interior zeros is excluded. The earlier F17 endpoint weight-five lower bound alone did not exclude that case.

There is also a PAPER mass consequence for two distinct original interior positive-score observers `P,Q`, each with such a pure original-interior-zero block `U,V`. Positive observers cannot belong to the other's zero block. A shared member would give two angles at least `3λ` in the actual triangle `P,Q,u`, so the blocks are disjoint. They contribute at least twelve units of zero mass, the two positive observers contribute at least four, and the original full hull has at least three vertices disjoint from all these original interior points, contributing at least three more. The original mass would be at least 19, contradicting F17. This excludes the two-pure-apex subdomain; it does not assert that either apex must be pure or consist of interior zeros.

This result cannot be applied to a clump containing original hull zero points: those points do not supply the three nonempty original interior classes used above. It also does not apply to a block containing positive-score points, or to a merely `2λ` separated class of an interior-zero partition.

For a global selection proof, one still needs an actual geometric theorem forcing either such a block of size at most five, or a deletion set whose retained expense exceeds the original ledger. A pair of zero targets that clears only one retained zero observer's class costs one and merely saturates the two-zero budget. A contradiction requires an additional retained charge, or growth at a retained positive-score observer. No such global selector has been proved here.

One smaller strict fact is available without the boundary limit: some original interior-zero class has span at most `(π - 3λ)/3 < λ/2`. If that class contains a zero target, its nonsingleton companion gives a strictly shorter actual edge than the edge from the target to the observer. The class need not contain a zero target; a positive singleton remains possible. This fact therefore supplies no unconditional deletion choice on its own.

An explicit actual LOW negative control separates the available zero/boundary facts from a `3λ` selection theorem. Take the seven vertices `(cos(2πj/7), sin(2πj/7))`, `j=0,...,6`, and `λ=π/4`. Every complete projective cyclic row has five gaps `π/7` and the wrap gap `2π/7`; all original scores are zero. Any single deletion merges either two internal gaps into `2π/7`, or an internal gap and the wrap into `3π/7`. Both remain below `2λ`, and the larger is strictly below the closed boundary `2ρ=4π/9`. All actual incoming gains are therefore zero, including throughout `ρ < λ' ≤ λ`. Yet every actual angle is at most `5π/7 < 3λ`, so there is no actual three-scale wide angle to select. This is an actual legal all-hull configuration of potential 7, **not** an F17 Model counterexample. It shows why a global selector must use the original potential 17 and actual interior structure in addition to the zero-target and boundary facts.

## Verification boundary

The pairing helper's first genuine strict failure and its raw source snapshot are preserved; the only repair was explicit simplification of the final distinctness condition, together with replacement of deprecated `if_pos`/`if_neg` spellings. Its corrected source passed both routes within the 3 GiB single-Lean guard, without a cap event.

The actual consumer must receive its own authorized strict and genuine-normal checks before it is called kernel checked. Existing PASS sources, definitions, and original models were not changed. The global F17 selection claim remains open even if this local actual consumer later passes.
