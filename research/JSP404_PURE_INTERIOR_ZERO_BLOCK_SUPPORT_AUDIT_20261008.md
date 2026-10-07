# Support audit of the pure-interior zero block route

**Conclusion:** the checked six-point lower bound remains true, but its geometric premises are already impossible. It gives no useful F17 deletion-set selector. The stronger support argument below supersedes the relevance claims in the frozen selection note; no frozen source, note, or receipt was edited.

Status of the new support argument: independently reviewed **PAPER**, with no new Lean invocation or kernel-check claim.

Audited declarations:

- `ActualPureInteriorZeroBlock.card_ge_six_of_original_zero_incoming`;
- `ActualPureInteriorZeroBlock.actual_low_four_pure_interior_zero_block_card_ge_six`.

The existing source SHA remains `4201e775644d47fc4715375c6e97255539b11978d513671f714c1b72df717184`, and its strict/genuine-normal receipt remains valid. This audit concerns the usefulness of its hypotheses, not a kernel failure.

## Stronger geometric statement

Let `c` be a finite injective actual plane configuration. Let `U` be a nonempty set of its original indices, and let `p ∉ U`. Fix just one `u₀ ∈ U`. If

`angle(c u₀, c p, c v) ≥ π/2`

for every original `v ∉ U` with `v ≠ p`, then `U` contains an **original full-hull vertex**.

In particular, `U` cannot consist entirely of original non-hull points. The six-point theorem assumes the stronger inequality `angle(c u, c p, c v) ≥ 3λ` for every `u ∈ U`, with `3λ > π/2`; it therefore falls inside this impossible all-interior case. Zero scores, zero deletion gains, the original potential, minimal cardinality, and the LOW upper endpoint play no role in this support obstruction.

## Angle center and projection sign

The actual source hypothesis is the ordinary Euclidean angle

`∠ (c u) (c p) (c v)`.

Its center is `c p`. It is not a projective line angle or a cyclic gap. Set

`e = c u₀ - c p`, and `L(x) = inner(e, x - c p)`.

Injectivity and `u₀ ≠ p` give `e ≠ 0`. Consequently

`L(c u₀) = norm(e)^2 > 0`, while `L(c p) = 0`.

For every outside point `v ≠ p`, the actual angle formula gives

`L(c v) = norm(e) * norm(c v - c p) * cos(angle(c u₀,c p,c v)) ≤ 0`.

For the original `3λ` hypothesis the cosine is strictly negative. The closed `π/2` lower bound already suffices, because the positive value at `u₀` gives a strict separation between the maximum and every outside point, including `p`.

## Original support face and ties

Let `K = convexHull(range c)`. The finite original point set has a maximum `M` of `L`, with `M ≥ L(c u₀) > 0`. Every original index attaining `M` lies in `U`.

The face `F = {x ∈ K | L(x) = M}` is the convex hull of exactly those original maximizing points. This follows directly from affine linearity: a convex combination can attain the maximum only when every point with positive coefficient is itself a maximizer.

A support face of a finite plane polygon contains an extreme point of the original polygon. No assumption of distinct projection values is needed. Under the existing actual legality, no three original points are collinear, so the maximizing original set has at most two points. If there is one, it is the singleton support face. If there are two, the face is their segment, and either endpoint is an extreme point of `K`. In both cases the selected original index belongs to `U`.

The actual definition in `Jsp000404/Deletion.lean:1534` is

`IsHullVertex c i := c i ∈ Set.extremePoints ℝ (convexHull ℝ (Set.range c))`.

Thus this is original full-hull membership. No subset-hull membership is substituted for it. The face-endpoint proof also works without the no-three-collinear assumption by choosing an endpoint of the finite collinear maximizing set.

## Consequences for the earlier route

The conditional bound `U.card ≥ 6` is logically valid because no nonempty all-original-interior `U` satisfies its actual cross-angle premises. Its finite-five counting proof and its standard-axiom verification remain intact. They should not be described as progress toward selecting a realizable F17 deletion set.

The proposed application to an HO endpoint containing only original interior zero points has the same redundancy: that endpoint already must contain an original hull vertex by the support argument. The proposed mass-19 consequence for two such pure-interior blocks also adds no new realizable restriction, because either block is individually impossible.

The checked all-light F18 TwoInterior result is unaffected. Its proof establishes that **every** member of an original interior apex is hull by the independent all-light nine-point class-count argument. The elementary support statement here guarantees only **some** hull vertex in a separated block. The actual PureLightBlock consumer also allows original hull members and is unaffected.

The global F17 deletion-set selector remains **UNKNOWN**. Future block arguments must allow original hull zero points and compute their actual deletion expense. The support argument gives no lower bound of six on a full zero block that contains hull points, no three-hull-vertices-per-class conclusion, and no license to transfer an original minimum Model or original scores to a restriction.

## Possible small formal follow-up

A useful new elementary producer would have a contract such as:

`exists_original_hull_vertex_in_obtuse_separated_block`:
finite actual injective `c`, nonempty `U`, `p ∉ U`, and actual `π/2` separation of every block ray from every outside ray imply `∃ u ∈ U, IsHullVertex c u`. The proof internally chooses one `u₀ ∈ U`; a weaker variant can accept an existential actual separating-ray witness.

Its proof should internally construct the inner-product functional and its original maximizing face or a tie-resolved original maximizer. It should accept no caller support functional, maximizing index, face, or hull conclusion. No new Lean source or check was run in this audit; a later implementation should use a new filename and preserve all existing receipts.
