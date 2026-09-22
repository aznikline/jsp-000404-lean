# First-strip closure and faithful cell normalization

All new unconditional results below have been checked with Lean 4.34.0.
Their transitive dependencies are only `propext`, `Classical.choice`,
and `Quot.sound`. Neither native computation nor an unfinished theorem
is used in these proofs. The arbitrary-N lower root remains incomplete.

## First strip: no missing boundary case

For floor(pi/lambda) = 1, `exponents_lt_of_floor` says every exponent
is zero. The weighted capacity is therefore the number of centers.

- If delta < 1/2, then 3 lambda > 2 pi, so every triangle would have
  three angles less than pi/3. The angle sum rules out three centers:
  the capacity is at most 2.
- Throughout the first strip, pi < 2 lambda, so all angles are strictly
  acute. Four distinct plane points always determine a nonacute angle:
  the capacity is at most 3, exactly the n = 1 high cap.

`four_points_nonacute` uses Mathlib's Radon partition. An acute set is
in convex position: at each point, an inner-product functional strictly
separates every other point from it. Each side of a Radon partition of
four points must consequently have two elements. Intersecting segments
contradict the weighted sum of the four positive endpoint inner products.

The Radon proof strategy was also inspected in the comparison project's
`Prize/JSP404/FourPoints.lean` from the supplied
`jsp404-four-clusters-20260921` snapshot of
`jerrylijize1224-star/jsp404-lean-partial`. This is a classical argument,
not a claim of a new mathematical result or first formalization. The
local finite-index formulation feeds the center-capacity theorem directly.

`sendov_lower_four` transfers this result to `PtCfg` and `alphaN 4`.

## Direct geometric assembly

`CertificateIntegration.GeometricCertificates` is the uniform, still-open
claim that the geometric certificate exists for all n >= 2 and all legal
center counts in each permitted regime.

The following are now proved:

```text
GeometricCertificates
  -> GadgetSelection
  -> sendov_lower_of_selection
  -> JSP404.alpha N = Jsp404.alphaN N, for every N >= 3
```

The first implication uses the unconditional first strip for n = 1
and `staircase_of_cert` for n >= 2. It does not need to construct an
abstract skeleton from actual geometry. The final upper bound is already
unconditional. The certificate premise is not discharged by this assembly.

## Signed cells: a proved normalization

The gap proof works for arbitrary s and n, not just four centers.

1. `Proper.pos_surjective`: injectivity of positions on the other
   vertices is a permutation, because the domain and codomain both
   have cardinality s - 1.
2. `ModeA.arc_sum_bounds`: every nontrivial arc has sum between 0 and
   n + delta, regardless of which direction-bit branch applies.
3. Every non-wrap gap is a singleton arc. The wrap gap is the fan sum
   minus the arc from the first position to the last. A one-gap fan is
   handled separately. Therefore every real gap q + r is nonnegative.
4. If r < 1, integer q must be nonnegative. If merely r <= 1, a negative
   integer q can only be -1 with r = 1, giving a zero real gap.
5. Replace q by max(q,0) and r by r + q - max(q,0). The exceptional pair
   (-1,1) becomes (0,0); all other cells are unchanged. The resulting
   model has the same gap sums, angles, delta, positions, bits, exponents,
   and rational weight W. It still satisfies every field of `ModeA`.

`exists_nonnegative_model` packages the construction for consistent
proper skeletons. `capacity_of_nonnegative_models` shows that any weight
bound proved for nonnegative cells transfers to the proper closed model.
This does not prove the desired bound and does not transport a selected
gadget witness; those are separate questions.

## Remaining central theorem

Prove the arbitrary-size geometric certificate / Kraft capacity bound,
or finish the arbitrary-size gadget capacities and geometric adapter.
`MainTheorem.sendov_lower` now handles N = 3 and N = 4 explicitly, but
its N >= 5 branch still contains the original proof hole. The completion
audit continues to print `sorryAx` for that root and therefore rejects
any complete-proof claim.
