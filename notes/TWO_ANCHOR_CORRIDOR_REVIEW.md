# Independent review of the two-anchor corridor

## Verdict

The corridor and weighted-count argument are consistent, with one
necessary orientation clarification: for a fixed orientation, order the
two anchors so that the other centers lie on the positive side of the
directed base `AB`. Replacing the reference vector by its negative alone
does not do this, because projective representatives are unchanged.
Swapping the anchor labels and using the correspondingly reversed base
does work and avoids any need for orientation-reversal invariance.

Once this ordering is fixed, no geometric or numerical obstruction was
found. The common minimum, outward direction, exact endpoints, positive
corridor span, and original-row weights all admit elementary checks.
The numerical probe is evidence against mistakes, not a replacement for
the Lean proof of the geometry.

## Coordinates and the orientation issue

Use coordinates compatible with the fixed orientation, with
`A = (0,0)`, `B = (1,0)`, and all remaining centers above the base.
Write

```text
aP = angle B A P,
bP = angle A B P,
beta = pi - n*lambda.
```

Saturation and legality give `0 < aP,bP ≤ beta < lambda`, and in fact
`beta < pi/2`. The two directed rays from the anchors have angles
`aP` and `pi-bP`. At `P`, reversing those rays leaves the same projective
line representatives, so the two anchor entries are exactly
`aP` and `pi-bP`.

If the points instead lie below the directed base, the representatives
to `A,B` are `pi-aP,bP`, respectively. A reflected legal sample from the
probe has

```text
n = 3, lambda = 0.8112851994645974,
aP = 0.38491974041801624,
bP = 0.5753273113759343.
```

Its actual representatives to `A,B` are
`2.756672913171777, 0.5753273113759343`, not
`0.38491974041801624, 2.5662653422138586`.
Thus the positive-side formula fails literally without the ordering
condition. Swapping `A,B` swaps `aP,bP`, reverses the base reference, and
restores the claimed first/last entries in the same orientation.

Noncollinearity supplies the strict positivity of `aP,bP`. In particular,
`bP > 0` is needed for the literal last representative `pi-bP` to be below
`pi`; a line representative cannot be the real number `pi`.

## Why the two minima occur at one point

For a nested pair with

```text
Sbtw A E B,   Sbtw D C E,
```

angle addition gives

```text
aD = aC + angle C A D,
bD = bC + angle C B D.
```

The extra angles are positive by noncollinearity. Hence both coordinates
increase strictly from the inner center `C` to the outer center `D`.
`two_saturated_nested` makes every distinct pair of non-anchor centers
comparable in this way. Choose `P0` minimizing `aP`. If any other point
were inside triangle `ABP0`, it would have strictly smaller `a`, a
contradiction. Therefore `P0` is the inner member of every such pair and
also minimizes `bP`.

Set `a0 = aP0`, `b0 = bP0`. The actual triangle `ABP0` gives

```text
angle A P0 B = pi-a0-b0 ≤ pi-lambda,
so a0+b0 ≥ lambda.
```

Taking the minimum of `a` and the minimum of `b` separately without this
common-minimizer argument would leave a real gap in the width proof.

## Chord corridor: a simpler proof needs no pairwise nesting

Once the positive-side anchor charts are established, the corridor proof
can avoid identifying which endpoint is the inner one.

For any non-anchor chord, choose its directed representative `Y-X` with
angle `phi` in `[0,pi)`; `linRep_class` gives either this direction or
the reversed direction, so `X` is whichever endpoint is its source.
At that source, the rays `X-A` and `X-B` have angles `aX` and `pi-bX`.
The angle caps at `X`, after negating those two rays, imply

```text
abs(phi-aX) ≥ lambda,
abs(phi-(pi-bX)) ≥ lambda.
```

Because `0 ≤ phi < pi` and `aX,bX < lambda`, the branch below `aX` in
the first inequality and the branch above `pi-bX` in the second are
impossible. Consequently

```text
lambda+aX ≤ phi ≤ pi-lambda-bX.
```

Since `a0≤aX` and `b0≤bX`, every chord lies in the common closed corridor

```text
L = lambda+a0 ≤ phi ≤ R = pi-lambda-b0.
```

This proof uses only the two angle caps at the selected source endpoint.
Nesting is needed for the common minimum, not for this directed-chord
step. It also handles reversing the original order of the chord endpoints.

As an additional analytic check, when `C` is explicitly the inner point,
`D-C` points above the base and the exact formulas are

```text
angle A C D = pi+aC-phi,
angle B C D = bC+phi.
```

The two cap inequalities yield precisely the same interval. No supplement
or sign is lost in passing to the unoriented line representative.

## Rows, margins, and width

All anchors satisfy `aP,bP < lambda`. Every chord is at least `L≥lambda`
and at most `R≤pi-lambda`. Therefore the anchor directions occur strictly
outside the chord block in every non-anchor row:

```text
directionRow(P) = aP :: (remainingDirectionRow(P) ++ [pi-bP]).
```

The outside wrap has length `aP+bP < 2*lambda` and hence contributes
zero to `gapScore`. The inside part is exactly the linear score from
`aP` to `pi-bP`. Its two margins satisfy

```text
L-aP = lambda+a0-aP ≤ lambda,
(pi-bP)-R = lambda+b0-bP ≤ lambda.
```

For at least four centers, the proved four-point deficit gives `n≥3`.
Let `W=R-L` and `m=n-2`. Then

```text
W = pi-2*lambda-a0-b0
  ≤ pi-3*lambda
  < (n-2)*lambda,
```

using `a0+b0≥lambda` and the strict floor inequality `pi<(n+1)*lambda`.
There is also no zero-span problem:

```text
W ≥ pi-2*lambda-2*beta
  = (2*n-2)*lambda-pi
  > (n-3)*lambda ≥ 0.
```

Thus the uniform width `W/m` lies strictly between zero and `lambda`,
including `n=3,m=1`. The existing clamped-floor bins accept closed
corridor endpoints. `weighted_two_anchored_rows` then bounds the actual
remaining full-row weights by `2^(n-2)`. Adding the two anchor bounds
`2^(n-1)` gives the high-regime capacity `2^n+2^(n-2)`.

## Reproducible numerical checks

Run `python3 tools/two_anchor_corridor_probe.py`. The probe uses seed 404
and tests 140,000 candidates across `n=3,...,9` and four through seven
centers. Half of the samples impose increasing angular coordinates; half
leave their pairing unconstrained before checking every actual triangle
angle and both actual saturated row scores.

There were 1,260 accepted legal configurations: 849 from the nested
sampling and 411 from unconstrained pairing. Accepted sizes were:

| n | 4 centers | 5 centers | 6 centers |
|---|---:|---:|---:|
| 3 | 87 | 0 | 0 |
| 4 | 159 | 0 | 0 |
| 5 | 189 | 2 | 0 |
| 6 | 191 | 8 | 0 |
| 7 | 197 | 11 | 0 |
| 8 | 190 | 11 | 1 |
| 9 | 195 | 19 | 0 |

Every accepted sample passed the common-minimum, nested-line intersection,
directed-angle identity, corridor, complete-row decomposition, wrap-zero,
margin, empty-bin exponent, and binary-volume checks. The maximum error
in the exact angle identities was `8.9e-16`; the smallest random corridor
slack was about `2.31e-6` radians. Separate left endpoint, internal grid
boundary, and right endpoint fixtures also passed, with assigned bins
`0,1,1` for a two-bin corridor. The endpoint fixtures attained residual
weight `4`, while the internal-boundary fixture had residual weight `2`.

The probe uses floating-point tolerances and snaps quotients within
`1e-10` of an integer for the exact-grid fixtures. Zero accepted samples
at a size are not evidence of nonexistence. The reflected sample is a
counterexample only to the unqualified orientation formula, not to the
correctly ordered corridor or capacity claim.

## Suggested elementary Lean lemmas

1. Extract the two strict anchor-angle inequalities for a nested pair
   from the angle-addition calculation already in
   `outer_nested_gapScore_add_three_le` and noncollinearity.
2. Use the actual pairwise nesting theorem and `Finset.exists_min_image`
   to construct one point minimizing both anchor angles.
3. Order the two anchors so their common strict side is positive for the
   fixed orientation; derive the actual oriented chart values `aP` and
   `pi-bP`, not merely their projective angle classes.
4. Prove the directed two-anchor corridor lemma from the two absolute
   difference inequalities above, using
   `angle_eq_abs_of_half_plane_chart`; split `linRep_class` to apply it
   at one of the two source endpoints.
5. Derive the full-row list identity by removing the two anchor entries
   and proving the resulting concatenation sorted. Then apply
   `weighted_two_anchored_rows` with `start=L`, `width=(R-L)/(n-2)`.

These steps avoid any new capacity premise, any unproved chart-invariance
claim for a reversed orientation, and any assumption that the selected
chord direction necessarily points from the inner to the outer endpoint.
