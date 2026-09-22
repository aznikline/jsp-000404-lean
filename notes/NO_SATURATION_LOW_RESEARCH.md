# LOW deletion terminals: exact obstructions and useful scope

2026-09-22. These findings are independent of the still-open arbitrary-n
capacity claim. Numerical samples are discovery evidence, not Lean proofs.

## The proposed deletion rule is false at minimum size

The claim "every legal no-saturation LOW configuration has a deletion
that does not decrease W" is false.

Take the square `(±1,±1)`, lambda=4pi/9, n=2, delta=1/4. Its largest
angle is90 degrees, below the100-degree cap. Every row has projective gaps
45,45,90 degrees, so all exponents are0 and W=4=2^n. Deleting any vertex
gives a45–45–90 triangle. All its projective gaps are at most135 degrees,
below2lambda=160 degrees, so its potential is3. Every deletion strictly
decreases W, despite no saturation.

Four is the smallest possible witness: the proved three-center LOW bound
gives W<=2^n, whereas either two-center deletion has exactly potential2^n.

There is also a minimum-size nonflat terminal. Use an equilateral triangle
and its center, lambda=11pi/36, n=3, delta=3/11. The three outer rows have
gaps30,30,120 degrees and exponent1; the center has gaps60,60,60 and
exponent0. Thus W=7 and there is no saturated exponent2. Deleting the
center leaves the equilateral triangle with potential6. Deleting an outer
vertex gives a30–30–120 triangle, again potential6. All original angles
are at most120 degrees, below the125-degree cap.

These witnesses refute unconditional progress. They do not refute the
weaker, still-open statement that every irreducible potential is below
the appropriate capacity; that statement requires genuine new geometry.

## An infinite family of flat convex terminals

For any n>=2 and LOW delta in[0,1/2), the regular2n-gon is legal and has
all exponents0. Its largest angle is pi-pi/n, at most pi-lambda. Its
projective row gaps are at most pi/n. After deleting any vertex, a merged
gap is at most3pi/(2n), strictly less than2lambda because
`3(n+delta)<4n`. Therefore W=2n and every deletion gives2n-1.

For a convex LOW configuration, summing hull exterior angles gives
`h*lambda<=2pi`, hence h<=2n. Thus a *flat convex* irreducible configuration
is automatically bounded by `2n<=2^n`. It remains unproved that every
nonflat convex configuration has a nondecreasing deletion. The four-center
triangle-plus-center example shows that such a conclusion cannot simply
be extended to configurations with interior points.

The reproducible bounded probe `tools/no_saturation_low_probe.py` covers
n=2..6, the exact witnesses, the earlier integer pentagon, regular2n-gons,
binary clusters, and12000 seeded circular/convex/interior candidates.
The binary examples have W=2^n and all tested deletions preserve W. No
nonflat convex irreducible example appeared in the samples. Interior
sampling produced few legal cases, so its negative findings are weak.
Full counts and representative terminal profiles are in
`verification/no-saturation-low-probe.json`.

## Why deformation alone is insufficient

In a legal configuration with a saturated hull vertex, write
beta=pi-n*lambda. The hull interior-angle sum gives

```text
(h-2)pi <= beta+(h-1)(pi-lambda),
so h-1 <= n+2delta.
```

In LOW this forces h<=n+1. The legal integer pentagon
`[(11,6),(6,10),(-5,5),(-3,-7),(3,-9)]` at lambda=7pi/24 has h=5 and n=3.
No saturated configuration can lie in its convex order type. Continuous
injective deformation under a cap strictly below pi cannot change order
type: a triangle orientation change crosses a collinear triple with an
angle pi. Thus even coordinated deformation alone cannot reach saturation
from this component. Actual deletions or collision/cluster limits are
essential to any such route. Several deletions of this particular
pentagon preserve W=5, so this does not refute mixed deletion/deformation.

## A separate interior profile constraint

An interior center has three other centers surrounding it. The three
projective gaps of those rays are the complements of their three
successive full-circle angles. Each gap is at least lambda and their sum
is pi. Thus n>=3 and their restricted score is at most n-3; the proved
`rowScore_le_of_sublist` transfers the bound to the full row. This is a
useful defect constraint, not a complete bound on the number or weight of
interior centers.

For n=2 there can be no interior center. The subsequent five-point route
in `FIVE_POINT_ROUTE.md` avoids formal polygon topology altogether and
instead constructs separated inward bisectors directly from the angle cap.
