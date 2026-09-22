# Global packing: what a direction cut does and does not prove

2026-09-22. Bounded review of the maximal-gap / bipartite-bin mechanism.
No unconditional capacity theorem is proved here. No Lean source or root was
changed. The one-saturated low and two-saturated high cases are outside this
review's scope.

## A single empty residual interval does not exist in general

The tempting global reduction is false, including in the low regime:

> Find a global gap of length at least `rho = pi - n*lambda`; remove a
> residual interval of that length and cover its complement by `n`
> consecutive intervals of width `lambda`.

Take five integer centers, in the order displayed,

```text
P = [(11,6), (6,10), (-5,5), (-3,-7), (3,-9)].
lambda = 7*pi/24, n = 3, delta = 3/7 < 1/2.
rho = pi - 3*lambda = pi/8.
```

All angles are at most `2*pi/3 < pi-lambda = 17*pi/24`. Every global
projective-direction gap is strictly less than `pi/8`. Consequently every
possible residual interval of length `rho` contains a segment direction.
This defeats the proposed empty-residual reduction even for an ordinary,
strictly legal, no-saturation configuration. Numerically its row exponents
are `[0,0,0,0,0]`, its largest angle is about 117.8973 degrees, and its
largest global gap is about 22.0113 degrees, below the required 22.5 degrees.

The two claims needed for the counterexample have **exact integer
certificates**, independent of the displayed decimal approximations:

* For every ordered triangle with outgoing vectors `u,v`, write
  `q = dot(u,v)`. Whenever `q < 0`, direct integer evaluation gives
  `4*q^2 <= dot(u,u)*dot(v,v)`. Thus every angle has cosine at least `-1/2`.
* Upper-half-plane representatives of all ten line directions occur in the
  following order. For each row, `d` and `q` are the determinant and dot
  product with the next representative; at the final row the next vector
  is the negative of the first. All satisfy `d>0`, `q>0`, and
  `2*q^2-(q+d)^2>0`. Hence `tan(gap)=d/q < sqrt(2)-1=tan(pi/8)`.

| Direction vector | d | q | 2q² − (q+d)² |
|---|---:|---:|---:|
| (16,1) | 69 | 181 | 3022 |
| (11,5) | 73 | 219 | 10658 |
| (14,13) | 106 | 307 | 17929 |
| (8,15) | 1 | 327 | 106274 |
| (9,17) | 120 | 350 | 24100 |
| (3,19) | 74 | 222 | 10952 |
| (-2,12) | 68 | 184 | 4208 |
| (-8,14) | 38 | 96 | 476 |
| (-5,4) | 14 | 38 | 184 |
| (-6,2) | 38 | 94 | 248 |

The vector order is also certified using positive pairwise determinants.
For each individual row, every adjacent dot product, including the wrap,
is positive. Its row gaps are therefore all below 90 degrees, below
`2*lambda=105` degrees. This proves every row exponent is zero as well.
`tools/global_packing_probe.py` checks these integer statements; its output
is `verification/global-packing-probe.json`. These are reproducible exact
arithmetic checks plus the stated elementary implications, **not a
kernel-checked Lean geometric theorem**.

## Even an empty residual interval is not enough for termwise weights

One must separately check the exponent versus empty-bin comparison.
For an explicit example take an isosceles triangle with one vertex at the
origin and the other two at unit distance in directions 0 and `pi/12`.
Its projective segment directions are 0, 15, and 97.5 degrees. Keep
`lambda=52.5` degrees and choose the three consecutive bins

```text
[-45,7.5], [7.5,60], [60,112.5] degrees.
```

The residual `(112.5,135)` degrees contains no edge direction. The origin's
row has gaps 15 and 165 degrees, so `k=2`; it occupies two main bins and
has only one empty main bin. Thus the proposed termwise claim `k <= empty`
fails. The triangle itself satisfies the final capacity bound; the failure
is in this particular encoding comparison. This is why choosing a global
empty gap cannot substitute for the local boundary-counting proof.

## A correct quantitative partial-cover reduction

The following is a proved-on-paper combinatorial reduction, still requiring
formalization. It permits the residual interval to contain directions and
therefore survives the first counterexample.

Assume `0<delta<1`, set `rho=delta*lambda`, and choose a generic cut `a`:
no segment direction lies on a bin boundary. Partition the projective
circle into main bins `I_j=[a+j*lambda,a+(j+1)*lambda)` for `0<=j<n`,
and the residual bin `R` of width `rho`. The case `delta=0` needs a separate
boundary treatment and is not asserted by this generic-cut formulation.

1. Orient each bin's edges in its positive semicircle. The angle cap and
   strict within-bin angular diameter imply that a vertex cannot have both
   an incoming and an outgoing edge in the same bin. This is exactly the
   existing `DirectionalCover` source/sink argument, also valid for `R`.
2. For each vertex `v`, prescribe its incoming/outgoing bit in each main
   bin in which it has an incident edge. Let `Q_v` be the resulting Boolean
   subcube of `{0,1}^n`, and let `e_v` count its free coordinates, so
   `|Q_v|=2^e_v`.
3. If `Q_v` and `Q_w` intersect, the edge `vw` must lie in `R`: any main
   bin containing that edge prescribes opposite bits. Since the residual
   graph is bipartite, no three subcubes can share a word. Write `O` for
   the number of words covered twice and `U` for those covered zero times.
   Then `sum_v 2^e_v = 2^n - U + O`.
4. Let `k_v` be the geometric row exponent. Counting complete bins inside
   each cyclic row gap gives
   `k_v <= e_v + 1_{v has no incident residual edge}`.
   Indeed a gap of length `g` contains at least
   `max(floor(g/lambda)-1,0)` empty bins of the full `(n+1)`-bin partition:
   the two occupied endpoint bins contribute strictly less than
   `2*lambda`, and every intervening bin has width at most `lambda`.
   Different row gaps count different empty bins.
5. A deficient row means `k_v=e_v+1`; it necessarily has no residual edge.
   Its cube is therefore disjoint from **every** other vertex's cube.
   Put `D=sum_deficient |Q_v|`. Put
   `S=sum_nondeficient (|Q_v|-2^k_v)`, which is nonnegative. Then the exact
   accounting identity is

```text
sum_v 2^k_v = 2^n - U + O + D - S.
```

In particular, `sum_v 2^k_v <= 2^n + O + D`. The sets counted by `O` and
`D` are disjoint subsets of the Boolean cube. A genuinely sufficient
geometric lemma would be:

```text
There is a generic cut with O+D=0                    in the low regime;
there is a generic cut with O+D <= 2^(n-2)           in the high regime.
```

This is a **new open cut-selection lemma**, not a result established by
the reduction. It is stronger than the desired capacity theorem and
cannot be substituted for `GeometricCertificates` without proof. The
weaker statement retaining `U` and `S` is just the exact accounting
identity and should not be advertised as a solution to the global crux.

## What finite probing says about that open lemma

The probe enumerates midpoint cuts between every direction/boundary event,
so it checks every generic combinatorial cut state for each supplied
configuration at the comparison precision used (with floating-point
coordinates, rounded event deduplication, and comparisons).

| Configuration | min(O+D) | max(O+D) | high bonus |
|---|---:|---:|---:|
| Integer pentagon above, n=3 low | 0 | 4 | — |
| Regular pentagon, n=2, delta=3/4 | 1 | 2 | 1 |
| Existing nonflat nine-center example, n=3, delta=3/4 | 2 | 8 | 2 |

Thus neither an arbitrary cut nor the bound `O<=2^(n-2)` for all cuts is
valid. In the nine-center example a bad cut doubles every word of the
three-dimensional cube: `O=8`, with the excess balanced by `S=6`.
A selected cut attains `O=2,D=S=U=0`, showing how the full high bonus can
arise in a configuration with no saturated vertex.

An exploratory sample of perturbed convex configurations for `n=2..5`
and `delta` in `{.25,.49,.5,.75,.95}` found no violation of the *existence*
version of the coarse cut bound. This is weak discovery evidence: the
sample is not exhaustive, rarely approaches high-strip capacity, and
does not supply a geometric selection argument. No general result should
be inferred from it.

## Recommendation and proof boundary

Discard the single-empty-global-gap lemma: it has the exact five-center
counterexample above. If pursuing direction cuts, keep residual edges and
explicit deficient rows, and target the stronger `O+D` cut-selection
statement. Its finite state space and local changes under rotating the
cut give a precise object to study, but its required global bound remains
open. The existing binary-encoding theorem proves the disjoint-subcube
count once separation is obtained; it supplies no cut-selection theorem.

This review does not resolve `CertExists`, the zero-saturation capacity
cases, or the arbitrary-N lower root.
