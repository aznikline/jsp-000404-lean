# One saturated HIGH anchor: cube holes and exponent slack

2026-09-22. Bounded mathematical review; no Lean files or root imports
changed. The arbitrary-size one-saturated HIGH case remains open.

## Conclusion

The literal claim that the anchor forces a quarter of the ordinary
active-bin Boolean cube to remain unoccupied is **false**. More strongly,
the proposed existence of a reservable quarter-face on **any** two fixed
uniform-bin coordinates is also **false**. An integer thirteen-center
counterexample below has exactly one saturated anchor and attains the
desired HIGH capacity. The capacity theorem itself is not contradicted.

There are useful noncircular sufficient premises below: one remaining row
occupying one bin; two suitably deficient rows occupying at most two bins;
or a concrete local criterion for reserving a quarter-face after shrinking
encoding cubes. The criterion remains valid as a sufficient lemma, but
its proposed universal existence statement for this fixed cover is now
disproved. The sparse-row certificate existence statements remain open.

## Setup and exact margin information

Let the saturated anchor be A, let

```text
pi/lambda = n+delta,  1/2 <= delta < 1,
beta = pi-n*lambda = delta*lambda,
L = pi-2*lambda+beta,
w = L/n < lambda.
```

Use the saturated ray chart `theta_v in [0,beta]` and the n uniform bins
in `[lambda, pi-lambda+beta]`. Orient each chord in the positive
semicircle. Each bin is bipartite by the existing narrow-cone argument.
The uniquely assigned bins give disjoint cubes `Q_v subset {0,1}^n` for
the remaining vertices. If `a_v` bins are active and `e_v=n-a_v`, then
`|Q_v|=2^e_v`. The anchored linear-gap count gives `k_v<=e_v`.

The exact per-vertex constraints behind the common corridor are stronger
than its endpoints. For a chord with projective angle phi, at v:

```text
outgoing/positive edge: phi >= theta_v + lambda;
incoming/negative edge: phi <= theta_v + pi - lambda.
```

These follow directly from the two anchor-triangle angle caps. Both
counterexamples below satisfy these inequalities, with positive slack.

## Exact rational counterexample to an unmodified quarter-hole

Take

```text
A=(-1000,0), B=(1000,0), D=(1001,3), C=(0,700).
n=2, lambda=3*pi/8, delta=2/3, beta=pi/4.
```

The row exponents in this order are exactly `(1,0,0,0)`. A is the only
saturated center. All angles are strictly below `5*pi/8`; the numerical
maximum is about 110.1583 degrees, below the 112.5-degree cap.

The remaining chord directions are approximately

```text
BD: 71.5651 degrees;
BC: 145.0080 degrees;
DC: 145.1504 degrees.
```

The two uniform corridor bins are `[67.5,112.5]` and `[112.5,157.5]`
degrees. With positive-edge bit 1, the remaining cubes are

```text
B: 11       D: 01       C: *0.
```

They partition all four words of `{0,1}^2`. There is **no unoccupied word**,
whereas the proposed quarter-hole would require one. The actual remaining
weight is `1+1+1=3`, exactly the desired `3*2^(n-2)`; its encoding has
size `1+1+2=4`. The missing quarter appears entirely as exponent slack at
C, not as an existing hole.

This is not merely a poor placement of the two uniquely assigned bins.
Any bipartite edge partition of the remaining triangle into two nonempty
parts consists of a two-edge star and the remaining edge. Its active-bin
cubes always have dimensions 1,0,0 and fill the square. In this example
BD differs from each of BC,DC by more than lambda, so a narrow interval
cover cannot place BD together with either other edge in a bin.

The rational example's legality and exponents have exact integer checks
in `tools/one_saturated_high_probe.py`. For outgoing vectors u,v, put
`d=abs(det(u,v))` and `q=dot(u,v)`. Whenever q is negative, the checks give

```text
d+q > 0,   (d+q)^2 > 2*q^2.
```

Thus `d/(-q)>1+sqrt(2)=tan(3*pi/8)`, proving the angle is less than
`5*pi/8`. To certify exponents, sort the integer projective direction
representatives at each row. A positive-determinant adjacent gap is at
least `3*pi/4=2*lambda` exactly when its dot product q is negative and
`d<=-q`. Exactly one row gap, belonging to A, meets this threshold. Every
gap is below pi, hence below `3*lambda`, so this determines all scores.
These are exact arithmetic certificates with elementary geometric
implications, not kernel-checked Lean theorems.

## Boundary-bin quarter-faces can fail even after shrinking

The seven-center probe retains one center at `(-1,0)` and uses the two
other clusters from the already attributed binary/three-cluster
construction, with n=3, delta=3/4, outer scale .001, and scale ratio .01.
The full coordinates are in `verification/one-saturated-high-probe.json`.
The results are floating-point geometric evidence:

```text
lambda=48 degrees, beta=36 degrees, bin width=40 degrees;
maximum angle about129.0225 degrees <132 degrees;
k=(2,0,0,0,0,0,0), exactly one saturated anchor.
```

The remaining cube patterns are

```text
111, 101, 011, 001, 1*0, 0*0.
```

They again fill the entire cube. Their actual weight is6, precisely the
target `3*2^(3-2)`, while their encoded size is8. The two last cubes each
carry one unit of exponent slack.

More strongly, no quarter-face obtained by fixing the **first and last**
bin bits can be reserved while retaining each positive vertex weight:
all four such boundary-bit pairs occur in cubes already specifying both
boundary coordinates. A face with last bit1 contains a fixed-weight
singleton; a face with last bit0 is one of the entire cubes `1*0` or
`0*0`. Shrinking cannot move a vertex outside its original cube.

A quarter-face fixing the **middle and last** bits can be reserved. This
shows that a viable coordinate-selection argument cannot simply select
the two bins next to the anchor's missing direction interval.

## A valid local slack certificate

Since the ordinary cubes are disjoint, put

```text
H = 2^n - sum_v 2^e_v >= 0,
S_v = 2^e_v - 2^k_v >= 0.
```

Then

```text
sum_v 2^k_v = 2^n - H - sum_v S_v.
```

The claim `H+sum S_v >= 2^(n-2)` is exactly the desired remaining-weight
bound in different notation; this identity alone is not progress on its
general proof. The following **specific sufficient local premises** are
stronger and can be checked without knowing the total potential:

1. If exactly one center is saturated and some remaining row occupies
   only one corridor bin, then `e_v=n-1` but `k_v<=n-2`. Its single slack
   satisfies `S_v>=2^(n-2)`, proving the required remaining-weight bound.
   The rational four-center example has this certificate at C.
2. If n>=3 and two distinct remaining rows each occupy at most two bins
   and each has `k_v<=n-3`, their slacks each are at least `2^(n-3)`.
   Together they give the required quarter. The seven-center example
   has this certificate at the two apex-cluster centers.
3. More generally, for `1<=r<n`, a family of `2^(r-1)` distinct remaining
   rows each occupying at most r bins and satisfying `k_v<=n-r-1`
   contributes at least
   `2^(r-1)*2^(n-r-1)=2^(n-2)` total slack.

In the first item the exponent bound follows from non-saturation and the
already proved universal row bound `k_v<=n-1`. The later items require the
displayed stronger local exponent bounds. No claim is made that every
one-saturated configuration contains one of these certificates.

## A valid quarter-face reservation criterion

There is also a direct structural condition compatible with
`BinaryEncoding.sum_free_binary_coordinates_le`. Choose two distinct
coordinates p,q and a bit pair (b_p,b_q). Let F be the corresponding
quarter-face. A cube Q_v is compatible with F when it does not already
prescribe an opposing bit at p or q.

The following local premise suffices:

> Every cube compatible with F has at least one of p,q free, and satisfies
> `k_v<e_v`.

For a compatible cube, fix one free selected coordinate opposite to F.
Its resulting subcube has size `2^(e_v-1)>=2^k_v` and misses F. Incompatible
cubes already miss F. These subcubes remain pairwise disjoint. Adding F
as an additional cube to the disjoint-subcube count gives

```text
sum_v 2^k_v + 2^(n-2) <= 2^n.
```

This premise is noncircular: it only examines specified bits on a selected
coordinate pair and individual strict exponent slack. It is equivalent
to each Q_v retaining at least `2^k_v` words outside F. Indeed a compatible
cube with t free selected coordinates loses the fraction `2^(-t)` to F;
t=0 is impossible, and for t=1 or2 the surviving count admits an integer
power `2^k_v` exactly when `k_v<e_v`.

An initial probe of2670 legal random anchored configurations, with n=2,3,4,
found no failure for some coordinate pair. A further sweep of60 standard
retained-left-anchor three-cluster constructions used n=3..6, delta in
{.55,.65,.75,.85,.95}, and scale ratios {.002,.01,.03}. Of these52 were
strictly legal; every legal standard example admitted a reservable face.
The following modified construction nevertheless disproves universal
existence. These positive finite samples must not be promoted to a lemma.

## Exact counterexample for every coordinate pair

Set `lambda=atan(3/4)`, n=4, and
`delta=pi/lambda-4`, approximately .88203145. Take an anchor and two binary
clusters, all with integer coordinates:

```text
A=(-100000000,0).
Right base B=(100000000,0), independent binary offsets
  u0=(60000,50000), u1=(100,600), u2=(-3,5).
Top base C=(0,36000000), independent binary offsets
  v0=(10000,30100), v1=(-100,200).
```

Thus the set is `{A}` together with the eight points
`B+b0*u0+b1*u1+b2*u2` and the four points `C+c0*v0+c1*v1`, where all
coefficients are0 or1. The full coordinate list is saved in the probe
output. Its exponents are exactly `(3,0,0,0,0,0,0,0,0,0,0,0,0)`, so A is
the only saturated point, its weight is8, and the remaining weight is12.
The total20 attains `2^4+2^(4-2)`.

The fixed HIGH corridor has four equal bins. Its five boundary rays are
exactly proportional to

```text
(4,3), (1,3), (-7,24), (-307,249), (-3116,237).
```

The corresponding angles are `lambda`, `pi/2-lambda/2`, `pi-2lambda`,
`3pi/2-7lambda/2`, and `2pi-5lambda`. Every remaining chord lies strictly
inside one of these bins. Source/sink encoding gives the exact patterns

```text
Right: 1111,1101,1011,1001,0111,0101,0011,0001.
Top:   *110,1100,0010,*000.
```

Every quarter-face contains a **fixed singleton cube of positive weight**:

* A face that does not prescribe the last bit contains a right-cluster
  singleton with last bit1.
* A face prescribing last bit1 likewise contains a right singleton.
* A face prescribing last bit0 fixes just one other bit. The fixed top
  singleton words1100 and0010 have complementary first-three bits, so one
  of them belongs to that face.

Therefore no quarter-face on any coordinate pair can be reserved, even
after arbitrary shrinking of the original cubes. The obstruction is
combinatorial and does not depend on a near-boundary floating comparison.
There are two initially unoccupied words and two units of exponent slack;
they suffice for the numerical HIGH bound but cannot be assembled into
a coordinate quarter-face by this construction.

### Exact geometric certificates

The probe verifies all of the following using integers:

1. `(4+3i)^5=-3116-237i` and
   `(4+3i)^9=1721764-922077i`. Since `pi/6<lambda<pi/4`, the fifth-power
   sign implies `5lambda>pi` and the ninth-power sign implies
   `9lambda<2pi`. Hence `4<pi/lambda<5` and `delta>1/2`.
2. For every obtuse ordered triangle, with
   `d=abs(det(u,v))` and `q=dot(u,v)<0`, the integer inequality
   `4d+3q>0` holds. It gives `d/(-q)>3/4=tan(lambda)`, proving the angle
   is strictly below `pi-lambda`. The smallest integer margin is1100.
   The numerical maximum is140.7798 degrees, below143.1301 degrees.
3. Relative to A, every ray `(x,y)` has x positive, y nonnegative, and
   `527y<336x`. As `tan(beta)=336/527` for `beta=pi-4lambda`, all anchor
   rays lie in `[0,beta)`. One ray is0. The long wrap gap is therefore
   greater than `4lambda` and less than `5lambda`; all other anchor gaps
   are below lambda. This proves anchor exponent3.
4. At every other center, each consecutive cyclic gap has determinant d
   nonnegative and dot product q positive with `7d<24q`. Since
   `tan(2lambda)=24/7` and `2lambda<pi/2`, every such gap is below
   `2lambda`, proving all remaining exponents are0. The smallest integer
   margin `24q-7d` is48700.
5. The bin rays above follow from the rational half-angle ray `(3,1)`
   for `lambda/2`. Positive integer determinant comparisons establish
   the unique bin of every chord and hence all displayed code words.
6. All24 coordinate-pair/pattern choices meet a fixed singleton cube.

This is a mathematical counterexample supported by exact arithmetic and
the stated elementary angle identities. It is not a kernel-checked Lean
counterexample. It is stronger than the earlier floating seven-center
obstruction and decisively rules out the fixed-cover universal face lemma.

## Delivery and status

The probe verifies the rational examples' exact assertions, all examples'
bin words and margins, and all candidate quarter-faces. Output is in
`verification/one-saturated-high-probe.json`. The universal fixed-cover
quarter-face existence claim is false. Sparse-row slack certificates, a
different bin cover, or non-face reservations require new geometry. The
unconditional one-saturated HIGH capacity remains open.
