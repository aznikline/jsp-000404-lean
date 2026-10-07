# F17 mandatory selection: bounded audit and a positive-observer supply

Status: PAPER plus one new SOURCE_ONLY leaf, 2026-10-08. No Lean, Git,
solver enumeration, quota operation or old frozen-source edit was run for
this task. The global F17 exclusion and mandatory selector remain OPEN.

The checked `ActualN4LowCriticalReduction` (final source `d0fdb060…632968`)
now derives potential 17 internally from every original n4 LOW cap16
minimum-counter Model. The checked F18 assembly is consumed only in that
reduction. It does not classify potential-16 restrictions. Let
`rho=2*pi/9 < lambda <= pi/4` throughout, and keep all scores, weights and
minimum-cardinality assumptions on the original actual configuration.

## Controls before the new claim

The regular unit-circle heptagon at `lambda=pi/4` has potential seven,
all scores zero, all single incoming gains zero, and the closed
single-zero deletion boundary. It has no light target, so the new
positive-observer/light-target claim below is vacuous there. It remains
an essential countercontrol against deriving a mass-17 selector from
zero gains and the closed boundary alone: deleting two adjacent vertices
creates two unit emitters, which is legitimate at potential seven.

The existing actual potential-16 control at `lambda=7*pi/30` is

`B=(0,-1000), U=(-50,0), V=(-49,1), W=(49,1), Z=(50,0)`.

Its original scores are `(3,1,1,1,1)`. Deleting the light point U raises
the positive observer V from score one to two. Thus the new conclusion
cannot be promoted to a theorem for arbitrary legal configurations or
for potential 16. At V, the original projective directions are

`0, pi/4, pi/2+atan(49/1001), pi-atan(1/99)`.

The original gap from the third to the fourth direction is greater than
`2*lambda=7*pi/15`; use `atan(x)<x` and
`49/1001+1/99 < pi/30`. Deleting U merges the first two gaps into
`pi/2+atan(49/1001)`, also between `2*lambda` and `3*lambda`, while the
old scoring gap remains. The new score is exactly two. A separate tiny
double-precision recomputation reproduced all five original scores and
the four symmetric light-deletion gains; it was a control, not a formal
certificate or an F17 Model.

## The complete 24 small histograms

Write H,L,Z for original scores two, one and zero. Existing actual
nonsaturation and heavy-count arguments give

`4*H+2*L+Z=17`, `H<=3`, `Z>=1` odd, `N=H+L+Z>=6`.

There are exactly 24 nonnegative integer profiles. Each table entry is
`(L,Z,N)`; every listed profile is a residual numerical possibility, not
a claim that an actual Model realizing it exists.

| H | All possible `(L,Z,N)` |
|---|---|
| 0 | (0,17,17), (1,15,16), (2,13,15), (3,11,14), (4,9,13), (5,7,12), (6,5,11), (7,3,10), (8,1,9) |
| 1 | (0,13,14), (1,11,13), (2,9,12), (3,7,11), (4,5,10), (5,3,9), (6,1,8) |
| 2 | (0,9,11), (1,7,10), (2,5,9), (3,3,8), (4,1,7) |
| 3 | (0,5,8), (1,3,7), (2,1,6) |

In particular a two-zero selector has no input in the four Z=1 branches
`(H,L,N)=(0,8,9),(1,6,8),(2,4,7),(3,2,6)`. It cannot be a complete route
without a separate exclusion of those branches. At the other extreme,
the all-zero N=17 branch has at least nine original interior points
because the original hull has at most eight vertices. No argument in
this note excludes that branch.

## A new actual supply using the original mass 17

The owned new leaf is
`Jsp000404/ActualF17PositiveObserverZeroGain.lean`, with sole export
`Jsp404.ActualF17PositiveObserverZeroGain.actual_positive_observer_light_target_gain_zero`.
It is SOURCE_ONLY and has not been compiled. Its inputs are the original
n4 LOW Model, a target q with original score one, a distinct observer i
with positive original score, and a nonzero direction reference. The
original potential value and actual single-deletion cap are produced
internally. No gain, budget or deletion-cap certificate is a caller input.

The proof is short and keeps the original Model throughout:

1. The checked critical reduction gives original potential 17.
2. The checked LOW small-cardinality theorem supplies enough original
   points for the actual single-deletion cap. This is LOW cap16, not HIGH20.
3. Removing q of weight two leaves original retained mass fifteen.
4. Original minimum counter-cardinality caps the actual deleted
   configuration at sixteen, so its weighted expense is at most one.
5. Any positive original observer has weight at least two. Its positive
   gain would cost at least two, which is impossible.

Hence every original positive observer has actual gain zero when deleting
an original light target. An original zero observer may gain one. The
claim does not assert that light-target incoming gains are globally zero.
Deletion of an original zero target already has globally zero incoming
gains by the checked original critical form. Heavy-observer outgoing-zero
facts remain a separate established supply.

## Consequences for all four Z=1 branches

The following are PAPER consequences of the new leaf and the checked
actual score-one partition producer, not new compiled exports. They use
the general actual partition, not the F18 canonical weighted producer.
Let z be the unique original zero point, and let p be an original
interior point of original score one. Its three actual classes partition
the original indices other than p and have original weight sum fifteen.

A singleton class emits at p. Its unique member cannot be zero, because
zero-target incoming gains vanish. It cannot be light, by the new
positive-observer/light-target supply. It may be heavy, with weight four.
Any class with at least two members and without z has weight at least
four. A class containing z has weight at least three. Thus

* each class has weight at least three;
* at most one class can use the lower value three;
* every pair of classes has total weight at least seven;
* every individual class has weight at most eight.

The value three is essential. A class consisting of z and one light
member has weight three and is not excluded by the available premises.
Replacing these bounds by the F18 lower bound four would be an error.

Now let p and q be distinct original interior score-one points. Suppose q
is in p's apex. Every member r of p's other two classes has angle at p
at least `3*lambda` from q. If r and p were in different classes at q,
the angle at q would be at least `2*lambda`, contradicting the actual
triangle angle sum because `5*lambda>pi`. Therefore p and both of its
nonapex classes lie in one class at q. Their mass is at least
`2+7=9`, contradicting the upper bound eight. This proves mutual
nonapex for score-one interior points in the Z=1 subdomain.

Their apexes are pairwise disjoint: a common member would give two
actual angles at least `3*lambda` in the same triangle. Every member of
one such apex is an original hull point, except possibly z. Indeed a
heavy member is already original hull, and another interior score-one
member was just excluded. At most one apex can contain z. The possibility
that z itself is original interior has not been discarded.

There is a further PAPER nonacute-heavy exclusion in this subdomain.
If a nonacute heavy h were in p's apex, actual triangle sums force p
and both nonapex classes into the same physical clump at h. Their mass
is at least nine. The checked heavy-clump producer gives opposite-clump
weight at least five at F17, whereas all original points other than h
have total weight thirteen. The inequality `9+5>13` is impossible.
Thus an apex heavy in the Z=1 subdomain must be HA. This does not prove
that an apex contains any heavy.

For completeness, a separate mass calculation extends the reviewed HO
alignment geometry to general F17 profiles: HO cannot coexist with a
different nonacute heavy. The first heavy's far clump has weight at
least five. Its actual HO angle at least `3*lambda` forces that clump and
the first heavy (weight four) into one clump of the second heavy.
That clump has weight at least nine and its opposite at least five,
exceeding the second heavy's original others mass thirteen. This is
PAPER here; it does not exclude a sole HO, an HA-heavy profile, or any
all-zero profile.

## What the closed boundary does and does not provide

In an original fixed-cardinality F17 maximum, an original zero source
after deleting one original zero target has every actual projective gap
at most `2*rho`, with equality allowed. For two original zero deletions,
positive original observers retain their scores; the actual outside gap
of an original hull positive observer with old outside score t is at
most `(t+2)*rho` under the original scale plateau. A zero observer can
grow by one; its twice-deleted outside gap is strictly below `3*lambda`
and, after passing the maximum plateau argument through that gain bound,
at most `3*rho`. Two current-scale boundary events cannot occur for one
target pair. None of these statements asserts a score at rho or replaces
a closed bound by a strict bound.

Two proposed short geometric inferences were rejected in this audit.
First, three twisted runs and small total run width do not put each run
below `lambda/2`; only one of the three has that small width. Second,
`projective flip gap<=2*rho` does not imply that the physical gaps between
run cones exceed a right angle. Converting the flip gap to the empty
physical gap also subtracts the widths of both adjoining runs. Omitting
those widths would create a false support argument. Nor can an original
interior exposed by deletion be relabeled an original hull vertex.

## Exact unresolved selection bridge

For Z>=3 the original two-zero budget still supplies a concrete sufficient
actual target: choose two original zero targets so that either a positive
surviving observer actually grows, or two distinct zero surviving
observers actually grow. The checked ledger then contradicts expense at
most one. The existing outside-gap event consumers give specific angle
versions at retained original hull observers; no producer of such a pair
is known here. Interior rays can shield the boundary shrinkage, and
original hull-zero points need not occur in the needed multiplicity.

A broader geometric target would allow deleting a nonempty set D of
original zeros while retaining at least three points. If at least |D|
distinct retained original zero observers are actual hull vertices of
that restriction and each has a retained ray cone of width at most
`pi-2*lambda`, each gains at least one. This exceeds the original
expense budget `|D|-1`. The observers may be newly exposed original
interiors: their hull status must be produced in the actual restriction,
not asserted for the original cloud. This is an explicit sufficient
geometric predicate, not an established existence theorem. No D or
collection of such observers is constructed by this note.

The new zero-gain leaf therefore supplies genuine original F17 information
and the Z=1 consequences are implementable weighted geometry, but neither
settles the four Z=1 cases nor the other twenty profiles. In particular
the all-zero N=17 mandatory selector remains open. No deformation of an
actual cloud has been assumed to remain legal or to raise potential, and
the vacuous pure-original-interior separated-block route is not reused.
