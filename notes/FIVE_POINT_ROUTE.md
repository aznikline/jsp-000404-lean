# Five-point lower bound via separated inward bisectors

2026-09-22. Geometry, circular counting, and the lower-bound assembly are
proved in `AcuteFanPacking`, `CircleSeparation`, and `SmallAngleLower`.
The exact original theorem is complete for N=3 through 8, and both
second-strip capacity regimes are proved. The proof-plan sections below
record how the completed argument was obtained; the final section lists
the integrated exports. The arbitrary-N root remains open for N>=9.

## Why this avoids the polygon API gap

The available Mathlib development has `Convex.radon_partition`, the
Carathéodory theorem `convexHull_eq_union`, triangle angle sums, and the
usual oriented-angle / strict-side APIs. I did not find a finite convex
polygon ordering-and-angle-sum theorem in this checkout. Constructing a
convex pentagon through Radon would require additional finite order-type
and angle-splitting work.

The following route proves the needed angular bound without introducing
polygon topology, a convex-order hypothesis, or any capacity premise.

## Proved geometric lemmas

### A common ray window below120 degrees

`exists_ray_window_of_three_mul_lt_two_pi` takes a finite nonempty family
of nonzero planar vectors u, `0<=alpha`, `3alpha<2pi`, and pairwise angles
at most alpha. It returns a nonzero reference e and representatives
`theta_i in [0,alpha]` of all oriented ray angles from e.

Choose one vector u0 and write
`a_i=(o.oangle u0 u_i).toReal`, so `a_i in [-alpha,alpha]`. Choose a
minimal representative a_j. The positive difference d=a_i-a_j is at most
2alpha. If d>pi, the angle between u_j and u_i is `2pi-d`, which exceeds
alpha because `3alpha<2pi`. This contradicts the pairwise cap. Thus
d<=pi, its angle is exactly d, and d<=alpha.

This is the existing narrow-window argument with its wrap case proved,
extending the range from alpha<pi/2 to the sharp alpha<2pi/3 threshold.

### Each window gives an inward bisector

`exists_inward_bisector_of_ray_window` rotates e by alpha/2. The resulting
nonzero vector m makes angle at most alpha/2 with every vector in the
window. It uses the existing `angle_eq_abs_of_half_plane_chart` directly.

### Actual centers give separated bisectors

The exported interface is:

```lean
theorem exists_separated_inward_bisectors
    (o : Orientation ℝ Plane₂ (Fin 2)) {s : ℕ} (hs : 2 ≤ s)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    {alpha : ℝ} (halpha : 0 ≤ alpha) (hsmall : 3*alpha < 2*Real.pi)
    (hcap : ∀ i j k : Fin s, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ alpha) :
    ∃ m : Fin s → Plane₂, (∀ i, m i ≠ 0) ∧
      ∀ i j, i ≠ j →
        Real.pi-alpha ≤ InnerProductGeometry.angle (m i) (m j)
```

At i, the chord `c_j-c_i` lies within alpha/2 of m_i. At j, its negative
lies within alpha/2 of m_j. Angle negation and the angle triangle
inequality therefore give `angle(m_i,m_j)>=pi-alpha`.

All three theorem axiom closures are exactly
`[propext, Classical.choice, Quot.sound]`. No custom axiom, sorry, five-point
bound, or potential premise enters these results.

## Finite circle count (now proved)

For five nonzero planar vectors with pairwise angles at least d>0, prove
`5d<=2pi`. Sort oriented representatives `a_i in (-pi,pi]`. They are
distinct because a repeated representative would give angle0. The four
successive differences and the wrap difference sum to2pi. Each is at
least the smaller unoriented angle between its endpoints and hence at
least d.

A useful tiny helper is:

```text
u,v nonzero, 0<=t, o.oangle u v = (t : Real.Angle)
  ==> angle u v <= t.
```

For t>=pi this follows from `angle_le_pi`; for t<pi it follows from
`Real.Angle.toReal_coe_eq_self_iff` and the absolute-value angle formula.
The wrap case only needs `Real.Angle.coe_two_pi`.

The root can reuse the current sorted-list/gap summation infrastructure
by mapping normal representatives to `(pi-a_i)/2 in [0,pi)`; alternatively
a five-element sorted list has only four ordinary gaps plus one wrap,
so their telescoping identity needs no general polygon theorem.

## Intended unconditional consequence

If all angles of five actual points are at most alpha<3pi/5, then
`3alpha<2pi`, so the proved geometry supplies bisectors separated by
`pi-alpha>2pi/5`. The circle count would give
`5(pi-alpha)<=2pi`, contradiction.

For the no-saturation n=2 LOW subcase, `lambda>2pi/5` implies
`alpha=pi-lambda<3pi/5`. The five-point contradiction bounds the number
of centers by4; non-saturation and the universal row bound force every
exponent to0. Thus the potential is at most4. The existing saturated LOW
theorem treats the complementary case. This closes a genuine boundary
once the circle count and assembly are proved; it is not the arbitrary-n
capacity theorem.

## Concrete APIs used

* `Real.Angle.toReal_coe_eq_self_sub_two_pi_iff` and
  `Real.Angle.toReal_coe_eq_self_iff`:
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Angle.lean`.
* `o.angle_eq_abs_oangle_toReal`, `o.oangle_sub_left`:
  `Mathlib/Geometry/Euclidean/Angle/Oriented/Basic.lean`.
* `o.oangle_rotation_self_right`:
  `Mathlib/Geometry/Euclidean/Angle/Oriented/Rotation.lean`.
* `InnerProductGeometry.angle_neg_right` and
  `InnerProductGeometry.angle_le_angle_add_angle`.
* Local `angle_eq_abs_of_half_plane_chart` in `ConeCorridor.lean`.

Only the new `AcuteFanPacking.lean` module was added for this implementation;
existing geometry modules and root imports were not edited by this agent.

## Independent semantic review of CircleSeparation

The root's subsequently added `CircleSeparation.lean` was reviewed against
the mathematical argument above. No semantic defect was found. Its
standard-only build was reported by the root; this review concerns the
actual statements and proof structure, not a new build claim.

* `abs_angle_rep_le_both` bounds the shorter circular distance by both
  the raw representative difference and its complement. The boundary
  inputs0, plus/minus pi, and plus/minus2pi are covered correctly.
* The raw signed representatives lie in `(-pi,pi]`, so their differences
  satisfy the required absolute bound2pi. The oriented-angle subtraction
  identity is applied with all three needed nonzero-vector witnesses.
* The raw list includes every index, including repeated direction values.
  `Pairwise R` is derived from distinct indices and transported through
  sorting using the symmetry of R. No deduplication or cardinality loss
  occurs. Repeated directions force gamma<=0; the theorem permits that
  harmless case rather than silently assuming direction injectivity.
* `separated_list_span` charges exactly `length-1` ordinary gaps. The
  head/last complementary inequality supplies exactly one wrap gap.
* For s=2 the two terms give `2gamma<=2pi`, including equality for opposite
  directions. Repeated or coincident directions are also handled. There
  is no unsupported s=1 extrapolation.

The proposed `SmallAngleLower` inference is also mathematically sound.
For s>=3, suppose every distinct-triple angle is below beta, with
`0<=beta<=2pi/3` and `2pi<=s(pi-beta)`. The finite distinct-triple family
is nonempty and has an attained maximum alpha>=0. Thus alpha<beta and
`3alpha<2pi`, even at the endpoint beta=2pi/3. The proved bisectors and
circle count give

```text
s(pi-alpha) <= 2pi <= s(pi-beta),
```

contradicting alpha<beta and s>0. An implementation using a finite maximum
must retain attainment (or a finite uniform strict bound), rather than
substituting beta directly into the strict120-degree window theorem.

Choosing beta=3pi/5 for s=5 and beta=2pi/3 for s=6,7,8 yields the intended
lower constants. Combined with the already proved upper construction,
those would establish the exact N=5..8 values. The bisector method does
not establish the stronger formula needed starting at N=9, because that
target exceeds the120-degree ray-window threshold.
# Completed lower-bound assembly

`CircleSeparation.circle_separation_bound` and the actual inward-bisector
construction are now combined in `SmallAngleLower`. Maximizing over the
finite set of distinct triples supplies a strict common angle cap whenever
the target lower bound is assumed false. This handles the 120-degree
endpoint without assuming a strict gap at that endpoint.

`sendov_lower_five_to_eight` proves the original point-list lower statement
for N=5 through 8. `sendov_lower_le_eight` joins the earlier N=3,4 results,
and `sendov_alpha_eq_le_eight` combines them with the existing all-N upper
construction to prove exact equality of the genuine extremal quantity.
All four final exports have only standard Lean axioms. The general lower
root now branches to this result for N<=8; its remaining open range is N>=9.
