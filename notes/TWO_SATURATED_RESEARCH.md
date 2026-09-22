# Two saturated anchors: the fourth point supplies the extra loss

Date: 2026-09-22. Status: **the local claim is fully formalized in Lean,
with standard-only axiom closures**. This is not an arbitrary-size
capacity proof, and does not change the completion status in `STATUS.md`.

## Exact claim

Let `c : Fin s → Plane₂` satisfy `Section4Legality c lam`, with `s ≥ 4`,
`lam > 0`, and `n = floor(pi / lam) ≥ 2`. Fix the nonzero chart reference
and orientation required by `directionRow`. Suppose distinct centers A
and B have `rowDefect = 1`. Then:

1. Necessarily `n ≥ 3`.
2. Every other center P has row exponent at most `n − 3`.
3. Equivalently, its `rowDefect` is at least 3; the competitor note's
   deficit relative to the saturated exponent, `(n − 1) − exponent`, is
   at least 2.

The explicit `n ≥ 3` conclusion matters: writing only a natural-number
bound `exponent ≤ n − 3` would silently truncate the right side to zero
when `n = 2` and miss the actual impossibility in that strip.

No extra same-side or nesting assumption is part of the checked claim.
They follow from legality and the already proved saturated-angle bound.
The following derivation explains that implication. The actual geometric
connection is now formalized in `SaturatedNesting.lean`, including a
strict nested betweenness witness for four selected centers of an
arbitrary-size original configuration.

## 1. Saturated anchors make a narrow lens

Put `β = π − nλ`. The floor relation gives `0 ≤ β < λ`, and `n ≥ 2`
gives `λ ≤ π/2`, hence `β < π/2`.
`Induction.angle_le_pi_sub_of_saturation` bounds every angle at A and
every angle at B by β.

Apply a Euclidean similarity taking A to `(0,0)` and B to `(1,0)`.
For every other point P, define

```text
a_P = angle B A P,        b_P = angle A B P.
```

Both angles are at most β, so `0 < x_P < 1`. Every triangle is
nondegenerate: three distinct collinear points have an angle π, whereas
legality caps every angle by `π − λ < π`. In particular P is off AB,
and `a_P,b_P > 0`. The cap at P in triangle ABP gives

```text
a_P + b_P ≥ λ.                                      (1)
```

## 2. Every other point lies on the same side of AB

Take any two distinct remaining points C,D. If they were on opposite
sides, their rays at A make angle `a_C + a_D`, and those at B make
angle `b_C + b_D`. These sums are below π because every summand is
at most β and `2β < π`; thus they really are the unoriented angles,
not their complements. Saturation at A and B implies

```text
a_C + a_D ≤ β,       b_C + b_D ≤ β.
```

Adding (1) for C and D would give `2λ ≤ 2β < 2λ`, a contradiction.
Reflect across AB if necessary so all other points are above AB.

## 3. The triangles sharing AB are strictly nested

A and B are extreme points of any four-point subset: the other two
points have x-coordinates strictly between 0 and 1. There are no
collinear triples. Thus A,B,C,D either form a strictly convex
quadrilateral, or one of C,D is strictly inside the triangle formed
by the other three points.

In the convex case, the quadrilateral angles at A and B are each at
most β, and those at C and D are each at most `π − λ` by legality.
Their sum is at most

```text
2β + 2(π − λ) < 2π,
```

contradicting the quadrilateral angle sum. Therefore, after exchanging
C and D, C is strictly inside triangle ABD. Equivalently, there is E
strictly between A and B with C strictly between D and E. This is the
betweenness witness used by the checked lemmas below.

This classification uses actual planar geometry. The triangle sums and
per-triple inequalities in an abstract model alone do not justify it.

## 4. The inner point C loses three cells

The rays CA, CB, CD surround C. Their three circular gaps are all below
π, and so equal the three unoriented angles

```text
angle A C B,    angle A C D,    angle B C D.
```

They sum to `2π`. Passing from ray directions to unoriented line
directions gives, up to permutation, the three projective gaps

```text
π − angle A C B,    π − angle A C D,    π − angle B C D.
```

Each is at least λ by legality, and their sum is π. For
`f(g) = max(floor(g/λ) − 1, 0)`, their total score is therefore

```text
floor(g₁/λ) + floor(g₂/λ) + floor(g₃/λ) − 3 ≤ n − 3.
```

The same inequalities give `3λ ≤ π`, hence `n ≥ 3`. Thus two saturated
anchors are impossible in a legal configuration of at least four points
when `n = 2`.

## 5. The outer point D also loses three cells

Use the following exact notation:

```text
a = angle B A C,    b = angle A B C,
c = angle B A D,    d = angle A B D,
x = angle A D C,    y = angle C D B,
z = c + d.
```

Strict nesting gives `c > a`, `d > b`; the closed versions are enough
below. Equation (1) gives `a+b ≥ λ`. Saturation gives `c,d ≤ β`, so

```text
λ ≤ z ≤ 2β < 2λ.                                    (2)
```

The ray DC lies strictly inside the angle ADB. The three projective gaps
at D are therefore `x,y,z`, up to cyclic order, with

```text
x + y + z = π.                                      (3)
```

In triangle ACD, the angle at A is `c−a`; legality at C implies
`x + (c−a) ≥ λ`. Consequently

```text
x + z ≥ λ + a + d ≥ λ + a + b ≥ 2λ.                 (4)
```

The analogous triangle BCD gives `y + z ≥ 2λ`. In particular,
`x,y ≤ π−2λ`. Strict nesting gives the final bounds `x+z > 2λ` and
`y+z > 2λ`; the intermediate inequalities can attain equality.
Strictness is unnecessary for the floor argument.

By (2), `floor(z/λ)=1`, so `f(z)=0`.

- If `x,y ≥ λ`, then `floor(x/λ)+floor(y/λ) ≤ n−1`, using (3)
  and `z ≥ λ`. Subtracting the two occupied cells gives at most `n−3`.
- If one is below λ, it scores zero; the other is at most `π−2λ`,
  so its floor is at most `n−2` and its score at most `n−3`.
- If both score zero, the result follows from the already proved `n≥3`.

This includes the closed arithmetic boundary `z=λ`. No hidden strict
remainder assumption, generic-position perturbation, or strengthened
angle cap is used. The actual strict nesting gives `z>λ` here, but the
checked arithmetic accepts the weaker closed boundary.

## 6. Return to the full configuration

For every target P different from A,B, choose a fourth point Q. The
previous steps bound the three-direction row at both P and Q. Adding
any of the remaining directions only splits cyclic gaps. The established
`Deletion.gapScore_merge` gives

```text
f(u) + f(v) ≤ f(u+v)       for u,v ≥ 0,
```

so refinement cannot increase the score. This proves the claimed bound
for every full row. Equivalently, one can repeatedly use
`Deletion.rowScore_eraseIdx` while retaining the three selected
directions; the row score cannot decrease during deletion.

This is a local profile restriction. It does not bound the number or
total mass of the remaining smaller rows, so it does not prove the
arbitrary-size Kraft cap. In particular it does not revive the false
zero-saturation shortcut audited in `KRAFT_CRUX_AUDIT.md`.

## Checked Lean components

`Jsp000404/TwoSaturatedFour.lean` contains:

- `three_gapScore_add_three_le_of_ge`: three gaps at least λ give
  `score + 3 ≤ n`.
- `three_gapScore_add_three_le_of_outer`: (2), (3), (4), and `n≥3`
  give `score + 3 ≤ n`, including the boundary `z=λ`.
- `angle_sum_eq_two_pi_of_nested`: actual Euclidean betweenness
  `Sbtw A E B` and `Sbtw D C E` imply the angle sum around C is `2π`.
- `inner_supplement_gapScore_add_three_le`: the same actual geometry
  and its three legal angle caps give the inner score bound.
- `outer_nested_gapScore_add_three_le`: the actual nested geometry,
  anchor angles below λ, and the three legal angle caps at C give the
  outer score bound. Triangle sums and angle splits are derived inside
  Lean; they are not assumed as an abstract certificate.

Every theorem above is checked with standard axioms only. Project-wide
imports are left to the integration owner by this task.
Its direct check and axiom output are saved in
`verification/two-saturated-four-check.txt`.

## Follow-up: actual same-side and nesting now checked

`Jsp000404/SaturatedNesting.lean` proves the previously missing geometric
connection. Its principal endpoints are:

- `two_saturated_sSameSide`: any two other centers lie on the same
  strict side of the line through the saturated anchors.
- `two_saturated_not_crossing`: the alternative open diagonal segments
  cannot intersect.
- `saturated_anchor_outside_convexHull`: a saturated anchor is outside
  the convex hull of any collection of the other centers. The proof
  only needs acute angles at that anchor, not elsewhere.
- `two_saturated_nested`: for original saturated rows at i,j and any
  distinct other centers k,l, produces E with

  ```text
  Sbtw ℝ (c i) E (c j) ∧
    (Sbtw ℝ (c l) (c k) E ∨ Sbtw ℝ (c k) (c l) E).
  ```

The proof uses Radon's theorem to derive convex-hull membership from
four local angle caps totaling less than `2π`. It excludes the anchors
by their acute fans, then obtains the strict witness from a segment
decomposition of the triangle's convex hull. Legality-derived
noncollinearity excludes every boundary case.

The arbitrary-size wrapper restricts only actual geometry and angle
bounds to the selected four centers. It uses saturation of the original
full rows; it neither assumes nor needs saturation of a restricted row.
The six pairwise inequalities on i,j,k,l already imply at least four
centers. Its verification is recorded in
`verification/saturated-nesting-check.txt`.

## Follow-up: full original-row deficit now checked

`ThreeDirectionCapacity.lean` now identifies both nested three-gap
tuples for arbitrary orientations and nonzero chart references. Its
proof uses the three matched endpoint pairs and positive-gap complement
uniqueness, without a strengthened angle or chart premise.

`TwoSaturatedDeficit.lean` completes the original-row theorem:

- `rowScore_le_sorted_three_directions` transports subpermutation of
  center indices through the direction map before sorting. This handles
  multiplicities without assuming injectivity of the direction map.
- `exists_fourth_center` selects the necessary fourth center from `s≥4`.
- `three_le_of_two_saturated_four_centers` proves `n≥3` directly from
  actual nested geometry and legality.
- `rowScore_add_three_le_of_two_saturated_four_centers` proves the
  original target row has `rowScore + 3 ≤ n` for four selected indices.
- `rowScore_add_three_le_of_two_saturated` gives the requested arbitrary
  `s≥4` local bound for every center other than the two saturated anchors.
- `rowDefect_ge_three_of_two_saturated` concludes `rowDefect ≥ 3`, using
  the actual cell bound to handle natural subtraction correctly.

The final two theorem statements assume only original
`Section4Legality`, `λ>0`, `n=floor(π/λ)≥2`, a nonzero chart reference,
`s≥4`, the three selected indices being distinct, and saturation of the
two original anchor rows. No nesting, gap identity, row-restriction,
capacity, or progress certificate remains as an extra hypothesis.

All six printed endpoints in `TwoSaturatedDeficit.lean` have axiom set
`[propext, Classical.choice, Quot.sound]`. The final direct check is
recorded in `verification/two-saturated-deficit-check.txt`.

This settles the local profile restriction, not the global mass of all
smaller rows. The existing unconditional lower root still has its
previously documented open global obligation.
No numerical experiment is used as proof here.
