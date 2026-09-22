# One saturated HIGH anchor: separate covers for two groups

2026-09-22. Bounded analytic exploration. **No unconditional
one-saturated HIGH bound is proved here.** This note was written after
reading the exact thirteen-point obstruction in
`ONE_SATURATED_HIGH_RESEARCH.md`; it does not reuse the falsified fixed
uniform-grid quarter-face claim.

There are two concrete outcomes:

1. A simple geometry-only two-group split is sufficient, but its
   universal existence is disproved by a small exact integer example.
2. Separate, adaptive angular covers give an explicit certificate for
   the thirteen-point obstruction itself. A broader angular-prefix
   version survives the bounded probes below, but its existence for
   arbitrary actual configurations remains unproved.

## A sound simple split, and its exact limitation

Write

```text
π/λ = n+δ,    β = δλ,    1/2 ≤ δ < 1,
α = λ−β = (1−δ)λ.
```

Let A be the unique saturated center, and use its actual ray chart.
Suppose the remaining centers can be partitioned into G and H such that:

- G lies in an anchor-ray interval of width γ<α.
- Some B in G sees A together with every point in H in a common ray
  interval of width strictly less than λ.

The first group fits into `n−1` angular bins: after rotating to the
first ray of G, all its chord directions lie in
`[λ, π−λ+γ]`, of width

```text
π−2λ+γ < (n−1)λ.
```

Keeping A and G only can increase original row scores, so the usual
anchored row and empty-bin argument bounds G's original weight by
`2^(n−1)`.

For H, use A and B as two retained boundary anchors. The two-anchor
nesting argument only needs a common fan bound strictly below λ at
both anchors, and an acute fan. Since λ≤π/2, these follow here; B need
not be saturated and its fan bound need not equal β. A common innermost
point gives facing minima whose sum is at least λ. Their corridor has
length at most `π−3λ < (n−2)λ`, and the exterior row gap has size below
`2λ`, hence score zero. The two-anchor bin argument then gives H's
original weight at most `2^(n−2)`.

Small H should be treated directly: an empty group contributes zero;
a singleton's triangle with A,B has exponent at most n−2. With at least
two points in H, the inner triangle geometry forces n≥3. A zero-length
chord interval can be enlarged slightly before choosing bins; it should
not be silently divided into zero-width bins.

This is a sufficient construction, not a proof that the partition exists.
In fact the displayed partition can fail.

### Exact four-point counterexample to existence of that split

Take

```text
λ = atan(3/4),    n=4,    δ≈0.88203145,
A=(0,0), B=(10,0), C=(7,2), D=(9,5).
```

The configuration is strictly legal, and its exact row exponents are
`(3,1,1,1)`. Thus A is uniquely saturated. The three anchor-ray angles
are approximately `0°,15.9454°,29.0546°`, while `α≈4.34949°`.
Every pair of these rays differs by more than α, so any nonempty G of
width below α must be a singleton. For each possible second anchor,
the fan containing A and the other two remaining points is too wide:

| Second anchor | Maximum angle in that fan |
|---|---:|
| B | 78.6901° |
| C | 139.6355° |
| D | 72.2553° |

All exceed `λ≈36.8699°`. Therefore no such G,H,B construction exists.
The desired capacity is not contradicted: the actual remaining weight
is only 6, below the target 12.

The new probe checks this example using integers:

- For every obtuse ordered triangle, `4|det|+3 dot>0`, certifying the
  cap `π−λ`; the minimum integer margin is 8.
- For each cyclic row gap, comparisons with the integer rays for
  λ,2λ,3λ,4λ determine its floor exactly. Those rays are
  `(4,3),(7,24),(-44,117),(-527,336)`; the minimum nonzero comparison
  magnitude is 8. The resulting exponents are exactly `(3,1,1,1)`.
- The ray for α is `(3116,237)`. Every pair of anchor rays has
  `3116|det|−237 dot>0`; the minimum margin is 35671.
- A fan angle above λ is witnessed at each possible second anchor by
  `4|det|−3 dot>0`, with witness margins 170,131,152.

The strip identity and δ>1/2 use the same exact complex-power argument
for `λ=atan(3/4)` already documented for the thirteen-point example.
These are exact arithmetic certificates with elementary geometric
interpretations, not Lean theorems.

## A more flexible, local two-cover certificate

Let `k_v` be each original full-row exponent. Partition the remaining
centers into G,H. For a group X with assigned dimension m, require:

1. Choose a reference chart for X and at most m disjoint angular
   intervals, each of width strictly less than λ.
2. Every line between distinct points of X belongs to exactly one
   interval.
3. At each v in X, let `a_X(v)` count the intervals containing a line
   from v to another point of X. Require the individual bound
   `k_v ≤ m−a_X(v)`.

Then the narrow-cone argument makes each interval graph bipartite.
Every pair of vertices is separated on its uniquely assigned interval,
so the binary encoding cubes are disjoint. Condition 3 gives

```text
sum_(v in X) 2^k_v ≤ 2^m.
```

Taking `m_G=n−1` and `m_H=n−2` proves the desired remaining bound.
The two groups may have different references and different interval
boundaries. The intervals need not cover all the empty angular gaps
between occupied directions, and unused coordinates are allowed.

This certificate is concrete and local. It examines actual edge
directions and each original exponent; it does not assume a total mass
inequality. Nevertheless, proving its existence is a new geometric
obligation. Defining a predicate that it exists would not resolve that
obligation.

### The thirteen-point obstruction has an exact two-cover certificate

Use the two original binary clusters from
`ONE_SATURATED_HIGH_RESEARCH.md`:

- The right cluster has 8 points, generated by three offsets.
- The top cluster has 4 points, generated by two offsets.

Give the right cluster three direction intervals and the top cluster
two. Assign a chord to its first differing binary offset. Each family
of chord directions lies in an interval strictly narrower than λ.
For every pair of oriented integer chord vectors in one family, the
probe checks

```text
dot>0,    3 dot − 4|det| > 0.
```

The minimum margins are 102 for the right cluster and 150000 for the
top cluster. All oriented vectors have positive y-coordinate, so these
pairwise acute-angle comparisons give an ordinary angular interval.
Each vertex is incident to every coordinate of its own cluster, and
all original exponents are zero. Thus the two group counts are exactly
8 and 4, proving 12 by separate covers, even though every fixed
coordinate quarter-face in the original uniform encoding is blocked.

This is an explicit certificate for that example, not evidence that
the original fixed-cover face claim can be repaired.

## Bounded search and remaining question

The probe tests the following more specific unproved search target:

> Sort the remaining vertices by their anchor-ray angle. Some prefix
> split, with either side assigned the larger dimension, admits the
> separate-cover certificate above.

Within each group, the search considers every cyclic cut of its edge
directions and partitions the sorted directions into contiguous
blocks of width below λ. It tracks each vertex's active-block count
against `m−k_v`, rather than checking the total weight. Equal directions
are not split across blocks. Blocks containing one direction can be
enlarged slightly; they do not represent zero-width bins in the proof.

With seed 404901, no failure was found in:

- The exact four-point example, the exact thirteen-point example, and
  the seven-point retained-anchor construction.
- 1188 accepted random legal uniquely-saturated configurations for
  n=2,3,4,5. These mostly have only two or three nonanchor centers;
  this is weak coverage of the difficult large cases.
- 434 legal uniquely-saturated subsets of retained-anchor binary
  constructions, with n=3,4,5 and 3 through 12 remaining centers.
  These provide denser examples but retain a strongly structured origin.

These adaptive-cover and random results use floating-point arithmetic
and are **discovery evidence only**. No universal partition theorem,
slack theorem, or capacity theorem follows from them.

The actionable open step is to derive an angular-prefix split and its
individual active-bin inequalities from actual geometry, or find a
legal counterexample. The simple narrow-subcone/two-anchor construction
above is insufficient, so any proof must also handle configurations
whose capacity comes from local exponent slack without that geometry.

Reproduce with `python3 tools/one_saturated_high_geometry_probe.py`.
The script prints its exact certificates and bounded-search summaries;
it changes no existing data or Lean source files.
