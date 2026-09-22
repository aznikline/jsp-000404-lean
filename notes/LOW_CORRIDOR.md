# Low-regime interval-cover route

The results below are proved with standard Lean axioms. They are pieces
of the one-saturated low case, not a completed general capacity theorem.

## Geometry supplied by saturation

`ConeCorridor.saturated_ray_window` constructs a nonzero reference vector
and actual oriented coordinates for all rays from the saturated center.
The window has width at most beta = pi - n lambda. It is obtained by
minimizing signed angles relative to one of the rays; no ray-window
hypothesis is added to the geometric model.

For a chord X Y between two other centers, the angle cap at X bounds
its direction away from the anchor ray at X. The cap at Y bounds the
other side. `chord_in_corridor` gives

```text
lambda <= projective_direction(XY) <= pi - lambda + beta.
```

In the low regime beta < lambda/2. `saturated_low_corridor` consequently
places every non-anchor line in the fixed interval
[lambda, pi-lambda/2] and the anchor rays in [0,lambda/2].

`low_corridor_grid_width` proves that this interval has positive length
and that dividing it into n-1 equal pieces gives widths strictly between
zero and lambda. This includes the first later strip n = 2.

## Exact local counting

`IntervalPacking.linearGapScore` sums the floor-minus-one score along
a linearly ordered row between two anchor endpoints.

`linearGapScore_le_empty_of_interval` constructs uniform bin indices
and proves that the score is at most the number of unoccupied bins.
It includes repeated directions, repeated bin indices and exact right
endpoints. The two anchor margins may be as large as lambda; every bin
must be strictly narrower than lambda.

`weighted_interval_packing` then uses the attributed binary-subcube
counting theorem: pairwise separating bits and the local empty-coordinate
bound imply total weight at most 2^m.

## Connections still required

1. Identify the actual cyclic row in the constructed reference chart
   with the linear anchored row. The anchor direction precedes all
   non-anchor directions in this chart. Match the occupied-bin count
   with the active coordinates of the edge graphs.
2. Construct the uniquely assigned bin graphs and their two-colorings
   from the actual angle cap, then apply the weighted bound with m=n-1.
   Existing cone-coloring lemmas supply the geometric mechanism, but
   these data are not yet assembled here.
3. Add the saturated center's own bound 2^(n-1). A direct point-count
   proof may use the constructed reference vector. A statement about
   the potential in an arbitrary original reference chart additionally
   requires chart invariance; that assertion is not silently assumed.

Even after this case closes, the zero-saturation case and the high
regime still need global arguments. In particular the high-regime
zero-saturation mass can be 5/4, as checked in `PentagonPacking.lean`.
The new competitor update gives local three-term constraints, not the
remaining bound on all terms.
