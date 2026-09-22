# Low-regime interval-cover route

The one-saturated LOW capacity case is now proved for arbitrary center
count, with standard Lean axioms. The complete general capacity theorem
still needs the zero-saturation LOW case and the HIGH cases.

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

## Completed geometric assembly

1. `AnchoredRows.anchored_rowScore_eq_linear` identifies the actual
   cyclic row with the linear anchored row, including repeated
   directions. The anchor precedes all remaining lines.
2. `BinGraphs.directionBinGraph_row_weighted_bound` constructs unique
   direction bins and their two-colorings from the actual angle cap.
   Occupied-bin counts equal active graph-coordinate counts. With
   m=n-1, the remaining vertices have total weight at most 2^(n-1).
3. `ChartInvariance.potential_directionRows_reference_eq` proves the
   exact original potential is independent of the nonzero reference.
   Adding the anchor weight gives
   `OneSaturatedLow.potential_le_two_pow_of_saturated` in that original
   chart. Its hypotheses are legality, the floor/LOW relations, n>=2,
   at least two centers and an actual saturated row; there is no
   certificate or capacity hypothesis. `rest_kraft_le_half_of_saturated`
   gives the equivalent normalized remaining-mass bound <=1/2.

After this case, the zero-saturation case and the high
regime still need global arguments. In particular the high-regime
zero-saturation mass can be 5/4, as checked in `PentagonPacking.lean`.
The new competitor update gives local three-term constraints, not the
remaining bound on all terms.
