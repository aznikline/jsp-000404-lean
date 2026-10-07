# Original weighted F17 zero-deletion boundary

2026-10-07 UTC: **READY — genuine strict and normal compiler PASS.**
New source: `Jsp000404/ActualF17ZeroDeletionBoundary.lean`.
No previous PASS source or definition was changed; no Git command was run.
The first whole-source strict run (`--trust=0 -M8000`) and the first genuine
own-target Lake build exited 0 in 16.571 and 20.498 seconds. Both printed
declarations use exactly `propext`, `Classical.choice`, and `Quot.sound`.
Own warning counts are zero; inherited normal-build warnings are counted
separately in the compiler receipt. Neither the 8 GiB nor 180 s guard fired.

## Inputs and exact conclusion

The final LOW interface retains the original
`ActualMinimalBandCounterexample.FixedCardModel` at cap 16 and attained
potential 17, with `rho=pi/(4+1/2)=2*pi/9`, `rho<lambda<=pi/4`, actual
original points `c : Fin (s+1) -> Plane₂`, and `3<=s`. It also takes the
original zero-score target `q` and the original zero-score surviving source
`q.succAbove i`. Other original rows may have positive scores; the theorem
is not restricted to an all-flat model.

Every actual cyclic gap in the original geometric deletion row
`directionRow o e (c composed with q.succAbove) i` is bounded by

`g <= 2*rho = 4*pi/9`.

The source is the surviving center `q.succAbove i`, and the deleted target
is `q`. The original point coordinates and reference are fixed throughout.
The caller supplies no post-deletion capacity, zero gain, or desired gap
bound.

## Open-band derivation

The first checked public export,
`actual_zero_delete_row_zero_at_smaller_scale`, is a generic-band helper for
the same weighted cap-16/potential-17 fixed-card model. For every
`rho<lambda'<=lambda`:

1. `actual_fixed_card_model_of_smaller_scale` keeps the same original point
   set, the same minimum-counter-cardinality property and the same attained
   fixed-card potential 17. Its proof uses the original same-card maximum.
2. `actual_fixed_card_score_plateau` preserves both original zero scores,
   as well as the other original whole-row scores.
3. The zero target is a minimum-score point, and its unit weight divides
   the explicit cap 16. `actual_delete_potential_le_cap` obtains the actual
   deletion cap from the **original** smaller-scale model's `minimum_card`.
4. `actual_minimum_delete_normal_form` gives the actual retained-row score
   equality. The originally zero source row therefore has score zero after
   deleting `q`, at this same strictly interior scale `lambda'`.

No critical, minimum-cardinality, or maximality property is assumed for the
deleted configuration. All such uses stay on the original model, with its
genuine same-card maximum retained rather than omitted.

## Closed estimate and existing API boundary

The existing `BandMaximumScorePlateau` closed `2*rho` theorem requires a
whole flat band maximizer. The existing `BandMaximumDeletionBoundary`
all-deleted-row estimate gives only `3*rho` and likewise starts with a flat
model. Neither can be applied to this weighted deleted configuration by
pretending it inherits those hypotheses.

The new source therefore uses a private single-row version of the same
midpoint argument. If an actual gap had `g>2*rho`, choose

`lambda'=(rho + min(lambda,g/2))/2`.

This scale is strictly above `rho`, at most `lambda`, and strictly below
`g/2`. The first export supplies deleted-source row score zero there. The
already proved `cycGaps_lt_two_mul_of_rowScore_zero` then gives
`g<2*lambda'<g`, a contradiction. This yields the **closed** bound `g<=2*rho`.

The final checked public export is
`actual_low_four_zero_delete_gap_le_two_rho`.

## Boundary and scope limits

Only the geometric closed gap bound is asserted at `rho`. The source does
not assert legality, a floor strip, potential equality, flatness, no
saturation, zero gains, or a critical model at that boundary. In particular,
`g=2*rho` is allowed by the bound and can have positive `gapScore rho g`.
It is not legitimate to transfer the open-band score-zero statement to
`rho`.

The whole-source checks validated the inherited `toModel` field on the
smaller-scale fixed-card model and the fourth conclusion of
`actual_minimum_delete_normal_form`. This is a checked weighted F17
strengthening, not an F17 exclusion or original arbitrary-N completion.
