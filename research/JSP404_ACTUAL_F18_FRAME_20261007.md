# Original actual F18 frame

2026-10-07 UTC: **READY — genuine strict and normal compiler PASS.**
Whole-source strict validation (`--trust=0 -M8000`) and the genuine own Lake
target build exited 0 in 33.184 and 53.350 seconds. The public producer uses
exactly `propext`, `Classical.choice`, and `Quot.sound`. Both checks retain
one own `if_neg` deprecation warning; no lint-only repeated check was made.
Neither check reached the single-process 8 GiB or 180 s bound. There were
no failed compiler runs for this module.

`Jsp000404/ActualF18Frame.lean` provides the checked producer
`Jsp404.ActualF18Frame.actual_f18_frame`. Its inputs are the actual plane
orientation, an original nonzero reference, the existing original minimum
counter-model at cap 16 in the LOW band
`pi/(4+1/2) < lambda <= pi/4`, and original potential exactly 18. The lower
band endpoint is exactly `2*pi/9`.

The output `Frame` keeps all scores and convex-hull predicates in the
original configuration. It records floor 4, every original score in
`{1,2}`, full original hull membership of every score-two center, heavy
count `t <= 3`, the light/heavy partition, `L+2*t=9`, `s+t=9`,
`s=9-t`, and `s>=6`.

The argument uses existing checked mathematical interfaces, not a desired
capacity bound as a premise:

1. `low_band_strip` derives the real floor and LOW remainder. The existing
   `low_model_nonsaturated` internally invokes the independently proved
   `Jsp404.potential_le_two_pow_of_saturated` theorem in `OneSaturatedLow.lean`.
   Together with original row cells at most four,
   this gives every original score at most two.
2. Every original weight is consequently at most four. Potential 18 first
   gives `s>=5`; this is sufficient to apply the existing actual minimum
   score critical form, which forces the minimum weight to be two and the
   minimum score to be one. Thus all original scores are one or two.
3. A score-two original row has defect two. The checked
   `FullHullInteriorDefect.low_defect_is_full_hull_vertex` puts this original
   center on the full original hull. No hull assertion is transferred to a
   restricted configuration.
4. If there were four heavy original centers, a finite restriction of five
   actual points can retain them and one additional original center.
   `PositiveRowCount.rowScore_le_restrict` keeps the four restricted scores
   at least two. Their weights total at least sixteen, and the fifth
   restricted point contributes at least one. The resulting potential at
   least seventeen contradicts the independently checked uniform five-point
   LOW bound, specialized to `n=4` and hence capacity sixteen.
5. Exact original binary-score counting gives potential `2*s+2*t=18` and
   `L+t=s`. Therefore `s+t=9`, `L+2*t=9`, and `t<=3` gives `s>=6`.

The five-point restriction is used only for real legality, row-score
monotonicity, and the checked five-point capacity contradiction. The caller
does not supply binary scores, the heavy count bound, convex-hull membership,
the final frame, or a full F18 exclusion.

This producer does not exclude any of the resulting `t=0,1,2,3` cases by
itself. Actual hull-type stronger caps, class-size and deletion consumers,
the full F18/F17 exclusions, other HIGH cases, and the original arbitrary-N
theorem remain separate obligations. The final whole-source checks include
the finite-set image/card rewrites and natural-cardinality rebinding in the
minimum-score proof. Root composition is a separate integration check.
