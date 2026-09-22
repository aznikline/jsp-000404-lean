# Kraft crux: geometric saturation and a rejected shortcut

## Newly integrated geometric theorems

Proof-only changes from
`agent/jsp404-angle-cert-goal-01-owner @
0b525bee0ab85f30028a7b76de31356d2ac394e4` were integrated into
`Deletion.lean` and `Induction.lean`, retaining source-branch attribution
to aznikline and the recorded Devin coauthor.

- `rowDefect_eq_one`: a saturated row has a unique dominant gap.
- `cyclicDiff_le_or_ge`: every arc either contains that gap or misses it.
- `angle_le_pi_sub_of_saturation`: actual geometric angles at a saturated
  center are at most pi - n lambda.
- `not_two_saturated_of_delta_lt_half`: actual geometry forces delta >= 1/2
  when two centers are saturated and at least three centers exist.

`SaturationPacking.lean` adds the full geometric count: at most two
saturated centers in either regime; for at least three centers, at most
one is saturated in the low regime.
All these results have standard-only axiom closures.

## The no-saturation shortcut is false

The source branch's research note conjectured that a configuration with
no saturated vertex has Kraft sum K <= 1 in both regimes. That is not a
valid decomposition of the high-regime theorem.

`PentagonPacking.lean` provides a **kernel-checked strict counterexample**
in the exact skeleton model, with:

```text
s = 5, n = 2, delta = 3/4
q >= 0, Proper, 0 <= r < 1, ModeA
k = [0, 0, 0, 0, 0]
W = 5/2, hence K = W/2 = 5/4 > 1
```

This is not a ghost vertex, negative cell, or closed-boundary artifact.
The exact finite checks use `decide +kernel`, not `native_decide`.
The model's embedding into actual geometry is **not** formalized by this
file; it checks the rational data and every ModeA condition explicitly.

Its geometric origin is the regular pentagon. Taking lambda = 4 pi/11
gives T = 11/4. Each projective fan has three gaps pi/5 and one gap
2 pi/5, so the normalized gaps are three copies of 11/20 and one copy
of 11/10. Every exponent is zero. The largest angle is 3 pi/5, below
the allowed 7 pi/11. This elementary geometric explanation is separate
from the checked skeleton theorem.

The shortcut also fails beyond n = 2 and beyond flat configurations.
`tools/no_saturation_counterexample.py` instantiates the attributed
three-cluster construction at n = 3, delta = 3/4 and removes one point.
The resulting nine-point configuration has:

```text
k = [1, 0, 0, 0, 0, 0, 0, 0, 0]
no saturated vertex (saturation would require k = 2)
K = 5/4
maximum angle about 129.0225 degrees < allowed 132 degrees
```

This nine-point calculation is **floating-point discovery evidence**,
not a formal geometric proof. Coordinates, angle slack and distance
from floor boundaries are saved in `verification/no-saturation-geometry.json`.
The five-point rational theorem supplies the independent checked
counterexample to the abstract shortcut.

Neither example refutes the intended high cap K <= 5/4. They show why
the high bonus cannot be assigned only to cases with saturated centers.

## Original-paper check

The publisher-hosted [1995 journal volume](https://real-j.mtak.hu/7467/)
was read by byte ranges. Printed pages 39-40 (PDF pages 41-42) were
checked from their unmodified page images. Lemma 4.1 gives the proposed
maximizing profiles there but does not provide the missing general
packing argument. The source cache is outside this repository; paper
pages are not redistributed here. This does not establish that Sendov's
final theorem is false. It prevents treating those profile claims as
already proved Lean lemmas.

## A narrower direction worth formalizing

The following is a mathematical proof sketch, **not a checked theorem**.
It addresses the one-saturated low case only.

Put a saturated center at the origin. The other rays lie in an angular
interval [a,b] of width at most delta lambda. For a pair with ray angles
theta_x < theta_y, the directed chord angle phi satisfies

```text
theta_x + lambda <= phi <= theta_y + pi - lambda.
```

Both inequalities follow from the triangle-angle cap. Thus all remaining
line directions lie in [a+lambda, b+pi-lambda], whose length is at most
pi - 2 lambda + delta lambda < (n-1) lambda in the low regime.
Cover this interval by n-1 disjoint angular bins of width < lambda.
Each bin defines a bipartite edge graph, using the existing cone argument.

For a weighted proof, one must still show that each original row exponent
is at most its number of empty bins. Interior gaps contribute their floor
minus one; the two boundary gaps extend beyond the cover interval by at
most lambda. The existing `JSP404.sum_free_binary_coordinates_le` would
then bound the remaining weight by 2^(n-1). The angular-chart, boundary
counting and actual-geometry bridges remain to be formalized. This sketch
does not handle the zero-saturation high case and is not the full proof.

## Completion status

The general capacity / certificate theorem remains open. All boundary
cases and downstream assembly previously proved remain valid. The
unconditional lower root still depends on `sorryAx`; no complete-proof
submission is justified yet.
