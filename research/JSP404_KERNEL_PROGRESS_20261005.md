# JSP-000404: original N=9,10 and the entire LOW third strip

Status: source kernel proofs, all270 normal Lake producer targets, the
full9315-job project build and the composed trust-zero audit have passed. The arbitrary-N root theorem
is still OPEN; no completed competition entry or prize is claimed.

## Exact unconditional results

- `Jsp404.sendov_lower_nine_to_ten` has the original lower-bound type for
  every N=9,10, without any geometric-certificate premise.
- `Jsp404.sendov_lower_le_ten` and `sendov_alpha_eq_le_ten` extend the
  proved original range from 3..8 to **3..10**. The N=9,10 value is 5*pi/7.
- `N3LowPairClosure.low_capacity` proves **F<=8 for every actual n=3 LOW
  configuration**, including no-saturation cases. No finite-exclusion
  hypothesis remains in this statement.

All six exported results passed source `--trust=0` and have only
propext, Classical.choice and Quot.sound.

## Bare nine-point proof

Actual legality gives a strict directed-chord order. All three caps of each
ordered triangle enter `NoSatNineDBMTerminal.NineModel`: middle separation,
strict chord betweenness, and both endpoint caps. No positive-row, floor,
deletion, or minimality hypothesis is supplied.

The complete exact difference-bound search has 1087 genuine binary splits
and 1088 terminal states. Forced orientations are replayed from original
inequalities, never added as trusted assumptions. The 268 small proof shards
and their combination were all checked by Lean, and their axiom/source-hash
receipts match the frozen source. The actual extractor proves that
lambda>2*pi/7 permits at most eight actual points, at any configuration size.

The original lower-bound consumer takes the finite maximum of the angles.
If it were below 5*pi/7, lambda=pi-maxAngle would exceed2*pi/7, yielding a
legal nine-point configuration forbidden by the actual exclusion. The upper
bound is already proved; the original extremal quantity therefore equals
the original formula through N=10.

## Why all LOW no-saturation profiles close together

At n=3 with no saturation, each row score is zero or one and F=s+r, where
r counts positive rows. A positive row has a projective gap of at least
2*lambda. `PositiveSplitAxis` constructs an actual nonzero split direction
whose two signs meet every old ray at an angle at most pi-lambda.

`ActualPairExpansion` replaces each positive center by a nearby pair and
keeps the other centers unchanged. For any0<lambda'<lambda, finite angle
continuity gives a concrete positive scale at which all s+r new points are
distinct and satisfy the original legality at lambda'. Two copies in one
cluster are handled by positive scaling of their internal chord before
taking the limit; no degenerate limiting configuration is called legal.

Choose lambda' strictly between2*pi/7 and lambda. The actual nine-point
exclusion bounds the expanded point count by eight. Consequently F=s+r<=8.
The independently proved saturated LOW cap covers the remaining case.

The strict relaxation lambda'<lambda is essential. This argument constructs
an actual finite perturbation and does not identify an infimum with an
attained or structurally feasible configuration.

## Remaining work

- n=3 HIGH without saturation remains open. The retained minimal profiles
  are (7,4),(8,3),(9,2),(10,1),(11,0).
- A bare eleven-point difference-bound diagnostic visited93579 nodes in
  50 seconds and exhausted its budget. It is neither an UNSAT proof nor an
  actual counterexample.
- General n>=4 strip/deeper-tail capacities remain open. The fixed-six
  compression and seven certified orientation branches do not close them.
- `MainTheorem.sendov_lower` still has its original arbitrary-N gap; the
  required root negative control remains in place.

The prior verified publication is review/jsp404-proof-continuation-20261004
at14af308. The nine-point bundle is published only after these standard build and
composed checks. This remains a partial original-problem solution, with
N>=11 and general later strips still open.
