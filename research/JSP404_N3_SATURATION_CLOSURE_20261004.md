# JSP-000404: the entire saturated third strip is proved

This is a partial original-geometry proof. The all-N `sendov_lower` remains
open and its axiom audit still detects `sorryAx`. No prize submission or
prize payment is claimed.

## New exact result

`N3SaturatedBounds.saturated_high_capacity` proves that every actual legal
configuration with at least three centers, floor(pi/lambda)=3, and an
actual row of defect one has potential at most **10**. It applies over the
whole delta interval [0,1), with no uniqueness, minimality, or tail-profile
premise. `saturated_strip_capacity` also consumes the existing LOW bound
**8**, using its original delta<1/2 premise.

This closes the remaining n=3 HIGH1 R0/R1 cases; the n=3 R2 and all LOW
saturated cases were already proved. There are now no open saturated
n=3 cases.

## Derivation

1. Actual saturation constructs a ray chart. Sort its nonanchor theta
   coordinates using an actual bijection. Actual triangle geometry supplies
   the shared-chord corridor and the two alternatives for every ordered
   triple. These are necessary constraints derived from the points.
2. For eight centers (seven nonanchors), those constraints alone contradict
   3*lambda <= pi < 4*lambda. The terminal is proved by 107 ordinary Lean
   linear-arithmetic leaves. It does not assume any nonanchor defect.
3. Retaining a center under an injective actual restriction cannot reduce
   its score. Every third-strip score is at most two, so retaining a
   saturated anchor keeps it saturated. Any larger saturated configuration
   could retain eight points, contradicting step 2. Hence it has at most
   seven points.
4. For seven centers, the six-nonanchor chart has only four feasible
   triangle-orientation patterns. In each, every anchored primitive gap
   is less than 2*lambda. Ordinary Lean arithmetic eliminates 730 other
   branches and proves all six original nonanchor row scores are zero.
   The extraction explicitly adds the anchor back via `score_add_defect`
   and transports the reference direction. Thus F=4+6=10.
5. At six centers, a second saturated row invokes the proved two-saturated
   cap. With a unique saturated anchor, two score-one rows would violate
   the existing actual n=3 R2 terminal. At most one score-one row remains,
   giving F <= 4+2+4=10. Three through five centers invoke the existing
   unconditional small-cardinality cap.

The diagnostic selected case splits. Every accepted branch is a Lean
proof; the theorem imports no solver verdict or external certificate.

## Remaining n=3 work

For a no-saturation actual configuration, every score is zero or one and
`N3NoSaturatedBound` proves the exact identity F=s+r, where r is the
number of positive rows. The actual positive-row bounds are r<=4 in LOW
and r<=5 in HIGH. A smallest over-capacity configuration contains a
zero-score victim; deleting it gives exact excess one and preserves all
surviving scores.

Consequently the no-saturation minimal profiles are precisely:

| Band | (s,r) tasks |
|---|---|
| LOW, F=9 | (5,4), (6,3), (7,2), (8,1), (9,0) |
| HIGH, F=11 | (6,5), (7,4), (8,3), (9,2), (10,1), (11,0) |

The LOW (5,4) task is now proved by `NoSatFiveTerminal` and its actual
extraction `NoSatFiveGeometry`. `N3PositiveBounds` lifts the new positive
count of three to every configuration with s>=5 and proves the original
five-point LOW cap8. Its remaining-LOW consumer exposes only (6,3)..(9,0).
The HIGH (6,5) task is also proved by `NoSatSixTerminal` and
`NoSatSixGeometry`: six actual third-strip points have at most four positive
rows, without any no-saturation or deletion assumptions. The terminal
checks all194 orientation profiles and12144 ordinary leaves. The other
nine actual geometric exclusions above remain open. An earlier
weaker angle diagnostic admitted solutions
for the first LOW/HIGH profiles, but it omitted the caps at both endpoint
vertices of each triangle. After adding all three actual triangle caps,
the targeted first-profile diagnostics are UNSAT. The LOW five-point proof
has 4439 ordinary Lean leaves and retains actual repeated directions and
zero projective representatives. The HIGH six-point counterpart has also
passed source trust-zero checks with standard axioms.

`N3PositiveBounds.high_positive_card_le_four` lifts the six-point bound to
all s>=6 through actual restrictions. `six_high_capacity` proves F<=10 for
every actual six-center third-strip configuration, treating saturation
separately with the proved cap. `HighRemainingExclusion` therefore exposes
only (7,4),(8,3),(9,2),(10,1),(11,0); its consumer retains this explicit
unproved hypothesis. The corresponding LOW consumer retains four tasks.

## General strips

The compression/extraction modules preserve original full-row defects in
a necessary scalar six-center model with 3<=n'<=24. They do not preserve
planar realizability. Remaining arbitrary-n deeper-tail bounds and actual
geometric no-saturation bounds must still be proved before consuming the
original jump/strip induction and completing `MainTheorem`.

The dated continuation receipt records source hashes and fresh build/axiom
checks. The dedicated review branch is suitable for auditing and merging
these partial proofs; it is not a completed competition entry.
