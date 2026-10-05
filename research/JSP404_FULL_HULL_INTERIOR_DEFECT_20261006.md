# Full actual hull consequence of interior defect

Owned new leaf: `Jsp000404/FullHullInteriorDefect.lean`, separate from the
frozen, verified InteriorRowDefect core. This leaf has now passed genuine
strict and normal target checks, with three standard-three-axiom exports,
and is frozen. No frozen dependency source is edited.

## FORMALLY PROVED full-hull bridge

For a finite actual family `c`, if `c q` is outside the convex hull of all
other original centers, finite-point strict separation exposes it in the
convex hull of the entire original range. This is a full-hull theorem.
It does not replace the full range by a selected subset's hull.

Combining its contrapositive with the verified Caratheodory/three-ray core
gives, at the actual floor `n=floor(pi/lam)` and original legality:

- `not IsHullVertex c q -> rowDefect n lam (directionRow o e c q) >= 3`;
- `rowDefect n lam (directionRow o e c q) <= 2 -> IsHullVertex c q`.

The nonzero reference is required for the original direction-row score
identity. No minimum-cardinality, gain-zero, saturation, maximal-score,
potential-capacity, or desired high-weight classification is assumed.

## Finite separation proof

The hull of the finite others set is closed and convex. Hahn-Banach
supplies a continuous linear functional `f` and number `u` such that
`f x < u < f(c q)` for every point of that hull.

Use the convex set
`T={x | f x <= f(c q) and (f(c q)<=f x -> x=c q)}`.
It contains every original center. For a positive convex combination,
reaching equality forces both endpoints to reach equality, hence both
are `c q`; this proves T is convex. The entire original convex hull is
therefore contained in T, where `c q` is the unique maximizer of f.
It is an exposed point, hence an extreme point of the full hull.

The bridge needs no injectivity separately: its nonmembership hypothesis
already excludes an alias of q among the other indices. Actual legality
supplies injectivity for the two row-defect consequences.

## Limitations

Only defect at most two is asserted to lie on the hull. There is no claim
that a maximum-score point of arbitrary defect, or a zero-gain point,
must be on the full hull. No sharp capacity or allN theorem is proved here.

## Verification and handoff

Frozen source SHA-256:
`d0f1bc283e8be312f03b0a1c7bbf7e01903c0464cd6feb6d726e6cbdf4e39a11`.
The core dependency remained unchanged at SHA-256
`7457d4cdec6038dea7b257a37d38b7c9349a535234e9a86ebb075f72faaeeb50`.

Both completed checks used the exact same source:

| Check | Actual exit | Seconds | time-l maximum RSS | Sampled actual Lean peak |
|---|---:|---:|---:|---:|
| Single-file strict0 | 0 | 3.728 | 3,150,184,448 B | 3,069,181,952 B |
| Genuine specified target normal | 0 | 4.520 | 3,151,986,688 B | 3,119,775,744 B |

Both checks succeeded on the first attempt. They printed three declarations
with exactly `[propext, Classical.choice, Quot.sound]`, with no warnings in
this owned source. The actual-process admission cap was 8 GiB; no
interruption occurred. Group peaks 3,833,593,856 B and 3,896,164,352 B were
recorded only. The target build replayed old dependency warnings, retained
in the raw log; it was not a full root build.

Raw logs: `.lake/full-hull-interior-defect-strict-20261006.log` and
`.lake/full-hull-interior-defect-normal-20261006.log`.
The true normal `.olean` exists at
`.lake/build/lib/lean/Jsp000404/FullHullInteriorDefect.olean`.
It has 141,776 bytes and SHA-256
`982441289e10b652b8a2e9410037d35c679bb704f4c378c764970b7cab62ca71`.

The three verified exports are `isHullVertex_of_not_mem_hull_others`,
`rowDefect_ge_three_of_not_hull_vertex`, and `low_defect_is_full_hull_vertex`.
The new source explicitly disables autoImplicit; every statement is fully
typed. There is no sorry, native_decide, custom axiom, or desired-capacity
field. The first geometric finite-hull bridge does not even require center
injectivity; the actual row consequences receive legality and the actual
floor, with a nonzero reference vector for the projective row identity.

All owned Lean/Lake processes exited before the sole slot was explicitly
handed to the boundary-deletion leaf owner, followed by the tenth
publication. No root import, audit, Git, quota operation, or frozen source
edit was performed. This does not close general sharp capacity or allN.
