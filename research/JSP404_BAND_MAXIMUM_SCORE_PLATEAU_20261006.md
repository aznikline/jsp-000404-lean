# Fixed actual band-maximum score plateau

Owned new source: `Jsp000404/BandMaximumScorePlateau.lean` only, plus this
receipt. All previous sources are frozen and unchanged. The final source
passed its first genuine strict and normal target checks, with six exports
depending only on `[propext, Classical.choice, Quot.sound]`, and is frozen.

## Exact hypotheses and conclusion

Take fixed actual `c : Fin s -> Plane₂`, `s>=3`, fixed orientation/reference,
`rho>=0`, original legality at `scale`, `rho<scale<=upper`, potential equal
to `M`, and `ActualMaximumMassReduction.BandMaximal o e rho upper M`.
For every `rho<scale'<=scale`:

1. the same actual configuration remains legal;
2. its potential remains `M`;
3. every original actual rowScore remains exactly unchanged;
4. every individual actual cyclic-gap gapScore remains exactly unchanged.

BandMaximal is the attained maximum supplied by the independently proved
coarse-bound construction. It is not a caller's desired sharp capacity.
No minimum-cardinality hypothesis is required.

## Proof mechanism

Actual sorted direction rows have nonnegative cyclic gaps, including the
wrap gap and duplicated rays. For a fixed nonnegative gap, decreasing a
positive scale increases `g/scale`, hence cannot decrease its natural floor
or `gapScore = floor(g/scale)-1`. Summing gives rowScore monotonicity, and
the powers of two give potential monotonicity.

Actual triangle caps remain valid after decreasing scale, including the
equality case. BandMaximal supplies the reverse potential inequality. The
finite natural sum therefore remains equal to `M`. Equality in a sum of
componentwise ordered powers of two gives equality of each power, then of
each rowScore. Equality in each finite sum of componentwise ordered gap
scores gives equality of every gapScore. Repeated gaps remain counted with
their actual List multiplicity.

## Flat lower-boundary geometry

If the original configuration is Flat, the row plateau preserves Flat at
every scale strictly above rho and below the original scale. Consequently
every actual cyclic gap satisfies `g<=2*rho`.

If `g>2*rho`, choose
`scale'=(rho+min(scale,g/2))/2`. This scale is strictly above rho, at most
scale, and strictly below g/2. Flat gives `g<2*scale'`, contradicting
`2*scale'<g`. No global continuity assertion for cycGaps is needed: the
points, reference, direction rows and gap lists are fixed throughout.

## Raw-floor and boundary limitations

The plateau concerns gapScore, not the raw floor. A floor may change from
zero to one without changing gapScore. For example `g=1`, scales two and
one give respective raw floors zero and one, but both gap scores are zero.
The source never asserts raw-floor invariance.

The lower boundary is open. If `g=2*rho`, every tested scale above rho can
still give gapScore zero, while gapScore at rho jumps to one. Therefore the
result does not assert Flat, score plateau, or the band maximum at rho itself.
The closed gap bound is intentional.

This necessary geometry does not prove sharp capacity or rule out all
flat counter-models. Bare17/bare21 and the original prize goal remain open.

## Verification and handoff

Frozen source SHA-256:
`fbeee320067641404a51461a928d834bd124e4aae1ecefe05832818f599f8885`.
The unchanged direct dependency ActualMaximumMassReduction has SHA-256
`994f865b569a9954304eade3ad1e4f16be9bdfdf77080d5c412085b516c4f41c`.

Both completed checks used this same source:

| Check | Actual exit | Seconds | time-l maximum RSS | Sampled actual Lean peak |
|---|---:|---:|---:|---:|
| `lake env lean --trust=0` | 0 | 4.730 | 3,157,229,568 B | 3,097,034,752 B |
| `lake build Jsp000404.BandMaximumScorePlateau` | 0 | 6.693 | 3,156,525,056 B | 3,085,828,096 B |

Both actual Lean peaks were below the 3.5-GiB admission cap without
interruption. Group peaks 3,797,368,832 B and 3,930,521,600 B were recorded
only. The strict scope had six standard-three-axiom declarations and zero
warnings. The specified normal target genuinely built the new module,
again printed its six standard-three-axiom declarations, and had no warning
in the owned source. Old dependency warnings were replayed and preserved.
This was not a full root build.

Raw logs: `.lake/band-maximum-score-plateau-strict-20261006.log` and
`.lake/band-maximum-score-plateau-normal-20261006.log`.
A real normal `.olean` exists at
`.lake/build/lib/lean/Jsp000404/BandMaximumScorePlateau.olean`.
It has 304,528 bytes and SHA-256
`c0ede2733a8a240664afce910d1100397d1a4dafe3dd9629236e1025a639aca8`.

The six checked exports are `gapScore_le_of_scale_le`,
`actual_rowScore_le_of_scale_le`, `actual_band_maximum_score_plateau`,
`actual_band_maximum_gap_score_plateau`, `actual_band_maximum_flat_plateau`,
and `actual_flat_band_maximum_gap_le_two_rho`.

The typed public lower-bound assumption is `rho >= 0`; every tested scale
is strictly greater than rho and hence positive. The actual LOW/HIGH bands
have strictly positive rho. No claim is made about scores or Flat at rho.

All owned Lean/Lake processes exited before the sole slot was explicitly
released to the uniform producer's final cohort. The source has no `sorry`,
`native_decide`, or custom axiom. No frozen source, root import, audit, Git,
or quota operation is changed or performed.
