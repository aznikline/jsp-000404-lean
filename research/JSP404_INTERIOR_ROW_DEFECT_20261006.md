# Actual containing-triangle and others-hull row defect

Owned frozen source: `Jsp000404/InteriorRowDefect.lean`, plus this receipt.
The completed source has five strict/normal standard-three-axiom exports.
No earlier frozen source, root import, audit, Git, or quota was changed.

## Exact actual geometry and original full row

For a legal actual configuration `c : Fin s -> Plane₂`, nonzero reference
`e`, and `n=floor(pi/lam)`, a center `q` lying in the triangle of three
distinct actual other centers has

`rowScore lam (directionRow o e c q) + 3 <= n`.

It therefore has actual original `rowDefect >= 3`. The statements do not
assume a row score, saturation, capacity, or gap identification certificate.
Their typed domain is more general than `s>=4,n>=3`: the actual containing
triangle supplies four distinct indices, and the proved bound implies n>=3.
Positivity of lambda is supplied by Section4Legality.

Three surrounding angles at a strictly interior point sum to `2*pi` and
are at most `pi-lam`. Their three supplements are positive, each at least
lambda, and sum to pi. Existing ThreeDirectionCapacity identifies these as
the actual three sorted projective gaps for all direction lifts, permutations
and wrap cases. Existing TwoSaturatedDeficit's general three-ray restriction
gives full original rowScore at most the selected three-ray score, retaining
every additional original center and all direction multiplicities.
The existing supplement arithmetic then gives the full three-cell bound.

The original defect definition is `rowBig + (n-rowCells)`, not simply a
syntactic `n-rowScore`. The actual `rowCells<=n` theorem, the exact
`rowScore=n-rowDefect` identity, and `rowDefect<=n` are all used before
natural-subtraction arithmetic yields the defect bound.

## Actual whole-others-hull extraction

If `c q` belongs to `convexHull(c '' {q}^c)`, Caratheodory supplies an
affinely independent finite support of at most three actual other points.
Empty and singleton supports contradict membership or center injectivity;
two-point support places q on an actual segment and contradicts legal
noncollinearity. The support therefore consists of three distinct actual
centers, giving a containing triangle and the same original full-row bound.

This extraction uses all original centers other than q. It is not a claim
about a merely selected subset's hull vertex status.

The separate full-hull extreme-point bridge is intentionally not in this
compiled module. A new `FullHullInteriorDefect.lean` is WIP: its Hahn-Banach
finite separation/exposed-point bridge and resulting full-hull corollaries
have not yet been kernel checked. No full-hull extreme-point theorem is
claimed as verified in this core receipt.

## Verification

Frozen source SHA-256:
`7457d4cdec6038dea7b257a37d38b7c9349a535234e9a86ebb075f72faaeeb50`.
`autoImplicit=false` prevents unknown names from becoming hidden assumptions.

| Check | Actual exit | Seconds | time-l maximum RSS | Sampled actual Lean peak |
|---|---:|---:|---:|---:|
| Repaired single-file strict0 | 0 | 4.221 | 3,150,970,880 B | 3,121,758,208 B |
| Genuine specified target normal | 0 | 4.860 | 3,157,344,256 B | 3,101,163,520 B |

Both completed checks printed five standard-three-axiom declarations
`[propext, Classical.choice, Quot.sound]` with no warnings in this source.
Actual-process admission was 8 GiB; neither check was interrupted. Group
peaks 3,823,534,080 B and 3,874,029,568 B were recorded only.

Logs: `.lake/interior-row-defect-repair1-strict-20261006.log` and
`.lake/interior-row-defect-normal-20261006.log`.
The first failed source check, before the actual-cell defect conversion,
exited one and is not a PASS; its real errors are retained separately at
`.lake/interior-row-defect-strict-20261006.log`.

Real normal `.olean`:
`.lake/build/lib/lean/Jsp000404/InteriorRowDefect.olean`.
All owned Lean/Lake processes exited before the sole slot was explicitly
returned to uniform case575. No duplicate full root build was performed.
The source has no sorry, native_decide, or custom axiom. General capacity,
bare17/bare21 and the original prize remain open.
