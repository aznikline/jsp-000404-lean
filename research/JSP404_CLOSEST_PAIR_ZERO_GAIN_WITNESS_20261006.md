# Closest-pair zero-gain outward witness

Owned new source: `Jsp000404/ClosestPairZeroGainWitness.lean` only, plus
this receipt. No frozen source, root import, audit, Git, or quota operation
is changed. The entire new source passed its first genuine strict check
with four standard-three-axiom declarations and zero warnings, and is frozen.

## Exact local geometric interface

For actual `c : Fin s -> Plane₂`, `s >= 3`, original legality at `lam`,
nonzero reference `e`, a globally closest distinct pair `p,q`, and
`rowGain` at `p` on actual deletion of `q` equal to zero, the module gives
an actual index `j != p,q` satisfying:

- `lam/2 <= angle(q,p,j) < lam`;
- `pi-2*lam < angle(p,q,j) <= pi-lam`;
- `angle(p,j,q) <= angle(q,p,j)`.

These angles are actual ordinary triangle angles. No projective adjacency
or circle cut order is assumed.

If additionally `lam <= pi/4`, the actual projection is strictly positive:

`inner (c q-c p) (c j-c q) > 0`.

Thus `j` lies strictly beyond the hyperplane perpendicular to `pq` through
`q`, in the direction from `p` to `q`. It is a precise half-plane conclusion,
not a claim that `p,q` can be collapsed legally.

## FORMALLY PROVED deduction

The existing actual emission-or-near-collinearity theorem says that either
`p` emits to deleted point `q`, or an actual third point has
`theta=angle(q,p,j)<lam`. The zero-gain hypothesis excludes emission.

Since `pq` is globally shortest, `dist(q,p)<=dist(q,j)`. The standard
side/angle comparison gives `gamma=angle(p,j,q)<=theta`. Noncollinearity is
supplied by positive-margin actual legality. The triangle sum is
`theta+beta+gamma=pi`, and legality gives `beta<=pi-lam`.
Consequently `lam<=theta+gamma<=2*theta`, giving `theta>=lam/2`.
Also `theta+gamma<2*lam`, so `beta>pi-2*lam`.

For `lam<=pi/4`, this means `beta>pi/2`. The inner-product/angle criterion
gives `inner(c p-c q,c j-c q)<0`; reversing the first vector gives the
strict outward projection stated above.

## Genuine minimum-cardinality extremizer connection

The coupled theorem takes the actual
`ActualMinimumCardBandMaximizer.Model`. Its existing excluded-CertA theorem
implies that positive gain from `p` to `q` would require
`score(p)<score(q)`. Only the two-endpoint comparison
`score(q)<=score(p)` is needed to force zero gain. There is no assumption
that `p` has globally maximal score.

The final export chooses the closest pair internally, then orients it by
the two original row scores (ties allowed), and supplies the actual
outward witness. Maximum and minimum-cardinality properties are those of
the genuine band model, not an invented sharp-capacity field.

## Precise limitations

The result does not prove projective fan adjacency, an inverse single split,
a legal merge, a vertex-count bound, bare17/bare21 exclusion, or allN.
It supplies a genuine additional local metric/angle constraint for the
weighted minimum-cardinality model. No further unproved geometric path is
reported as established.

## Verification and handoff

Frozen source SHA-256:
`21fe6483423814e6a1fa7739a5f99195d4685c720e2e33a35182c08993878551`.

The single-file `lake env lean --trust=0` check genuinely exited zero,
printing four standard-three-axiom declarations
`[propext, Classical.choice, Quot.sound]`, with zero warnings. Raw log:
`.lake/closest-pair-zero-gain-witness-strict-20261006.log`.
Elapsed 3.762 seconds; `/usr/bin/time -l` maximum RSS 3,154,051,072 bytes
(2.937 GiB); sampled actual Lean peak 3,083,681,792 bytes. The actual-process
admission cap was 3.5 GiB with no interruption. Group peak 3,785,375,744 bytes
was recorded only, not used as the admission criterion.

The four checked exports are `exists_witness_of_zero_gain`,
`witness_positive_outward_projection`, `exists_witness_of_min_card_score_order`,
and `exists_oriented_closest_pair_witness`.

A real `.olean` was generated at
`.lake/build/lib/lean/Jsp000404/ClosestPairZeroGainWitness.olean`.
It has 289,352 bytes and SHA-256
`5b1ac7bb88acd01a417b4496adeb40905a562ed63e10345470d8201dd5b0e68f`.
The model dependency was consumed only after its owner confirmed genuine
strict/normal PASS and freeze at SHA-256
`1a00236f13e91ca6a2221d984d71db558ddc307a833a65aa57750c86cabecda3`.
The closest-pair dependency remained unchanged at SHA-256
`cd3919627e9c29065d07bcf4972241a42bd5a16eb75d8678b6ca9648f734b747`.

All owned Lean processes exited before the sole slot was explicitly released
to the uniform producer's next cohort. Normal publication is left to the
publisher; no duplicate normal/full build is performed by this owner.
There is no `sorry`, `native_decide`, or custom axiom in the source.
