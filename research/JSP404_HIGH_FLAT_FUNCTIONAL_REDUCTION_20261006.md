# Actual HIGH flat functional counter-model

Owned new source: `Jsp000404/HighFlatFunctionalReduction.lean` only, plus
this receipt. The frozen HIGH maximum-mass source and root's band-deletion
consumer are reused without edits. The whole new source has passed a genuine
strict check and is frozen. The exported declaration prints exactly the
standard three axioms `[propext, Classical.choice, Quot.sound]`.

## Exact exported interface

`Jsp404.HighFlatFunctionalReduction.exists_high_flat_functional_counter_model`
has only the original actual-counterexample hypotheses:

- `n >= 4`, `s >= 3`;
- orientation `o`, nonzero reference `e`;
- actual `c : Fin s -> Plane₂` legal at `lam`;
- `floor(pi/lam)=n` and `pi/lam-n >= 1/2`;
- `sendovCap n true < potential lam (directionRows o e c)`.

It internally constructs `t >= 3`, a real scale in
`(pi/(n+1), pi/(n+1/2)]`, and actual distinct points
`d : Fin (t+1) -> Plane₂` such that:

1. `sendovCap n true < t+1 <= 2^(n+1)`;
2. `Section4Legality d scale` and every row score is zero;
3. `potential scale (directionRows o e d) = t+1`;
4. for every deleted point `q`, every survivor's actual `rowGain` is at
   most one, and the actual set of survivors with positive gain has
   cardinality at most one.

The incoming set is precisely the filter of `Finset.univ.erase q` by
`1 <= rowGain scale (directionRow o e d i) (deleteIndex o e d q i)`.
No arbitrary scalar row array or separately assumed graph is used.

## Proof composition

The verified HIGH maximum-mass reduction constructs an attained band
maximum `M` from the independent classical bound `2^(n+1)`, together
with its genuine flat realization and derived `BandMaximal` property.
The sharp HIGH cap is only the input excess threshold.

Since `sendovCap n true >= 2^n >= 16`, strict excess makes `M` a
successor `t+1` with `t >= 3`. After the actual successor case split,
root's verified band-maximal deletion theorem is applied to each `q`.
The legality of the actual deleted configuration and its mass bound
come from that theorem and the internally constructed band maximum.

The caller supplies no `BandMaximal`, free deletion-capacity bound,
flatness, emitter certificate, or sharp-capacity field. This source does
not duplicate the maximum construction or deletion-budget proof.

## Remaining mathematical obligation

For n=4 this gives an actual functional model with `21..32` points;
for n=5 it gives one with `41..64` points. Excluding these constrained
actual models is still a geometric theorem to prove. A bound on incoming
emitters does not itself prove a sharp capacity or a general graph count.
This module does not close bare21, arbitrary HIGH capacity, allN, or the prize.

## Verification and handoff

Frozen source SHA-256:
`ec50fdc4838356ab077cf6ee3568012a73930078de57da83f255dd17440013c3`.

The first single-file check genuinely passed `lake env lean --trust=0`,
actual exit zero, one standard-three-axiom declaration, and zero warnings.
Raw log: `.lake/high-flat-functional-reduction-strict-20261006.log`.
Elapsed 3.623 seconds; `/usr/bin/time -l` maximum RSS 3,137,093,632 bytes
(2.922 GiB); sampled actual Lean peak 3,059,122,176 bytes. The actual Lean
admission cap was 3.5 GiB, with no interruption. Group peak 3,760,701,440 bytes
was recorded only and was not the admission criterion.

A real `.olean` was generated at
`.lake/build/lib/lean/Jsp000404/HighFlatFunctionalReduction.olean`.
It has 170,232 bytes and SHA-256
`09d57adaa7ecf723317000369a51ba1025ef5052c42f315a9498fda2cc5139f7`.
The unchanged direct dependency source hashes are:

- ActualHighMaximumMassReduction:
  `57177e34a7531726c299725b3448448b2662fd42ee0f8763942738c7efc58655`;
- FlatBandMaximumDeletion:
  `b1a65c9959a11c7f28fe3ea79dd833eb30409fb52b003502e933b33c541d196a`.

All owned Lean processes exited before the sole slot was explicitly released
to the n4 packet producer, followed by the eighth publication's normal/audit
stream. The normal target belongs to that publisher and is not reported as
completed by this owner; no duplicate normal/full build is performed here.

No literal `sorry`, `native_decide`, or custom axiom occurs in the new source.
No frozen source, root import, audit, Git, or quota operation was changed.
