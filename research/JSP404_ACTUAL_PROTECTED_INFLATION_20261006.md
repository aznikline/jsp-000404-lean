# Selective actual inflation with arbitrary protected rows

Owned source: `Jsp000404/ActualSingleSplitScoreTable.lean` and
`Jsp000404/ActualProtectedInflation.lean`, plus this receipt. Every previously
PASS source is unchanged. No root import, Git, quota or card is changed.

## Current validation status

PASS_ACTUAL_PROTECTED_INFLATION on 2026-10-06. Both complete new source
files passed actual `lake env lean --trust=0`, followed separately by their
genuine specified new Lake targets. Twenty printed exports (7 split + 13
protected) all depend only on `[propext, Classical.choice, Quot.sound]`;
both owned sources have zero warnings. Both normal targets genuinely built
the new modules and produced their first real normal `.olean` files.

The split source's first two strict attempts failed in its new position
lemmas and missing local scope for an existing dimension instance. Their
source snapshots, stdout bytes and source hashes are preserved unchanged.
The repairs only changed the new split leaf; the final copied score-table
assembly and all frozen dependencies were retained. After each source's
first successful whole-file strict check its source bytes were frozen.
The protected source passed its first whole-file strict attempt unchanged.

## Exact public interface

For any actual configuration `c : Fin s -> Plane2`, `s >= 3`, fixed
orientation and nonzero reference, arbitrary `sigma : Fin p -> Fin s` with
`Function.Injective sigma`, original Section4Legality at lambda, and
`0 < tau < lambda`, the public conclusion returns:

- one lambdaFinal strictly between tau and lambda;
- an actual legal configuration on exactly
  `p + (F - protectedMass)` distinct points;
- an explicit protected injection sigmaFinal from Fin p into that domain;
- unchanged protected actual point positions and all original protected
  row scores under sigmaFinal;
- score zero for every final row outside the range of sigmaFinal;
- the exact original total potential F.

Here F is `potential lambda (directionRows o e c)` from the original points,
and protectedMass is the sum of all `2 ^ originalScore(sigma j)`. No target
capacity, initially flat tail, scalar realization, or desired point count
is a hypothesis. No final subset is extracted or discarded.

The theorem quantifies over arbitrary p, including p=0 and p=s. Separate
public cardinal identities cover these two endpoints: empty protection
has target F; an injection protecting all s original rows has target s.
The fixed-point terminal proof preserves every row score while decreasing
lambda by a finite common gap-floor margin, so positive protected rows are
also retained at the strict endpoint.

## Construction and decreasing measure

The new single-split leaf imports the frozen SingleSplitScorePreservation
and repeats its final proof assembly to expose the complete internally
proved score table. The selected parent has two actual children with score
kappa(v)-1; every other parent has one child with its exact old score.
A positive epsilon, constructed axis, common smaller lambda, and actual
Section4Legality are returned. Actual epsilon zero is never treated as a
legal point configuration.

Public aliases expose index, originalCopy, extraCopy and points. The new
originalIndex is injective. Actual original copies equal their original
point positions; the extra child equals `c v + eps * u`.

The protected induction selects a positive row outside range sigma. Its
next injection is originalIndex composed with sigma. The complete score
table preserves every protected score, hence protectedMass, while also
preserving F. The target T = p+(F-protectedMass) is invariant, but the
actual point count rises from t to t+1. Strong induction on T-t terminates.
The algebraic identity T = t + tailSurplus proves nonnegativity and supplies
a positive unprotected row whenever T>t. At T=t the finite tail surplus
vanishes, so every remaining unprotected score is zero.

All terminal old scores are preserved at one strictly smaller scale by
applying GapSplitFloorStability to the flattened finite list of actual
cyclic gaps. Sorted direction rows supply the nonnegative gaps, including
zero gaps and the real cyclic wrap. Every raw floor is preserved here.

## n4 / R2 arithmetic meaning

Protecting one SAT row of score 3 and two low rows of score 2 gives protected
mass 8+4+4=16 and p=3. An original potential F=21 yields exactly 8 final
points, with all 5 unprotected tail points of score zero. F=22 yields exactly
9 final points and 6 zero-score tails. The latter conclusion does not permit
selecting only 8 points and asserting that the five retained tails keep
score zero; arbitrary point deletion can change their actual direction rows.

This module proves a geometric selective inflation operation. It does not
prove an independent eight/nine-point capacity or any arbitrary-N theorem.

## Frozen source hashes

- `Jsp000404/ActualSingleSplitScoreTable.lean`: `7db85a9236ad5fcdb120309738eceba75ad92f9446858994e9d99084cf37b986`
- `Jsp000404/ActualProtectedInflation.lean`: `951ca5a47a896d785bb8936cc434b5cc4169022608c9ba7f8a2547f6694e5ca3`
- `Jsp000404/SingleSplitScorePreservation.lean`: `af04d663329454b62a170646b9af0c27ef8c5a939ff2435a74acfa7c124c0284`
- `Jsp000404/ActualPotentialInflation.lean`: `fb922937f4ca56fa29f7a1ae9b789b46aaa24749bd68077d47d10ea4567b7abb`
- `Jsp000404/GapSplitFloorStability.lean`: `9b9ac6dc1fa5a55ca4c6e45a4af914f0592b994798b7663005f63737354b1097`

## Completed verification

| Source / check | Actual exit | Seconds | Sampled actual Lean peak B | time-l max RSS B |
|---|---:|---:|---:|---:|
| ActualSingleSplitScoreTable / strict | 0 | 4.465 | 3097198592 | 3104292864 |
| ActualSingleSplitScoreTable / normal | 0 | 4.857 | 3152986112 | 3162488832 |
| ActualProtectedInflation / strict | 0 | 4.304 | 3099901952 | 3104899072 |
| ActualProtectedInflation / normal | 0 | 4.940 | 3106603008 | 3163209728 |

Every actual Lean peak and time-l maximum RSS stayed below the 3.5-GiB
admission cap (3,758,096,384 B). No check was interrupted. Whole owned-process
group peaks were recorded separately and were below the sole 8-GiB window.
Normal logs replay pre-existing dependency warnings; no warning belongs to
either new owned source. The scoped target builds were not full root builds.

The genuine normal products are:

- `.lake/build/lib/lean/Jsp000404/ActualSingleSplitScoreTable.olean`: 413008 bytes, SHA-256 `3b341c9b1f8274d8988a2a3acc0609a696dac269b84eb494af7b29d14f105e1f`.
- `.lake/build/lib/lean/Jsp000404/ActualProtectedInflation.olean`: 645680 bytes, SHA-256 `b34e5d4ba2576fa01f4f9d427e0af8a578b84fe0c22e336e5dffb58cc7ca0b0d`.

All success and failure raw logs and attempt source snapshots are retained
under `.lake/protected-inflation-*` with individual JSON measurement records.
The complete machine-readable receipt is
`research/JSP404_ACTUAL_PROTECTED_INFLATION_20261006.json`, including all
successful commands, exact log hashes, twenty fully qualified export names,
per-export axiom sets, the two failed attempts and the frozen source hashes.

After both strict and genuine normal checks passed, all owned Lean/Lake
processes exited. The producer explicitly released the sole compilation
window to n4 ReifiedRow10 + Cycle8 according to the parent's fresh schedule.
No frozen source, root import, global audit, Git, quota or card was touched.
