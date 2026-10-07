# Original F18 all-light assembly

2026-10-07 UTC: **READY — whole-source strict trust-zero and genuine normal target PASS.**
Source: `Jsp000404/ActualF18AllLight.lean`, with two selected public exports.
Old PASS sources, other owners' sources, root, audit, status, Git and the
index were not edited.

## Exact original-model contract

`actual_F18_all_light_false` takes the original actual n4 LOW minimum
counter-model at cap16, original potential18, an original nonzero reference,
and `forall i, rowScore lambda (directionRow o e c i)=1` on the original
configuration `c : Fin (s+1) -> Plane₂`.

It accepts no caller split by interior count, inductive exclusion, hull
cardinality, nearest-neighbor map, angle array, or desired capacity bound.
All hull predicates below are on the full original point configuration.

## Internal exhaustive cases

The proof first tests whether every original point is a full-hull vertex.
If so, `ActualF18Frame` derives original cardinality nine from potential18
and the all-light score hypothesis. The checked actual
`selected_hull_card_le_eight` applied to the identity selection gives at
most eight original points, a contradiction. No polygon adjacency or
caller exterior-angle sum is assumed.

Otherwise, the proof internally chooses an original nonvertex `p`.
It then tests whether all original points other than `p` are hull vertices:

- If yes, the original configuration has exactly one interior point and
  is consumed by
  `ActualF18SingleInterior.actual_F18_all_light_single_interior_false`.
- If no, an original second nonvertex `q != p` is chosen and consumed by
  `ActualF18TwoInterior.actual_F18_all_light_two_interior_false`.

The strengthened TwoInterior public interface has **no** premise that all
remaining points are hull vertices. Its universal no-apex-between argument
internally proves that the two relevant apex blocks consist of original
hull points. Thus this branch handles two or more original interior points;
it does not silently discard the cases with three or more interiors.

## Heavy existence consequence

The optional second export `actual_F18_has_heavy` uses the original Frame's
score-one-or-two dichotomy. If no original score-two point existed, every
original point would have score one, contradicting the first export.
Its conclusion is an actual original index of score two, not an externally
provided type or count certificate.

## Dependency readiness and static review

The exact SingleInterior public API was confirmed with its owner. Its
original candidate `843873...` was superseded by genuine strict/normal PASS
source `3602563c6d66b080405b81ea4f9fbdfef999469c6a39d75494718c91193f1921`;
the changes were API-only and its public signature was retained.

The strengthened TwoInterior public API was confirmed with its owner:
`o e he H hF hall X Y hXY hX hY : False`, without `hother`.
Its final checked source is
`3f7c7e1e08d1f8485e03d69820b48d1510222eee595cfec1ef514c1ef8f02003`.
The owner receipt records genuine strict2 and normal1 PASS/Std3; the earlier
API failure is retained separately as NOT_PROVED, with its actual source
and raw output. The final consumer accepts any two original interior points,
without a hull premise on the other original points.

An independent read-only review by `window_api_audit` found no concrete API
or logical mismatch in the 83-line assembly: identity-pick cardinality,
the second-interior inequality direction after `push Not`, the Single and
strengthened Two signatures, and the all-original-index Frame dichotomy
were checked. That review did not run Lean or edit files.

## Genuine validation and publication boundary

The unchanged source
`7c0eca1bb495b58b888d9dda35bc0e4cc2948e17aae5abea90a565a485554f6e`
passed strict trust-zero attempt1 in 20.9966 seconds (time max RSS
5,932,515,328 bytes), then genuine normal `lake build` attempt1 in
29.0184 seconds (time max RSS 5,876,613,120 bytes). The normal output records
the actual target Built and successful 9,049-job build. Each run printed
both selected declarations with exactly `propext`, `Classical.choice`, and
`Quot.sound`. The 8 GiB single-Lean and 180-second guards did not fire.
There were no failed runs and no warnings from this source. The normal
output retains 495 inherited warnings; the strict output has none.

The original raw output bytes and both actual source snapshots remain
unchanged. The published normal output is lossless gzip because the raw
output contains eight lines ending in whitespace; the producer receipt
records both compressed and decompressed hashes. No output was stripped.

This closes the entire `t=0` / all-light F18 branch for the stated original
minimum counter-model and derives an actual original score-two center in
any such F18 model. It does not close the remaining heavy-containing F18
branches, F17, all n4 capacity, or the original arbitrary-N theorem. This
producer receipt does not claim a new composed root build or audit.
