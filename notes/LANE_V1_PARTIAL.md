# Lane V1 (vacuum lemma) — partial results, lane cancelled

Status: **CHECKER-VALIDATED evidence, not Lean theorems.**  The lane was
cancelled mid-hunt; this note archives what the logs show.

## Target

`sk.Proper → sk.Consistent n → sk.W n ≤ 5/2` (the "vacuum lemma" that
would make `GadgetSelectionHighP` vacuous).

## Record correction (2026-09-22): the "found" skeletons are NOT counterexamples

`tools/v1_3311.log` prints `*** CONSISTENT (Lean) skeleton at W>5/2 ***`
three times, but the campaign header for that run is:

```
profile k=[3, 3, 1, 1] d=(0, 0, 2, 2) W=5/2 (>5/2? False)
```

All three candidates have `k = [3,3,1,1]`, i.e. `d = (0,0,2,2)` and

    W = 1 + 1 + 1/4 + 1/4 = 5/2   —   exactly at the bound, NOT strict.

The log flag is a labeling bug (the hunt was launched on a profile list
that included this boundary profile; the flag text claims `>5/2`
unconditionally).  These skeletons show negative-q consistent models
exist **at** `W = 5/2` in the Lean `ModeA` domain — relevant for domain
alignment (Lean ModeA admits negative q cells; cf. `ProperGaps`
normalization), but they do **not** refute `W ≤ 5/2`.

The earlier revision of this note claimed the vacuum lemma was
"probably FALSE in the Lean model" — that claim is withdrawn.  Status
returns to: **OPEN, unfalsified**.

## What the genuine `W > 5/2` profile scans found

| profile k | W | log | result |
|---|---|---|---|
| (3,3,1,1) | 5/2 (boundary, mislabeled campaign) | `v1_3311.log` | 3 consistent skeletons — boundary, not counterexamples |
| (3,3,2,0) | 21/8 | `v1_3320.log` | found 0, **deadline hit** (incomplete) |
| (3,3,2,1) | 11/4 | `v1_3321.log` | found 0, **deadline hit** (incomplete) |
| (3,3,3,3) | 4 | `v1_3333.log` | found 0, complete (883,176 nodes) |

So under the Lean ModeA semantics (negative q allowed, no edge-side
consistency): no strict `W > 5/2` consistent skeleton found, but two
profiles are incomplete — this is evidence, not a proof and not a
refutation either way.

## Caveats

- LP-based consistency check, exact Fractions, NOT Lean-checked.
- Negative-q consistent skeletons at `W = 5/2` do exist; whether the
  vacuum lemma holds may hinge on the nonnegative-cell / realizable
  domain (see `ProperGaps.ModeA.normalize`, `exists_nonnegative_model`).
