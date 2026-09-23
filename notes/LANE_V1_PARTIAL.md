# Lane V1 (vacuum lemma) — partial results, lane cancelled

Status: **CHECKER-VALIDATED evidence, not Lean theorems.**  The lane was
cancelled mid-hunt; this note archives what the logs show.

## Target

`sk.Proper → sk.Consistent n → sk.W n ≤ 5/2` (the "vacuum lemma" that
would make `GadgetSelectionHighP` vacuous).

## Headline finding: the vacuum lemma is probably FALSE in the Lean model

`tools/v1_hunt.py` enumerates W>5/2 profiles at s=4 under the *Lean*
semantics — `ModeA` as formalized allows **negative q cells** (no
`0 ≤ q ≤ n`, no per-gap `q + r ≥ 0`) and has no edge-side consistency.
That is a strictly larger domain than the geometric/checker model used
by Lane E2's census.

`tools/v1_3311.log` — profile search found **3 consistent skeletons at
W > 5/2**, e.g. qs containing `-1` and `4`:

```
*** CONSISTENT (Lean) skeleton at W>5/2 ***
[{'order': [1,2,3], 'bits': {'1':0,'2':0,'3':0}, 'qs': [0,-1,4]},
 {'order': [0,2,3], 'bits': {'0':0,'2':0,'3':0}, 'qs': [0,-1,4]},
 {'order': [0,1,3], 'bits': {'0':0,'1':1,'3':0}, 'qs': [0,0,2]},
 {'order': [0,1,2], 'bits': {'0':0,'1':1,'2':1}, 'qs': [1,0,2]}]
STATS {..., 'found': 3, ...}
```

Consequence: `Proper → Consistent → W ≤ 5/2` is very likely refutable
inside the current Lean `ModeA` — the counterexamples exploit negative
q cells.  Repair candidates: add a nonnegative-cell hypothesis (cf.
`ProperGaps.ModeA.normalize` / `exists_nonnegative_model`, which show
closed remainders can be normalized to nonnegative cells), or
edge-side consistency.  **Not yet Lean-verified** — kernelizing one of
the found skeletons as a `ModeA` witness is the obvious next step.

## Other profiles (s=4, W>5/2)

| profile k | log | result |
|---|---|---|
| (3,3,2,0) | `v1_3320.log` | found 0, **deadline hit** (incomplete) |
| (3,3,2,1) | `v1_3321.log` | found 0, **deadline hit** (incomplete) |
| (3,3,3,3) | `v1_3333.log` | found 0, complete (883,176 nodes) |

## Caveats

- LP-based consistency check, exact Fractions, but NOT Lean-checked.
- The hunt space itself is bounded by the heuristics in `v1_hunt.py`
  (q bounds justified by arc structure, see file header).
- Negative-q consistent skeletons may or may not survive the geometric
  realizability the application actually needs — the repair hypothesis
  must match what `ProperGaps`/the geometry adapter can supply.
