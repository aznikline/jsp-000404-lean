# Exact actual potential inflation: strict receipt

New owned source: `Jsp000404/ActualPotentialInflation.lean`.
Previously proved SingleSplit, SafeFanReference, UniformFanScoreStability,
and all earlier helper sources remain frozen. No root imports, audit edits,
commit, full Lake build, or account-quota operation were performed here.

## Complete proved interface

```lean
exists_exact_actual_inflation
  (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
  (hs : 3 ≤ s) (c : Fin s → Plane₂)
  (hleg : Section4Legality c lam)
  (htau0 : 0 < tau) (htau : tau < lam) :
  ∃ lamFinal, tau < lamFinal ∧ lamFinal < lam ∧
    ∃ cFinal : Fin (potential lam (directionRows o e c)) → Plane₂,
      Section4Legality cFinal lamFinal
```

Thus the final actual configuration has exactly
`F = ∑ i, 2^(rowScore lam (directionRow o e c i))` distinct plane points.
Distinctness is the injectivity field of the produced Section4Legality,
and cardinality is the exact `Fin F` domain. The angle parameter remains
strictly above the caller's threshold and strictly below the original scale.

No capacity, point-cardinality bound, scalar-array realization, removable
vertex certificate, or prescribed score-preservation event is a hypothesis.
The final parameter's row scores are not additionally asserted to be zero.
In the terminal case the angle cap is weakened directly; this avoids an
unnecessary chart-seam or floor-stability condition on the old fan.

## Termination proof

The source proves `s ≤ potential` from each natural power being at least one.
If `s < potential`, at least one actual row has positive score; otherwise
all scores are zero and the potential equals `s`.

Strong induction is on the natural surplus `F-s`.

* At `F=s`, retain the original points, reindex onto `Fin F`, and choose the
  midpoint parameter `(tau+lam)/2`. Its weaker angular cap preserves legality.
* At `F>s`, invoke the frozen genuine single-positive-row split. It produces
  actual legal `s+1` points at a common smaller parameter, while preserving
  `F` exactly. The surplus therefore decreases by one. The inductive result
  is reindexed back from the equal new potential to the original `Fin F`.

Every step calls SingleSplit on the actual current configuration and newly
extracts a positive genuine gap and its endpoint axis. No original axis is
reused across generations. The number of points never falls below three,
and the fixed positive threshold is preserved through the entire finite run.

## Strict validation

The first scoped invocation
`lean --trust=0 -o .lake/build/lib/lean/Jsp000404/ActualPotentialInflation.olean ...`
passed with **exit 0**, **3.558 s**, **zero warnings**, and a real `.olean`.
All four audited exports used only `propext`, `Classical.choice`, and
`Quot.sound`:

* `card_le_potential`;
* `exists_positive_score_of_card_lt_potential`;
* `Section4Legality_weaken`;
* `exists_exact_actual_inflation`.

Frozen source SHA-256:
`fb922937f4ca56fa29f7a1ae9b789b46aaa24749bd68077d47d10ea4567b7abb`.
Actual captured stdout, command, hash, and resource receipt:
`.lake/actual-potential-inflation-strict-20261005.log`.
Time maximum RSS: **3,151,118,336 bytes**; sampled actual Lean peak:
**3,090,579,456 bytes**; sampled process-group peak: **3,791,208,448 bytes**.
Actual Lean stayed below the authorized 3.5 GiB admission threshold; the
group sum was recorded only. The scope ran after the N4 extractor heavy
processes had exited and was coordinated with the permitted lightweight
pure-Nat lane. All own compiler processes exited and their slot was released.

## Remaining global boundary

The genuine weighted-to-ordinary-point inflation bridge is now formally
proved. It does not by itself prove the sharp ordinary-point cardinal bound
in every higher strip. A separately proved ordinary-point bound can consume
the final legal configuration to obtain the weighted capacity; treating that
missing bound as already known would remain circular. No all-`n` closure is
claimed in this receipt.
