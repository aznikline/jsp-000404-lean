# Actual LOW maximal observers: checked leaf

Status: **SCOPED_PASS_ACTUAL_LOW_MAXIMAL_OBSERVERS**. The first strict
`--trust=0` check and first genuine normal build both exited zero on the
same source. All three selected exports have exactly the standard
three axioms. This is a checked leaf, not a final global capacity proof.

## Source and scope

- Source: `Jsp000404/ActualLowMaximalObservers.lean` (137 lines).
- Source SHA-256: `bf55a05e4aba4991c9e7a8a8be676fd0f8d37439609d491d514b2d6ac7af2ef2`.
- Original model: `ActualMinimalBandCounterexample.Model o e
  (π / (n + 1/2)) (π / n) (2^n) (s+1) c λ`, with `n ≥ 4` and `e ≠ 0`.
- The deletion and three-observer conclusions require `3 ≤ s`, so the
  original actual configuration has at least four points.
- No F17/F18 hypothesis, flatness, caller score bound, gain budget,
  hull certificate, window, classes, or companions is accepted.

The three public exports are:

1. `actual_low_score_le_maximal`: every original observer has score at
   most `n-2`.
2. `actual_maximal_observer_gain_eq_zero`: if the original observer `p`
   has score `n-2`, deleting any other original target `q` gives zero
   row gain at `p`.
3. `no_three_nonacute_maximal_observers`: an injective selection of
   three original score-`n-2` observers, each with an actual ray pair
   making angle at least `2λ`, is impossible.

The score and wide-pair hypotheses in the last theorem concern the
original actual configuration, not its selected three-point subset.

## Internal proof chain

The original LOW band gives `floor (π/λ) = n`. The existing public
`low_model_nonsaturated` theorem gives original row defect at least two.
Together with the actual row-cell bound and
`rowScore_eq_sub_defect`, this proves the original score bound.

For a maximal-score observer, a positive gain after deleting a target
would satisfy Certificate A: the target score is at most the observer
score. `removable_of_gain1_ge` therefore makes that original target
removable, contrary to the original model's `not_actual_removable`.
The emitter is `p`; the deleted target is `q` throughout this argument.

An original score `n-2`, with `n ≥ 4`, also forces row defect at most
two. The public full-hull theorem therefore supplies original hull
membership. `exists_actual_maximal_low_row_clumps` then constructs the
actual two-clump data from the original row and the actual wide pair.
The common same-clump bound is `R = π - nλ`; different clumps have
actual angle at least `2λ`.

If an original target had no distinct same-clump companion, all other
actual rays at that observer would be in the opposite clump. Their
angles with the target would all be at least `2λ`, hence at least `λ`.
The existing actual emission lemma would give positive row gain,
contradicting the internally proved zero gain. This constructs the
`TwoClusters.companion` field internally.

Finally, the original strict band lower bound gives `R < λ/2` directly
for symbolic `n`. The new `SmallTwoClusterGeometry` core excludes three
such actual centers. No specialized `n=4` inequality is reused here.

## Checked dependency sources

- `ActualMaximalLowRowClumps.lean`: 309 lines,
  SHA-256 `be3fadb794370c98c3e62db1e75bc0fa6c7768f873f628ae3328d8a75904d148`.
- `SmallTwoClusterGeometry.lean`: 217 lines,
  SHA-256 `55d261ffc65167b022ed93dceccab25cd4172ad4bba76de9163fa7bb37b75fb9`.

Static checking used the actual public signatures and a separate
read-only check of the generic score/Certificate-A API direction.
Both dependency owners independently checked their public interfaces,
the common remainder, companion-negation direction and observer/target
roles and reported no concrete mismatch. No old PASS source was changed;
no Git operation was performed.

## Verification and release

- Strict attempt 01: actual exit 0, 28.0147 seconds, sampled peak process
  tree RSS 6,492,560 KiB; three selected standard-three-axiom results.
- Genuine normal attempt 01: actual exit 0, 18.2500 seconds, sampled peak
  process tree RSS 6,557,488 KiB; the own module was genuinely built and
  the build completed successfully (9017 jobs). All three selected
  standard-three-axiom results were printed again.
- Source unchanged throughout; no failed attempts or API repairs.
- One own `push_neg` deprecation warning is retained and counted in
  each check. Inherited normal warnings are accounted separately in the
  receipt. No warning suppression or extra compiler round was used.
- Guard: one Lean process globally, 8 GiB process-tree RSS, 180 seconds;
  no resource stop occurred.
- Source snapshots and complete raw outputs are preserved under
  `verification/oct7-actual-low-maximal-observers/`; the receipt is
  `research/JSP404_ACTUAL_LOW_MAXIMAL_OBSERVERS_RECEIPT_20261007.json`.

After both processes exited, the sole heavy window was formally handed
directly to `seven_ha_hm_math` for the root-ordered PureLightBlock check.
No further Lean invocation was made while preparing this receipt.
