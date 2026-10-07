# Actual zero-pair deletion budget: static implementation handoff

Status: SCOPED PASS. The producer ran one guarded strict check at a time,
then the genuine normal module target. All four selected declarations have
exactly the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
No Git or quota command was run, and no old PASS source was modified.

Source: `Jsp000404/ActualZeroPairDeletionBudget.lean`.

## Actual interface

`actual_zero_pair_deletion_budget` takes an original
`ActualMinimalBandCounterexample.Model ... 16 (s+2) c lambda`, `3 <= s`,
an original index `p`, and an intermediate index `q`. Its only additional
configuration hypotheses are that the original scores at `p` and
`p.succAbove q` are zero.

The original potential 17 is derived inside the proof, so no separate F17
argument is needed. The caller supplies no second-deletion cap, desired
gain array, flatness, equality classification, or inflation assertion.

The result uses local abbreviations whose definitions are actual functions:

* `d = c ∘ p.succAbove`;
* `k i` is the original score at `p.succAbove i`;
* `g i` is the actual `rowGain` for deleting `q` from row `i` of `d`.

It proves original potential 17, first-deleted potential 16, retained old
weight sum 15, and the exact multiplicative budget

`sum_(i != q) 2^(k i) * 2^(g i) <= sum_(i != q) 2^(k i) + 1`.

Every positive original score has second gain zero; every surviving second
gain is at most one; there is at most one survivor with positive second
gain; every such survivor has original score zero. Finally the actual twice
deleted potential is 15 or 16.

## Proof boundary

The first deletion uses the existing
`actual_minimum_score_critical_form`. Its retained-score equalities identify
the intermediate scores with the original surviving scores, and removing
the second unit-weight point leaves baseline weight 15.

The second-deletion cap follows directly from **the original**
`H.minimum_card`: a twice-deleted actual configuration over 16 would have
cardinality `s`, contradicting the original least counter-cardinality
`s+2`. Hereditary legality comes from two applications of
`Section4Legality.erase`. The intermediate potential-16 configuration is
never treated as a counterexample or critical model.

The exact actual deletion ledger is reused from
`ActualMinimumDeletionNormalForm`. Three small weighted arithmetic lemmas
isolate its one-unit expense; existing `FlatDeletionBudget` expense lemmas
then give gain bounds and uniqueness. Their use is arithmetic and does not
assert that the intermediate configuration is flat.

## Static review and actual verification

Read-only API review covered the two-erase legality signature, the original
minimum-cardinality call, `Finset.sum_erase_add`, and definitional equality
of `Fin (s+2)` with `Fin ((s+1)+1)`. Actual elaboration then found two local
API issues: the restricted simplifier did not calculate `16+1`, and the
row-score rewrite needed an explicit bridge for the local configuration
`d`. These were repaired only in the new leaf.

| Check | Exit | Seconds | Peak process-tree RSS, KiB |
| --- | ---: | ---: | ---: |
| Strict attempt 1, failed API check | 1 | 87.408 | 4,223,984 |
| Strict attempt 2, final `--trust=0 -M8192` | 0 | 68.397 | 4,220,864 |
| Genuine `lake build Jsp000404.ActualZeroPairDeletionBudget` | 0 | 87.181 | 4,105,056 |

All runs used an 8 GiB process-tree guard and a 300-second time guard;
none hit either limit. Every attempt has its exact pre-dispatch source
snapshot and raw stdout, including the failed original 179-line source.
The normal log confirms this module was actually built and that the build
completed successfully. Both successful runs print all four selected
declarations with standard axioms only, and the final leaf has no warnings.

Frozen final source SHA-256:
`880995a7391a08a1a2048662302b998e20fa2f83acf3d6fd74262ec8d2c9e380`.
The companion JSON records exact log, snapshot, selected-name, runner, and
real normal-artifact hashes. The sole compiler window was explicitly
released to the Partition producer immediately after the normal run.

This leaf proves no LOW flat/all-zero convex-hull shortcut, no final F17
exclusion, no capacity theorem, and no transfer of zero gains through
inflation.
