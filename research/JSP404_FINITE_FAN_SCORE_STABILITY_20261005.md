# Complete finite-permutation fan score bridge

## Scope

Owned new source: `Jsp000404/FiniteFanScoreStability.lean`.
Frozen `GapSplitFloorStability.lean` and
`ActualScorePreservingExpansion.lean` were not edited. No root imports,
commit, full Lake build, numerical/LP/SMT search, or other-lane source edits
were performed. Only scoped strict source validation is used here.

## Exact interface

For any nonempty finite label type `α`, let `A : ℝ → α → ℝ`. Assume only:

* every coordinate `ε ↦ A ε i` is continuous at zero;
* every limiting coordinate `A 0 i` lies strictly in `(0,π)`;
* `0 < τ < λ`.

The file internally enumerates `α` using `(Fintype.equivFin α).symm` and
internally sorts each actual tuple using `Tuple.sort`. Its complete public
interface is:

```lean
exists_finite_sorted_score_stability
  (A : ℝ → α → ℝ)
  (hcont : ∀ i, ContinuousAt (fun eps => A eps i) 0)
  (hrange : ∀ i, A 0 i ∈ Set.Ioo 0 Real.pi)
  (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
  ∃ lam', tau < lam' ∧ lam' < lam ∧
    ∀ᶠ eps in 𝓝 (0 : ℝ),
      rowScore lam' (finiteSortedFan (A eps)) =
        rowScore lam (finiteSortedFan (A 0))
```

The underlying `exists_sorted_gap_floor_stability` proves the stronger
coordinate-by-coordinate equality of every actual sorted `gapAfter` floor,
with one common `λ'`. The `rowScore` equality is obtained from the existing
`exponents_entry_eq_rowScore` / cyclic-gap identity and a finite index
equivalence. No caller supplies a floor event or sorting permutation.

## Proof structure

1. Sort the limiting tuple canonically and collect its actual nonnegative
   gaps. Keep every zero gap caused by duplicates and keep the wrap.
2. Apply the frozen finite floor-margin theorem to that finite gap list.
   It chooses a single `τ<λ'<λ`. Positive floors have strict lower margins;
   every floor has a strict upper margin.
3. For each of the finitely many label permutations that sorts the limit,
   `Tuple.comp_sort_eq_comp_iff_monotone` identifies its **value tuple** with
   the canonical sorted value tuple. This does not identify the permutations
   themselves and therefore does not eliminate duplicate labels.
4. Every gap of each fixed permutation is a continuous linear `gapAfter`
   formula. Derive its floor event from continuity and the strict margins.
   Use `eventually_all` over the finite permutation type and finite gap
   indices to intersect all events at the already chosen common parameter.
5. The frozen intercluster/sorting-limit theorem says that, for sufficiently
   small `ε`, any permutation sorting the actual tuple also sorts the limit.
   The actual `Tuple.sort (A ε)` always sorts the actual tuple, so the finite
   intersection covers it even when it varies with `ε`.
6. Preserve each actual sorted gap floor, then sum its natural-floor score.

This proves the finite-permutation event aggregation requested in this lane.
It never asserts global continuity of cut representatives, a changing
`cycGaps` list, or a fixed sorting permutation.

## Edge cases

The theorem requires nonempty labels, not two or more labels. For cardinality
one, its sole genuine wrap is `π`; the frozen fixed-gap formula is
`a_first+π-a_last`, so it remains the full circle. If all limiting values
coincide but there are several labels, the gap list consists of zero gaps
and the same full-circle wrap `π`. Partial repetitions are also retained.
Neither injectivity nor strict monotonicity of the limiting values is assumed.

## What this does not assert

This is the complete analytic finite-fan bridge. It does not yet identify
each normalized actual pair-expansion ray family with the original geometric
`directionRow`, construct its safe reference, identify its old limiting score
after the end split, or perform recursive weighted inflation. Those are
separate remaining geometric/assembly steps.

For the forthcoming end split, a post-gap boundary coordinate zero cannot be
fed directly into the frozen chart-continuity theorem. Use an interior empty
gap cut, for example `a=λ/2`: old first `a`, old last `a+π-G`, and new axis
`a+π-λ` all lie strictly in `(0,π)`, while the two new incident gaps remain
`G-λ` and `λ`. The same construction handles `G=π`.

## Validation

The first scoped `lean --trust=0 -o ...` invocation passed with exit zero in
**3.571 s**, no warnings, and a real
`.lake/build/lib/lean/Jsp000404/FiniteFanScoreStability.olean`. Its five
audited exports all printed only `propext`, `Classical.choice`, and
`Quot.sound`:

* `indexedGap_sorted_nonneg`;
* `exists_sorted_gap_floor_stability`;
* `rowScore_sortedFan_eq_sum`;
* `exists_sorted_score_stability`;
* `exists_finite_sorted_score_stability`.

Frozen source SHA-256:
`d113b7e023b6980ab92c63856b79315d6ae72ddb1afb04a6282ead0b17c3fce2`.
The actual captured stdout, command, source hash, and resource receipt are
`.lake/finite-fan-score-stability-strict-20261005.log`.
`/usr/bin/time -l` maximum RSS was **3,141,009,408 bytes**; sampled Lean RSS
peak was **3,049,029,632 bytes**; process-group peak was **3,750,756,352
bytes**. The actual Lean process stayed below the authorized 3.5 GiB cap;
the process-group sum was recorded only and did not control admission.
All compiler processes exited. No source repairs or second verification
were needed, and the source is now frozen.

This is a strict PASS for the complete analytic finite-permutation bridge.
No higher-strip or all-`n` capacity claim follows merely from this result.
