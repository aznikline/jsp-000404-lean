# Actual maximal LOW row: two-clump producer

Status: **SCOPED PASS** for the single public producer. The corrected source passed a strict `--trust=0` check and a genuine normal target build. Both checks report only `propext`, `Classical.choice`, and `Quot.sound`, with zero warnings from this file. This is a row-clump producer result, not a capacity theorem.

Owned source: `Jsp000404/ActualMaximalLowRowClumps.lean`.

## Public contract

`ActualMaximalLowRowClumps.exists_actual_maximal_low_row_clumps` takes:

- a genuine finite configuration `c : Fin s → Plane₂`, with `3 ≤ s` and its original `Section4Legality c lam`;
- an integer `n ≥ 4` and the actual LOW interval `π / (n + 1/2) < lam ≤ π / n`;
- an original full-hull vertex `p`;
- the original actual row score `rowScore lam (directionRow o e c p) = n - 2`, with a nonzero reference `e`;
- two original noncentral distinct rays whose actual physical angle is at least `2 * lam`.

It returns `Nonempty (Data n o c lam p)`. The data contains an internally produced actual hull `Window`, a positive integer internal gap score, and the existing public `ActualHullSmallScoreTypes.Clumps` for separation `2 * lam` and total remaining width

`R_n = π - (n : ℝ) * lam`.

The data also proves `0 ≤ R_n` and `R_n < lam / 2`. In particular, public Clumps methods give:

- `D.clumps.same_angle_le hleg`: equal computed Bool codes imply actual angle at most `R_n`;
- `D.clumps.different_angle_ge hleg`: unequal codes imply actual angle at least `2 * lam`;
- `D.clumps.actual_witnesses`: both computed clumps contain distinct actual noncentral ray witnesses.

The caller supplies neither a Window nor a gap, cut, class, partition, normalized row, or mass budget. No minimal-counterexample Model, potential bound, F17/F18 assumption, or subset-criticality hypothesis is used.

## Actual bridge

The producer obtains `Support` from the already public
`ActualHullSmallScoreTypes.exists_actual_hull_full_row_support`.
Only public fields are consumed. For this actual original full row, the outside gap is `E = π - W.width`, belongs to its actual cyclic gap list, and satisfies `E ≥ lam` and `floor(E / lam) ≥ 1`.

The new file includes the minimal adjacent-list and accounting helpers needed because their counterparts in Types are private. It does not name or call any private declaration from another module. The existing public, scale-independent `ActualMixedRigidCardinality.actual_window_angle_le_width` bounds the supplied wide actual pair by the produced physical Window width.

## Scalar accounting with multiplicity

Write `k` for the sum of internal gap scores, `b` for the outside gap score, and `t` for the number of positive-score internal gaps. Lists and filters retain every occurrence. The full actual score identity gives

`k + b = n - 2`.

For a positive-score gap `g`, the natural-floor definition gives

`(gapScore(lam,g) + 1) * lam ≤ g`.

Summing this over the internal list gives `(k + t) * lam ≤ W.width`. Because `E ≥ lam`, even when its score is zero the outside gap satisfies `(b + 1) * lam ≤ E`. Consequently

`(k + t + b + 1) * lam ≤ π`.

If `t ≥ 2`, the integer identity forces `(n + 1) * lam ≤ π`, contrary to the strict LOW lower endpoint. Thus `t ≤ 1`.

If `k = 0`, the outside score is `n - 2`, so `E ≥ (n - 1) * lam`. The actual wide pair gives `W.width ≥ 2 * lam`, again forcing `(n + 1) * lam ≤ π`. Therefore `k > 0`, the positive internal filter has exactly one occurrence, and that actual adjacent gap `g` has score exactly `k`.

It follows that `g ≥ 2 * lam` and `E + g ≥ n * lam`. Hence the two actual endpoint spans have total width

`W.width - g ≤ π - n * lam = R_n`.

The source extracts the actual adjacent endpoints from the complete sorted original row, proves that every original noncentral ray lies to one side of this actual cut, and constructs the existing public Clumps object. The actual gap membership is proved from the full cyclic-list decomposition; it is not a caller premise.

## Check boundary

The source now has a strict and genuine-normal verification receipt. The original static candidate, first strict failure, and each subsequent checked source snapshot remain in `verification/actual-maximal-low-row-clumps-20261007/`. The first strict run failed on the two list API names `List.length_eq_zero` and `List.length_eq_one`; changing them to `List.length_eq_zero_iff` and `List.length_eq_one_iff` was the entire repair. No mathematical statement, original definition, public Data field, or producer input changed.

Strict attempt 2 exited zero in 28.77 seconds; genuine normal attempt 1 exited zero in 21.85 seconds and actually built `Jsp000404.ActualMaximalLowRowClumps`. Both checked the same source SHA `be3fadb794370c98c3e62db1e75bc0fa6c7768f873f628ae3328d8a75904d148`. Each used the existing single-target guard with an 8 GiB sampled single-Lean RSS cap and a 180-second wall cap; neither cap fired. The largest sampled single-Lean RSS in the successful routes was 6,027,558,912 bytes. The sole heavy window was formally returned to Root after both processes exited and the absence of active Lean/lake processes was checked.

The machine-readable receipt is `research/JSP404_ACTUAL_MAXIMAL_LOW_ROW_CLUMPS_RECEIPT_20261007.json`. Raw output is preserved byte-for-byte. Existing checked Types and other source files were not modified; no Git, whole-project build, or quota operation was run. No F17/F18 capacity or arbitrary-configuration theorem is claimed by this receipt.
