# Actual maximal LOW row: two-clump producer

Status: **SOURCE_ONLY**. No Lean invocation, strict check, genuine-normal check, or kernel-success claim accompanies this note.

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

All arithmetic and actual bridges above are implemented in the new source, but their elaboration is unverified. An independent read-only static audit found no definite type/API mismatch in the Support bridge, positive-filter accounting, singleton extraction, cut reconstruction, or output fields. Static audits are not a strict or normal Lean check. Existing checked Types and other source files were not modified. A later authorized verification window must preserve the candidate, check the new target, and record any actual API failures and repairs before changing this status.
