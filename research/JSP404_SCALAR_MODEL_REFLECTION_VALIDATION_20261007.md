# Generic necessary scalar model reflection

2026-10-07 UTC: **READY — genuine strict and normal compiler PASS.**
Source: `Jsp000404/SatScalarModelReflection.lean`.

Final strict attempt 2 and genuine own-target normal attempt 1 exited 0 in
4.722 and 5.521 seconds. Seven selected declarations use exactly `propext`,
`Classical.choice`, and `Quot.sound`, with zero own warnings. Neither the
8 GiB nor 180 s guard fired. Inherited normal-build diagnostics are counted
separately in the compiler receipt.

## Exact mathematical scope

The new reflection applies to `SatScalarModel.GenericModel m n` at every
finite row count `m`. It reverses the row indices, sets
`theta'_i=delta-theta_(rev i)`, and reflects every shared chord through
height `n+2*delta`. It retains all necessary scalar fields and the full row
multisets. Every full linear gap, including both endpoints, is reversed;
the full linear gap score and row defect are correspondingly preserved.

The seven-row profile wrappers transport low ranks `(0,1)` to `(5,6)` and
back, with all five other defects preserved. They contain no terminal
impossibility premise or conclusion. No inverse planar realization, new
actual geometry, full eight-point exclusion, arbitrary scalar-pair exclusion,
R2 capacity, or original arbitrary-N completion is claimed.

## Actual source history

The owner's original 201-line SOURCE_ONLY candidate had SHA256
`809548921d0bd5c8737746c7e8db6d6bb2bd07a59b830b3005d9f5a2b42fca60`.
Its exact bytes remain in
`verification/sat-scalar-model-reflection-20261007/prior-source-only-candidate-source.lean`.
It was never compiled and is not a failed or PASS source. The old
SOURCE_ONLY receipt is an unchanged historical record.

Before the first check, with the owner's authorization, only the obsolete
status comment was made conditional on the dedicated producer receipt.
That candidate's SHA256 was
`69043b03452ec71e663f5a1b2147da627c8f2ba792b692d3e39dd1400db0e60b`.
Strict attempt 1 genuinely failed: bare `rowDefect` resolved to the outer
`Jsp404.rowDefect`, which expects a natural strip parameter, rather than the
intended `SatScalarModel.rowDefect` on a generic model. The failure snapshot
and raw stdout are preserved and classified NOT_PROVED.

The sole mathematical API repair qualified those 26 occurrences as
`SatScalarModel.rowDefect`. No original model, old six-point reflection, or
old PASS source was modified. The final source SHA256 is
`47a13a25b48b6454c60cd7be893890fad706b985faf2c356ff41f3bc3d7e1d54`.

The module also has the internally used public helpers
`erase_finRange_rev_perm` and `reflect_linearGapScore`; the whole-source
compiler checked them, while the selected axiom print list has seven names.
No separate composed root audit is claimed by this producer validation note.
