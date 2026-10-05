# Actual generic SatChart extraction: strict Lean receipt (2026-10-05)

**SCOPED PASS.** Both new modules passed actual Lean `--trust=0` with exit0, no errors/warnings, and only `propext`, `Classical.choice`, `Quot.sound` for all13 audited helpers. Runs were sequential, one thread, below the authorized8 GiB limit; no full Lake build was performed.

| Module | Seconds | Maximum RSS | Audited helpers |
|---|---:|---:|---:|
| SatScalarModel | 3.84 | 2.919 GiB | 3 |
| SatScalarExtraction final | 10.46 | 5.586 GiB | 10 |

`SatScalarModel.GenericModel m n` contains only necessary scalar fields: hn3, delta/range, theta/order/bounds, shared symmetric d, all corridors/triples, full rowxs sorted/permutation. It contains no profile, capacity, solver outcome or planar-realizability field. Its rowDefect is the exact complement of existing `linearGapScore1(theta_i,theta_i+n+delta,rowxs_i)`. Typed helpers bound every chord/retained row entry and prove length m-1.

The actual extractor needs only the existing `SatChart C` on Fin(m+1), plus m>=2 for exact defects. It internally orders theta, proves the rank permutation sigma bijective, normalizes actual data by positive lambda, and derives every model field from C. Full finRange.erase lists and multiplicities are retained. Both actual linear endpoints and the full wrap are preserved. For every row, `model_rowDefect` equals the original full configuration's actual defect at `v.succAbove(sigma i)`.

`model_delta` and all three exists_model results expose `M.delta=pi/lambda-n`, transferring an actual HIGH condition. `exists_model_seven/eight` provide GenericModel6n/GenericModel7n with every actual non-anchor defect. GenericModel5n copies all fields into the frozen ModelSix n; its defect equality is rfl.

The JSON binds final sources, compiled objects, real logs and commands by SHA-256. Actual logs: `.lake/sat-scalar-model-strict-20261005.log` and `.lake/sat-scalar-extraction-strict-fullnames-20261005.log`. One prior extractor run also exited0; the final rerun moved only the full-name printing option outside its section to spell all standard axiom names fully.

This closes the actual-to-generic-scalar interface, including seven/eight centres. It proves no capacity or critical-profile impossibility and claims no inverse planar realization. The27 prior Z3 UNSAT results remain diagnostics awaiting Lean certificates. Old sources/diagnostics, weight/finite-reduction helpers, old ModelSix, root imports/audits, and Git were not modified or operated on.
