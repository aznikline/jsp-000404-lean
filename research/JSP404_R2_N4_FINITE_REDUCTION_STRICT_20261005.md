# Actual n=4 R2 finite reduction: strict conditional receipt (2026-10-05)

**SCOPED PASS — CONDITIONAL FINITE CAPACITY.** Final actual Lean `--trust=0` checking exited 0; all three public declarations print only `propext`, `Classical.choice`, and `Quot.sound`. It took 11.43 seconds and its maximum resident set size was 5997199360 bytes (5.585 GiB), below the explicitly authorized final 8 GiB limit. The run used `-M8000 -j1`; no full Lake build was performed.

The verified source is `Jsp000404/R2N4FiniteReduction.lean`. It imports only `Jsp000404.FivePointCapacity` and uses the original `Plane₂` point configuration, `Section4Legality`, angle/floor equation, nonzero reference vector, `directionRow`, `rowDefect`, and `potential`.

- `potential_ge_card_add_thirteen` proves the original potential is at least `t+13`: at floor4 the three specified distinct defect1/2/2 rows have scores3/2/2 and weights8/4/4; all other natural-score weights are at least1. It needs no HIGH-band hypothesis, no all-tail3 assumption, and no capacity premise.
- `r2_n4_eight_plus_impossible_of_eight_capacity` proves every actual R2 configuration with at least8 points is impossible **given** `hcap8`, a capacity<=20 bound for all actual legal eight-point R2 configurations at the same angle and reference vector. At size8 the preceding lower bound is21, contradicting the finite premise. For size>=9, actual `r2_tail_delete_closed` keeps the anchor/two low rows; actual legality erasure and `succAbove` transport meet the strong induction hypothesis. The floor, angle, and reference vector are preserved.
- `r2_n4_capacity_of_finite_eight_capacity` proves arbitrary-size actual R2 potential<=20 **given** `hfinite`, the corresponding capacity premise for actual sizes3..8. The three distinct rows force size>=3. Sizes3..7 use the finite premise; sizes>=8 are vacuous by the verified conditional exclusion. No arbitrary-size capacity premise is assumed.

**The finite premises are not proved here.** They remain explicit parameters over all actual finite R2 configurations at the given angle/reference. They are not declarations of axioms, assumed scalar profiles, or repackaged UNSAT diagnostics. The previous 27 Z3 results remain DIAGNOSTIC_ONLY. This receipt does not claim the original theorem is closed.

Final actual command:

```sh
/usr/bin/time -l lake env lean --trust=0 -M8000 -j1 -DautoImplicit=false -o .lake/build/lib/lean/Jsp000404/R2N4FiniteReduction.olean Jsp000404/R2N4FiniteReduction.lean
```

Its real stdout/stderr and time statistics are at `.lake/r2-n4-finite-reduction-strict8000-repair1-20261005.log`. The adjacent JSON binds the final source, compiled object, and log by SHA-256 and records every printed axiom set.

The initial3.5 GiB attempt failed during imported proof checking with a memory exception (exit134, 33.12 seconds, peak4.825 GiB). After an explicit increase to8 GiB, the next run reached the source and found a local implicit configuration inference error in the final consumer; that ordinary source error was repaired. The final run above passed. All three actual logs and outcomes are retained in the JSON attempt ledger; no resource-failure retry was performed under the unchanged lower limit.

Independent static review found no mathematical reduction/index transport gap. A source scan found no custom axiom, sorry, admit, native_decide, or assumeProfile. Existing proof files, prior weight helpers/diagnostics, and import/audit roots were not modified. No Git commands were run.
