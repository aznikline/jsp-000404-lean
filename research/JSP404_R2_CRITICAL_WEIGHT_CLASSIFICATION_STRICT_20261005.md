# R2 critical tail arithmetic: strict Lean receipt (2026-10-05)

**PASS for the four declarations in this independent scope.** Actual Lean `--trust=0` checking exited 0 and each public helper prints only `propext`, `Classical.choice`, and `Quot.sound`. The run took 2.09 seconds and its maximum resident set size was 1463042048 bytes (1.363 GiB), below the 3.5 GiB bound. It used one Lean thread and a 3500 MiB memory limit; no full Lake build was performed.

Source: `Jsp000404/R2CriticalWeightClassification.lean`.

The two main results are genuinely typed:

- `minimal_tail_count_classification`: for a finite tail T with weights in {1,2}, W=sum_T w>4 and every original-survivor total W-w(q)<=4, the count pair (weight2,weight1) is exactly one of (3,0), (2,1), (1,3), (0,5).
- `exists_over_four_subset_card_le_five`: any such weighted tail of total >4 contains U⊆T with 3≤|U|≤5 and sum_U w>4. This theorem does not assume the deletion inequality or a capacity bound. If T has at most five members take T itself; otherwise take any five members, whose weights sum to at least five. The lower cardinality bound follows because each weight is at most two.

The auxiliary typed results are `tail_sum_eq_counts` and `tail_sum_le_two_mul_card`. The classification proof derives W=count1+2*count2 and splits on whether a weight-1 member exists; the remaining conclusions use Nat arithmetic. There is no custom axiom, sorry, admit, native_decide, assumeProfile, assumed target profile, or assumed geometric mass bound.

The actual scoped command was:

```sh
/usr/bin/time -l lake env lean --trust=0 -M3500 -j1 -DautoImplicit=false -o .lake/build/lib/lean/Jsp000404/R2CriticalWeightClassification.olean Jsp000404/R2CriticalWeightClassification.lean
```

The command's real stdout/stderr and time statistics were captured in `.lake/r2-critical-weight-classification-strict-20261005.log`; the adjacent JSON receipt binds the source, compiled object, and log by SHA-256 and records the printed axiom sets.

This scope supplies the finite arithmetic behind the at-most-eight-centre R2 reduction. It does not prove the actual geometric deletion bridge, the generalized seven/eight-centre chart interface, a scalar certificate, or the original theorem. The prior 27 Z3 UNSAT placements remain diagnostics. Existing proof files, old diagnostics, import roots, and audit roots were not changed. No Git commands were run.
