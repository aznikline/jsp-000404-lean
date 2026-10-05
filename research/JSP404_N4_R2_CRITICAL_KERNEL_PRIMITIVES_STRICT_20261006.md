# N4 R2 critical-kernel primitives: strict and normal receipt (2026-10-06)

**SCOPED PASS — 13 arithmetic helpers only.** Actual `lean --trust=0` exited0 and the actual Lake target built successfully. Every audited helper depends only on a subset of `propext`, `Classical.choice`, `Quot.sound`. Source and this receipt are frozen.

| Check | Wall time | Maximum RSS |
|---|---:|---:|
| strict0 single source | 7.80 s | 2.929 GiB |
| actual Lake target | 5.04 s | 2.944 GiB |

Source: `Jsp000404/N4R2CriticalKernelPrimitives.lean`. It proves full gap-list sum/nonnegativity, exact complete score from positive stated defect, n4 low score2, tail-defect4 gap<2, actual score/min-indicator hull, full-list score+indicator<=sum, unit-gap score lower bound, off-unit-gap indicator<=1, shared-end score sum<=3, and two actual Model-field four-step geometric negations. Those negations are derived, not masks supplied by the caller.

`indicator` is computed from each genuine score `floorNat(g)-1`; it marks positive score and differs from raw floor>=1 support. Whole row lists, both endpoints and full wrap are retained. Endpoint helpers retain explicit complete-list/arithmetic premises; their full Model endpoint instantiation is still to be assembled.

Actual logs: `.lake/n4-r2-critical-kernel-primitives-strict-20261006.log` and `.lake/n4-r2-critical-kernel-primitives-normal-20261006.log`. The JSON binds source, real artifacts and logs by SHA-256 and records all13 axiom sets. Real olean/ilean/trace/hash artifacts were produced; no fake trace or full Lake build was used. The new scope has0warnings; normal Lake output replays existing dependency warnings without modifying those frozen sources.

**The eight-point representative exclusion is not proved.** All27 old UNSAT placements remain diagnostics. No capacity/profile/solver verdict became a Model field; old frozen files, root imports/audits and Git were not operated on.
