# HIGH4 R0 eight-point positive scalar diagnostic — one recorded probe

**DIAGNOSTIC ONLY / ZERO KERNEL DECLARATIONS.** This note records the existing Root-authorized single probe in `verification/oct8-r0-eight-positive-scalar-probe-once/`. Preparing this package ran no Lean, solver or search and changed no mathematical source, Root/Audit or STATUS count. The measured mathematical baseline remains11040 jobs/2795 declarations; this packet adds0.

The actual result is `unsat` from one QF_LRA solver check: solver3.7463887499761768s, total wall3.9794019580003805s, peak worker-tree plus controller79184KiB, process exit0, resource_stop=null. The resource receipt records a512MiB budget and120s outer budget. The source sets a95000ms solver timeout and105s CPU limit; the shared controller stops at110s with a5s termination grace. No budget was reached. `solver_checks=1`, `solver_runs=1`, and outer word/profile enumeration=false.

The encoded relaxation has fixed m=7,n=4 and HIGH1/2<=delta<1. It uses seven ordered fan coordinates with0<=theta_i<=delta,21 shared real chords, all35 triangle alternatives and seven complete rows. Each row has six non-diagonal chord entries and seven gaps: both endpoint gaps plus all five internal gaps. All49 gaps are nonnegative. Each row is merely required to have some gap>=2, the weak positive-score condition; there are seven such alternatives per row. The serialized assertions declare29 Real variables and0 Int variables. No distinguished heavy row, exact integer-floor profile, theta0=0 gauge, potential equality or minimum-Model premise is supplied.

`problem.smt2` is the exact serialized assertion set from `solver.sexpr()`. It does not itself contain `(check-sat)`; the one actual check is the subsequent `solver.check()` in the frozen probe source. The raw worker output and JSON result both report UNSAT. This is external solver evidence, **not a Lean certificate** and not a proven R0 contradiction.

The independent verifier uses only stdlib `Fraction` arithmetic and imports neither the encoder nor a solver. If a rational SAT candidate were returned, it would recompute21 corridor checks,35 triangle arms, all49 complete gaps/floors and the actual positive scores, together with the anchor gaps. Here no SAT model was returned, no candidate file was produced and that Fraction-SAT validation branch was **not triggered**. Merely shipping the validator does not constitute validation of an UNSAT proof.

| Frozen item | SHA256 |
| --- | --- |
| New probe tool and exact source snapshot | `7673c5cec44479aab8c9e19bf592573910d2cd9fa82c908f68699566b4f2b4e9` |
| Independent Fraction validator and exact snapshot | `f35e72dc983dbae2364e25936b75f2a0333f840e6c2c877f7fe191eb7599cbaa` |
| Serialized `problem.smt2` | `bdc36a9ddd4b295b80cf3a69571d14d211b579a8f91831d740f10f15561ddcec` |
| Actual `result.json` | `fed3d050a768a928c2961f8d44fe66ce7483f11c967582a0cac7f2500472872e` |
| Actual resource receipt | `95dc74c945348171c6aff714c8d786059bedf8d0f589355590b3f58c7ca86a1e` |
| Actual raw worker output | `094e669e2162085a4effe8d0793613f9837427804b86e4bdbcfe49d3f09246cd` |

The `.log` output is retained locally unchanged. Its published `worker.stdout.txt` is an identity copy with the same hash, not a rerun or a replacement original path. The publication manifest records both paths. Existing R1-named helpers are included only because the new probe reuses their controller and source-copy mechanism. The new module replaces `guard.worker` and `guard.__file__`; the older R1 worker's heavy/gauge/integer encoder is not the executed m7 encoder. All four snapshots match their corresponding tool bytes. The common RSS monitor is an existing unchanged dependency. Preparatory SOURCE_ONLY headers are preserved as historical source bytes.

The static R2 review was reported separately; it supplies no new kernel result here. This packet does **not** establish R0False, exact full-kappa1, weight22, planar realizability, an original HModel contradiction or general capacity. The R0 potential22/card8 reduction remains the earlier PAPER route awaiting kernel implementation. The next formal frontier is an actual fixed-m7 positive decoder/cycle/DAG checker, a genuine kernel-checked root and the original geometric bridge. Diagnostic UNSAT, partialDAG and source-closed labels cannot replace those checks. The original lower theorem and the general problem remain OPEN.
