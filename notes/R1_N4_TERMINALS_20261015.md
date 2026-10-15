# Actual R1 seven-point terminals, 2026-10-15

The two seven-point boundary exclusions are verified. The full JSP404
lower bound, `sendov_lower`, and the prize submission remain incomplete.

| Boundary | Actual theorem | Verified evidence |
|---|---|---|
| T1: 7 points, potential 22 | `Jsp404.r1_seven_phi22_terminal` | `verification/r1-t1-terminal-20261015/` |
| T2: 7 points, potential 21 | `Jsp404.r1_seven_phi21_terminal` | `verification/r1-t2-terminal-20261015/`; published base `13cb6cb371acd8b046b861a471ddba3b75cb4522` |

Each theorem starts with actual plane points, Section4Legality, a positive
lambda with floor(pi/lambda)=4, a nonzero chart reference, distinct v/a,
defects 1/2 at those points, all remaining defects at least 3, and the
specified potential. The conclusion is False. No model, certificate
existence, terminal exclusion, or capacity callback is required from the
caller. Independent strongly typed original-API probes passed in normal
and `--trust=0` mode. Both terminal axiom closures are contained in
`{propext, Classical.choice, Quot.sound}`.

T1 has a complete 566-module project import closure. Its evidence combines
541 unchanged modules with previously verified standard-axiom evidence,
three separately reported unchanged baseline modules containing four old
admissions, and 22 newly executed standard-axiom modules. The borrowed
modules retain their original T2 context, source, transitive dependency,
artifact and raw receipt bindings. The new runs all used the original
single-process 4 GiB / 180 second resource guard. The T1 terminal does not
depend on the baseline admissions.

All 180 T1 canonical keys, six certificate specs and six rank branches are
retained. The original eight dispatch theorem statements are unchanged;
the dispatch corrections only fix proof calls, witness syntax, and
arithmetic normalization. The terminal normal/strict runs took
74.400/65.298 seconds. The independent API normal/strict runs took
66.810/64.226 seconds. Root's final acceptance is KERNEL_COVERED with no
pending modules or evidence errors.

T2's earlier complete evidence covers 1687 modules: 1684 standard-axiom
modules and the same three separately reported baseline modules. Its 972
canonical keys, 14 specs and 30 ordered rank pairs were verified.

The source reduction in `R1N4Capacity.lean` lists six boundary profiles.
The four remaining profiles have potential 21 and 8, 9, 10, or 11 points
(T3 through T6). The two verified terminals do not supply those exclusions
or complete the R1 assembly or the arbitrary-size geometric capacity
theorem.

Each evidence directory distinguishes archival receipt verification from
a fresh kernel rerun. The original retained runs, including the new T1
runs and its independent API probe, were actually executed. A duplicate
full clean-room 566-module T1 rerun was not performed after packaging;
the rerun entry point is separately checked for configuration readiness.
Quarantined overlapping probe attempts are forensic records and contribute
no accepted evidence.
