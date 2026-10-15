R1-T1-ACTUAL-TERMINAL: seven-point Phi=22 exclusion (archival evidence)

Jsp404.r1_seven_phi22_terminal (Jsp000404/R1DispatchT1.lean) proves False
for actual Fin 7 plane points satisfying Section4Legality, lambda > 0,
floor(pi/lambda)=4, a nonzero reference, distinct saturated v and defect-2 a,
all other defects >=3, and potential=22. Chart, model and certificates are
constructed internally. The original theorem signature is retained
(root_dispatch_statement_ledger.json: 8 statements byte-identical).

Module coverage: complete 566-module import closure.
- 541 modules BORROWED from the verified T2 lane
  (verification/r1-t2-terminal-20261015): identical source bytes, original
  T2 context/dep_fp/audit/olean provenance retained verbatim.
- 3 unchanged baseline modules BORROWED_NON_STD3 (pre-existing admissions;
  excluded from passed count).
- 22 T1-specific modules verified FRESH under the new T1 context:
  normal compile + --trust=0 + declaration axiom audit, all Std3.

Coverage: 180 canonical keys, 6 certificate specs, 6 s2-rank branches
(t1_input_manifest.json coverage block; dispatch carries 6 r1t1_u* calls
under fin_cases ra).

Final independent acceptance: root_t1_acceptance.json is KERNEL_COVERED.
The Root-exclusive original-API probe (root_terminal_probe_state.json,
probe sha bound to root_probe_pin.json) confirms r1_seven_phi22_terminal
and r1_phi22_all_defect3 each depend only on propext, Classical.choice and
Quot.sound, in both normal and --trust=0 runs.

Scope honesty: T1+T2 are two of the six n=4 R1 profile boundaries.
T3-T6, R1N4Boundary assembly, CertExists, sendov_lower and the complete
JSP404 lower bound remain OPEN. Archival verification is not a fresh
kernel rerun; reproduce/ is the resumable fresh path (full 566 modules,
original guard, no borrowing).

Inspect recorded evidence without binary caches (cross-platform, no Lean):
  python3 verification/r1-t1-terminal-20261015/verify_recorded.py

Fresh guarded reproduction (macOS only; resolves the shared
.coordinations/run_jsp_heavy.py ancestor lock or JSP404_HEAVY_GUARD;
elan-resolved pinned compiler; independent reproduce/build output):
  python3 verification/r1-t1-terminal-20261015/reproduce/run.py --check-config
  python3 verification/r1-t1-terminal-20261015/reproduce/run.py
The full run recompiles all 566 modules fresh (no borrowing) then runs the
original-API terminal probe; --check-config / --batch are partial stages only
and never report a pass. Not rerun end-to-end at pack time.

No .olean, .ilean or build cache is shipped. Raw receipts retain original
execution paths and context values. Quarantined duplicate-probe artifacts
are retained but explicitly non-acceptance (recorded/quarantine_ledger.json).

Independent static review: recorded/independent_review/ contains the original
package snapshot review and a final delta review. The delta corrects the
original 563-module count to 566 and confirms unchanged theorem statements
and 180 canon slots. Kernel acceptance is Root's separately recorded result.
Root negative archive tests reject partial acceptance, a replaced canonical
key despite unchanged counts, and a forged successful child exit.
