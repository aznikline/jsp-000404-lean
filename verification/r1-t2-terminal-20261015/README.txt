R1-T2-ACTUAL-TERMINAL-04: verified actual seven-point terminal

Jsp404.r1_seven_phi21_terminal (Jsp000404/R1DispatchT2.lean) proves False
for actual Fin 7 plane points satisfying Section4Legality, lambda > 0,
floor(pi/lambda)=4, a nonzero reference, distinct saturated v and defect-2 a,
all other defects >=3, and potential=21. Chart, model and certificates are
constructed internally. The original theorem signature is retained.

Final independent acceptance: recorded/root_local_acceptance.json is
KERNEL_COVERED. All 972 canonical keys, 14 certificate classes, 30 distinct
rank pairs and the complete 1687-module import closure are covered.
1684 modules have Std3 declaration audits. Three unchanged baseline modules
contain four pre-existing admissions, remain AUDITED_NON_STD3, and are excluded
from the passed count. The actual terminal and potential-ledger theorem each
depend only on propext, Classical.choice and Quot.sound; both normal and
--trust=0 original-API probe runs confirm this. Other profiles, sendov_lower
and the complete JSP404 lower bound remain OPEN.

Inspect recorded evidence without binary caches:
  python3 verification/r1-t2-terminal-20261015/verify_recorded.py

This verifies archived raw receipts, current source hashes, the exact state
snapshot, module/declaration coverage, guard outcomes and terminal axiom output.
It does not execute a fresh kernel run. Raw receipts retain original execution
paths. recorded/code contains the exact executed scripts. Failed and superseded
logs are retained. recorded/probe contains actual audit/API probe sources.
No .olean, .ilean or build cache is shipped.

Fresh/resumable guarded reproduction on macOS:
  Prepare the pinned Lean toolchain and lake-manifest.json dependencies.
  The repository dependency-cache setup is: lake exe cache get
  Then run:
    python3 verification/r1-t2-terminal-20261015/reproduce/run.py --check-config
    python3 verification/r1-t2-terminal-20261015/reproduce/run.py

Reproduction scripts differ from recorded/code only in checkout/toolchain path
discovery. Proof, axiom, resource and coverage acceptance logic is retained.
They create new state/logs under reproduce/, reuse only complete matching
receipts, run normal/strict original-API probes, then independently check full
acceptance. Generated state/logs are ignored by Git. The original guard is
copied byte-identically: default RSS <=4 GiB, 180 seconds per call, Lean -j1
-M4096, nice 15, one guard lock and exclusion of existing Lean/Lake tasks.
Its pre-existing mapped-RSS calibration retains the original eligibility and
physical-footprint <=4 GiB rule. Measured thin leaf/certificate steps use RSS4.

Resource splits and proof repairs have individual byte/hash ledgers under
recorded/. Every reachable source is pinned. The generator repairs preserve
all 16 dispatch theorem statements and reproduce the committed source exactly.
Outside dispatch repairs, the sole non-verbatim tactic change is
cyclicDiff_eq_add_of_le, whose unchanged statement is recorded in
K3bArcAux3_tactic_change.json. Definition/interface source hashes remain frozen.
R3 import-shell diagnostic print commands were moved to text; the required
strict declaration axiom audit is retained.
