# LEAD_FINAL — PROOF-CONVERGENCE-02 round report

VERDICT=M0 complete; M1 decode calibration complete; no selection
breakthrough claimed.
MATHEMATICAL_SCOPE=integration 9945ee8 baseline preserved; certB
family (signed_chain_cert{,B}, signed_chain_extend, leaf regressions,
fat-arc, polygon certs) ported kernel-checked; certb_scan direction
decode fixed and gauge-invariance regression reproduced.
PROVED=port compiles on integration (8996 jobs); all ported decls
axioms [propext, Classical.choice, Quot.sound]
CONDITIONAL=sendov_lower N≥9 still sorry at root; GeometricCertificates
path unchanged
EMPIRICAL=certb_scan coverage numbers are hypothesis-availability
diagnostics only (n4_high 407/519, n4_low 285/401, s6 101/101)
FALSIFIED=(carried) maxGap_boundary_emission; fixed quarter-face;
two-group narrow split; S=0⇒K≤1 shortcut
REMOTE_BRANCH=agent/jsp404-proof-convergence-02-owner
INTEGRATION_BASE_SHA=9945ee8bd25ed3520aa89a063493cf3398e6f884
CERT_SOURCE_SHA=9ae823086d0a13d8f0d98545c9346a73c4e7938b
TASK_PATH=.agate/tasks/JSP-000404-PROOF-CONVERGENCE-02
BUILD=PASS (8996 jobs, worktree, toolchain leanprover/lean4:v4.34.0)
ROOT_AXIOMS=sendov_lower depends on sorryAx (unchanged, pre-existing);
all other roots clean
ASSUMPTION_AUDIT=no new sorry/admit/axiom/native_decide introduced
FORBIDDEN_DEPENDENCIES=maxGap_boundary_emission unused by port
TREE_CLEAN=pending commit at report time
LIVE_BLOCKER=none new; selection (K>B ⇒ certificate) remains the crux
NEXT_ACTION=M1b witness emission + corrected union pass; then
leaf_0177 mixed-sign check; then R-HIGH1 mechanism
