Unpublished JSP404 n=3 R2 proof candidate, 2026-10-03

Remote comparison pin: 8365f3cb5ec3738ecb8787c14a2514e6e7e4bb46.
Local dependency-cache provenance: owner 1826c91ca5ce2170c25395eaae8d9a42334cd9da.
This bundle has not been committed, pushed, or merged into AIR or integration.

Sources:
  Jsp000404/R2SixCentreN3.lean
    SHA256 7568c8d21192025bc42b29b6433da6a9ecc332a029649bcfeff42e6b846e09f2
    Finite symbolic scalar leaf proofs, retaining all real parameters.
  Jsp000404/N3Extraction.lean
    SHA256 654ede99876d4eb530b7faec07b098acc4f00bb0a6f79d6619a1ac38977a2f76
    Actual SatChart/model and sorted-row adapters; actual six-point exclusion.
  research/JSP404_R2_N3_CLOSURE_20261003.lean
    Actual arbitrary-size R2 cardinality at most five, and potential at most ten.
    Current exact SHA256 is recorded in MANIFEST.json.

The scalar module imports Jsp000404.R2SixCentre; extraction imports the scalar
module; the closure imports extraction. The R2SixCentre/FivePointCapacity/Up
helpers are present in the pinned remote core. The two new scalar/extraction
modules are unpublished local candidates. Existing project dependencies are
copied privately as compiled objects and fingerprinted in MANIFEST.json;
Mathlib/toolchain caches are reused. No fresh-machine build is claimed.

Verification command from the recorded owner workspace:
  lake env python3 <absolute-bundle-path>/verify_candidate.py
This compiles every frozen candidate source sequentially using --trust=0,
places candidate objects only in this private bundle, and saves raw logs.
The only project source owned by this task is the new research closure file.
No live AIR source or other shared existing file is changed.

The closure hypotheses are: legal actual c:Fin s->Plane2, e!=0, lambda>0,
floor(pi/lambda)=3, a defect-one anchor, and two distinct defect-two centers
different from the anchor. The capacity corollary also assumes 3<=s.
No minimum-counterexample assumption, capacity IH, tail-profile assumption,
or assumed zero-gain/facing certificate is used.

This closes only the n=3 R2 subdomain. It does not close other n=3 regimes,
arbitrary n, MainTheorem.sendov_lower, or the full Sendov theorem.
