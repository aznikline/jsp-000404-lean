# October 3 scoped JSP404 proof verification

This review integrates trunk2917368 and AIR8f7752. The actual sixth-center
terminal is upstream. The additional deletion lift proves arbitrary-size
third-strip R2 cardinality at most five and potential at most ten.
The jump and strip consumers retain explicit unproved geometry hypotheses.
The original arbitrary-N lower theorem still depends on sorryAx.

From the repository root, using the pinned Lean/toolchain and available caches:

```sh
lake build
lake env python3 verification/oct3-review/verify_review.py
```

The driver defaults to --trust=0, recompiles all seven scoped source modules
and the composed audit, records exact source hashes and full axiom names,
and reports the original root separately. SCOPED PASS is only a scoped pass.
Expected current root result: REJECTED (still incomplete).

For the unchanged original full audit:

```sh
lake build Jsp000404.IntegrationCounterexample
lake env lean --trust=0 verification/ProofAudit.lean
```

Run the existing research/JSP404_CHECK_ROOT_AUDIT_20261002.py on the saved
audit output. It must reject the current original root because of sorryAx.
That rejection is the preserved negative control, not a completed theorem.

public-*.txt outputs and public-package-receipt.json record the final composed
verification against public8f7752 sources. Unprefixed G6 logs, the private
manifest, and frozen-sources preserve earlier draft verification and its
owner1826 dependency provenance; they are not substituted for the final check.
remote*-build.txt distinguish the two fixed-source builds. No .lake cache
objects are committed. See the research derivation for exact remaining gaps.
