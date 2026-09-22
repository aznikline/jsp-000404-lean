# Attributed Sendov upper constructions

These Lean sources are copied without modification from
[`superpilot69/awards`, commit `722cb3caa86710c788296ca0ec954a79e9a0adcc`](https://github.com/superpilot69/awards/tree/722cb3caa86710c788296ca0ec954a79e9a0adcc/submissions/jsp-000404).
The upstream proof authors are **superpilot69 and ChatGPT 6 Astra**, as
recorded in the retained `ATTRIBUTION.md`. The mathematical results belong
to Szekeres, Erdős–Szekeres and Sendov. These are reused contributions,
not new proofs by this repository's owner.

The original MIT license is retained in `LICENSE`. Upstream attribution
documentation is retained under its stated CC BY 4.0 license, with the
original source linked above. `UPSTREAM.json` pins the revision, source
directory and SHA-256 of every copied file. The files have not been edited.

The Lake library `JSP404` makes these modules available at their original
import paths. Both projects use Lean 4.34.0 and the same mathlib revision,
`5ed2965256430c3649e86755f9576b54eca72435`. The original library's
`autoImplicit` setting is preserved locally; the `Jsp000404` library
continues to use `autoImplicit = false`.

`JSP404.ThreeClusterGeometry.sendov_piecewise_upper_bound` proves both
upper bands for the supremum of guaranteed angles. The new local bridge
`Jsp000404/UpperBound.lean` connects that theorem to the project's `alphaN`
formula and `PtCfg` type and covers the N = 3, 4 boundary cases.

Reproduction from the project root:

```sh
lake build JSP404.ThreeClusterGeometry Jsp000404.UpperBound
```

An upper bound alone does not complete JSP-000404. The arbitrary-N lower
bound remains open; see `notes/STATUS.md` at the repository root.
