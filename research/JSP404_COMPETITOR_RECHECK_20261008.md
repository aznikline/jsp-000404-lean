# JSP-000404 competitor and award-record recheck — 2026-10-08

Read-only check performed 2026-10-07 UTC. No competitor repository was built, copied into the proof library, messaged, or modified. Public PR claims are not verification results.

## Official record and acceptance threshold

The [official catalog](https://github.com/TheJustinSunPrize/awards/blob/e9e118d00022d693151d87af0c69d180dc5e5efd/problems/catalog-0401-0500.md#jsp-000404--blumenthals-problem) records JSP-000404 as mathematically solved, with Lean proof No and eligibility No. This is not a permanent exclusion: the [award process](https://github.com/TheJustinSunPrize/awards/blob/e9e118d00022d693151d87af0c69d180dc5e5efd/docs/award-process.md) explains that shared eligibility becomes Yes after a solved problem has an accepted complete Lean formalization. A submission or merge alone is not an award; verification, public review, identity and recipient confirmation remain separate.

The [contribution requirements](https://github.com/TheJustinSunPrize/awards/blob/e9e118d00022d693151d87af0c69d180dc5e5efd/CONTRIBUTING.md) accept complete solutions of the original problem. Intermediate lemmas, special cases and unproved conditional bridges do not qualify. Our current work is not submission-ready.

## Open claims checked

- [PR 2804](https://github.com/TheJustinSunPrize/awards/pull/2804) selects Yi-111-a/jsp-000404-blumenthal-sendov commit `f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061`.
- Read exactly [Defs.lean](https://github.com/Yi-111-a/jsp-000404-blumenthal-sendov/blob/f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061/lean/JSP404/Defs.lean) and [Main.lean](https://github.com/Yi-111-a/jsp-000404-blumenthal-sendov/blob/f7bf2cce3bd37fec9f1bce2d04c47b8b88c88061/lean/JSP404/Main.lean). Their SHA-256 values are `12b046818cea1e2177a4af3f2adaeac1006c51b4db4f0e273f4db43cb94f5600` and `a862a60fd226972283d99b97090ef11d202e83aed9b7c5192c0c506572399c81`.
- `alpha N` is defined directly by a piecewise numerical formula using `Nat.clog 2 N`. The selected theorem unfolds that definition and uses the binary-logarithm interval lemma. This selected proof does not establish equality between that numerical definition and the original extremum over actual planar configurations. A clean axiom audit or successful build would not supply this missing statement correspondence. We did not compile it or audit the entire repository.
- [PR 2751](https://github.com/TheJustinSunPrize/awards/pull/2751) selects plby/lean-proofs commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, file `src/latest/ErdosProblems/Erdos404.lean`. The GitHub content API returned HTTP 404 for that exact file/commit in this check. We cannot independently assess this proof from the retrieved evidence. Inaccessibility is not a mathematical refutation.

## Newly closed claim

[PR 2785](https://github.com/TheJustinSunPrize/awards/pull/2785) was closed without merge at `2026-10-07T12:05:44Z`. The [maintainer comment](https://github.com/TheJustinSunPrize/awards/pull/2785#issuecomment-5812369635) says the submission does not meet the complete-original-solution/formalization requirements and invites a complete replacement. This records the maintainer's decision, not our independent audit of that source.

## Consequence for our work

No retrieved competitor evidence supplies a replacement for our open all-N geometric lower bound. Continue the actual-geometry proof. Preserve the original definition of the extremal quantity, eliminate real proof gaps, and submit a complete pinned version only after statement correspondence and axiom closure pass. Do not infer completion or priority from an open PR, a theorem name, a source-token scan, or a formula placed in a definition.
