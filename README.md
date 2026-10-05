# JSP-000404: Blumenthal–Sendov angle problem

**Partial formalization. The full arbitrary-N lower bound is not yet
proved, and this revision is not a complete prize submission.**

The project uses actual Mathlib Euclidean-plane points and unoriented
angles. `Jsp404.alphaN` is Sendov's two-band formula; `Jsp404.PtCfg`
contains a list of distinct points.

- `Jsp404.sendov_upper` is proved for every N >= 3: for every epsilon > 0
  there are exactly N distinct points whose angles are all below
  `alphaN N + epsilon`.
- `Jsp404.sendov_lower_le_sixteen` proves the original lower bound for
  every N from 3 through 16. `sendov_alpha_eq_le_sixteen` proves equality
  of the original extremal quantity and formula over the same range.
- The complete n = 1, 2, and 3 capacity strips are proved. At n = 3,
  `N3HighPairClosure.strip_capacity` combines LOW cap 8 and HIGH cap 10
  for every number of actual centers. `strip_certificates` discharges
  both original certificate-existence obligations in this strip.
- `GlobalFiveLowCapacity.potential_le_two_pow_of_le_five_low` proves
  LOW capacity for every n >= 3 and three through five actual centers.
- `N4StrongFourRowGeometry.between_pure_tail_impossible` excludes the
  actual n = 4 six-center between class with a saturated anchor, two
  defect-2 rows, and three defect-3 tail rows. The two outer theta classes
  and the remaining n = 4 cases are open.
- `Jsp404.sendov_lower` is the unresolved arbitrary-N lower target and
  still depends on `sorryAx` in its N >= 17 branch.
- `Jsp404.sendov_alpha_eq_of_selection` connects a future general
  capacity theorem to equality with the genuine geometric extremal
  quantity. Its `GadgetSelection` argument remains unproved. The direct
  geometric route is now assembled in `sendov_alpha_eq_of_geometricCertificates`;
  its general certificate existence premise also remains unproved.

The eleven-point bundle is described in
[`research/JSP404_ELEVEN_INTEGRATION_PROGRESS_20261005.md`](research/JSP404_ELEVEN_INTEGRATION_PROGRESS_20261005.md).
The subsequent local n = 4 result is described in
[`research/JSP404_N4_INTEGRATION_PROGRESS_20261005.md`](research/JSP404_N4_INTEGRATION_PROGRESS_20261005.md).
The proof boundary and branch audit are in [`notes/STATUS.md`](notes/STATUS.md).
Conditional results with standard
axioms are not presented as proofs of their extra hypotheses.

## Build and inspect

Lean: `leanprover/lean4:v4.34.0`.
Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
Transitive dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean --trust=0 verification/oct5-review/ProofAudit.lean > verification/oct5-review/n4-composed-audit.txt
python3 tools/check_proof_axioms_20261005.py --log verification/oct5-review/n4-composed-audit.txt
```

`lake build` succeeds with the documented unfinished declarations.
The audit explicitly exposes the unresolved lower root; a successful
build alone is not a completion certificate. Latest checked output is
in [`verification/oct5-review/n4-composed-audit.txt`](verification/oct5-review/n4-composed-audit.txt).
The same gate with `--mode root` intentionally rejects the unresolved
arbitrary-N lower theorem. Its rejection is retained as a negative control.

## Sources and attribution

The mathematical result is due to Sendov, building on Szekeres and
Erdős–Szekeres. The formula follows the final theorem, with numerator
2 in the intermediate band:

- Sendov, *Minimax of the angles in a plane configuration of points*,
  Acta Math. Hungar. 69 (1995), 27–46, Theorem 4.1, p. 42
  ([journal volume](https://real-j.mtak.hu/7467/)).
- Sendov, *Compulsory configurations of points in the plane*,
  Fundam. Prikl. Mat. 1:2 (1995), 491–516, Theorem 4.4, p. 514
  ([paper record](https://www.mathnet.ru/eng/fpm81)).

The upper construction library is reused, with its original license and
credit to **superpilot69 and ChatGPT 6 Astra**, from a pinned public
revision. See [`ThirdParty/Sendov/README.md`](ThirdParty/Sendov/README.md)
for provenance and hashes. Local contributions connect these constructions
to this project's formula and configuration type and develop the lower
bound infrastructure. Git history and the integration audit retain the
contributions of the existing proof lanes. No new discovery of the
historical formula or exclusive authorship is claimed.
