# JSP-000404: Blumenthal–Sendov angle problem

**Partial formalization. The full arbitrary-N lower bound is not yet
proved, and this revision is not a complete prize submission.**

The project uses actual Mathlib Euclidean-plane points and unoriented
angles. `Jsp404.alphaN` is Sendov's two-band formula; `Jsp404.PtCfg`
contains a list of distinct points.

- `Jsp404.sendov_upper` is proved for every N >= 3: for every epsilon > 0
  there are exactly N distinct points whose angles are all below
  `alphaN N + epsilon`.
- `Jsp404.sendov_lower_three` and `sendov_lower_four` prove the first
  two lower-bound cases. The full n = 1 capacity strip is also proved.
- `Jsp404.sendov_lower` is the unresolved arbitrary-N lower target and
  still depends on `sorryAx`.
- `Jsp404.sendov_alpha_eq_of_selection` connects a future general
  capacity theorem to equality with the genuine geometric extremal
  quantity. Its `GadgetSelection` argument remains unproved. The direct
  geometric route is now assembled in `sendov_alpha_eq_of_geometricCertificates`;
  its general certificate existence premise also remains unproved.

The current proof boundary and branch audit are in
[`notes/STATUS.md`](notes/STATUS.md). Conditional results with standard
axioms are not presented as proofs of their extra hypotheses.

## Verified R1 seven-point terminal

`Jsp404.r1_seven_phi21_terminal` excludes the actual geometric R1 seven-point
profile with `floor(pi / lambda) = 4`, one saturated row, one defect-2 row,
all other row defects at least 3, and potential exactly 21. Its chart, model
and 14 certificates are constructed within the proof. The original API is
retained, and the terminal depends only on the standard three axioms.

The complete 1687-module import closure, all 972 canonical keys and all 30
rank assignments were checked with guarded normal/strict compilation and
raw declaration axiom audits. Three unchanged baseline modules with old
admissions are reported separately; they are excluded from the 1684 passed
module count. The final terminal does not depend on those admissions.
Recorded evidence and guarded reproduction instructions are in
[`verification/r1-t2-terminal-20261015/README.txt`](verification/r1-t2-terminal-20261015/README.txt).
Other lower-bound profiles and `sendov_lower` remain open.

## Build and inspect

Lean: `leanprover/lean4:v4.34.0`.
Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
Transitive dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean --trust=0 verification/ProofAudit.lean
```

`lake build` succeeds with the documented unfinished declarations.
The audit explicitly exposes the unresolved lower root; a successful
build alone is not a completion certificate. Latest checked output is
in [`verification/axiom-audit.txt`](verification/axiom-audit.txt).

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
