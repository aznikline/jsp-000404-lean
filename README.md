# JSP-000404 / Erdős Problem 504 — partial Lean 4 formalization

Formalization of Sendov's solution of Blumenthal's minimax-angle problem
(`α(N)`, the largest angle every planar `N`-point set must determine).

**Status: partial.** This repository is `sorry`-free; everything stated here
is proved. The *complete* classification is proved **conditional on a single
explicitly stated geometric hypothesis** (`GeometricCertificates`), which is
an ordinary Lean proposition taken as a parameter — not an axiom, not a
`sorry`.

## What is proved (kernel-checked)

| Theorem | Content | Status |
| --- | --- | --- |
| `Jsp404.sendov_upper` | Sharpness for **all** `N ≥ 3`: an extremal configuration exists whose largest angle is `≤ alphaN N + ε` | unconditional |
| `Jsp404.sendov_lower_le_eight` | Lower bound for `3 ≤ N ≤ 8` | unconditional |
| `Jsp404.sendov_alpha_eq_le_eight` | `α(N) = alphaN N` exactly, for `3 ≤ N ≤ 8` | unconditional |
| `Jsp404.sendov_alpha_eq_of_geometricCertificates` | The **full** Sendov classification `JSP404.alpha N = alphaN N`, all `N ≥ 3` | conditional on `GeometricCertificates` |
| `Jsp404.sendov_lower` | The `PtCfg`-form lower bound, all `N ≥ 3` | conditional on `GeometricCertificates` |
| `Jsp404.gadgetSelection_of_geometricCertificates` | The open hypothesis reduces to the weighted-capacity selection used by the induction | proved |
| `Jsp404.potential_le_sendovCap` | Strong-induction potential bound | proved (uses the certificate hypothesis) |

All `#print axioms` audits report exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`,
no custom axioms.

## The remaining gap (honest)

`GeometricCertificates` (in `Jsp000404/CertificateIntegration.lean`) is the
strip-wise existence claim `CertExists` for strips `n ≥ 3` — the weighted
capacity/dichotomy step that Sendov's paper performs only by a brief
sketch. The `n = 1` (first strip) and `n = 2` (second strip) cases are
discharged unconditionally inside `CertificateIntegration`; `N ≤ 8` needs
no certificate at all. **The unconditional `N ≥ 9` lower bound is the only
missing piece.**

Deliberately *not* stated: several attractive helper lemmas
(`maxGap_boundary_emission`, unrestricted staircase bounds, removable-vertex
existence) were found to be **false** as naively quantified — kernel-checked
countermodels were constructed during the campaign. Their needed content is
folded into `CertExists` on the domain where the induction actually runs.

## Layout

- `Jsp000404/` — the formalization (35 modules: geometry of direction
  rows/circle separation, the exponent potential and deletion induction,
  small-`N` proofs, sharpness, certificate integration).
- `ThirdParty/Sendov/` — vendored, **unmodified** upper-bound
  constructions by superpilot69 / ChatGPT 6 Astra, from
  `superpilot69/awards@722cb3ca` (MIT license retained; see
  `ThirdParty/Sendov/README.md` and `ATTRIBUTION.md`).
- `Jsp000404.lean` — library root importing the proved surface.

## Reproduce

```sh
git clone https://github.com/aznikline/jsp-000404-lean
cd jsp-000404-lean
git checkout <pinned commit>
lake exe cache get   # mathlib cache
lake build           # compiles cleanly, no sorry
```

Toolchain: Lean `leanprover/lean4:v4.34.0`, mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Axiom audit:

```sh
cat > AxiomCheck.lean <<'EOF'
import Jsp000404
#print axioms Jsp404.sendov_upper
#print axioms Jsp404.sendov_alpha_eq_le_eight
#print axioms Jsp404.sendov_alpha_eq_of_geometricCertificates
#print axioms Jsp404.sendov_lower
EOF
lake env lean AxiomCheck.lean
```

Expected output for each: `depends on axioms: [propext, Classical.choice, Quot.sound]`.

## License

MIT (see `LICENSE`). Third-party vendored files retain their own
licenses/attribution as documented under `ThirdParty/Sendov/`.
