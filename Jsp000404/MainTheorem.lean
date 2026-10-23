import Jsp000404.CertificateIntegration
import Jsp000404.SmallAngleLower

/-!
# Sendov's theorem — the target statement (Erdős problem 504)

Blumenthal's problem asks for `α(N)`: the largest angle that every planar
configuration of `N` points must determine. Sendov (1995) proved

- `α(N) = (1 - 2/(2n+1))·π`  for `2^n < N ≤ 2^n + 2^{n-2}`,
- `α(N) = (1 - 1/(n+1))·π`   for `2^n + 2^{n-2} < N ≤ 2^{n+1}`,

for `N ≥ 4`, where `n` is determined by `2^n < N ≤ 2^{n+1}`; and
`α(3) = π/3`.

NOTE on the catalogue: erdosproblems.com/504 prints the first branch with
numerator `1` (`π(1 - 1/(2n-1))`), which is wrong — e.g. at `N = 5` it gives
`4π/5` while the true value is `3π/5`. The formula below is Sendov's
Theorem 4.1 as printed in Acta Math. Hungar. 69 (1995).

## Status of this formalization

This artifact proves, with no `sorry` and only the standard axioms
`[propext, Classical.choice, Quot.sound]`:

- `sendov_upper` — sharpness for every `N ≥ 3` (explicit extremal
  configurations exist for all `N`), and
- `sendov_lower_le_eight` / `sendov_alpha_eq_le_eight` — the exact value
  `α(N) = alphaN N` for `3 ≤ N ≤ 8`, unconditionally;
- `sendov_alpha_eq_of_geometricCertificates` — the *complete* Sendov
  classification `JSP404.alpha N = alphaN N` for all `N ≥ 3`, conditional
  on the single explicitly stated geometric hypothesis
  `GeometricCertificates` (the strip-wise `CertExists` claim for `n ≥ 3`).

The remaining mathematical content of Sendov's argument is exactly that
one hypothesis: `GeometricCertificates` is stated as ordinary Lean
proposition (not an axiom) and taken as a parameter.  The `N ≥ 9`
unconditional lower bound is therefore *not yet* a theorem of this
repository.
-/

open scoped EuclideanGeometry

namespace Jsp404

/-- **Sendov's theorem (Erdős Problem 504), lower bound.** Every
configuration of `N` distinct points determines an angle at least
`alphaN N`.  Conditional on `GeometricCertificates` — the single open
geometric hypothesis of this formalization.  For `N ≤ 8` the hypothesis
is not needed (see `sendov_lower_le_eight`). -/
theorem sendov_lower (hcert : GeometricCertificates) (N : ℕ) (hN : 3 ≤ N) :
    ∀ C : PtCfg, C.pts.length = N →
      ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r :=
  sendov_lower_of_selection (gadgetSelection_of_geometricCertificates hcert) hN

end Jsp404
