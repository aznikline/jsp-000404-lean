import Jsp000404.CertificateIntegration
import Jsp000404.SmallAngleLower

open scoped EuclideanGeometry

namespace Jsp404

/-- **Sendov's theorem (Erdős Problem 504), lower bound.** Every
configuration of `N` distinct points determines an angle at least
`alphaN N`. -/
theorem sendov_lower (N : ℕ) (hN : 3 ≤ N) :
    ∀ C : PtCfg, C.pts.length = N →
      ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
        p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN N ≤ ∠ p q r := by
  intro C hlen
  by_cases hN8 : N ≤ 8
  · exact sendov_lower_le_eight hN hN8 C hlen
  have hN9 : 9 ≤ N := by omega
  -- The arbitrary-size geometric certificate / capacity theorem remains open.
  sorry

end Jsp404
