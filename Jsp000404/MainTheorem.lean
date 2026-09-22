import Jsp000404.CertificateIntegration

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
  rcases eq_or_ne N 3 with rfl | hN3
  · exact sendov_lower_three C hlen
  rcases eq_or_ne N 4 with rfl | hN4
  · exact sendov_lower_four C hlen
  have hN5 : 5 ≤ N := by omega
  -- The arbitrary-size geometric certificate / capacity theorem remains open.
  sorry

end Jsp404
