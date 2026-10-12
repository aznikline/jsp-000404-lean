import Jsp000404.R1N4Capacity
import Jsp000404.R2N4Assembly

/-!
# `R1` reduction wrapper — original no-callback API

`r1_n4_overcap_reduces` is the original exported theorem: it has no
`R2N4OvercapExclusion` premise.  The callback-carrying helper
`r1_n4_overcap_reduces_of_r2_exclusion` in `R1N4Capacity` stays an
internal device; here `hr2` is supplied internally from the proved
`r2_n4_overcap_impossible` (its `R2N4Profile` hypothesis unfolds
definitionally to the ∃-statement quantified over by
`R2N4OvercapExclusion`).

This module transitively imports the R2 certificate assembly and is
therefore heavy; it exists only to preserve the public contract.
-/

namespace Jsp404

open scoped EuclideanSpace

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- **Reduction to the six boundary profiles** — original API.  An
over-capacity `R1` configuration at `n = 4` with `t ≥ 6` centres
contains, as a literal subconfiguration `c ∘ ι`, a configuration at
`T` centres whose potential is pinned to the boundary:
`(T, F)` is `(7, 22)` or `(T, 21)` for `7 ≤ T ≤ 11`. -/
theorem r1_n4_overcap_reduces :
    ∀ {t : ℕ} (_ht : 6 ≤ t) {lam : ℝ} (_hlam : 0 < lam)
      (_hn : Nat.floor (Real.pi / lam) = 4) {c : Fin t → Plane₂}
      (_hleg : Section4Legality c lam) (_he : e ≠ 0),
      R1N4Profile o e lam c →
      2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c) →
      ∃ (T : ℕ) (c' : Fin T → Plane₂) (ι : Fin T ↪ Fin t),
        c' = c ∘ ⇑ι ∧ Section4Legality c' lam ∧
        R1N4Profile o e lam c' ∧
        ((T = 7 ∧ potential lam (directionRows o e c') = 22) ∨
         (T = 7 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 8 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 9 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 10 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 11 ∧ potential lam (directionRows o e c') = 21)) :=
  r1_n4_overcap_reduces_of_r2_exclusion r2_n4_overcap_impossible

end Jsp404
