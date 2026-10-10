import Jsp000404.R2N4Capacity
import Jsp000404.S7Dispatch
import Jsp000404.S8Dispatch

/-!
# `R2` over-capacity impossibility at `n = 4`

Closes the `n = 4` capacity layer: `r2_n4_overcap_reduces` extracts
a critical seven- or eight-centre sub-profile from any over-capacity
`R2` configuration, and `seven_centre_n4_terminal` /
`eight_centre_n4_terminal` exclude each.  The remaining defect-`4`
rows of the critical profiles are inert — the certificates need only
the anchor, the two defect-`2` rows, and (at seven centres) the
defect-`3` row.
-/

namespace Jsp404

open scoped EuclideanSpace

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- **Over-capacity `R2` at `n = 4` is impossible.**  Any `t ≥ 6`
centre `R2` profile at `n = 4` has `potential ≤ 2^4 + 2^2`. -/
theorem r2_n4_overcap_impossible {t : ℕ} (ht : 6 ≤ t) {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin t → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (hR2 : R2N4Profile o e lam c)
    (hover : 2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c)) :
    False := by
  rcases r2_n4_overcap_reduces ht hlam hn hleg he hR2 hover with
      ⟨c', -, -, hleg', v, a, b, u, hva, hvb, hvu, hab, hau, hbu,
        hsat, hda, hdb, hdu, -⟩ |
      ⟨c', -, -, hleg', v, a, b, hva, hvb, hab, hsat, hda, hdb, -⟩
  · exact seven_centre_n4_terminal o e he hlam hn hleg'
      hva hvb hvu hab hau hbu hsat hda hdb hdu
  · exact eight_centre_n4_terminal o e he hlam hn hleg'
      hva hvb hab hsat hda hdb

#print axioms r2_n4_overcap_impossible

end Jsp404
