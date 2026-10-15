import Jsp000404.MixedTwoInCentralCore
import Jsp000404.MixedTwoInOuterLow
import Jsp000404.MixedTwoInOuterHigh

/-!
# Mixed two-in receivers: the central insertion is impossible

In a five-point `R = 3` configuration (saturated anchor `A`, defect `≥ 3`
row `H`, defect-`2` rows `P, Q, R`), let `P → H` be a short-first chord and
`R → H` a short-last chord.  Write

    u = φ_HP,  w = φ_HR,  z = φ_HQ,
    x = φ_RP,  y = φ_RQ,  t = φ_PQ.

The main theorem `mixed_two_in_central` proves `u < z < w → ⊥`: the third
incoming direction cannot split the gap between the two received
directions.  Combined with `two_in_mixed_between` this pins a mixed two-in
receiver to defect `3` (and with legality, `z` outside `(u, w)`).

Proof outline (six leaves, mirroring the packet):
* `five_point_high_receiver_not_full_in` gives `¬ ShortWitness Q H`, so
  both `H`-direction end gaps of the `Q`-row are `≥ λ`.
* `Up(H,P)`, `Up(R,H)` give `Up(R,P)` with `u < x < w` (`up_trans`).
* The three unknown `Up`-orientations on `HQ, PQ, RQ` collapse to four
  consistent triples; zero merge gains (`five_point_no_adjacent_big`) or
  the cross-row argument (a forced `≥ (n−1)λ` gap in one row, the
  `≤ π − nλ` end-span of `linearGapScore_span_le_of_big_ends` in the next,
  adjacent big gaps in the third) yield the contradiction.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section TwoInCentral

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- **Mixed two-in receivers are impossible at a high-defect row.**

Combining `two_in_mixed_central_exclusion` (`c_H = 3` and the third
direction lands strictly outside `u, w`) with `mixed_two_in_outer_low`
and `mixed_two_in_outer_high`, which exclude both outer positions. -/
theorem mixed_two_in_excluded {H P Q R : Fin 4}
    (hHP : H ≠ P) (hHQ : H ≠ Q) (hHR : H ≠ R)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hH : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove H)))
    (hP : rowDefect n lam (directionRow o e c (v.succAbove P)) = 2)
    (hQ : rowDefect n lam (directionRow o e c (v.succAbove Q)) = 2)
    (hR : rowDefect n lam (directionRow o e c (v.succAbove R)) = 2)
    (hfs : dirRep o e (c ∘ v.succAbove) P H - theta P < lam)
    (hls : theta R + Real.pi - dirRep o e (c ∘ v.succAbove) R H < lam)
    (hθP : theta H < theta P) (hθR : theta R < theta H)
    (hu : theta H + lam ≤ dirRep o e (c ∘ v.succAbove) H P)
    (hu' : dirRep o e (c ∘ v.succAbove) H P < theta P + lam)
    (hw : Real.pi - lam < dirRep o e (c ∘ v.succAbove) H R) : False := by
  obtain ⟨-, hout⟩ := two_in_mixed_central_exclusion C hHP hHQ hHR hPQ hPR hQR
    hA hH hP hQ hR hfs hls hθP hθR hu hu' hw
  rcases hout with hzu | hzw
  · exact mixed_two_in_outer_low C hHP hHQ hHR hPQ hPR hQR hA hH hP hQ hR hfs
      hls hθP hθR hu hu' hw hzu
  · exact mixed_two_in_outer_high C hHP hHQ hHR hPQ hPR hQR hA hH hP hQ hR hfs
      hls hθP hθR hu hu' hw hzw

end TwoInCentral

end Jsp404
