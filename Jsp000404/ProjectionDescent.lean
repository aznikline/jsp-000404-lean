import Jsp000404.OneSaturatedHigh
import Jsp000404.ProjectionDescentCore

open scoped EuclideanGeometry EuclideanSpace RealInnerProductSpace

namespace Jsp404

section Anchored

variable {s n : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
  {lam : ℝ} {c : Fin (s + 1) → Plane₂} (v : Fin (s + 1))
  (theta : Fin s → ℝ)

variable {o e v theta}

/-- **The `Ψ`-minimal non-anchor row has both end gaps big.**  Any short
end would supply a witness of strictly smaller `Ψ`. -/
theorem psi_min_row_ends_big (he : e ≠ 0) (hn3 : 3 ≤ n)
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hleg : Section4Legality c lam)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (Real.pi - n * lam) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    {r : Fin s} (hmin : ∀ j, psi (c := c) e v r ≤ psi (c := c) e v j)
    (hne : directionRow o e (c ∘ v.succAbove) r ≠ []) :
    lam ≤ (directionRow o e (c ∘ v.succAbove) r).head hne - theta r ∧
      lam ≤ theta r + Real.pi -
        (directionRow o e (c ∘ v.succAbove) r).getLast hne := by
  constructor
  · by_contra hlt
    push_neg at hlt
    obtain ⟨j, hrj, -, hdir⟩ := short_first_gap_gives_lower o e he hn3
      hlam hn hleg v htheta r hne hlt
    have h := shortWitness_projection_lt he hn3 hlam hn hleg htheta
      (i := r) (j := j) ⟨hrj, Or.inl (by rw [hdir]; exact hlt)⟩
    linarith [hmin j]
  · by_contra hlt
    push_neg at hlt
    obtain ⟨j, hrj, -, hdir⟩ := short_last_gap_gives_higher o e he hn3
      hlam hn hleg v htheta r hne hlt
    have h := shortWitness_projection_lt he hn3 hlam hn hleg htheta
      (i := r) (j := j) ⟨hrj, Or.inr (by rw [hdir]; exact hlt)⟩
    linarith [hmin j]

end Anchored

#print axioms directed_chord_in_corridor'
#print axioms acute_margin_of_floor
#print axioms short_first_inner_neg
#print axioms short_last_inner_neg
#print axioms shortWitness_projection_lt
#print axioms shortWitness_no_cycle
#print axioms psi_min_row_ends_big

end Jsp404
