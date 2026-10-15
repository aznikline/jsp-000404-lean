import Jsp000404.MixedStarExclusion
import Jsp000404.DeletionRigidityGaps

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section FivePoint

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- The anchored full row of a non-anchor vertex. -/
theorem anchor_row (i : Fin 4) :
    directionRow o e c (v.succAbove i) =
      theta i :: directionRow o e (c ∘ v.succAbove) i := by
  have hlampi : lam < Real.pi := by
    have := C.hnl; have := C.hn3'; have := C.hlam; nlinarith
  exact directionRow_anchor_cons o e C.he c C.hleg.inj v C.hlam hlampi theta
    (fun k => ⟨Set.Icc_subset_Icc le_rfl C.hβ.le (C.htheta k).1, (C.htheta k).2⟩)
    (fun a b hab => phi_ge_lam C hab) i

/-- Five-point sub-row identification. -/
theorem row4_eq {h a b d : Fin 4} (hha : h ≠ a) (hhb : h ≠ b) (hhd : h ≠ d)
    (h1 : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (h2 : dirRep o e (c ∘ v.succAbove) h b < dirRep o e (c ∘ v.succAbove) h d) :
    directionRow o e (c ∘ v.succAbove) h =
      [dirRep o e (c ∘ v.succAbove) h a, dirRep o e (c ∘ v.succAbove) h b,
        dirRep o e (c ∘ v.succAbove) h d] := by
  have hlen : (directionRow o e (c ∘ v.succAbove) h).length = 3 := by
    rw [directionRow_length]
  obtain ⟨p, q, r, hl⟩ := List.length_eq_three.mp hlen
  have hsort := (directionRow_sorted o e (c ∘ v.succAbove) h).pairwise
  rw [hl] at hsort
  have hpq : p ≤ q := by simp at hsort; exact hsort.1.1
  have hqr : q ≤ r := by simp at hsort; exact hsort.2
  have hmem : ∀ j, j ≠ h → dirRep o e (c ∘ v.succAbove) h j ∈ [p, q, r] := by
    intro j hj; rw [← hl]
    exact (mem_directionRow o e (c ∘ v.succAbove)).mpr ⟨j, hj, rfl⟩
  have hA := hmem a hha.symm
  have hB := hmem b hhb.symm
  have hD := hmem d hhd.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA hB hD
  rw [hl]
  rcases hA with hA | hA | hA <;> rcases hB with hB | hB | hB <;>
    rcases hD with hD | hD | hD <;>
    first
    | (exfalso; linarith)
    | (rw [hA, hB, hD])

end FivePoint

end Jsp404
