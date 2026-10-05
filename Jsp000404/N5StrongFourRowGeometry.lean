import Jsp000404.N4StrongFourRowGeometry
import Jsp000404.SixExactFloorKernelN5BetweenTerminal

/-!
# Actual six-centre exclusion for the n = 5 between / pure-tail branch

The actual chart determines the angle order. In the between class the two
defect-2 rows occupy ranks 0 and 4, while the pure defect-3 tail occupies
ranks 1, 2 and 3. The generic extraction transports these actual defects to
the strip-5 scalar model without a caller-supplied scalar profile.

HIGH uses the exact-floor strip-5 four-row terminal. LOW uses the proved
saturated-centre capacity 32 versus actual potential 44. The resulting
band-free exclusion removes the between class from the actual theta
classification and retains its two outer classes. This is a local pure-tail
result, not the complete strip-5 or arbitrary-strip exclusion.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.N5StrongFourRowGeometry

open SixModelExtraction

section ActualN5Chart

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 6 → Plane₂} {v : Fin 6} {theta : Fin 5 → ℝ}
  (C : SatChart o e 5 lam c v theta)

include C

/-- All five genuine defects, transported to their actual angle ranks by
the generic extraction. No normalized row profile is assumed. -/
theorem model_defects_of_between_pure_tail {lo hi : Fin 5}
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 5 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 5 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 5 lam (directionRow o e c (v.succAbove z)) = 3) :
    SixModelCompression.rowDefect (model C) 0 = 2 ∧
      SixModelCompression.rowDefect (model C) 1 = 3 ∧
      SixModelCompression.rowDefect (model C) 2 = 3 ∧
      SixModelCompression.rowDefect (model C) 3 = 3 ∧
      SixModelCompression.rowDefect (model C) 4 = 2 := by
  obtain ⟨hσ0, hσ4⟩ :=
    N4StrongFourRowGeometry.sigma_zero_four_of_between C hθ hbetween
  have htail : ∀ i : Fin 5, i ≠ 0 → i ≠ 4 →
      SixModelCompression.rowDefect (model C) i = 3 := by
    intro i hi0 hi4
    rw [model_rowDefect C i]
    apply htail3
    · rw [← hσ0]
      exact sigma_ne C hi0
    · rw [← hσ4]
      exact sigma_ne C hi4
  refine ⟨?_, htail 1 (by decide) (by decide),
    htail 2 (by decide) (by decide), htail 3 (by decide) (by decide), ?_⟩
  · rw [model_rowDefect C 0, hσ0]
    exact hdlo
  · rw [model_rowDefect C 4, hσ4]
    exact hdhi

/-- Actual six-point geometry in HIGH strip 5 consumes the exact-floor
terminal. All scalar data and rank defects are constructed internally. -/
theorem between_pure_tail_high_impossible {lo hi : Fin 5}
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 5)
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 5 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 5 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 5 lam (directionRow o e c (v.succAbove z)) = 3) : False := by
  obtain ⟨hd0, hd1, -, hd3, hd4⟩ :=
    model_defects_of_between_pure_tail C hθ hbetween hdlo hdhi htail3
  exact SixExactFloorKernel.n5_between_impossible (model C)
    hhigh hd0 hd1 hd3 hd4

/-- The actual strip-5 profile has potential 16 + 8 + 8 + 4 + 4 + 4 = 44,
computed from the genuine rows independently of the terminal. -/
theorem potential_eq_forty_four_of_between_pure_tail {lo hi : Fin 5}
    (hsat : rowDefect 5 lam (directionRow o e c v) = 1)
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 5 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 5 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 5 lam (directionRow o e c (v.succAbove z)) = 3) :
    potential lam (directionRows o e c) = 44 := by
  classical
  obtain ⟨hd0, hd1, hd2, hd3, hd4⟩ :=
    model_defects_of_between_pure_tail C hθ hbetween hdlo hdhi htail3
  have hscore (i : Fin 6) :
      rowScore lam (directionRow o e c i) =
        5 - rowDefect 5 lam (directionRow o e c i) :=
    rowScore_eq_sub_defect lam C.hlam 5 _
      (rowCells_directionRow_le_of_floor_eq o e c C.hlam i (by omega) C.hn)
  have hsum : (∑ i : Fin 5,
      (2 : ℕ) ^ (5 - rowDefect 5 lam
        (directionRow o e c (v.succAbove (sigma C i))))) =
      ∑ i : Fin 5, (2 : ℕ) ^
        (5 - rowDefect 5 lam (directionRow o e c (v.succAbove i))) :=
    Fintype.sum_bijective (sigma C) (sigma_bijective C) _ _ (fun _ => rfl)
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  simp only [hscore, hsat]
  rw [← hsum]
  simp only [← model_rowDefect C]
  norm_num [Fin.sum_univ_succ, hd0, hd1, hd2, hd3, hd4]

/-- The actual strip-5 between class with pure defect-3 tail is impossible
in both bands: LOW has capacity 32 < 44, and HIGH uses the exact terminal. -/
theorem between_pure_tail_impossible {lo hi : Fin 5}
    (hsat : rowDefect 5 lam (directionRow o e c v) = 1)
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 5 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 5 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 5 lam (directionRow o e c (v.succAbove z)) = 3) : False := by
  by_cases hlow : Real.pi / lam - 5 < (1 / 2 : ℝ)
  · have hcap := potential_le_two_pow_of_saturated o e C.he (by omega)
      (by omega) C.hlam C.hn C.hleg v hsat hlow
    rw [potential_eq_forty_four_of_between_pure_tail C hsat hθ hbetween
      hdlo hdhi htail3] at hcap
    norm_num at hcap
  · exact between_pure_tail_high_impossible C (le_of_not_gt hlow)
      hθ hbetween hdlo hdhi htail3

end ActualN5Chart

/-- For the actual six-centre strip-5 profile (1,2,2,3,3,3), the genuine
theta classification retains only its two outer classes. The reference is
arbitrary; chart construction, transport and between exclusion are internal. -/
theorem six_centre_n5_pure_tail_outer_class
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 5)
    {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    {v A B : Fin 6} (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect 5 lam (directionRow o e c v) = 1)
    (hdA : rowDefect 5 lam (directionRow o e c A) = 2)
    (hdB : rowDefect 5 lam (directionRow o e c B) = 2)
    (htail3 : ∀ z : Fin 6, z ≠ v → z ≠ A → z ≠ B →
      rowDefect 5 lam (directionRow o e c z) = 3) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin 5 → ℝ,
      SatChart o e' 5 lam c v theta ∧ ∃ lo hi : Fin 5,
        ((v.succAbove lo = A ∧ v.succAbove hi = B) ∨
          (v.succAbove lo = B ∧ v.succAbove hi = A)) ∧
        theta lo < theta hi ∧
        ((∀ z : Fin 5, z ≠ lo → z ≠ hi → theta z < theta lo) ∨
          (∀ z : Fin 5, z ≠ lo → z ≠ hi → theta hi < theta z)) := by
  obtain ⟨e', he', theta, C, lo, hi, hswap, hθ, hclass⟩ :=
    defect_two_pair_theta_cluster o e he (by omega) (by omega) hlam hn hleg
      hvA hvB hAB hsat hdA hdB
  have href : ∀ x : Fin 6,
      rowDefect 5 lam (directionRow o e' c x) =
        rowDefect 5 lam (directionRow o e c x) :=
    fun x => rowDefect_directionRow_reference_eq o e' e he' he c
      hleg.inj x hlam (by omega) hn
  have hsat' : rowDefect 5 lam (directionRow o e' c v) = 1 := by
    rw [href]
    exact hsat
  have hdlo : rowDefect 5 lam (directionRow o e' c (v.succAbove lo)) = 2 := by
    rcases hswap with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1, href] <;> assumption
  have hdhi : rowDefect 5 lam (directionRow o e' c (v.succAbove hi)) = 2 := by
    rcases hswap with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2, href] <;> assumption
  have htail' : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 5 lam (directionRow o e' c (v.succAbove z)) = 3 := by
    intro z hzlo hzhi
    rw [href]
    rcases hswap with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · apply htail3 _ (Fin.succAbove_ne v z)
      · exact fun h => hzlo (Fin.succAbove_right_injective (h.trans hA.symm))
      · exact fun h => hzhi (Fin.succAbove_right_injective (h.trans hB.symm))
    · apply htail3 _ (Fin.succAbove_ne v z)
      · exact fun h => hzhi (Fin.succAbove_right_injective (h.trans hA.symm))
      · exact fun h => hzlo (Fin.succAbove_right_injective (h.trans hB.symm))
  refine ⟨e', he', theta, C, lo, hi, hswap, hθ, ?_⟩
  rcases hclass with hbelow | hbetween | habove
  · exact Or.inl hbelow
  · exact (between_pure_tail_impossible C hsat' hθ hbetween hdlo hdhi htail').elim
  · exact Or.inr habove

#print axioms model_defects_of_between_pure_tail
#print axioms between_pure_tail_high_impossible
#print axioms potential_eq_forty_four_of_between_pure_tail
#print axioms between_pure_tail_impossible
#print axioms six_centre_n5_pure_tail_outer_class

end Jsp404.N5StrongFourRowGeometry
