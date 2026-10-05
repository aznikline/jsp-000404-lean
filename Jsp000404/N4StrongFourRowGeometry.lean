import Jsp000404.SixModelExtraction
import Jsp000404.N4StrongFourRowTerminal
import Jsp000404.FivePointCapacity
import Jsp000404.OneSaturatedLow

/-!
# Actual six-centre exclusion for the n = 4 between / pure-tail branch

The angle order is derived from the actual chart. In the between class the
two defect-2 rows have ranks 0 and 4, so a pure defect-3 tail supplies the
terminal's required rank-1 and rank-3 rows. The necessary scalar model is
constructed by `SixModelExtraction.model`, whose delta bounds and row
defects are proved from this same chart.

The high half uses the ordinary four-row kernel certificate. The low half
uses the proved saturated-centre capacity bound and the actual potential
22. Thus the pure-tail between branch is excluded without a band premise.
This is not the complete n = 4 exclusion and does not close arbitrary n.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.N4StrongFourRowGeometry

open SixModelExtraction

section AngleOrder

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin 6 → Plane₂} {v : Fin 6} {theta : Fin 5 → ℝ}
  (C : SatChart o e n lam c v theta)

/-- The actual low pair surrounding all other rows occupies the two
extreme ranks of the extraction permutation. -/
theorem sigma_zero_four_of_between {lo hi : Fin 5}
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi) :
    sigma C 0 = lo ∧ sigma C 4 = hi := by
  have hge : ∀ z : Fin 5, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | hzlo
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | hzhi
      · exact hθ.le
      · exact (hbetween z hzlo hzhi).1.le
  have hle : ∀ z : Fin 5, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | hzhi
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | hzlo
      · exact hθ.le
      · exact (hbetween z hzlo hzhi).2.le
  obtain ⟨rlo, hrlo⟩ := (sigma_bijective C).surjective lo
  obtain ⟨rhi, hrhi⟩ := (sigma_bijective C).surjective hi
  have hmin := (sortedTheta_strictMono C).monotone
    (show (0 : Fin 5) ≤ rlo from by omega)
  have hmax := (sortedTheta_strictMono C).monotone
    (show rhi ≤ (4 : Fin 5) from by
      rw [Fin.le_iff_val_le_val]
      omega)
  rw [← sigma_spec C 0, ← sigma_spec C rlo, hrlo] at hmin
  rw [← sigma_spec C rhi, hrhi, ← sigma_spec C 4] at hmax
  exact ⟨SixModelExtraction.theta_injective C (le_antisymm hmin (hge _)),
    SixModelExtraction.theta_injective C (le_antisymm (hle _) hmax)⟩

end AngleOrder

section ActualN4Chart

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 6 → Plane₂} {v : Fin 6} {theta : Fin 5 → ℝ}
  (C : SatChart o e 4 lam c v theta)

include C

/-- All five actual row defects, transported internally to their angle
ranks. In particular the terminal's ranks 1 and 3 are tail rows. -/
theorem model_defects_of_between_pure_tail {lo hi : Fin 5}
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 4 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 4 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 4 lam (directionRow o e c (v.succAbove z)) = 3) :
    SixModelCompression.rowDefect (model C) 0 = 2 ∧
      SixModelCompression.rowDefect (model C) 1 = 3 ∧
      SixModelCompression.rowDefect (model C) 2 = 3 ∧
      SixModelCompression.rowDefect (model C) 3 = 3 ∧
      SixModelCompression.rowDefect (model C) 4 = 2 := by
  obtain ⟨hσ0, hσ4⟩ := sigma_zero_four_of_between C hθ hbetween
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

/-- Genuine six-point geometry in the high half of strip 4. No scalar
array, row permutation, or solver-success premise is supplied by callers. -/
theorem between_pure_tail_high_impossible {lo hi : Fin 5}
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 4 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 4 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 4 lam (directionRow o e c (v.succAbove z)) = 3) : False := by
  obtain ⟨hd0, hd1, -, hd3, hd4⟩ :=
    model_defects_of_between_pure_tail C hθ hbetween hdlo hdhi htail3
  exact N4StrongFourRowTerminal.four_rows_impossible (model C)
    hhigh hd0 hd1 hd3 hd4

/-- The actual critical profile has potential 22 in strip 4. This
identity is geometric row-score bookkeeping, independent of the terminal. -/
theorem potential_eq_twenty_two_of_between_pure_tail {lo hi : Fin 5}
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 4 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 4 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 4 lam (directionRow o e c (v.succAbove z)) = 3) :
    potential lam (directionRows o e c) = 22 := by
  classical
  obtain ⟨hd0, hd1, hd2, hd3, hd4⟩ :=
    model_defects_of_between_pure_tail C hθ hbetween hdlo hdhi htail3
  have hscore (i : Fin 6) :
      rowScore lam (directionRow o e c i) =
        4 - rowDefect 4 lam (directionRow o e c i) :=
    rowScore_eq_sub_defect lam C.hlam 4 _
      (rowCells_directionRow_le_of_floor_eq o e c C.hlam i (by omega) C.hn)
  have hsum : (∑ i : Fin 5,
      (2 : ℕ) ^ (4 - rowDefect 4 lam
        (directionRow o e c (v.succAbove (sigma C i))))) =
      ∑ i : Fin 5, (2 : ℕ) ^
        (4 - rowDefect 4 lam (directionRow o e c (v.succAbove i))) :=
    Fintype.sum_bijective (sigma C) (sigma_bijective C) _ _ (fun _ => rfl)
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  simp only [hscore, hsat]
  rw [← hsum]
  simp only [← model_rowDefect C]
  norm_num [Fin.sum_univ_succ, hd0, hd1, hd2, hd3, hd4]

/-- The actual n = 4 between class with pure defect-3 tail is impossible
in both halves. LOW uses the proved capacity 16 versus actual potential
22; HIGH uses the extracted four-row terminal. -/
theorem between_pure_tail_impossible {lo hi : Fin 5}
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hθ : theta lo < theta hi)
    (hbetween : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi)
    (hdlo : rowDefect 4 lam (directionRow o e c (v.succAbove lo)) = 2)
    (hdhi : rowDefect 4 lam (directionRow o e c (v.succAbove hi)) = 2)
    (htail3 : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 4 lam (directionRow o e c (v.succAbove z)) = 3) : False := by
  by_cases hlow : Real.pi / lam - 4 < (1 / 2 : ℝ)
  · have hcap := potential_le_two_pow_of_saturated o e C.he (by omega)
      (by omega) C.hlam C.hn C.hleg v hsat hlow
    rw [potential_eq_twenty_two_of_between_pure_tail C hsat hθ hbetween
      hdlo hdhi htail3] at hcap
    norm_num at hcap
  · exact between_pure_tail_high_impossible C (le_of_not_gt hlow)
      hθ hbetween hdlo hdhi htail3

end ActualN4Chart

/-- Consumer of the genuine two-low-row theta classification: for the
six-centre strip-4 profile (1,2,2,3,3,3), only the two outer theta classes
remain. The original reference is arbitrary, and all chart transport is
proved inside the theorem. This leaves the outer classes open. -/
theorem six_centre_n4_pure_tail_outer_class
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    {v A B : Fin 6} (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hdA : rowDefect 4 lam (directionRow o e c A) = 2)
    (hdB : rowDefect 4 lam (directionRow o e c B) = 2)
    (htail3 : ∀ z : Fin 6, z ≠ v → z ≠ A → z ≠ B →
      rowDefect 4 lam (directionRow o e c z) = 3) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin 5 → ℝ,
      SatChart o e' 4 lam c v theta ∧ ∃ lo hi : Fin 5,
        ((v.succAbove lo = A ∧ v.succAbove hi = B) ∨
          (v.succAbove lo = B ∧ v.succAbove hi = A)) ∧
        theta lo < theta hi ∧
        ((∀ z : Fin 5, z ≠ lo → z ≠ hi → theta z < theta lo) ∨
          (∀ z : Fin 5, z ≠ lo → z ≠ hi → theta hi < theta z)) := by
  obtain ⟨e', he', theta, C, lo, hi, hswap, hθ, hclass⟩ :=
    defect_two_pair_theta_cluster o e he (by omega) (by omega) hlam hn hleg
      hvA hvB hAB hsat hdA hdB
  have href : ∀ x : Fin 6,
      rowDefect 4 lam (directionRow o e' c x) =
        rowDefect 4 lam (directionRow o e c x) :=
    fun x => rowDefect_directionRow_reference_eq o e' e he' he c
      hleg.inj x hlam (by omega) hn
  have hsat' : rowDefect 4 lam (directionRow o e' c v) = 1 := by
    rw [href]
    exact hsat
  have hdlo : rowDefect 4 lam (directionRow o e' c (v.succAbove lo)) = 2 := by
    rcases hswap with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1, href] <;> assumption
  have hdhi : rowDefect 4 lam (directionRow o e' c (v.succAbove hi)) = 2 := by
    rcases hswap with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2, href] <;> assumption
  have htail' : ∀ z : Fin 5, z ≠ lo → z ≠ hi →
      rowDefect 4 lam (directionRow o e' c (v.succAbove z)) = 3 := by
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

#print axioms sigma_zero_four_of_between
#print axioms model_defects_of_between_pure_tail
#print axioms between_pure_tail_high_impossible
#print axioms potential_eq_twenty_two_of_between_pure_tail
#print axioms between_pure_tail_impossible
#print axioms six_centre_n4_pure_tail_outer_class

end Jsp404.N4StrongFourRowGeometry
