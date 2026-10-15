import Jsp000404.DeletionRigidityCore
import Jsp000404.DeletionRigidityRows

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section FivePoint

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- Common deletion step: deleting `v.succAbove k` keeps the score of row
`v.succAbove i`, provided another defect-`2` row `j ∉ {i, k}` survives. -/
theorem five_point_delete_score {i k j : Fin 4} (hik : i ≠ k) (hji : j ≠ i)
    (hjk : j ≠ k)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    rowScore lam ((directionRow o e c (v.succAbove i)).erase
        (dirRep o e (c ∘ v.succAbove) i k)) =
      rowScore lam (directionRow o e c (v.succAbove i)) := by
  have hne : v.succAbove i ≠ v.succAbove k :=
    fun h => hik (Fin.succAbove_right_injective h)
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hne
  have hr := (deletion_rigidity o e C.he (by have := C.hn3; omega) C.hlam C.hn
    C.hleg (le_refl 4) (Fin.ne_succAbove v i) (Fin.ne_succAbove v j)
    (fun h => hji (Fin.succAbove_right_injective h).symm)
    (Fin.ne_succAbove v k)
    (fun h => hjk (Fin.succAbove_right_injective h)) hA hi hj hi').1
  rw [erase_directionRow o e (c' := c) (v.succAbove k) i', hi'] at hr
  exact hr

/-- **Zero merge gain at the middle chord.** -/
theorem five_point_merge_zero_mid {i a b d j : Fin 4}
    (hia : i ≠ a) (hib : i ≠ b) (hid : i ≠ d) (hji : j ≠ i) (hjb : j ≠ b)
    (h1 : dirRep o e (c ∘ v.succAbove) i a < dirRep o e (c ∘ v.succAbove) i b)
    (h2 : dirRep o e (c ∘ v.succAbove) i b < dirRep o e (c ∘ v.succAbove) i d)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    mergeGain lam
      (dirRep o e (c ∘ v.succAbove) i b - dirRep o e (c ∘ v.succAbove) i a)
      (dirRep o e (c ∘ v.succAbove) i d - dirRep o e (c ∘ v.succAbove) i b) = 0 := by
  have hdel := five_point_delete_score C hib hji hjb hA hi hj
  rw [anchor_row C i, row4_eq C hia hib hid h1 h2] at hdel
  set A := dirRep o e (c ∘ v.succAbove) i a
  set B := dirRep o e (c ∘ v.succAbove) i b
  set D := dirRep o e (c ∘ v.succAbove) i d
  have hθA : theta i < A := by
    have := phi_ge_lam C hia; have := C.hβ; linarith [(C.htheta i).1.2]
  have hlist : [theta i, A, B, D].erase B = [theta i, A, D] := by
    simp [show theta i ≠ B by linarith, show A ≠ B by linarith]
  rw [hlist, rowScore_cons_eq_linear (sortedLE_three (by linarith) (by linarith)),
    rowScore_cons_eq_linear (sortedLE_four (by linarith) (by linarith) (by linarith))] at hdel
  simp only [linearGapScore] at hdel
  have hspec := mergeGain_spec C.hlam (by linarith : (0 : ℝ) ≤ B - A)
    (by linarith : (0 : ℝ) ≤ D - B)
  rw [show B - A + (D - B) = D - A by ring] at hspec
  omega

/-- **Zero merge gain at the first chord.** -/
theorem five_point_merge_zero_first {i a b d j : Fin 4}
    (hia : i ≠ a) (hib : i ≠ b) (hid : i ≠ d) (hji : j ≠ i) (hja : j ≠ a)
    (h1 : dirRep o e (c ∘ v.succAbove) i a < dirRep o e (c ∘ v.succAbove) i b)
    (h2 : dirRep o e (c ∘ v.succAbove) i b < dirRep o e (c ∘ v.succAbove) i d)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    mergeGain lam (dirRep o e (c ∘ v.succAbove) i a - theta i)
      (dirRep o e (c ∘ v.succAbove) i b - dirRep o e (c ∘ v.succAbove) i a) = 0 := by
  have hdel := five_point_delete_score C hia hji hja hA hi hj
  rw [anchor_row C i, row4_eq C hia hib hid h1 h2] at hdel
  set A := dirRep o e (c ∘ v.succAbove) i a
  set B := dirRep o e (c ∘ v.succAbove) i b
  set D := dirRep o e (c ∘ v.succAbove) i d
  have hθA : theta i < A := by
    have := phi_ge_lam C hia; have := C.hβ; linarith [(C.htheta i).1.2]
  have hlist : [theta i, A, B, D].erase A = [theta i, B, D] := by
    simp [show theta i ≠ A by linarith]
  rw [hlist, rowScore_cons_eq_linear (sortedLE_three (by linarith) (by linarith)),
    rowScore_cons_eq_linear (sortedLE_four (by linarith) (by linarith) (by linarith))] at hdel
  simp only [linearGapScore] at hdel
  have hspec := mergeGain_spec C.hlam (by linarith : (0 : ℝ) ≤ A - theta i)
    (by linarith : (0 : ℝ) ≤ B - A)
  rw [show A - theta i + (B - A) = B - theta i by ring] at hspec
  omega

/-- **Zero merge gain at the last chord.** -/
theorem five_point_merge_zero_last {i a b d j : Fin 4}
    (hia : i ≠ a) (hib : i ≠ b) (hid : i ≠ d) (hji : j ≠ i) (hjd : j ≠ d)
    (h1 : dirRep o e (c ∘ v.succAbove) i a < dirRep o e (c ∘ v.succAbove) i b)
    (h2 : dirRep o e (c ∘ v.succAbove) i b < dirRep o e (c ∘ v.succAbove) i d)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hj : rowDefect n lam (directionRow o e c (v.succAbove j)) = 2) :
    mergeGain lam
      (dirRep o e (c ∘ v.succAbove) i d - dirRep o e (c ∘ v.succAbove) i b)
      (theta i + Real.pi - dirRep o e (c ∘ v.succAbove) i d) = 0 := by
  have hdel := five_point_delete_score C hid hji hjd hA hi hj
  rw [anchor_row C i, row4_eq C hia hib hid h1 h2] at hdel
  set A := dirRep o e (c ∘ v.succAbove) i a
  set B := dirRep o e (c ∘ v.succAbove) i b
  set D := dirRep o e (c ∘ v.succAbove) i d
  have hθA : theta i < A := by
    have := phi_ge_lam C hia; have := C.hβ; linarith [(C.htheta i).1.2]
  have hDpi : D < Real.pi := (phi_mem C i d).2
  have hlist : [theta i, A, B, D].erase D = [theta i, A, B] := by
    simp [show theta i ≠ D by linarith, show A ≠ D by linarith,
      show B ≠ D by linarith]
  rw [hlist, rowScore_cons_eq_linear (sortedLE_three (by linarith) (by linarith)),
    rowScore_cons_eq_linear (sortedLE_four (by linarith) (by linarith) (by linarith))] at hdel
  simp only [linearGapScore] at hdel
  have hspec := mergeGain_spec C.hlam (by linarith : (0 : ℝ) ≤ D - B)
    (by linarith [(C.htheta i).1.1] : (0 : ℝ) ≤ theta i + Real.pi - D)
  rw [show D - B + (theta i + Real.pi - D) = theta i + Real.pi - B by ring] at hspec
  omega

/-- Packaged consequence: in a rigid defect-`2` row `[θ, x, y, z]`, no two
*linearly* adjacent gaps can both be `≥ λ`.  Hence a Type II row
(`rowBig = 2`) has its two big gaps only at positions `{0,2}`, `{0,3}`
or `{1,3}` — the cyclic pair `{3,0}` is the anchor merge, not covered.
Type I (`rowBig = 1`) is unaffected. -/
theorem five_point_no_adjacent_big {i a b d ja jb jd : Fin 4}
    (hia : i ≠ a) (hib : i ≠ b) (hid : i ≠ d)
    (hjai : ja ≠ i) (hjaa : ja ≠ a)
    (hjbi : jb ≠ i) (hjbb : jb ≠ b)
    (hjdi : jd ≠ i) (hjdd : jd ≠ d)
    (h1 : dirRep o e (c ∘ v.succAbove) i a < dirRep o e (c ∘ v.succAbove) i b)
    (h2 : dirRep o e (c ∘ v.succAbove) i b < dirRep o e (c ∘ v.succAbove) i d)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hi : rowDefect n lam (directionRow o e c (v.succAbove i)) = 2)
    (hja : rowDefect n lam (directionRow o e c (v.succAbove ja)) = 2)
    (hjb : rowDefect n lam (directionRow o e c (v.succAbove jb)) = 2)
    (hjd : rowDefect n lam (directionRow o e c (v.succAbove jd)) = 2) :
    ¬ (lam ≤ dirRep o e (c ∘ v.succAbove) i a - theta i ∧
        lam ≤ dirRep o e (c ∘ v.succAbove) i b - dirRep o e (c ∘ v.succAbove) i a) ∧
      ¬ (lam ≤ dirRep o e (c ∘ v.succAbove) i b - dirRep o e (c ∘ v.succAbove) i a ∧
        lam ≤ dirRep o e (c ∘ v.succAbove) i d - dirRep o e (c ∘ v.succAbove) i b) ∧
        ¬ (lam ≤ dirRep o e (c ∘ v.succAbove) i d - dirRep o e (c ∘ v.succAbove) i b ∧
          lam ≤ theta i + Real.pi - dirRep o e (c ∘ v.succAbove) i d) := by
  exact ⟨not_both_big_of_mergeGain_zero C.hlam
      (five_point_merge_zero_first C hia hib hid hjai hjaa h1 h2 hA hi hja),
    not_both_big_of_mergeGain_zero C.hlam
      (five_point_merge_zero_mid C hia hib hid hjbi hjbb h1 h2 hA hi hjb),
    not_both_big_of_mergeGain_zero C.hlam
      (five_point_merge_zero_last C hia hib hid hjdi hjdd h1 h2 hA hi hjd)⟩

end FivePoint

end Jsp404
