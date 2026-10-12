import Jsp000404.N4Extraction
import Jsp000404.FivePointCapacity

set_option autoImplicit false

/-!
Thin six-centre capacity adapter. This consumes only actual geometry and
the existing six-centre R2 exclusion. No HIGH condition, positive-row
condition, scalar Model, or capacity callback is supplied by the caller.
SOURCE_ONLY until independently compiled and its dependency axioms audited.
-/

namespace Jsp404.ThinSixCapacity

open scoped EuclideanSpace

theorem actual_six_sat_capacity
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 6 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = 4)
    (v : Fin 6)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1) :
    potential lam (directionRows o e c) ≤ 20 := by
  classical
  have hlam : 0 < lam := hleg.lam_pos
  have hcell (q : Fin 6) : rowCells lam (directionRow o e c q) ≤ 4 :=
    rowCells_directionRow_le_of_floor_eq o e c hlam q (by decide) hn
  have hdpos (q : Fin 6) : 1 ≤ rowDefect 4 lam (directionRow o e c q) :=
    one_le_rowDefect lam hlam 4 _ (by decide) (hcell q)
  have hscore (q : Fin 6) : exponentAt lam (directionRows o e c) q =
      4 - rowDefect 4 lam (directionRow o e c q) :=
    rowScore_eq_sub_defect lam hlam 4 _ (hcell q)
  by_cases hsecond : ∃ w : Fin 6, w ≠ v ∧
      rowDefect 4 lam (directionRow o e c w) = 1
  · obtain ⟨w, hwv, hw⟩ := hsecond
    have hcap := potential_le_high_of_two_saturated o e he
      (by decide : 3 ≤ 6) (by decide : 2 ≤ 4) hlam hn hleg hwv hw hsat
    exact hcap.trans (by norm_num)
  · have huniq (w : Fin 6) (hwv : w ≠ v) :
        2 ≤ rowDefect 4 lam (directionRow o e c w) := by
      have h1 := hdpos w
      have hne : rowDefect 4 lam (directionRow o e c w) ≠ 1 :=
        fun h => hsecond ⟨w, hwv, h⟩
      omega
    let T : Finset (Fin 6) := Finset.univ.filter
      (fun q => rowDefect 4 lam (directionRow o e c q) = 2)
    have hcard : T.card ≤ 2 :=
      defect_two_rows_le_two o e he (by decide : 5 ≤ 6)
        (by decide : 3 ≤ 4) hlam hn hleg v hsat
    have hmem (q : Fin 6) : q ∈ T ↔
        rowDefect 4 lam (directionRow o e c q) = 2 := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases htwo : T.card = 2
    · obtain ⟨A, B, hAB, hT⟩ := Finset.card_eq_two.mp htwo
      have hdA : rowDefect 4 lam (directionRow o e c A) = 2 :=
        (hmem A).mp (by rw [hT]; simp)
      have hdB : rowDefect 4 lam (directionRow o e c B) = 2 :=
        (hmem B).mp (by rw [hT]; simp)
      have hvA : v ≠ A := by intro h; rw [← h, hsat] at hdA; omega
      have hvB : v ≠ B := by intro h; rw [← h, hsat] at hdB; omega
      have htail (w : Fin 6) (hwv : w ≠ v) (hwA : w ≠ A) (hwB : w ≠ B) :
          3 ≤ rowDefect 4 lam (directionRow o e c w) := by
        have h2 := huniq w hwv
        have hne : rowDefect 4 lam (directionRow o e c w) ≠ 2 := by
          intro hd
          have hwT := (hmem w).mpr hd
          rw [hT] at hwT
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwT
          exact hwT.elim hwA hwB
        omega
      by_contra hnot
      have hover : 2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c) := by
        norm_num
        omega
      exact six_centre_n4_overcap o e he hlam hn hleg
        hvA hvB hAB hsat hdA hdB htail hover
    · have hcard1 : T.card ≤ 1 := by omega
      have hweight (q : Fin 6) :
          2 ^ exponentAt lam (directionRows o e c) q ≤
            2 + (if q = v then 6 else 0) +
              2 * (if rowDefect 4 lam (directionRow o e c q) = 2 then 1 else 0) := by
        by_cases hqv : q = v
        · subst q
          simp [hscore v, hsat]
        · have hd2 := huniq q hqv
          by_cases hd : rowDefect 4 lam (directionRow o e c q) = 2
          · simp [hscore q, hd, hqv]
          · have hd3 : 3 ≤ rowDefect 4 lam (directionRow o e c q) := by omega
            have hsle : exponentAt lam (directionRows o e c) q ≤ 1 := by
              rw [hscore q]; omega
            have hwle := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hsle
            simpa [hqv, hd] using hwle
      have hmass : potential lam (directionRows o e c) ≤ 18 + 2 * T.card := by
        rw [potential_eq_exponent_sum]
        calc
          _ ≤ ∑ q : Fin 6, (2 + (if q = v then 6 else 0) +
              2 * (if rowDefect 4 lam (directionRow o e c q) = 2 then 1 else 0)) :=
            Finset.sum_le_sum (fun q _ => hweight q)
          _ = 18 + 2 * T.card := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_boole, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
            rfl
      omega

#print axioms actual_six_sat_capacity

end Jsp404.ThinSixCapacity
