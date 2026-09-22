import Jsp000404.Statement
import JSP404.ThreeClusterGeometry

/-!
# Sharpness for every cardinality

The attributed construction in `ThirdParty/Sendov` proves the two upper
bands for the genuine supremum of guaranteed Euclidean angles. This file
connects those bands to `alphaN`, proves the three-point endpoint, and
extracts configurations for every positive error. No exact minimizer is
assumed. See `ThirdParty/Sendov/UPSTREAM.json` for the source revision.
-/

open scoped EuclideanGeometry

namespace Jsp404

noncomputable def equilateralPoint : Fin 3 → Plane₂ :=
  ![!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]]

lemma equilateralPoint_dist {i j : Fin 3} (h : i ≠ j) :
    dist (equilateralPoint i) (equilateralPoint j) = 1 := by
  have hs : dist (equilateralPoint i) (equilateralPoint j) ^ 2 = 1 := by
    fin_cases i <;> fin_cases j <;>
      simp_all [equilateralPoint, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two,
        Real.dist_eq, sq_abs] <;>
      norm_num <;> nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [dist_nonneg (x := equilateralPoint i) (y := equilateralPoint j)]

lemma equilateralPoint_injective : Function.Injective equilateralPoint := by
  intro i j hij
  by_contra hne
  have h := equilateralPoint_dist hne
  rw [hij, dist_self] at h
  norm_num at h

lemma equilateralPoint_angle {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∠ (equilateralPoint i) (equilateralPoint j) (equilateralPoint k) =
      Real.pi / 3 := by
  have heq₁ := EuclideanGeometry.angle_eq_angle_of_dist_eq
    ((equilateralPoint_dist hij).trans (equilateralPoint_dist hik).symm)
  have heq₂ := EuclideanGeometry.angle_eq_angle_of_dist_eq
    ((equilateralPoint_dist hjk).trans (equilateralPoint_dist hij.symm).symm)
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (equilateralPoint k) (fun h => hij (equilateralPoint_injective h))
  rw [EuclideanGeometry.angle_comm (equilateralPoint i) (equilateralPoint k)
    (equilateralPoint j)] at heq₁
  rw [EuclideanGeometry.angle_comm (equilateralPoint i) (equilateralPoint k)
    (equilateralPoint j),
    EuclideanGeometry.angle_comm (equilateralPoint k) (equilateralPoint j)
    (equilateralPoint i)] at hsum
  linarith

lemma alpha_upper_three : JSP404.alpha 3 ≤ Real.pi / 3 := by
  classical
  let s := Finset.univ.image equilateralPoint
  have hs : s.card = 3 := by
    rw [Finset.card_image_of_injective _ equilateralPoint_injective]
    simp
  apply JSP404.alpha_le_of_configuration (by norm_num) hs
  intro a ha b hb c hc hab hac hbc
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
  exact (equilateralPoint_angle
    (fun h => hab (congrArg _ h)) (fun h => hac (congrArg _ h))
    (fun h => hbc (congrArg _ h))).le

/-- Both Sendov bands bound the genuine extremal angle, including N = 3, 4. -/
theorem alpha_le_alphaN (N : ℕ) (hN : 3 ≤ N) : JSP404.alpha N ≤ alphaN N := by
  rcases eq_or_ne N 3 with rfl | hN3
  · exact alpha_upper_three
  rcases eq_or_ne N 4 with rfl | hN4
  · have h := JSP404.alpha_le_szekeres_upper (N := 4) (k := 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [alphaN, Nat.clog] at h ⊢
    exact h
  have hN5 : 5 ≤ N := by omega
  let n := Nat.clog 2 N - 1
  have hclog : 3 ≤ Nat.clog 2 N := by
    have h := Nat.clog_mono_right 2 hN5
    have h5 : Nat.clog 2 5 = 3 := by decide
    omega
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hlo : 2 ^ n < N :=
    Nat.pow_lt_of_lt_clog (by dsimp [n]; omega)
  have hhi : N ≤ 2 ^ (n + 1) := by
    have hn : n + 1 = Nat.clog 2 N := by dsimp [n]; omega
    rw [hn]
    exact Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) N
  have h := JSP404.sendov_piecewise_upper_bound hn2 hlo hhi
  have hpow : (2 : ℝ) ^ ((n : ℤ) - 2) = ((2 ^ (n - 2) : ℕ) : ℝ) := by
    have he : (n : ℤ) - 2 = ((n - 2 : ℕ) : ℤ) := by omega
    rw [he, zpow_natCast]
    norm_cast
  rw [alphaN_of_ge_four (by omega) (n := n) rfl, hpow]
  have hiff : ((N : ℝ) ≤ (2 : ℝ) ^ n + ((2 ^ (n - 2) : ℕ) : ℝ)) ↔
      N ≤ 2 ^ n + 2 ^ (n - 2) := by norm_cast
  simpa only [hiff, Nat.cast_add, Nat.cast_one] using h

/-- Sharpness in the original threshold sense: every strictly larger bound
fails on an actual configuration of exactly N distinct points. -/
theorem sendov_upper (N : ℕ) (hN : 3 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : PtCfg, C.pts.length = N ∧
      ∀ p q r : Plane₂, p ∈ C.pts → q ∈ C.pts → r ∈ C.pts →
        p ≠ q → r ≠ q → p ≠ r → ∠ p q r < alphaN N + ε := by
  classical
  obtain ⟨s, hs, hmax⟩ := JSP404.exists_configuration_maxAngle_lt hN
    ((alpha_le_alphaN N hN).trans_lt (lt_add_of_pos_right _ hε))
  refine ⟨⟨s.toList, s.nodup_toList, by simpa [hs] using hN⟩, ?_, ?_⟩
  · simpa using hs
  · intro p q r hp hq hr hpq hrq hpr
    exact (JSP404.angle_le_maxAngle
      (Finset.mem_toList.mp hp) (Finset.mem_toList.mp hq)
      (Finset.mem_toList.mp hr) hpq hpr hrq.symm).trans_lt hmax

#print axioms alpha_le_alphaN
#print axioms sendov_upper

end Jsp404
