import Jsp000404.AnchoredRows
import Jsp000404.BinGraphs
import Jsp000404.ChartInvariance
import Mathlib.Data.Fintype.Lattice

set_option autoImplicit false

/-! Actual small-cone capacity without saturation.
The cone width beta is independent of the actual period remainder delta.
All references, chord windows and common bins are constructed internally.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.SmallConeLowCapacity

private theorem cone_budget_chart {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 1 ≤ s) (hn3 : 3 ≤ n)
    {lam beta : ℝ} {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = n) (v : Fin (s + 1))
    (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin s, InnerProductGeometry.angle
      (c (v.succAbove i) - c v) (c (v.succAbove j) - c v) ≤ beta) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ potential lam (directionRows o e' c) ≤ 2 ^ n := by
  classical
  have hlam := hleg.lam_pos
  have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfloor
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlampi : lam < Real.pi := by nlinarith
  let : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  have hu : ∀ i : Fin s, c (v.succAbove i) - c v ≠ 0 :=
    fun i => sub_ne_zero.mpr (hleg.inj.ne (Fin.succAbove_ne v i))
  have hb0 : 0 ≤ beta := by
    have h := hspread ⟨0, by omega⟩ ⟨0, by omega⟩
    rwa [InnerProductGeometry.angle_self (hu ⟨0, by omega⟩)] at h
  have hbetal : beta < lam := by nlinarith
  have hbetapi : 2 * beta < Real.pi := by nlinarith
  obtain ⟨e', he', theta, htheta⟩ := exists_ray_window o
    (fun i : Fin s => c (v.succAbove i) - c v) hu hbetapi hspread
  have hcorr : ∀ i j : Fin s, i ≠ j →
      linRep (o.oangle e' (c (v.succAbove j) - c (v.succAbove i))) ∈
        Set.Icc lam (Real.pi - lam + beta) := by
    intro i j hij
    have hcij : v.succAbove i ≠ v.succAbove j :=
      fun h => hij (Fin.succAbove_right_injective h)
    exact chord_in_corridor o he'
      (hleg.inj.ne (Fin.succAbove_ne v i)) (hleg.inj.ne (Fin.succAbove_ne v j))
      (hleg.inj.ne hcij) hbetal (hbetal.trans hlampi)
      (htheta i).1 (htheta j).1 (htheta i).2 (htheta j).2
      (hleg.triAngle v _ _ (Fin.ne_succAbove v i) hcij (Fin.ne_succAbove v j))
      (hleg.triAngle v _ _ (Fin.ne_succAbove v j) hcij.symm (Fin.ne_succAbove v i))
  let m := n - 1
  let width : ℝ := (Real.pi - 2 * lam + beta) / m
  have hm : 0 < m := by dsimp [m]; omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : 0 < width := by
    dsimp [width]
    exact div_pos (by nlinarith) hmreal
  have hwidth : width < lam := by
    dsimp [width]
    rw [div_lt_iff₀ hmreal]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ n by omega))
    rw [hcast]
    nlinarith
  have hend : lam + (m : ℝ) * width = Real.pi - lam + beta := by
    dsimp [width]
    field_simp
    ring
  let p := c ∘ v.succAbove
  have hp : Function.Injective p := hleg.inj.comp Fin.succAbove_right_injective
  have hpos : ∀ i j : Fin s, i ≠ j →
      dirRep o e' p i j ∈ Set.Icc lam (lam + m * width) := by
    intro i j hij
    rw [hend]
    exact hcorr i j hij
  have hangle : ∀ i j k : Fin s, i ≠ j → i ≠ k → j ≠ k →
      ∠ (p i) (p j) (p k) ≤ Real.pi - lam := by
    intro i j k hij hik hjk
    exact hleg.triAngle _ _ _
      (fun h => hij (Fin.succAbove_right_injective h))
      (fun h => hjk (Fin.succAbove_right_injective h))
      (fun h => hik (Fin.succAbove_right_injective h))
  have hbins := directionBinGraph_row_weighted_bound o e' p he' hp hm hw hwidth
    hlam.le (by rw [hend]; linarith) hangle hpos
  have hlocal (i : Fin s) : rowScore lam (directionRow o e' c (v.succAbove i)) ≤
      m - ((directionRow o e' p i).map (uniformBin lam width m)).toFinset.card := by
    rw [anchored_rowScore_eq_linear o e' he' c hleg.inj v hlam hlampi theta
      (fun i => ⟨⟨(htheta i).1.1, (htheta i).1.2.trans hbetal.le⟩, (htheta i).2⟩)
      (fun i j hij => (hpos i j hij).1)]
    apply linearGapScore_le_empty_of_interval hm hw hwidth
      (by linarith [(htheta i).1.1]) (by rw [hend]; linarith [(htheta i).1.2])
      _ (directionRow_sorted o e' p i)
    intro x hx
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e' p).mp hx
    exact hpos i j hji.symm
  have hrest : (∑ i : Fin s, 2 ^ rowScore lam (directionRow o e' c (v.succAbove i)))
      ≤ 2 ^ m :=
    (Finset.sum_le_sum (fun i _ => Nat.pow_le_pow_right (by omega) (hlocal i))).trans hbins
  have hv : rowScore lam (directionRow o e' c v) ≤ m := by
    have hc := rowCells_directionRow_le_of_floor_eq o e' c hlam v (by omega) hn
    have hd := one_le_rowDefect lam hlam n _ (by omega) hc
    rw [rowScore_eq_sub_defect lam hlam n _ hc]
    dsimp [m]
    omega
  refine ⟨e', he', ?_⟩
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succAbove _ v]
  calc
    2 ^ rowScore lam (directionRow o e' c v) +
        ∑ i : Fin s, 2 ^ rowScore lam (directionRow o e' c (v.succAbove i))
      ≤ 2 ^ m + 2 ^ m := Nat.add_le_add (Nat.pow_le_pow_right (by omega) hv) hrest
    _ = 2 ^ n := by
      rw [← two_mul, ← pow_succ']
      congr 1
      dsimp [m]
      omega

/-- Actual cone capacity under the genuine joint period/cone budget.
The inequality is equivalent to delta+beta/lam<1. No SAT is required. -/
theorem potential_le_two_pow_of_cone_budget {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn3 : 3 ≤ n) {lam beta : ℝ} {c : Fin s → Plane₂}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (v : Fin s) (hbeta : beta < ((n : ℝ) + 1) * lam - Real.pi)
    (hspread : ∀ i j : Fin s, i ≠ v → j ≠ v →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ beta) :
    potential lam (directionRows o e c) ≤ 2 ^ n := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  obtain ⟨e', he', hbound⟩ := cone_budget_chart o (by omega) hn3 hleg hn v hbeta
    (fun i j => hspread _ _ (Fin.succAbove_ne v i) (Fin.succAbove_ne v j))
  rw [potential_directionRows_reference_eq o e e' he he' c hleg.inj lam]
  exact hbound

/-- A half-lambda actual cone in LOW has the sharp LOW potential bound,
even when its anchor is not saturated. beta=0 is included. -/
theorem potential_le_two_pow_of_low_small_cone {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn3 : 3 ≤ n) {lam beta : ℝ} {c : Fin s → Plane₂}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hdelta : Real.pi / lam - (n : ℝ) < 1 / 2)
    (v : Fin s) (hsmall : beta < lam / 2)
    (hspread : ∀ i j : Fin s, i ≠ v → j ≠ v →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ beta) :
    potential lam (directionRows o e c) ≤ 2 ^ n := by
  have hpi : Real.pi < ((n : ℝ) + 1 / 2) * lam :=
    (div_lt_iff₀ hleg.lam_pos).mp (by linarith)
  exact potential_le_two_pow_of_cone_budget o e he hs hn3 hleg hn v
    (by nlinarith) hspread

/-- Every anchor of an actual LOW counterexample has two distinct
outgoing rays separated by at least half lambda. -/
theorem exists_large_anchor_angle_of_low_counter {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} {c : Fin s → Plane₂}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hdelta : Real.pi / lam - (n : ℝ) < 1 / 2)
    (hover : 2 ^ n < potential lam (directionRows o e c)) (v : Fin s) :
    ∃ i j : Fin s, i ≠ v ∧ j ≠ v ∧ i ≠ j ∧
      lam / 2 ≤ InnerProductGeometry.angle (c i - c v) (c j - c v) := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  let : Nonempty (Fin t × Fin t) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  let angle : Fin t × Fin t → ℝ := fun p => InnerProductGeometry.angle
    (c (v.succAbove p.1) - c v) (c (v.succAbove p.2) - c v)
  obtain ⟨p, hmax⟩ := Finite.exists_max angle
  have hlarge : lam / 2 ≤ angle p := by
    by_contra hnot
    have hbound := potential_le_two_pow_of_low_small_cone o e he (by omega)
      hn3 hleg hn hdelta v (lt_of_not_ge hnot) (by
        intro i j hiv hjv
        obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hiv
        obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjv
        exact hmax (i', j'))
    omega
  have hne : p.1 ≠ p.2 := by
    intro hp
    have hu : c (v.succAbove p.1) - c v ≠ 0 :=
      sub_ne_zero.mpr (hleg.inj.ne (Fin.succAbove_ne v p.1))
    have hzero : angle p = 0 := by
      dsimp [angle]
      rw [← hp, InnerProductGeometry.angle_self hu]
    rw [hzero] at hlarge
    linarith [hleg.lam_pos]
  exact ⟨v.succAbove p.1, v.succAbove p.2, Fin.succAbove_ne v p.1,
    Fin.succAbove_ne v p.2, fun h => hne (Fin.succAbove_right_injective h), hlarge⟩

/-- Saturation at the closed LOW lower boundary gives a physical cone of
width rho/2. At the original larger scale this falls to the non-SAT cone
capacity theorem; no boundary-to-original saturation transfer is assumed. -/
theorem no_low_boundary_saturation_of_counter {s n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (hn3 : 3 ≤ n) {lam : ℝ} {c : Fin s → Plane₂}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hdelta : Real.pi / lam - (n : ℝ) < 1 / 2)
    (hover : 2 ^ n < potential lam (directionRows o e c)) (v : Fin s) :
    rowDefect n (Real.pi / ((n : ℝ) + 1 / 2)) (directionRow o e c v) ≠ 1 := by
  intro hsat
  let rho := Real.pi / ((n : ℝ) + 1 / 2)
  change rowDefect n rho (directionRow o e c v) = 1 at hsat
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hden : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hrhopos : 0 < rho := div_pos Real.pi_pos hden
  have hrat : Real.pi / rho = (n : ℝ) + 1 / 2 := by
    dsimp [rho]
    exact div_div_cancel₀ Real.pi_pos.ne'
  have hnrho : Nat.floor (Real.pi / rho) = n := by
    rw [hrat]
    apply (Nat.floor_eq_iff (by linarith : 0 ≤ (n : ℝ) + 1 / 2)).mpr
    constructor <;> linarith
  have hpi : Real.pi = ((n : ℝ) + 1 / 2) * rho := (div_eq_iff hrhopos.ne').mp hrat
  have hspan : Real.pi - (n : ℝ) * rho = rho / 2 := by nlinarith
  have hrholam : rho < lam := by
    have hp := (div_lt_iff₀ hleg.lam_pos).mp
      (show Real.pi / lam < (n : ℝ) + 1 / 2 by linarith)
    exact (div_lt_iff₀ hden).mpr (by nlinarith)
  have hlegrho : Section4Legality c rho := by
    refine ⟨hrhopos, hleg.inj, ?_⟩
    intro i j k hij hjk hik
    have h := hleg.triAngle i j k hij hjk hik
    linarith
  have hcone : ∀ i j : Fin s, i ≠ v → j ≠ v →
      InnerProductGeometry.angle (c i - c v) (c j - c v) ≤ rho / 2 := by
    intro i j hiv hjv
    by_cases hij : i = j
    · subst j
      rw [InnerProductGeometry.angle_self (sub_ne_zero.mpr (hleg.inj.ne hiv))]
      exact div_nonneg hrhopos.le (by norm_num)
    · have h := angle_le_pi_sub_of_saturation o e (by omega : 2 ≤ n) hrhopos
        hnrho hlegrho he (by omega : 2 ≤ s) hiv.symm hjv.symm hij hsat
      rw [hspan] at h
      exact h
  have hbound := potential_le_two_pow_of_low_small_cone o e he hs hn3 hleg hn
    hdelta v (show rho / 2 < lam / 2 by linarith) hcone
  exact (not_le_of_gt hover) hbound

#print axioms potential_le_two_pow_of_cone_budget
#print axioms potential_le_two_pow_of_low_small_cone
#print axioms exists_large_anchor_angle_of_low_counter
#print axioms no_low_boundary_saturation_of_counter

end Jsp404.SmallConeLowCapacity
