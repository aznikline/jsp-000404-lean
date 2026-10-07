import Jsp000404.R2N4PureTailInflation
import Jsp000404.ActualN4R2RankRegions
import Jsp000404.N4R2BetweenTerminal
import Jsp000404.N4R2OuterLeftTerminal
import Jsp000404.SatScalarModelReflection

set_option autoImplicit false
set_option pp.fullNames true

/-! SOURCE_ONLY: actual n4 HIGH exact-potential-21 R2 closure.

Selective actual inflation preserves the original protected scores and
produces all five zero-score tails. The actual saturated chart supplies
its own rank regions. Only this exact critical potential is addressed;
no arbitrary R2 capacity or original all-N conclusion is asserted.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualN4R2CriticalClosure

private theorem actual_pure_tail_eight_false
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} {c : Fin 8 → Plane₂} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi / lam) = 4)
    (v A B : Fin 8) (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hdA : rowDefect 4 lam (directionRow o e c A) = 2)
    (hdB : rowDefect 4 lam (directionRow o e c B) = 2)
    (htails : ∀ r : Fin 8, r ≠ v → r ≠ A → r ≠ B →
      rowDefect 4 lam (directionRow o e c r) = 4) : False := by
  obtain ⟨e', he', theta, htheta⟩ := saturated_ray_window o e he
    (s := 7) (by decide : 1 ≤ 7) (by decide : 2 ≤ 4) hleg.lam_pos hn hleg v hsat
  let C : SatChart o e' 4 lam c v theta :=
    ⟨he', by decide, hleg.lam_pos, hn, hleg, htheta⟩
  have href (r : Fin 8) : rowDefect 4 lam (directionRow o e' c r) =
      rowDefect 4 lam (directionRow o e c r) :=
    rowDefect_directionRow_reference_eq o e' e he' he c hleg.inj r
      hleg.lam_pos (by decide : 2 ≤ 8) hn
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hvA.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hvB.symm
  have hab : a ≠ b := by
    intro h
    exact hAB (ha.symm.trans ((congrArg v.succAbove h).trans hb))
  have hsat' : rowDefect 4 lam (directionRow o e' c v) = 1 := (href v).trans hsat
  have hda : rowDefect 4 lam (directionRow o e' c (v.succAbove a)) = 2 := by
    rw [ha, href]
    exact hdA
  have hdb : rowDefect 4 lam (directionRow o e' c (v.succAbove b)) = 2 := by
    rw [hb, href]
    exact hdB
  obtain ⟨lo, hi, _horder, hswap, hregions⟩ :=
    ActualN4R2RankRegions.actual_chart_low_rank_regions C hsat' hab hda hdb
  let rankPoint (i : Fin 7) : Fin 8 := v.succAbove (SatScalarExtraction.sigma C i)
  have hrank : Function.Injective rankPoint := by
    intro i j hij
    exact SatScalarExtraction.sigma_injective C (Fin.succAbove_right_injective hij)
  have hpositions : (rankPoint lo = A ∧ rankPoint hi = B) ∨
      (rankPoint lo = B ∧ rankPoint hi = A) := by
    rcases hswap with ⟨hl, hh⟩ | ⟨hl, hh⟩
    · exact Or.inl ⟨(congrArg v.succAbove hl).trans ha,
        (congrArg v.succAbove hh).trans hb⟩
    · exact Or.inr ⟨(congrArg v.succAbove hl).trans hb,
        (congrArg v.succAbove hh).trans ha⟩
  let M := SatScalarExtraction.model C
  have hdef (i : Fin 7) : SatScalarModel.rowDefect M i =
      rowDefect 4 lam (directionRow o e c (rankPoint i)) :=
    (SatScalarExtraction.model_rowDefect C (by decide : 2 ≤ 7) i).trans (href _)
  have hlo : SatScalarModel.rowDefect M lo = 2 := by
    rw [hdef lo]
    rcases hpositions with ⟨hl, _⟩ | ⟨hl, _⟩
    · rw [hl]; exact hdA
    · rw [hl]; exact hdB
  have hhi : SatScalarModel.rowDefect M hi = 2 := by
    rw [hdef hi]
    rcases hpositions with ⟨_, hh⟩ | ⟨_, hh⟩
    · rw [hh]; exact hdB
    · rw [hh]; exact hdA
  have htail (i : Fin 7) (hilo : i ≠ lo) (hihi : i ≠ hi) :
      SatScalarModel.rowDefect M i = 4 := by
    rw [hdef i]
    apply htails (rankPoint i) (Fin.succAbove_ne v _)
    · intro h
      rcases hpositions with ⟨hl, _⟩ | ⟨_, hh⟩
      · exact hilo (hrank (h.trans hl.symm))
      · exact hihi (hrank (h.trans hh.symm))
    · intro h
      rcases hpositions with ⟨_, hh⟩ | ⟨hl, _⟩
      · exact hihi (hrank (h.trans hh.symm))
      · exact hilo (hrank (h.trans hl.symm))
  rcases hregions with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
  · obtain ⟨_hzero, hone, htail'⟩ := SatScalarModelReflection.reflect_outer56_to_outer01 M
      hlo hhi (fun i hi5 => htail i (by omega) (by omega))
    exact N4R2OuterLeftTerminal.outer_left_low1_pure_tail_impossible
      (SatScalarModelReflection.reflect M) hone htail'
  · exact N4R2BetweenTerminal.between_pure_tail_impossible M hlo hhi
      (fun i hi0 hi6 => htail i (by omega) (by omega))
  · exact N4R2OuterLeftTerminal.outer_left_low1_pure_tail_impossible M hhi
      (fun i hi1 => htail i (by omega) (by omega))

/-- Exact original potential 21 with protected original scores 3,2,2
is impossible in the natural n4 HIGH band. Inflation, the saturated
chart, all ranks, all tail defects and three rank placements are internal. -/
theorem actual_n4_high_critical21_impossible {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 6 ≤ s) (c : Fin s → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    {a b d : Fin s} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha : rowScore lam (directionRow o e c a) = 3)
    (hb : rowScore lam (directionRow o e c b) = 2)
    (hd : rowScore lam (directionRow o e c d) = 2)
    (hF : potential lam (directionRows o e c) = 21) : False := by
  obtain ⟨lamFinal, _hlower, _hsmall, hnFinal, _hhighFinal, _hdeltaFinal,
    cFinal, hlegal, sigmaFinal, hinj, _hpoints, hscore0, hscore1, hscore2,
    hzero, _hpotential⟩ := R2N4PureTailInflation.exists_actual_n4_critical21_pure_tail_eight
      o e he hs c hleg hn hhigh hab had hbd ha hb hd hF
  have hcells (r : Fin 8) : rowCells lamFinal (directionRow o e cFinal r) ≤ 4 :=
    rowCells_directionRow_le_of_floor_eq o e cFinal hlegal.lam_pos r
      (by decide : 2 ≤ 8) hnFinal
  have hscore (r : Fin 8) : rowScore lamFinal (directionRow o e cFinal r) =
      4 - rowDefect 4 lamFinal (directionRow o e cFinal r) :=
    rowScore_eq_sub_defect lamFinal hlegal.lam_pos 4 _ (hcells r)
  have hsat : rowDefect 4 lamFinal (directionRow o e cFinal (sigmaFinal 0)) = 1 := by
    have h := hscore (sigmaFinal 0)
    omega
  have hlow1 : rowDefect 4 lamFinal (directionRow o e cFinal (sigmaFinal 1)) = 2 := by
    have h := hscore (sigmaFinal 1)
    omega
  have hlow2 : rowDefect 4 lamFinal (directionRow o e cFinal (sigmaFinal 2)) = 2 := by
    have h := hscore (sigmaFinal 2)
    omega
  have htail (r : Fin 8) (hr0 : r ≠ sigmaFinal 0) (hr1 : r ≠ sigmaFinal 1)
      (hr2 : r ≠ sigmaFinal 2) : rowDefect 4 lamFinal (directionRow o e cFinal r) = 4 := by
    have hz : rowScore lamFinal (directionRow o e cFinal r) = 0 := by
      apply hzero r
      rintro ⟨j, hj⟩
      fin_cases j
      · exact hr0 hj.symm
      · exact hr1 hj.symm
      · exact hr2 hj.symm
    have h := hscore r
    have hbound := rowDefect_le lamFinal hlegal.lam_pos 4 _ (hcells r)
    omega
  exact actual_pure_tail_eight_false o e he hlegal hnFinal
    (sigmaFinal 0) (sigmaFinal 1) (sigmaFinal 2)
    (hinj.ne (by decide : (0 : Fin 3) ≠ 1))
    (hinj.ne (by decide : (0 : Fin 3) ≠ 2))
    (hinj.ne (by decide : (1 : Fin 3) ≠ 2)) hsat hlow1 hlow2 htail

#print axioms actual_n4_high_critical21_impossible

end Jsp404.ActualN4R2CriticalClosure
