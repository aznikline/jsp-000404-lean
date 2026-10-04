import Jsp000404.PositiveRowCount

/-! Actual occupied-cut extraction for the low third-strip five-point terminal.
The reference and cut rays come from the actual direction row. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.NoSatFiveGeometry

/-- A positive actual row has an occupied projective cut whose complementary
window has width at most pi minus two lambda. Repeated directions are retained. -/
theorem positive_projective_cut {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) {lam : ℝ} (hlam : 0 < lam) (i : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c i)) :
    ∃ j : Fin s, j ≠ i ∧ ∀ k : Fin s, k ≠ i →
      projectiveShift (dirRep o e c i j) (dirRep o e c i k) ≤ Real.pi - 2*lam := by
  obtain ⟨G, hG, hbig⟩ :=
    PositiveRowFan.exists_big_gap_of_rowScore_pos hlam hpos
  obtain ⟨cut, hcut, hwindow⟩ := PositiveRowFan.exists_shift_window_of_gap
    (directionRow_sorted o e c i) (fun _ hx => directionRow_mem_Ico o e c hx) hG
  obtain ⟨j, hj, hcutj⟩ := (mem_directionRow o e c).mp hcut
  refine ⟨j, hj, ?_⟩
  intro k hk
  have hw := (hwindow _ ((mem_directionRow o e c).mpr ⟨k, hk, rfl⟩)).2
  rw [hcutj] at hw
  linarith

#print axioms positive_projective_cut

/-- Both endpoint caps of an ordered actual triangle. These are independent
of the middle-angle separation and are needed by the scalar exclusion. -/
theorem endpoint_caps {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hup : ∀ i j : Fin s, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    {i j k : Fin s} (hij : i < j) (hjk : j < k) :
    |dirRep o e c i k - dirRep o e c i j| ≤ Real.pi-lam ∧
      |dirRep o e c j k - dirRep o e c i k| ≤ Real.pi-lam := by
  have hik := hij.trans hjk
  have hnij : c j-c i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hij.ne.symm)
  have hnik : c k-c i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hik.ne.symm)
  have hnjk : c k-c j ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hjk.ne.symm)
  have hai := angle_eq_abs_of_half_plane_chart o he hnij hnik
    (linRep_mem_Ico _) (linRep_mem_Ico _) (hup i j hij) (hup i k hik)
  have hak := angle_eq_abs_of_half_plane_chart o he hnik hnjk
    (linRep_mem_Ico _) (linRep_mem_Ico _) (hup i k hik) (hup j k hjk)
  have hci := hleg.triAngle j i k hij.ne.symm hik.ne hjk.ne
  have hck := hleg.triAngle i k j hik.ne hjk.ne.symm hij.ne
  change InnerProductGeometry.angle (c j-c i) (c k-c i) ≤ _ at hci
  change InnerProductGeometry.angle (c i-c k) (c j-c k) ≤ _ at hck
  rw [show c i-c k = -(c k-c i) by abel,
    show c j-c k = -(c k-c j) by abel,
    InnerProductGeometry.angle_neg_neg] at hck
  rw [hai] at hci
  rw [hak] at hck
  exact ⟨hci, hck⟩

#print axioms endpoint_caps
end Jsp404.NoSatFiveGeometry
