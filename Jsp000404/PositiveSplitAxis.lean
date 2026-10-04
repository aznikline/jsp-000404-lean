import Jsp000404.NoSatFiveGeometry

/-! Actual split directions for positive projective rows. The direction is
an explicit rotation of an occupied ray. Both lifts of every projective
ray are retained, so repeated directions and zero representatives are
allowed. No triangle-legality, strip, or no-saturation assumption is used. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.PositiveSplitAxis

/-- Rotate the beginning of the occupied projective window into its
complementary gap, at angle pi-lambda. -/
noncomputable def axis
    (o : Orientation ℝ Plane₂ (Fin 2)) (r : Plane₂) (lam : ℝ) : Plane₂ :=
  o.rotation ((Real.pi-lam : ℝ) : Real.Angle) r

lemma axis_ne_zero
    (o : Orientation ℝ Plane₂ (Fin 2)) {r : Plane₂} (hr : r ≠ 0) (lam : ℝ) :
    axis o r lam ≠ 0 := by
  intro h
  exact hr ((o.rotation ((Real.pi-lam : ℝ) : Real.Angle)).injective
    (by simpa [axis] using h))

/-- A ray in the projective window makes angle between lambda and
pi-lambda with the constructed gap axis, whichever lift it uses. -/
theorem angle_axis_mem_Icc
    (o : Orientation ℝ Plane₂ (Fin 2)) {r v : Plane₂}
    (hr : r ≠ 0) (hv : v ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hwindow : linRep (o.oangle r v) ∈ Set.Icc 0 (Real.pi-2*lam)) :
    InnerProductGeometry.angle (axis o r lam) v ∈ Set.Icc lam (Real.pi-lam) := by
  let phi := linRep (o.oangle r v)
  have hphi : phi ∈ Set.Icc 0 (Real.pi-2*lam) := hwindow
  have haxis : axis o r lam ≠ 0 := axis_ne_zero o hr lam
  have haxisdir : o.oangle r (axis o r lam) = ((Real.pi-lam : ℝ) : Real.Angle) :=
    o.oangle_rotation_self_right hr _
  have ha : Real.pi-lam ∈ Set.Ico 0 Real.pi := by
    constructor <;> linarith [hphi.1, hphi.2]
  have hp : phi ∈ Set.Ico 0 Real.pi :=
    ⟨hphi.1, by linarith [hphi.2]⟩
  have hdirect (w : Plane₂) (hw : w ≠ 0)
      (hdir : o.oangle r w = (phi : Real.Angle)) :
      InnerProductGeometry.angle (axis o r lam) w ∈ Set.Icc lam (Real.pi-lam) := by
    rw [angle_eq_abs_of_half_plane_chart o hr haxis hw ha hp haxisdir hdir,
      abs_of_nonpos (by linarith [hphi.2])]
    constructor <;> linarith [hphi.1, hphi.2]
  rcases linRep_class (o.oangle r v) with hdir | hdir
  · exact hdirect v hv hdir.symm
  · have hneg : o.oangle r (-v) = (phi : Real.Angle) := by
      rw [o.oangle_neg_right hr hv]
      exact hdir.symm
    have h := hdirect (-v) (neg_ne_zero.mpr hv) hneg
    rw [InnerProductGeometry.angle_neg_right] at h
    constructor <;> linarith [h.1, h.2]

/-- Every actual positive row supplies a nonzero split axis with angular
margin lambda from both directions of every old center ray. -/
theorem positive_row_exists_split_axis {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin s → Plane₂) (hinj : Function.Injective c)
    {lam : ℝ} (hlam : 0 < lam) (i : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c i)) :
    ∃ u : Plane₂, u ≠ 0 ∧ ∀ j : Fin s, j ≠ i →
      lam ≤ InnerProductGeometry.angle u (c j-c i) ∧
        InnerProductGeometry.angle u (c j-c i) ≤ Real.pi-lam := by
  obtain ⟨z, hz, hcut⟩ := NoSatFiveGeometry.positive_projective_cut o e c hlam i hpos
  let r := c z-c i
  have hr : r ≠ 0 := sub_ne_zero.mpr (hinj.ne hz)
  refine ⟨axis o r lam, axis_ne_zero o hr lam, ?_⟩
  intro j hj
  have hjv : c j-c i ≠ 0 := sub_ne_zero.mpr (hinj.ne hj)
  have hwin : linRep (o.oangle r (c j-c i)) ∈ Set.Icc 0 (Real.pi-2*lam) := by
    change dirRep o r c i j ∈ _
    rw [dirRep_reference_shift o e r he hr c hinj hj.symm]
    change projectiveShift (dirRep o e c i z) (dirRep o e c i j) ∈ _
    exact ⟨(projectiveShift_mem_Ico (linRep_mem_Ico _) (linRep_mem_Ico _)).1, hcut j hj⟩
  exact angle_axis_mem_Icc o hr hjv hlam hwin

/-- The two signs of the split axis both satisfy the original angular
upper cap against every old ray. -/
theorem positive_row_exists_both_split_caps {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin s → Plane₂) (hinj : Function.Injective c)
    {lam : ℝ} (hlam : 0 < lam) (i : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c i)) :
    ∃ u : Plane₂, u ≠ 0 ∧ ∀ j : Fin s, j ≠ i →
      InnerProductGeometry.angle u (c j-c i) ≤ Real.pi-lam ∧
        InnerProductGeometry.angle (-u) (c j-c i) ≤ Real.pi-lam := by
  obtain ⟨u, hu, hbounds⟩ := positive_row_exists_split_axis o e he c hinj hlam i hpos
  refine ⟨u, hu, ?_⟩
  intro j hj
  obtain ⟨hlower, hupper⟩ := hbounds j hj
  refine ⟨hupper, ?_⟩
  rw [InnerProductGeometry.angle_neg_left]
  linarith

#print axioms axis_ne_zero
#print axioms angle_axis_mem_Icc
#print axioms positive_row_exists_split_axis
#print axioms positive_row_exists_both_split_caps
end Jsp404.PositiveSplitAxis
