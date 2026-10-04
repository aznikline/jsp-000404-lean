import Jsp000404.PositiveRowFan

/-! Actual diameter endpoints have a refined ray window. The occupied
diameter ray forces each internal projective gap below pi/2. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404
namespace DiameterFan

lemma diameter_projection_lower {A B P : Plane₂}
    (hdiam : ‖P - B‖ ≤ ‖A - B‖) :
    ‖P - A‖ ^ 2 / 2 ≤ inner (𝕜 := ℝ) (P - A) (B - A) := by
  have he : (P - A) - (B - A) = P - B := by abel
  have hs := norm_sub_sq_real (P - A) (B - A)
  rw [he] at hs
  rw [norm_sub_rev A B] at hdiam
  have hsq : ‖P - B‖ ^ 2 ≤ ‖B - A‖ ^ 2 := by gcongr
  nlinarith

lemma diameter_ray_acute {A B P : Plane₂}
    (hdiam : ‖P - B‖ ≤ ‖A - B‖) (hPA : P ≠ A) :
    InnerProductGeometry.angle (P - A) (B - A) < Real.pi / 2 := by
  have hb := diameter_projection_lower hdiam
  have hnorm : 0 < ‖P - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hPA)
  have hip : 0 < inner (𝕜 := ℝ) (P - A) (B - A) := by nlinarith
  by_contra hn
  have hangle : Real.pi / 2 ≤
      InnerProductGeometry.angle (P - A) (B - A) := le_of_not_gt hn
  have hnip := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr hangle
  linarith

/-- A list entry cannot lie strictly between two adjacent sorted entries. -/
lemma occupied_cut_brackets_adjacent {l : List ℝ} (hs : l.SortedLE)
    {t : ℝ} (ht : t ∈ l) (i : Fin l.length) (hi : i.val+1 < l.length) :
    t ≤ l.get i ∨ l.get ⟨i.val+1, hi⟩ ≤ t := by
  obtain ⟨j, rfl⟩ := List.get_of_mem ht
  have hm := List.sortedLE_iff_monotone_get.mp hs
  by_cases hj : j ≤ i
  · exact Or.inl (hm hj)
  · exact Or.inr (hm (by apply Fin.mk_le_mk.mpr; omega))

/-- Occupancy of the diameter direction bounds every internal gap. -/
lemma adjacent_gap_lt_half_pi {l : List ℝ} (hs : l.SortedLE)
    {t : ℝ} (ht : t ∈ l)
    (hwin : ∀ x ∈ l, t-Real.pi/2 < x ∧ x < t+Real.pi/2)
    (i : Fin l.length) (hi : i.val+1 < l.length) :
    l.get ⟨i.val+1, hi⟩ - l.get i < Real.pi/2 := by
  have hb := occupied_cut_brackets_adjacent hs ht i hi
  have hleft := (hwin _ (List.get_mem l i)).1
  have hright := (hwin _ (List.get_mem l ⟨i.val+1, hi⟩)).2
  rcases hb with hb | hb <;> linarith

/-- If all internal gaps have zero score, the row score is entirely
its external wrap gap. Repeated entries remain present. -/
lemma rowScore_eq_external_of_occupied_cut {l : List ℝ} (hs : l.SortedLE)
    (hne : l ≠ []) {t lam : ℝ} (ht : t ∈ l)
    (hlam : 0 < lam) (hquarter : Real.pi/4 < lam)
    (hwin : ∀ x ∈ l, t-Real.pi/2 < x ∧ x < t+Real.pi/2) :
    rowScore lam l = gapScore lam
      (l.head hne + Real.pi - l.getLast hne) := by
  have hlen := List.length_pos_iff.mpr hne
  let last : Fin l.length := ⟨l.length-1, by omega⟩
  have hg0 (i : Fin l.length) (hi : i ≠ last) : gapScore lam (gapAfter l i) = 0 := by
    have hi' : i.val+1 < l.length := by
      have hne' : i.val ≠ l.length-1 := fun hh => hi (Fin.ext hh)
      omega
    have hb := adjacent_gap_lt_half_pi hs ht hwin i hi'
    simp only [List.get_eq_getElem] at hb
    have hfl : Nat.floor ((l.get ⟨i.val+1, hi'⟩ - l.get i)/lam) < 2 :=
      (Nat.floor_lt' (by omega)).mpr ((div_lt_iff₀ hlam).mpr (by norm_num; linarith))
    unfold gapAfter gapScore
    rw [dite_eq_left hi']
    omega
  have hlast : gapAfter l last = l.head hne+Real.pi-l.getLast hne := by
    unfold gapAfter
    rw [dite_eq_right (show ¬last.val+1 < l.length by dsimp [last]; omega)]
    rw [List.head_eq_getElem hne, List.getLast_eq_getElem hne]
    simp only [List.get_eq_getElem, last]
  unfold rowScore
  rw [cycGaps_eq_ofFn_gapAfter hs, List.map_ofFn, List.sum_ofFn]
  change (∑ i : Fin l.length, gapScore lam (gapAfter l i)) = _
  rw [Finset.sum_eq_single last]
  · rw [hlast]
  · intro i _ hi
    exact hg0 i hi
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

private lemma linRep_coe_of_mem {x : ℝ} (hx : x ∈ Set.Ico 0 Real.pi) :
    linRep (x : Real.Angle) = x := by
  unfold linRep
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨by linarith [Real.pi_pos, hx.1], hx.2.le⟩,
    ite_eq_right (not_lt.mpr hx.1), ite_eq_right (ne_of_lt hx.2)]

private lemma head_eq_min {l : List ℝ} (hs : l.SortedLE) (hne : l ≠ [])
    {m : ℝ} (hm : m ∈ l) (hb : ∀ x ∈ l, m ≤ x) : l.head hne = m := by
  obtain ⟨j, rfl⟩ := List.get_of_mem hm
  apply le_antisymm
  · rw [List.head_eq_getElem hne]
    exact hs.getElem_le_getElem_of_le (Nat.zero_le _)
  · exact hb _ (List.head_mem hne)

private lemma last_eq_max {l : List ℝ} (hs : l.SortedLE) (hne : l ≠ [])
    {m : ℝ} (hm : m ∈ l) (hb : ∀ x ∈ l, x ≤ m) : l.getLast hne = m := by
  obtain ⟨j, rfl⟩ := List.get_of_mem hm
  apply le_antisymm
  · exact hb _ (List.getLast_mem hne)
  · rw [List.getLast_eq_getElem hne]
    exact hs.getElem_le_getElem_of_le (by have := j.isLt; omega)

/-- An actual diameter endpoint with positive row score k has a directed
ray window of width at most pi-(k+1)lambda. -/
theorem diameter_endpoint_exists_directed_ray_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} (hinj : Function.Injective c)
    {lam : ℝ} (hlam : 0 < lam) (hquarter : Real.pi/4 < lam)
    {A B : Fin s} (hAB : A ≠ B)
    (hdiam : ∀ P, ‖c P-c B‖ ≤ ‖c A-c B‖)
    (hpos : 0 < rowScore lam (directionRow o e c A)) :
    ∃ f : Plane₂, f ≠ 0 ∧ ∃ theta : {j : Fin s // j ≠ A} → ℝ,
      ∀ j, theta j ∈ Set.Icc 0
        (Real.pi-(rowScore lam (directionRow o e c A)+1 : ℕ)*lam) ∧
        o.oangle f (c j-c A) = (theta j : Real.Angle) := by
  classical
  let I := {j : Fin s // j ≠ A}
  let u : I → Plane₂ := fun j => c j-c A
  have hu (j : I) : u j ≠ 0 := sub_ne_zero.mpr (hinj.ne j.property)
  let b : I := ⟨B, hAB.symm⟩
  let : Nonempty I := ⟨b⟩
  let a (j : I) : ℝ := (o.oangle (u b) (u j)).toReal
  have ha (j : I) : -Real.pi/2 < a j ∧ a j < Real.pi/2 := by
    have hac := diameter_ray_acute (hdiam j) (hinj.ne j.property)
    rw [InnerProductGeometry.angle_comm,
      o.angle_eq_abs_oangle_toReal (hu b) (hu j)] at hac
    constructor <;> dsimp [a] <;> linarith [(abs_lt.mp hac).1, (abs_lt.mp hac).2]
  have hab : a b = 0 := by simp [a]
  obtain ⟨z, _, hz⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  obtain ⟨w, _, hw⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  let theta (j : I) := a j-a z
  let W := a w-a z
  have htheta (j : I) : theta j ∈ Set.Icc 0 W := by
    have hmin := hz j (Finset.mem_univ _)
    have hmax := hw j (Finset.mem_univ _)
    constructor <;> dsimp [theta, W] <;> linarith
  have hWpi : W < Real.pi := by dsimp [W]; linarith [(ha w).2, (ha z).1]
  have hdir (j : I) : o.oangle (u z) (u j) = (theta j : Real.Angle) := by
    rw [← o.oangle_sub_left (hu b) (hu z) (hu j), Real.Angle.coe_sub]
    simp only [a, Real.Angle.coe_toReal]
  let l := directionRow o (u z) c A
  have hs : l.SortedLE := directionRow_sorted o (u z) c A
  have hrep (j : I) : dirRep o (u z) c A j = theta j := by
    change linRep (o.oangle (u z) (u j)) = _
    rw [hdir j, linRep_coe_of_mem ⟨(htheta j).1, (htheta j).2.trans_lt hWpi⟩]
  have hmtheta (j : I) : theta j ∈ l := by
    rw [← hrep j]
    exact (mem_directionRow o (u z) c).mpr ⟨j, j.property, rfl⟩
  have hbounds (x : ℝ) (hx : x ∈ l) : x ∈ Set.Icc 0 W := by
    obtain ⟨j, hj, rfl⟩ := (mem_directionRow o (u z) c).mp hx
    rw [hrep ⟨j, hj⟩]
    exact htheta ⟨j, hj⟩
  have hzero : (0 : ℝ) ∈ l := by simpa [theta] using hmtheta z
  have hW : W ∈ l := by simpa [theta, W] using hmtheta w
  have hne : l ≠ [] := by intro hh; simp [hh] at hzero
  have hhead : l.head hne = 0 := head_eq_min hs hne hzero (fun x hx => (hbounds x hx).1)
  have hlast : l.getLast hne = W := last_eq_max hs hne hW (fun x hx => (hbounds x hx).2)
  have ht : -a z ∈ l := by simpa [theta, hab] using hmtheta b
  have hwin : ∀ x ∈ l, -a z-Real.pi/2 < x ∧ x < -a z+Real.pi/2 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_directionRow o (u z) c).mp hx
    rw [hrep ⟨j, hj⟩]
    dsimp [theta]
    constructor <;> linarith [(ha ⟨j, hj⟩).1, (ha ⟨j, hj⟩).2]
  have hscore : rowScore lam (directionRow o e c A) = gapScore lam (Real.pi-W) := by
    rw [rowScore_directionRow_reference_eq o e (u z) he (hu z) c hinj A lam]
    change rowScore lam l = _
    rw [rowScore_eq_external_of_occupied_cut hs hne ht hlam hquarter hwin, hhead, hlast]
    simp
  have hkfloor : rowScore lam (directionRow o e c A)+1 = Nat.floor ((Real.pi-W)/lam) := by
    unfold gapScore at hscore
    omega
  have hfloor : ((rowScore lam (directionRow o e c A)+1 : ℕ) : ℝ) ≤ (Real.pi-W)/lam := by
    rw [hkfloor]
    exact Nat.floor_le (div_nonneg (by linarith) hlam.le)
  have hbound : W ≤ Real.pi-(rowScore lam (directionRow o e c A)+1 : ℕ)*lam := by
    have hh := (le_div_iff₀ hlam).mp hfloor
    linarith
  exact ⟨u z, hu z, theta, fun j =>
    ⟨⟨(htheta j).1, (htheta j).2.trans hbound⟩, hdir j⟩⟩

#print axioms diameter_projection_lower
#print axioms rowScore_eq_external_of_occupied_cut
#print axioms diameter_endpoint_exists_directed_ray_window

end DiameterFan
end Jsp404
