import Jsp000404.ChartInvariance
import Jsp000404.AcuteFanPacking

/-! A positive actual projective row supplies a directed ray window.
The proof retains duplicate directions and uses only the actual triangle cap. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404
namespace PositiveRowFan

/-- Cut immediately after a cyclic gap. The complementary window retains
all entries, including repeated directions and a full-circle wrap gap. -/
lemma exists_shift_window_of_gap {l : List ℝ} (hs : l.SortedLE)
    (hx : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi)
    {G : ℝ} (hG : G ∈ cycGaps l) :
    ∃ cut ∈ l, ∀ x ∈ l, projectiveShift cut x ∈ Set.Icc 0 (Real.pi-G) := by
  rw [cycGaps_eq_ofFn_gapAfter hs, List.mem_ofFn] at hG
  obtain ⟨i, rfl⟩ := hG
  have hm := List.sortedLE_iff_monotone_get.mp hs
  have hn : 0 < l.length := Nat.zero_lt_of_lt i.isLt
  by_cases hi : i.val+1 < l.length
  · let next : Fin l.length := ⟨i.val+1, hi⟩
    refine ⟨l.get next, List.get_mem _ _, ?_⟩
    intro x hxm
    obtain ⟨j, rfl⟩ := List.get_of_mem hxm
    have hcut := hx _ (List.get_mem l next)
    have hj := hx _ (List.get_mem l j)
    have hbase := hx _ (List.get_mem l i)
    unfold gapAfter
    rw [dite_eq_left hi]
    change projectiveShift (l.get next) (l.get j) ∈ _
    have hnon := (projectiveShift_mem_Ico hcut hj).1
    refine ⟨hnon, ?_⟩
    unfold projectiveShift
    split_ifs with hlt
    · have hjle : j ≤ i := by
        by_contra hh
        have hnj : next ≤ j := by apply Fin.mk_le_mk.mpr; omega
        exact (not_le_of_gt hlt) (hm hnj)
      have := hm hjle
      linarith
    · linarith [hj.2, hbase.1]
  · let first : Fin l.length := ⟨0, hn⟩
    refine ⟨l.get first, List.get_mem _ _, ?_⟩
    intro x hxm
    obtain ⟨j, rfl⟩ := List.get_of_mem hxm
    have hfirst : l.get first ≤ l.get j := hm (by apply Fin.mk_le_mk.mpr; omega)
    have hlast : l.get j ≤ l.get i := hm (by apply Fin.mk_le_mk.mpr; omega)
    unfold gapAfter
    rw [dite_eq_right hi]
    change projectiveShift (l.get first) (l.get j) ∈ _
    rw [projectiveShift, ite_eq_right (not_lt.mpr hfirst)]
    constructor <;> linarith

private lemma lift_classes_separated {ι : Type*} (x : ι → ℝ) (bit : ι → Bool)
    {lam H : ℝ} (hH : H < 2 * lam)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ H) (z : ι) (hz : x z = 0)
    (hop : ∀ i j, bit i ≠ bit j → lam ≤ |x i - x j|) :
    ∀ i j, bit i = bit z → bit j ≠ bit z → x i + lam ≤ x j := by
  intro i j hi hj
  have hjlam : lam ≤ x j := by
    have hh := hop z j hj.symm
    rw [hz, zero_sub, abs_neg, abs_of_nonneg (hx j).1] at hh
    exact hh
  have hdist := hop i j (by simpa only [hi] using hj.symm)
  by_cases hij : x i ≤ x j
  · rw [abs_of_nonpos (sub_nonpos.mpr hij)] at hdist
    linarith
  · have hij' : x j < x i := lt_of_not_ge hij
    rw [abs_of_nonneg (sub_nonneg.mpr hij'.le)] at hdist
    linarith [(hx i).2]

/-- Actual nonzero rays in a narrow projective window yield a directed
window of width at most pi-lambda. The reference is an actual ray. -/
theorem exists_directed_window_of_projective_window
    {ι : Type*} [Fintype ι] (o : Orientation ℝ Plane₂ (Fin 2))
    (u : ι → Plane₂) (hu : ∀ j, u j ≠ 0) (z : ι)
    {lam H : ℝ} (hlam : 0 < lam) (hH : H < 2*lam)
    (hwidth : H ≤ Real.pi-2*lam)
    (hx : ∀ j, linRep (o.oangle (u z) (u j)) ∈ Set.Icc 0 H)
    (hang : ∀ i j, InnerProductGeometry.angle (u i) (u j) ≤ Real.pi-lam) :
    ∃ f : Plane₂, f ≠ 0 ∧ ∃ theta : ι → ℝ,
      ∀ j, theta j ∈ Set.Icc 0 (Real.pi-lam) ∧
        o.oangle f (u j) = (theta j : Real.Angle) := by
  classical
  let x (j : ι) := linRep (o.oangle (u z) (u j))
  let bit (j : ι) : Bool := decide ((x j : Real.Angle) = o.oangle (u z) (u j))
  have hx' (j : ι) : x j ∈ Set.Ico 0 Real.pi := linRep_mem_Ico _
  have hp (j : ι) (hj : bit j = true) :
      o.oangle (u z) (u j) = (x j : Real.Angle) := by
    exact (of_decide_eq_true hj).symm
  have hn (j : ι) (hj : bit j = false) :
      o.oangle (u z) (-(u j)) = (x j : Real.Angle) := by
    have hj' : ¬(x j : Real.Angle) = o.oangle (u z) (u j) := of_decide_eq_false hj
    have hc := (linRep_class (o.oangle (u z) (u j))).resolve_left hj'
    rw [o.oangle_neg_right (hu z) (hu j)]
    exact hc.symm
  have hop : ∀ i j, bit i ≠ bit j → lam ≤ |x i-x j| := by
    intro i j hij
    cases hbi : bit i <;> cases hbj : bit j
    · exact False.elim (hij (hbi.trans hbj.symm))
    · have ha := angle_eq_abs_of_half_plane_chart o (hu z) (hu j)
        (neg_ne_zero.mpr (hu i)) (hx' j) (hx' i) (hp j hbj) (hn i hbi)
      rw [InnerProductGeometry.angle_neg_right] at ha
      have hc := hang j i
      linarith
    · have ha := angle_eq_abs_of_half_plane_chart o (hu z) (hu i)
        (neg_ne_zero.mpr (hu j)) (hx' i) (hx' j) (hp i hbi) (hn j hbj)
      rw [InnerProductGeometry.angle_neg_right] at ha
      have hc := hang i j
      rw [abs_sub_comm] at ha
      linarith
    · exact False.elim (hij (hbi.trans hbj.symm))
  have hz : x z = 0 := by simp [x, linRep]
  have hbz : bit z = true := by simp [bit, hz]
  have hsep := lift_classes_separated x bit hH hx z hz hop
  by_cases hN : ∃ j, bit j = false
  · let S : Finset ι := Finset.univ.filter (fun j => bit j = false)
    have hS : S.Nonempty := by
      obtain ⟨j, hj⟩ := hN
      exact ⟨j, by simp [S, hj]⟩
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S x hS
    have hbj : bit j = false := (Finset.mem_filter.mp hj).2
    have hjlam : lam ≤ x j := by
      have := hsep z j rfl (by simp [hbz, hbj])
      simpa [hz] using this
    refine ⟨u j, hu j, fun k => if bit k = true then Real.pi+x k-x j else x k-x j, ?_⟩
    intro k
    dsimp only
    by_cases hbk : bit k = true
    · rw [ite_eq_left hbk]
      have hkj : x k+lam ≤ x j := hsep k j (hbk.trans hbz.symm)
        (by simp [hbz, hbj])
      have hanglej : o.oangle (u z) (u j) = (x j : Real.Angle)+Real.pi := by
        have hh := hn j hbj
        rw [o.oangle_neg_right (hu z) (hu j)] at hh
        have hc := congrArg (fun a : Real.Angle => a+Real.pi) hh
        simpa only [add_assoc, Real.Angle.coe_pi_add_coe_pi, add_zero] using hc
      refine ⟨⟨by linarith [(hx k).1, (hx' j).2], by linarith⟩, ?_⟩
      rw [← o.oangle_sub_left (hu z) (hu j) (hu k), hp k hbk, hanglej,
        Real.Angle.coe_sub, Real.Angle.coe_add]
      simp only [sub_eq_add_neg, neg_add_rev, Real.Angle.neg_coe_pi]
      abel
    · have hbk' : bit k = false := Bool.eq_false_iff.mpr hbk
      rw [ite_eq_right hbk]
      have hmin' : x j ≤ x k := hmin k (by simp [S, hbk'])
      refine ⟨⟨by linarith, by linarith [(hx k).2, (hx' k).2]⟩, ?_⟩
      have hjdir := hn j hbj
      have hkdir := hn k hbk'
      rw [o.oangle_neg_right (hu z) (hu j)] at hjdir
      rw [o.oangle_neg_right (hu z) (hu k)] at hkdir
      rw [← o.oangle_sub_left (hu z) (hu j) (hu k), Real.Angle.coe_sub]
      rw [← hkdir, ← hjdir]
      abel
  · refine ⟨u z, hu z, x, ?_⟩
    intro j
    have hj : bit j = true := by
      cases h : bit j
      · exact False.elim (hN ⟨j, h⟩)
      · rfl
    exact ⟨⟨(hx j).1, by linarith [(hx j).2]⟩, hp j hj⟩

/-- A positive score contains a gap spanning at least two lambda bins. -/
lemma exists_big_gap_of_rowScore_pos {lam : ℝ} (hlam : 0 < lam)
    {l : List ℝ} (hpos : 0 < rowScore lam l) :
    ∃ G ∈ cycGaps l, 2*lam ≤ G := by
  by_contra hh
  push Not at hh
  have hz : ∀ G ∈ cycGaps l, gapScore lam G = 0 := by
    intro G hG
    have hfl : Nat.floor (G/lam) < 2 := (Nat.floor_lt' (by omega)).mpr
      ((div_lt_iff₀ hlam).mpr (by simpa using hh G hG))
    unfold gapScore
    omega
  have hs : rowScore lam l = 0 := by
    unfold rowScore
    apply List.sum_eq_zero_iff.mpr
    intro a ha
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp ha
    exact hz G hG
  omega

/-- Actual positive rows above pi/4 lie in a directed window of width
pi-lambda. Its coordinates and reference are constructed from the points. -/
theorem positive_row_exists_directed_ray_window {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hquarter : Real.pi/4 < lam) (i : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c i)) :
    ∃ f : Plane₂, f ≠ 0 ∧ ∃ theta : {j : Fin s // j ≠ i} → ℝ,
      ∀ j, theta j ∈ Set.Icc 0 (Real.pi-lam) ∧
        o.oangle f (c j-c i) = (theta j : Real.Angle) := by
  classical
  obtain ⟨G, hG, hbig⟩ := exists_big_gap_of_rowScore_pos hleg.lam_pos hpos
  obtain ⟨cut, hcut, hwindow⟩ := exists_shift_window_of_gap
    (directionRow_sorted o e c i) (fun x hx => directionRow_mem_Ico o e c hx) hG
  obtain ⟨z, hzi, hz⟩ := (mem_directionRow o e c).mp hcut
  let I := {j : Fin s // j ≠ i}
  let u : I → Plane₂ := fun j => c j-c i
  have hu (j : I) : u j ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne j.property)
  let z' : I := ⟨z, hzi⟩
  have hx (j : I) : linRep (o.oangle (u z') (u j)) ∈ Set.Icc 0 (Real.pi-G) := by
    change dirRep o (c z-c i) c i j ∈ _
    rw [dirRep_reference_shift o e (c z-c i) he (hu z') c hleg.inj j.property.symm]
    change projectiveShift (dirRep o e c i z) (dirRep o e c i j) ∈ _
    rw [← hz]
    exact hwindow _ ((mem_directionRow o e c).mpr ⟨j, j.property, rfl⟩)
  have hang (j k : I) : InnerProductGeometry.angle (u j) (u k) ≤ Real.pi-lam := by
    by_cases hjk : j = k
    · subst k
      rw [InnerProductGeometry.angle_self (hu j)]
      have hnon : 0 ≤ Real.pi-G := (hx z').2.trans' (hx z').1
      linarith
    · exact hleg.triAngle j i k j.property k.property.symm
        (fun h => hjk (Subtype.ext h))
  exact exists_directed_window_of_projective_window o u hu z' hleg.lam_pos
    (by linarith) (by linarith) hx hang

#print axioms exists_shift_window_of_gap
#print axioms exists_directed_window_of_projective_window
#print axioms positive_row_exists_directed_ray_window

end PositiveRowFan
end Jsp404
