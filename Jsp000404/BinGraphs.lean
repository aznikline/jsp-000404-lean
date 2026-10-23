import Jsp000404.ConeCorridor
import Jsp000404.IntervalPacking
import JSP404.DirectionalCover
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
# Uniquely assigned direction bins

Each pair of distinct vertices belongs to the single bin selected by
`uniformBin`. The angle cap makes each bin graph bipartite, while its
active coordinates are exactly the occupied bins of the direction row.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

variable {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
  (p : Fin s → Plane₂) (he : e ≠ 0) (hp : Function.Injective p)

noncomputable def directionBinGraph (start width : ℝ) (m : ℕ)
    (b : Fin m) : SimpleGraph (Fin s) where
  Adj i j := i ≠ j ∧ uniformBin start width m (dirRep o e p i j) = b.val
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    rw [← dirRep_comm o e p he (fun hEq => h.1 (hp hEq))]
    exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem directionBinGraph_cover (start width : ℝ) {m : ℕ} (hm : 0 < m)
    (i j : Fin s) (hij : i ≠ j) :
    ∃ b, (directionBinGraph o e p he hp start width m b).Adj i j := by
  exact ⟨⟨uniformBin start width m (dirRep o e p i j), uniformBin_lt hm _⟩,
    hij, rfl⟩

theorem directionBinGraph_cover_unique (start width : ℝ) {m : ℕ} (hm : 0 < m)
    (i j : Fin s) (hij : i ≠ j) :
    ∃! b, (directionBinGraph o e p he hp start width m b).Adj i j := by
  obtain ⟨b, hb⟩ := directionBinGraph_cover o e p he hp start width hm i j hij
  refine ⟨b, hb, ?_⟩
  intro c hc
  exact Fin.ext (hc.2.symm.trans hb.2)

private lemma angle_rotation_le_of_chart (he : e ≠ 0) {u : Plane₂} (hu : u ≠ 0)
    {x center width : ℝ} (hx : x ∈ Set.Ico 0 Real.pi)
    (hc : center ∈ Set.Ico 0 Real.pi)
    (hdir : o.oangle e u = (x : Real.Angle))
    (hdist : |x - center| ≤ width / 2) :
    InnerProductGeometry.angle u (o.rotation (center : Real.Angle) e) ≤ width / 2 := by
  have hr : o.rotation (center : Real.Angle) e ≠ 0 := by
    intro h
    exact he ((o.rotation (center : Real.Angle)).injective (by simpa using h))
  rw [angle_eq_abs_of_half_plane_chart o he hu hr hx hc hdir
    (o.oangle_rotation_self_right he _), abs_sub_comm]
  exact hdist

theorem directionBinGraph_le_coneGraph {start width : ℝ} {m : ℕ}
    (hm : 0 < m) (hw : 0 < width) (hstart : 0 ≤ start)
    (hend : start + (m : ℝ) * width < Real.pi)
    (hpos : ∀ i j, i ≠ j →
      dirRep o e p i j ∈ Set.Icc start (start + (m : ℝ) * width))
    (b : Fin m) :
    directionBinGraph o e p he hp start width m b ≤
      JSP404.coneGraph p (o.rotation
        ((start + ((b.val : ℝ) + 1/2) * width : ℝ) : Real.Angle) e) (width / 2) := by
  intro i j hij
  have hne : p j - p i ≠ 0 :=
    sub_ne_zero.mpr (fun h => hij.1 (hp h).symm)
  have hb : (b.val : ℝ) + 1 ≤ m := by exact_mod_cast b.isLt
  have hb0 : (0 : ℝ) ≤ b.val := by positivity
  have hcenter : start + ((b.val : ℝ) + 1/2) * width ∈ Set.Ico 0 Real.pi := by
    constructor <;> nlinarith
  have hx : dirRep o e p i j ∈ Set.Ico 0 Real.pi := linRep_mem_Ico _
  have hbin := uniformBin_position hm hw (hpos i j hij.1)
  rw [hij.2] at hbin
  have hdist : |dirRep o e p i j - (start + ((b.val : ℝ) + 1/2) * width)| ≤
      width / 2 := abs_le.mpr ⟨by nlinarith [hbin.1], by nlinarith [hbin.2]⟩
  rcases linRep_class (o.oangle e (p j - p i)) with hdir | hdir
  · exact Or.inl ⟨hij.1, angle_rotation_le_of_chart o e he hne hx hcenter
      hdir.symm hdist⟩
  · have hreverse : o.oangle e (p i - p j) = (dirRep o e p i j : Real.Angle) := by
      rw [show p i - p j = -(p j - p i) by abel, o.oangle_neg_right he hne]
      exact hdir.symm
    exact Or.inr ⟨hij.1.symm, angle_rotation_le_of_chart o e he
      (sub_ne_zero.mpr (fun h => hij.1 (hp h))) hx hcenter hreverse hdist⟩

theorem directionBinGraph_colorable {lam start width : ℝ} {m : ℕ}
    (hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hstart : 0 ≤ start) (hend : start + (m : ℝ) * width < Real.pi)
    (hangle : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      ∠ (p a) (p b) (p c) ≤ Real.pi - lam)
    (hpos : ∀ i j, i ≠ j →
      dirRep o e p i j ∈ Set.Icc start (start + (m : ℝ) * width))
    (b : Fin m) : (directionBinGraph o e p he hp start width m b).Colorable 2 := by
  apply SimpleGraph.Colorable.mono_left
    (directionBinGraph_le_coneGraph o e p he hp hm hw hstart hend hpos b)
  apply JSP404.coneGraph_colorable hp
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · intro a b c hab hac hbc
    have h := hangle a b c hab hac hbc
    linarith

theorem directionBinGraph_weighted_bound {lam start width : ℝ} {m : ℕ}
    (hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hstart : 0 ≤ start) (hend : start + (m : ℝ) * width < Real.pi)
    (hangle : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      ∠ (p a) (p b) (p c) ≤ Real.pi - lam)
    (hpos : ∀ i j, i ≠ j →
      dirRep o e p i j ∈ Set.Icc start (start + (m : ℝ) * width)) :
    ∑ i, 2 ^ (m - (JSP404.activeParts
      (directionBinGraph o e p he hp start width m) i).card) ≤ 2 ^ m := by
  exact JSP404.bipartite_cover_weighted_bound m _
    (directionBinGraph_colorable o e p he hp hm hw hwidth hstart hend hangle hpos)
    (directionBinGraph_cover o e p he hp start width hm)

theorem directionBinGraph_activeParts_card (start width : ℝ) {m : ℕ}
    (hm : 0 < m) (i : Fin s) :
    (JSP404.activeParts (directionBinGraph o e p he hp start width m) i).card =
      ((directionRow o e p i).map (uniformBin start width m)).toFinset.card := by
  classical
  have himage :
      (JSP404.activeParts
        (directionBinGraph o e p he hp start width m) i).image
          (fun b : Fin m => b.val) =
        ((directionRow o e p i).map
          (uniformBin start width m)).toFinset := by
    ext b
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simp only [JSP404.activeParts, Finset.mem_filter,
        Finset.mem_univ, true_and] at ha
      change ∃ j, i ≠ j ∧
        uniformBin start width m (dirRep o e p i j) = a.val at ha
      obtain ⟨j, hij, hbin⟩ := ha
      exact ⟨dirRep o e p i j,
        (mem_directionRow o e p).mpr ⟨j, hij.symm, rfl⟩,
        hbin⟩
    · rintro ⟨x, hx, hbin⟩
      obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e p).mp hx
      refine ⟨⟨uniformBin start width m (dirRep o e p i j),
        uniformBin_lt hm _⟩, ?_, hbin⟩
      simp only [JSP404.activeParts, Finset.mem_filter,
        Finset.mem_univ, true_and]
      change ∃ k, i ≠ k ∧
        uniformBin start width m (dirRep o e p i k) =
          uniformBin start width m (dirRep o e p i j)
      exact ⟨j, hji.symm, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Fin.val_injective]

include he hp in
/-- The geometric bin cover in the occupied-bin form used by local gap bounds. -/
theorem directionBinGraph_row_weighted_bound {lam start width : ℝ} {m : ℕ}
    (hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hstart : 0 ≤ start) (hend : start + (m : ℝ) * width < Real.pi)
    (hangle : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      ∠ (p a) (p b) (p c) ≤ Real.pi - lam)
    (hpos : ∀ i j, i ≠ j →
      dirRep o e p i j ∈ Set.Icc start (start + (m : ℝ) * width)) :
    ∑ i, 2 ^ (m - ((directionRow o e p i).map
      (uniformBin start width m)).toFinset.card) ≤ 2 ^ m := by
  have h := directionBinGraph_weighted_bound o e p he hp hm hw hwidth
    hstart hend hangle hpos
  simpa only [directionBinGraph_activeParts_card o e p he hp start width hm] using h

#print axioms directionBinGraph_cover
#print axioms directionBinGraph_cover_unique
#print axioms directionBinGraph_le_coneGraph
#print axioms directionBinGraph_colorable
#print axioms directionBinGraph_activeParts_card
#print axioms directionBinGraph_weighted_bound
#print axioms directionBinGraph_row_weighted_bound

end Jsp404
