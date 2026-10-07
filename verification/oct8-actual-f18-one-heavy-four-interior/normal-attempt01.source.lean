import Jsp000404.ActualRigidFourNonapex
import Jsp000404.ActualPureLightBlock

set_option autoImplicit false

/-!
SOURCE_ONLY actual F18 one-heavy/four-interior consumer.
The eight original points, four selected original interior partitions,
their nonapex facts and the pure-light block bounds are all internal.
The public profile supplies no type, wide angle, clump or class count.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18OneHeavyFourInterior

private noncomputable def block {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) : Finset (Fin s) :=
  (ActualInteriorOneClassSize.members D k).image
    (fun i : {i : Fin s // i ≠ p} => i.val)

private theorem block_ne_center {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3)
    {i : Fin s} (hi : i ∈ block D k) : i ≠ p := by
  classical
  obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp hi
  intro hip
  exact j.property (hji.trans hip)

private theorem block_mem_iff {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3)
    (i : Fin s) (hip : i ≠ p) :
    i ∈ block D k ↔ D.classOf ⟨i, hip⟩ = k := by
  classical
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hjk := (Finset.mem_filter.mp hj).2
    have heq : j = ⟨i, hip⟩ := Subtype.ext hji
    simpa only [heq] using hjk
  · intro hik
    exact Finset.mem_image.mpr
      ⟨⟨i, hip⟩, by simp [ActualInteriorOneClassSize.members, hik], rfl⟩

private theorem block_nonempty {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    (block D k).Nonempty := by
  classical
  exact ⟨D.witness k,
    (block_mem_iff D k _ (D.witness k).property).mpr (D.witness_class k)⟩

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

/-- Exact four-original-interior profile in the one-heavy F18 branch.
No HA/HM/HO or actual-wide-angle input is needed. -/
theorem actual_F18_one_heavy_four_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 2)
    (hlight : ∀ q : Fin (s + 1), q ≠ p →
      rowScore lam (directionRow o e c q) = 1)
    (pick : Fin 4 → Fin (s + 1)) (hpick : Function.Injective pick)
    (hinterior : ∀ i : Fin 4, ¬ IsHullVertex c (pick i))
    (hotherHull : ∀ q : Fin (s + 1), q ≠ p →
      (∀ i : Fin 4, q ≠ pick i) → IsHullVertex c q) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hpHull := F.heavy_full_hull p hp
  have hPickNe (i : Fin 4) : pick i ≠ p := by
    intro h
    exact hinterior i (by simpa only [h] using hpHull)
  have hPickLight (i : Fin 4) :
      rowScore lam (directionRow o e c (pick i)) = 1 := hlight (pick i) (hPickNe i)
  have hheavy : ActualF18Frame.heavyIndices o e c lam = {p} := by
    ext q
    simp only [ActualF18Frame.heavyIndices, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      by_contra hqp
      have hqone := hlight q hqp
      omega
    · intro hqp
      simpa only [hqp] using hp
  have hN : s + 1 = 8 := by
    have hcard := F.card_plus_heavy
    rw [hheavy, Finset.card_singleton] at hcard
    omega
  have hselected (i : Fin 4) :
      (¬ IsHullVertex c (pick i) ∧ rowScore lam (directionRow o e c (pick i)) = 1) ∨
      (rowScore lam (directionRow o e c (pick i)) = 2 ∧
        ∃ u v : Fin (s + 1), u ≠ pick i ∧ v ≠ pick i ∧ u ≠ v ∧
          2 * lam ≤ ∠ (c u) (c (pick i)) (c v)) :=
    Or.inl ⟨hinterior i, hPickLight i⟩
  have hdata (i : Fin 4) :
      Nonempty (ActualRigidFourNonapex.Data c lam pick hpick i) :=
    ActualRigidFourNonapex.actual_rigid_four_nonapex
      o e he H pick hpick hselected i (hinterior i) (hPickLight i)
  let R (i : Fin 4) : ActualRigidFourNonapex.Data c lam pick hpick i :=
    Classical.choice (hdata i)
  let I : Finset (Fin (s + 1)) := Finset.univ.image pick
  have hI : I.card = 4 := by
    change (Finset.univ.image pick).card = 4
    rw [Finset.card_image_of_injective _ hpick]
    simp
  have hpI : p ∉ I := by
    intro h
    obtain ⟨i, _hi, hip⟩ := Finset.mem_image.mp h
    exact hPickNe i hip
  have hAcard : (insert p I).card = 5 := by
    rw [Finset.card_insert_of_notMem hpI, hI]
  have hHeavyApex (i : Fin 4) :
      (R i).partition.classOf ⟨p, (hPickNe i).symm⟩ = 1 := by
    by_contra hnotapex
    let D := (R i).partition
    let U := block D 1
    have hqi (q : Fin (s + 1)) (hq : q ∈ U) : q ≠ pick i :=
      block_ne_center D 1 hq
    have hqp (q : Fin (s + 1)) (hq : q ∈ U) : q ≠ p := by
      intro h
      subst q
      exact hnotapex ((block_mem_iff D 1 p (hPickNe i).symm).mp hq)
    have hqPick (q : Fin (s + 1)) (hq : q ∈ U) (j : Fin 4) : q ≠ pick j := by
      intro h
      subst q
      by_cases hji : j = i
      · subst j
        exact hqi (pick i) hq rfl
      · exact ((R i).no_apex ⟨j, hji⟩)
          ((block_mem_iff D 1 (pick j) (hpick.ne hji)).mp hq)
    have hUfour : 4 ≤ U.card := by
      apply ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four
        o e he H hF U (block_nonempty D 1) (pick i)
      · intro h
        exact hqi (pick i) h rfl
      · intro q hq
        exact hotherHull q (hqp q hq) (hqPick q hq)
      · intro q hq
        exact hlight q (hqp q hq)
      · intro q hq v hv hvi
        have hq1 := (block_mem_iff D 1 q (hqi q hq)).mp hq
        have hv1 : D.classOf ⟨v, hvi⟩ ≠ 1 := by
          intro h
          exact hv ((block_mem_iff D 1 v hvi).mpr h)
        exact D.apex_angle ⟨q, hqi q hq⟩ ⟨v, hvi⟩ hq1 hv1
    have hdisjoint : Disjoint U (insert p I) := by
      apply Finset.disjoint_left.mpr
      intro q hq hqA
      rcases Finset.mem_insert.mp hqA with h | h
      · exact hqp q hq h
      · obtain ⟨j, _hj, hjq⟩ := Finset.mem_image.mp h
        exact hqPick q hq j hjq.symm
    have hle := Finset.card_le_card (Finset.subset_univ (U ∪ insert p I))
    rw [Finset.card_union_of_disjoint hdisjoint, hAcard,
      Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hXY : pick (0 : Fin 4) ≠ pick (1 : Fin 4) := hpick.ne (by decide)
  have hX := (R 0).partition.apex_angle
    ⟨p, (hPickNe 0).symm⟩ ⟨pick 1, hXY.symm⟩ (hHeavyApex 0)
    ((R 0).no_apex ⟨1, by decide⟩)
  have hY := (R 1).partition.apex_angle
    ⟨p, (hPickNe 1).symm⟩ ⟨pick 0, hXY⟩ (hHeavyApex 1)
    ((R 1).no_apex ⟨0, by decide⟩)
  rw [EuclideanGeometry.angle_comm (c p) (c (pick 0)) (c (pick 1))] at hX
  rw [EuclideanGeometry.angle_comm (c p) (c (pick 1)) (c (pick 0))] at hY
  have hsum := actual_triangle_sum H.legality (pick 0) (pick 1) p hXY
  have hthird := EuclideanGeometry.angle_nonneg (c (pick 0)) (c p) (c (pick 1))
  linarith [F.scale_lower, Real.pi_pos]

#print axioms actual_F18_one_heavy_four_interior_false

end Jsp404.ActualF18OneHeavyFourInterior
