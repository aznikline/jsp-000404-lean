import Jsp000404.ActualPureLightBlock
import Jsp000404.ActualInteriorOneClassSize

set_option autoImplicit false

/-! SOURCE_ONLY. All-light F18 cannot have two original interior centers.
Original partitions, class sizes and the nine-point count are produced
internally. The caller supplies no apex information, classes, nearest
neighbors, cardinality, or deletion budget.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18TwoInterior

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

private theorem block_card {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    (block D k).card = (ActualInteriorOneClassSize.members D k).card := by
  classical
  exact Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)

private theorem block_nonempty {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) (k : Fin 3) :
    (block D k).Nonempty := by
  classical
  refine ⟨D.witness k, (block_mem_iff D k _ (D.witness k).property).2 ?_⟩
  exact D.witness_class k

private theorem blocks_disjoint {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) {k l : Fin 3} (hkl : k ≠ l) :
    Disjoint (block D k) (block D l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hip := block_ne_center D k hi
  exact hkl (((block_mem_iff D k i hip).mp hi).symm.trans
    ((block_mem_iff D l i hip).mp hj))

private theorem sum_block_card {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (D : ActualInteriorOnePartition.Data c lam p) :
    (∑ k : Fin 3, (block D k).card) = s - 1 := by
  classical
  have hsum : (Finset.univ : Finset {i : Fin s // i ≠ p}).card =
      ∑ k : Fin 3, (ActualInteriorOneClassSize.members D k).card := by
    simpa only [ActualInteriorOneClassSize.members] using
      (Finset.card_eq_sum_card_fiberwise (f := D.classOf)
        (s := Finset.univ) (t := Finset.univ) (by intro i hi; simp))
  have hothers : Fintype.card {i : Fin s // i ≠ p} = s - 1 := by
    simpa only [Fintype.card_fin,Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : Fin s => i = p)
  rw [Finset.card_univ,hothers] at hsum
  simpa only [block_card] using hsum.symm

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

/-- A three-scale angle at X places its two other endpoints in the
same actual class at Y. Only DY's actual separation is consumed. -/
private theorem same_class_at_second_of_apex {s : ℕ}
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (X Y q : Fin s)
    (hXY : X ≠ Y) (hqY : q ≠ Y)
    (DY : ActualInteriorOnePartition.Data c lam Y)
    (hbig : 3 * lam ≤ ∠ (c Y) (c X) (c q)) :
    DY.classOf ⟨q,hqY⟩ = DY.classOf ⟨X,hXY⟩ := by
  by_contra hdiff
  have hlarge := DY.different_angle ⟨q,hqY⟩ ⟨X,hXY⟩ hdiff
  rw [EuclideanGeometry.angle_comm (c q) (c Y) (c X)] at hlarge
  have hsum := actual_triangle_sum hleg X Y q hXY
  have hthird := EuclideanGeometry.angle_nonneg (c X) (c q) (c Y)
  linarith [Real.pi_pos]

/-- Apex containment would place five rays in one class at the second
center, leaving at least four rays in its other two actual classes. -/
private theorem other_interior_not_apex {s : ℕ}
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hN : s = 9)
    (X Y : Fin s) (hXY : X ≠ Y)
    (DX : ActualInteriorOnePartition.Data c lam X)
    (DY : ActualInteriorOnePartition.Data c lam Y)
    (hDX : ∀ k, 2 ≤ (block DX k).card)
    (hDY : ∀ k, 2 ≤ (block DY k).card) :
    DX.classOf ⟨Y,hXY.symm⟩ ≠ 1 := by
  classical
  intro hYapex
  let A := block DX 0 ∪ block DX 2
  have hdis : Disjoint (block DX 0) (block DX 2) := blocks_disjoint DX (by decide)
  have hAcard : 4 ≤ A.card := by
    dsimp only [A]
    rw [Finset.card_union_of_disjoint hdis]
    have h0 := hDX 0
    have h2 := hDX 2
    omega
  have hXA : X ∉ A := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact block_ne_center DX 0 h rfl
    · exact block_ne_center DX 2 h rfl
  let k := DY.classOf ⟨X,hXY⟩
  have hsubset : insert X A ⊆ block DY k := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      exact (block_mem_iff DY k X hXY).2 rfl
    · have hqX : q ≠ X := by
        rcases Finset.mem_union.mp hq with h | h
        · exact block_ne_center DX 0 h
        · exact block_ne_center DX 2 h
      have hnon : DX.classOf ⟨q,hqX⟩ ≠ 1 := by
        rcases Finset.mem_union.mp hq with h | h
        · rw [(block_mem_iff DX 0 q hqX).mp h]; decide
        · rw [(block_mem_iff DX 2 q hqX).mp h]; decide
      have hqY : q ≠ Y := by
        intro h
        subst q
        exact hnon hYapex
      have hbig := DX.apex_angle ⟨Y,hXY.symm⟩ ⟨q,hqX⟩ hYapex hnon
      exact (block_mem_iff DY k q hqY).2
        (same_class_at_second_of_apex hleg hlo X Y q hXY hqY DY hbig)
  have hkcard : 5 ≤ (block DY k).card := by
    have hle := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hXA] at hle
    omega
  let lower (j : Fin 3) : ℕ := if j = k then 5 else 2
  have hlower : ∀ j, lower j ≤ (block DY j).card := by
    intro j
    by_cases hj : j = k
    · subst j; simpa [lower] using hkcard
    · simpa [lower,hj] using hDY j
  have hsumLower : (∑ j : Fin 3, lower j) = 9 := by
    have hgeneric (l : Fin 3) : (∑ j : Fin 3, if j = l then (5 : ℕ) else 2) = 9 := by
      fin_cases l <;> norm_num [Fin.sum_univ_three]
    simpa only [lower] using hgeneric k
  have hsum : (∑ j : Fin 3, lower j) ≤ ∑ j : Fin 3, (block DY j).card :=
    Finset.sum_le_sum (fun j _ => hlower j)
  rw [hsumLower,sum_block_card DY,hN] at hsum
  omega

/-- Two original interior centers in the original all-light F18 model
are impossible. Apex hull membership and all class counts are internal. -/
theorem actual_F18_all_light_two_interior_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (hall : ∀ i, rowScore lam (directionRow o e c i) = 1)
    (X Y : Fin (s + 1)) (hXY : X ≠ Y)
    (hX : ¬ IsHullVertex c X) (hY : ¬ IsHullVertex c Y) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  have hheavy : ActualF18Frame.heavyIndices o e c lam = ∅ := by
    ext q
    simp [ActualF18Frame.heavyIndices,hall q]
  have hN : s + 1 = 9 := by
    have h := F.card_plus_heavy
    rw [hheavy,Finset.card_empty,Nat.add_zero] at h
    exact h
  have h5 : Real.pi / 5 < lam := by linarith [F.scale_lower,Real.pi_pos]
  let DX := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s + 1)
    o e he H.legality h5 X hX (hall X)
  let DY := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s + 1)
    o e he H.legality h5 Y hY (hall Y)
  have hcards (p : Fin (s + 1)) (hp : ¬ IsHullVertex c p) :
      ∀ k, 2 ≤ (block (ActualInteriorOnePartition.actualPartition
        (by omega : 2 ≤ s + 1) o e he H.legality h5 p hp (hall p)) k).card := by
    intro k
    rw [block_card]
    apply ActualInteriorOneClassSize.actual_interior_one_all_zero_class_card_ge_two
      (by omega : 3 ≤ s + 1) o e he H.legality h5 p hp (hall p)
    intro q hqp
    exact ActualInteriorOneClassSize.actual_low_four_F18_light_incoming_gain_zero
      hs o e H hF q (hall q) p hqp.symm
  have hDX : ∀ k, 2 ≤ (block DX k).card := hcards X hX
  have hDY : ∀ k, 2 ≤ (block DY k).card := hcards Y hY
  have hHullApex (P : Fin (s + 1)) (hP : ¬ IsHullVertex c P)
      (q : Fin (s + 1))
      (hq : q ∈ block (ActualInteriorOnePartition.actualPartition
        (by omega : 2 ≤ s + 1) o e he H.legality h5 P hP (hall P)) 1) :
      IsHullVertex c q := by
    by_contra hqnot
    let DP := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s + 1)
      o e he H.legality h5 P hP (hall P)
    let Dq := ActualInteriorOnePartition.actualPartition (by omega : 2 ≤ s + 1)
      o e he H.legality h5 q hqnot (hall q)
    have hqP : q ≠ P := block_ne_center DP 1 hq
    have hno := other_interior_not_apex H.legality F.scale_lower hN
      P q hqP.symm DP Dq (hcards P hP) (hcards q hqnot)
    exact hno ((block_mem_iff DP 1 q hqP).mp hq)
  have hYnon : DX.classOf ⟨Y,hXY.symm⟩ ≠ 1 :=
    other_interior_not_apex H.legality F.scale_lower hN X Y hXY DX DY hDX hDY
  have hXnon : DY.classOf ⟨X,hXY⟩ ≠ 1 :=
    other_interior_not_apex H.legality F.scale_lower hN Y X hXY.symm DY DX hDY hDX
  let U := block DX 1
  let V := block DY 1
  have hUX : ∀ q ∈ U, q ≠ X := fun q hq => block_ne_center DX 1 hq
  have hVY : ∀ q ∈ V, q ≠ Y := fun q hq => block_ne_center DY 1 hq
  have hUY : ∀ q ∈ U, q ≠ Y := by
    intro q hq h
    subst q
    exact hYnon ((block_mem_iff DX 1 Y hXY.symm).mp hq)
  have hVX : ∀ q ∈ V, q ≠ X := by
    intro q hq h
    subst q
    exact hXnon ((block_mem_iff DY 1 X hXY).mp hq)
  have hU4 : 4 ≤ U.card := by
    apply ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four
      o e he H hF U (block_nonempty DX 1) X
    · intro h; exact hUX X h rfl
    · intro q hq; exact hHullApex X hX q hq
    · intro q hq; exact hall q
    · intro q hq v hv hvX
      have hq1 := (block_mem_iff DX 1 q (hUX q hq)).mp hq
      have hv1 : DX.classOf ⟨v,hvX⟩ ≠ 1 := by
        intro h
        exact hv ((block_mem_iff DX 1 v hvX).2 h)
      exact DX.apex_angle ⟨q,hUX q hq⟩ ⟨v,hvX⟩ hq1 hv1
  have hV4 : 4 ≤ V.card := by
    apply ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four
      o e he H hF V (block_nonempty DY 1) Y
    · intro h; exact hVY Y h rfl
    · intro q hq; exact hHullApex Y hY q hq
    · intro q hq; exact hall q
    · intro q hq v hv hvY
      have hq1 := (block_mem_iff DY 1 q (hVY q hq)).mp hq
      have hv1 : DY.classOf ⟨v,hvY⟩ ≠ 1 := by
        intro h
        exact hv ((block_mem_iff DY 1 v hvY).2 h)
      exact DY.apex_angle ⟨q,hVY q hq⟩ ⟨v,hvY⟩ hq1 hv1
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro q hqU hqV
    have hqX := hUX q hqU
    have hqY := hVY q hqV
    have h1 := DX.apex_angle ⟨q,hqX⟩ ⟨Y,hXY.symm⟩
      ((block_mem_iff DX 1 q hqX).mp hqU) hYnon
    have h2 := DY.apex_angle ⟨q,hqY⟩ ⟨X,hXY⟩
      ((block_mem_iff DY 1 q hqY).mp hqV) hXnon
    rw [EuclideanGeometry.angle_comm (c q) (c X) (c Y)] at h1
    rw [EuclideanGeometry.angle_comm (c q) (c Y) (c X)] at h2
    have hsum := actual_triangle_sum H.legality X Y q hXY
    have hthird := EuclideanGeometry.angle_nonneg (c X) (c q) (c Y)
    linarith [F.scale_lower,Real.pi_pos]
  have hsub : U ∪ V ⊆ (Finset.univ.erase X).erase Y := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · simp [hUX q hq,hUY q hq]
    · simp [hVX q hq,hVY q hq]
  have hle := Finset.card_le_card hsub
  have hYmem : Y ∈ (Finset.univ : Finset (Fin (s + 1))).erase X := by simp [hXY.symm]
  rw [Finset.card_union_of_disjoint hUV,Finset.card_erase_of_mem hYmem,
    Finset.card_erase_of_mem (Finset.mem_univ X),Finset.card_univ,Fintype.card_fin] at hle
  omega

#print axioms actual_F18_all_light_two_interior_false

end Jsp404.ActualF18TwoInterior
