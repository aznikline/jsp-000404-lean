import Jsp000404.ActualRigidFourNonapex
import Jsp000404.ActualInteriorOneClassSize
import Jsp000404.ActualPureLightBlock
import Jsp000404.ActualF18Frame

set_option autoImplicit false

/-! Rigid-four covers of all non-hull-light original points in F18.
The partitions, apex blocks, block-size bounds and outside cardinality
are constructed internally from the original actual model and profiles.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18OneHeavyThreeInterior

private noncomputable def apex {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (P : ActualInteriorOnePartition.Data c lam p) : Finset (Fin t) :=
  (ActualInteriorOneClassSize.members P 1).image
    (fun q : {q : Fin t // q ≠ p} => q.val)

private theorem apex_ne_center {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (P : ActualInteriorOnePartition.Data c lam p) {q : Fin t} (hq : q ∈ apex P) : q ≠ p := by
  classical
  obtain ⟨v,_hv,hvq⟩ := Finset.mem_image.mp hq
  intro h
  exact v.property (hvq.trans h)

private theorem apex_mem_iff {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (P : ActualInteriorOnePartition.Data c lam p) (q : Fin t) (hqp : q ≠ p) :
    q ∈ apex P ↔ P.classOf ⟨q,hqp⟩ = 1 := by
  classical
  constructor
  · intro hq
    obtain ⟨v,hv,hvq⟩ := Finset.mem_image.mp hq
    have hc := (Finset.mem_filter.mp hv).2
    have heq : v = ⟨q,hqp⟩ := Subtype.ext hvq
    simpa only [heq] using hc
  · intro hc
    exact Finset.mem_image.mpr
      ⟨⟨q,hqp⟩,by simp [ActualInteriorOneClassSize.members,hc],rfl⟩

private theorem apex_nonempty {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ} {p : Fin t}
    (P : ActualInteriorOnePartition.Data c lam p) : (apex P).Nonempty := by
  classical
  refine ⟨P.witness 1,?_⟩
  exact Finset.mem_image.mpr ⟨P.witness 1,
    by simp [ActualInteriorOneClassSize.members,P.witness_class],rfl⟩

private theorem apex_avoids_selected {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ}
    (pick : Fin 4 → Fin t) (hpick : Function.Injective pick) (i : Fin 4)
    (D : ActualRigidFourNonapex.Data c lam pick hpick i) (a : Fin 4) :
    pick a ∉ apex D.partition := by
  by_cases h : a = i
  · subst a
    intro hmem
    exact apex_ne_center D.partition hmem rfl
  · intro hmem
    have hc := (apex_mem_iff D.partition (pick a) (hpick.ne h)).mp hmem
    exact D.no_apex ⟨a,h⟩ hc

private theorem apex_subset_outside {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ}
    (pick : Fin 4 → Fin t) (hpick : Function.Injective pick) (i : Fin 4)
    (D : ActualRigidFourNonapex.Data c lam pick hpick i) :
    apex D.partition ⊆ (Finset.univ.image pick)ᶜ := by
  classical
  intro q hq
  apply Finset.mem_compl.mpr
  intro him
  obtain ⟨a,_ha,haq⟩ := Finset.mem_image.mp him
  apply apex_avoids_selected pick hpick i D a
  simpa only [haq] using hq

private theorem actual_apex_card_ge_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (pick : Fin 4 → Fin (s+1)) (hpick : Function.Injective pick) (i : Fin 4)
    (D : ActualRigidFourNonapex.Data c lam pick hpick i)
    (hcover : ∀ q : Fin (s+1), q ∉ Finset.univ.image pick →
      IsHullVertex c q ∧ rowScore lam (directionRow o e c q) = 1) :
    4 ≤ (apex D.partition).card := by
  classical
  have hsub := apex_subset_outside pick hpick i D
  have hprofile (q : Fin (s+1)) (hq : q ∈ apex D.partition) :
      IsHullVertex c q ∧ rowScore lam (directionRow o e c q) = 1 :=
    hcover q (Finset.mem_compl.mp (hsub hq))
  apply ActualPureLightBlock.actual_F18_pure_light_block_card_ge_four
    o e he H hF (apex D.partition) (apex_nonempty D.partition) (pick i)
    (fun h => apex_ne_center D.partition h rfl)
    (fun q hq => (hprofile q hq).1) (fun q hq => (hprofile q hq).2)
  intro u hu v hv hvp
  have hup := apex_ne_center D.partition hu
  have huc := (apex_mem_iff D.partition u hup).mp hu
  have hvc : D.partition.classOf ⟨v,hvp⟩ ≠ 1 := by
    intro h
    exact hv ((apex_mem_iff D.partition v hvp).mpr h)
  exact D.partition.apex_angle ⟨u,hup⟩ ⟨v,hvp⟩ huc hvc

private theorem actual_triangle_sum {t : ℕ} {c : Fin t → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin t) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith only [hsum]

/-- A rigid-four selection covering every original non-hull-light point
cannot contain two distinct original interior light centers in F18.
The outside-pick hypothesis is an actual original profile case; neither
partitions, block sizes nor cardinality bounds are caller premises. -/
theorem actual_f18_rigid_four_cover_contradiction {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s+1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 (s+1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (pick : Fin 4 → Fin (s+1)) (hpick : Function.Injective pick)
    (hselected : ∀ a : Fin 4,
      (¬ IsHullVertex c (pick a) ∧ rowScore lam (directionRow o e c (pick a)) = 1) ∨
      (rowScore lam (directionRow o e c (pick a)) = 2 ∧
        ∃ u v : Fin (s+1), u ≠ pick a ∧ v ≠ pick a ∧ u ≠ v ∧
          2*lam ≤ ∠ (c u) (c (pick a)) (c v)))
    (i j : Fin 4) (hij : i ≠ j)
    (hi : ¬ IsHullVertex c (pick i) ∧ rowScore lam (directionRow o e c (pick i)) = 1)
    (hj : ¬ IsHullVertex c (pick j) ∧ rowScore lam (directionRow o e c (pick j)) = 1)
    (hcover : ∀ q : Fin (s+1), q ∉ Finset.univ.image pick →
      IsHullVertex c q ∧ rowScore lam (directionRow o e c q) = 1) : False := by
  classical
  obtain ⟨Di⟩ := ActualRigidFourNonapex.actual_rigid_four_nonapex
    o e he H pick hpick hselected i hi.1 hi.2
  obtain ⟨Dj⟩ := ActualRigidFourNonapex.actual_rigid_four_nonapex
    o e he H pick hpick hselected j hj.1 hj.2
  have hci := actual_apex_card_ge_four o e he H hF pick hpick i Di hcover
  have hcj := actual_apex_card_ge_four o e he H hF pick hpick j Dj hcover
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  have hlo : 2*Real.pi/9 < lam := by rw [← hrho]; exact H.scale_lower
  have hdisjoint : Disjoint (apex Di.partition) (apex Dj.partition) := by
    apply Finset.disjoint_left.mpr
    intro q hqi hqj
    have hqpi := apex_ne_center Di.partition hqi
    have hqpj := apex_ne_center Dj.partition hqj
    have hcqi := (apex_mem_iff Di.partition q hqpi).mp hqi
    have hcqj := (apex_mem_iff Dj.partition q hqpj).mp hqj
    have hAi := Di.partition.apex_angle ⟨q,hqpi⟩
      ⟨pick j,hpick.ne hij.symm⟩ hcqi (Di.no_apex ⟨j,hij.symm⟩)
    have hAj := Dj.partition.apex_angle ⟨q,hqpj⟩
      ⟨pick i,hpick.ne hij⟩ hcqj (Dj.no_apex ⟨i,hij⟩)
    rw [EuclideanGeometry.angle_comm (c q) (c (pick i)) (c (pick j))] at hAi
    rw [EuclideanGeometry.angle_comm (c q) (c (pick j)) (c (pick i))] at hAj
    have hsum := actual_triangle_sum H.legality (pick i) (pick j) q (hpick.ne hij)
    have hnonneg := EuclideanGeometry.angle_nonneg (c (pick i)) (c q) (c (pick j))
    linarith only [hAi,hAj,hsum,hnonneg,hlo,Real.pi_pos]
  let outside : Finset (Fin (s+1)) := (Finset.univ.image pick)ᶜ
  have hsubi : apex Di.partition ⊆ outside := apex_subset_outside pick hpick i Di
  have hsubj : apex Dj.partition ⊆ outside := apex_subset_outside pick hpick j Dj
  have hsub : apex Di.partition ∪ apex Dj.partition ⊆ outside := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hsubi hq
    · exact hsubj hq
  have hunion := Finset.card_union_of_disjoint hdisjoint
  have hle := Finset.card_le_card hsub
  have himage : (Finset.univ.image pick).card = 4 := by
    rw [Finset.card_image_of_injective _ hpick]
    simp
  have hout : outside.card = (s+1)-4 := by
    simp only [outside,Finset.card_compl,Fintype.card_fin,himage]
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have htotal : s+1 ≤ 9 := by have := F.card_plus_heavy; omega
  omega

/-- One original nonacute heavy and exactly three selected original
interior light points are excluded. The original eight-point potential
is derived from the unique-heavy profile, not supplied by the caller. -/
theorem actual_one_heavy_three_interior_contradiction
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 8 → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 8 c lam)
    (heavy : Fin 8) (hh : rowScore lam (directionRow o e c heavy) = 2)
    (hwide : ∃ a b : Fin 8, a ≠ heavy ∧ b ≠ heavy ∧ a ≠ b ∧
      2*lam ≤ ∠ (c a) (c heavy) (c b))
    (hlight : ∀ q : Fin 8, q ≠ heavy → rowScore lam (directionRow o e c q) = 1)
    (inside : Fin 3 → Fin 8) (hinj : Function.Injective inside)
    (hinside : ∀ a : Fin 3, ¬ IsHullVertex c (inside a) ∧
      rowScore lam (directionRow o e c (inside a)) = 1)
    (hothers : ∀ q : Fin 8, q ≠ heavy → (∀ a : Fin 3, q ≠ inside a) → IsHullVertex c q) :
    False := by
  classical
  have hmass : potential lam (directionRows o e c) = 18 := by
    have hw (q : Fin 8) : 2 ^ rowScore lam (directionRow o e c q) =
        2 + if q = heavy then 2 else 0 := by
      by_cases hq : q = heavy
      · subst q
        simp [hh]
      · simp [hlight q hq,hq]
    unfold potential exponentAt directionRows
    simp_rw [hw]
    rw [Finset.sum_add_distrib]
    simp
  have hne (a : Fin 3) : heavy ≠ inside a := by
    intro h
    have hk := (hinside a).2
    rw [← h,hh] at hk
    omega
  have h01 := hinj.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := hinj.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := hinj.ne (by decide : (1 : Fin 3) ≠ 2)
  let pick : Fin 4 → Fin 8 := ![heavy,inside 0,inside 1,inside 2]
  have hpick : Function.Injective pick := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [pick]
    all_goals exact (hne _) hab.symm
  have hselected : ∀ a : Fin 4,
      (¬ IsHullVertex c (pick a) ∧ rowScore lam (directionRow o e c (pick a)) = 1) ∨
      (rowScore lam (directionRow o e c (pick a)) = 2 ∧
        ∃ u v : Fin 8, u ≠ pick a ∧ v ≠ pick a ∧ u ≠ v ∧
          2*lam ≤ ∠ (c u) (c (pick a)) (c v)) := by
    intro a
    fin_cases a
    · exact Or.inr ⟨hh,hwide⟩
    · exact Or.inl (hinside 0)
    · exact Or.inl (hinside 1)
    · exact Or.inl (hinside 2)
  have hcover (q : Fin 8) (hq : q ∉ Finset.univ.image pick) :
      IsHullVertex c q ∧ rowScore lam (directionRow o e c q) = 1 := by
    have hqh : q ≠ heavy := by
      intro h
      apply hq
      exact Finset.mem_image.mpr ⟨0,Finset.mem_univ 0,by simpa [pick] using h.symm⟩
    have hqi (a : Fin 3) : q ≠ inside a := by
      intro h
      fin_cases a
      · apply hq
        exact Finset.mem_image.mpr ⟨1,Finset.mem_univ 1,by simpa [pick] using h.symm⟩
      · apply hq
        exact Finset.mem_image.mpr ⟨2,Finset.mem_univ 2,by simpa [pick] using h.symm⟩
      · apply hq
        exact Finset.mem_image.mpr ⟨3,Finset.mem_univ 3,by simpa [pick] using h.symm⟩
    exact ⟨hothers q hqh hqi,hlight q hqh⟩
  exact actual_f18_rigid_four_cover_contradiction o e he H hmass pick hpick hselected
    1 2 (by decide : (1 : Fin 4) ≠ 2) (hinside 0) (hinside 1) hcover

#print axioms actual_f18_rigid_four_cover_contradiction
#print axioms actual_one_heavy_three_interior_contradiction

end Jsp404.ActualF18OneHeavyThreeInterior
