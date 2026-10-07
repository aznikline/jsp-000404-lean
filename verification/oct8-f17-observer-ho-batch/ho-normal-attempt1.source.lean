import Jsp000404.ActualHeavyClumpWeight
import Jsp000404.ActualMixedRigidCardinality
import Jsp000404.ActualF18ClassWeight

set_option autoImplicit false

/-!
SOURCE_ONLY: an original LOW4 obtuse heavy cannot coexist with a
different original nonacute heavy. Original hull status, scale bounds
and all actual clumps are produced internally. The generic original
excess ledger includes the potential17 case without requiring its value.

The small actual-triangle, clump-transport and original-weight helpers
are adapted from DevinF18TwoHeavyApex source 13caf59d07692d00826884a7419ca5a296c39ae9323904a236c4677bb37506a4.
Only the generic originalWeight definition is used from ClassWeight;
no F18 Frame or F18 mass hypothesis is used in this consumer.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF17ObtuseHeavyExclusion

open ActualF18ClassWeight

private theorem bool_not_ne_self (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (p q r : Fin s) (hpq : p ≠ q) :
    ∠ (c q) (c p) (c r) + ∠ (c p) (c q) (c r) +
      ∠ (c p) (c r) (c q) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c p) (p₂ := c q) (c r) (hleg.inj.ne hpq.symm)
  rw [EuclideanGeometry.angle_comm (c q) (c r) (c p),
    EuclideanGeometry.angle_comm (c r) (c p) (c q)] at hsum
  linarith only [hsum]

private theorem weight_mono {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ)
    {S T : Finset (Fin s)} (hST : S ⊆ T) :
    originalWeight o e c lam S ≤ originalWeight o e c lam T := by
  classical
  unfold originalWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => Nat.zero_le _)

private theorem weight_insert {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂) (lam : ℝ)
    (q : Fin s) (S : Finset (Fin s)) (hq : q ∉ S) :
    originalWeight o e c lam (insert q S) =
      2 ^ rowScore lam (directionRow o e c q) + originalWeight o e c lam S := by
  classical
  unfold originalWeight
  exact Finset.sum_insert hq

private theorem clump_code_eq_of_three_scale {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2*Real.pi/9 < lam)
    (p h q : Fin s) (hph : p ≠ h) (hqh : q ≠ h)
    (G : ActualMaximalLowRowClumps.Data 4 o c lam h)
    (hbig : 3*lam ≤ ∠ (c h) (c p) (c q)) :
    G.clumps.code q = G.clumps.code p := by
  by_contra hdiff
  have hlarge := G.clumps.different_angle_ge hleg q p hqh hph hdiff
  rw [EuclideanGeometry.angle_comm (c q) (c h) (c p)] at hlarge
  have hsum := actual_triangle_sum hleg p h q hph
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c q) (c h)
  linarith only [hbig,hlarge,hsum,hthird,hlo,Real.pi_pos]

private theorem clump_weights_sum {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ} {h : Fin s}
    (G : ActualMaximalLowRowClumps.Data 4 o c lam h) (b : Bool) :
    originalWeight o e c lam (ActualHeavyClumpWeight.members G b) +
      originalWeight o e c lam (ActualHeavyClumpWeight.members G (!b)) =
      originalWeight o e c lam (Finset.univ.erase h) := by
  classical
  have hdisjoint : Disjoint (ActualHeavyClumpWeight.members G b)
      (ActualHeavyClumpWeight.members G (!b)) := by
    apply Finset.disjoint_left.mpr
    intro q hqb hqnb
    have hcb := (Finset.mem_filter.mp hqb).2.2
    have hcnb := (Finset.mem_filter.mp hqnb).2.2
    exact bool_not_ne_self b (hcnb.symm.trans hcb)
  have hcover : ActualHeavyClumpWeight.members G b ∪
      ActualHeavyClumpWeight.members G (!b) = Finset.univ.erase h := by
    ext q
    cases b <;> cases hcode : G.clumps.code q <;>
      simp [ActualHeavyClumpWeight.members,hcode]
  unfold originalWeight
  rw [← Finset.sum_union hdisjoint,hcover]

private theorem original_weight_erase_heavy {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin s → Plane₂} {lam : ℝ}
    (h : Fin s) (hh : rowScore lam (directionRow o e c h) = 2) :
    originalWeight o e c lam (Finset.univ.erase h) + 4 =
      potential lam (directionRows o e c) := by
  classical
  have hmass := Finset.sum_erase_add (Finset.univ : Finset (Fin s))
    (fun q => 2 ^ rowScore lam (directionRow o e c q)) (Finset.mem_univ h)
  unfold originalWeight potential exponentAt directionRows
  simpa only [hh,show (2 : ℕ)^2 = 4 by decide] using hmass

private theorem wide_of_window_lower {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p) (hlower : 2*lam ≤ W.width) :
    ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2*lam ≤ ∠ (c a) (c p) (c b) :=
  ⟨W.left,W.right,W.left_ne_center,W.right_ne_center,
    W.boundary_distinct,W.width_eq_actual_angle ▸ hlower⟩

private theorem original_heavy_full_hull {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (p : Fin s) (hp : rowScore lam (directionRow o e c p) = 2) : IsHullVertex c p := by
  obtain ⟨hn,_hlow,_hpi⟩ := ActualMinimumCardBandMaximizer.low_band_strip
    (by decide : 2 ≤ 4) H.legality.lam_pos H.scale_lower H.scale_upper
  have hcells := rowCells_directionRow_le_of_floor_eq o e c H.legality.lam_pos p
    (by have := H.card_ge_three; omega : 2 ≤ s) hn
  have hscore := rowScore_eq_sub_defect lam H.legality.lam_pos 4 _ hcells
  have hdef : rowDefect 4 lam (directionRow o e c p) ≤ 2 := by omega
  exact FullHullInteriorDefect.low_defect_is_full_hull_vertex o e he H.legality hn p hdef

/-- In an original LOW4 minimum counter-model, a score-two point with
an actual angle above pi-2*lam cannot coexist with a different score-two
point having an actual angle at least 2*lam. No potential, hull, window,
clump, code or weight budget is supplied by the caller. -/
theorem actual_obtuse_heavy_other_nonacute_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi/((4 : ℝ)+1/2)) (Real.pi/4) 16 s c lam)
    (B : Fin s) (hB : rowScore lam (directionRow o e c B) = 2)
    (hobtuse : ∃ a b : Fin s, a ≠ B ∧ b ≠ B ∧ a ≠ b ∧
      Real.pi-2*lam < ∠ (c a) (c B) (c b))
    (C : Fin s) (hC : rowScore lam (directionRow o e c C) = 2) (hCB : C ≠ B)
    (hCwide : ∃ a b : Fin s, a ≠ C ∧ b ≠ C ∧ a ≠ b ∧
      2*lam ≤ ∠ (c a) (c C) (c b)) : False := by
  classical
  have hrho : Real.pi/((4 : ℝ)+1/2) = 2*Real.pi/9 := by ring
  have hscale : 2*Real.pi/9 < lam := by rw [← hrho]; exact H.scale_lower
  have hleg := H.legality
  obtain ⟨a0,b0,ha0,hb0,_hab0,hangle0⟩ := hobtuse
  obtain ⟨⟨W,K⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    H.card_ge_three o e he hleg hscale B (original_heavy_full_hull o e he H B hB) hB
  have hle := ActualMixedRigidCardinality.actual_window_angle_le_width W hleg a0 b0 ha0 hb0
  cases K with
  | HA _hout hcone => linarith only [hangle0,hle,hcone,hleg.lam_pos]
  | HM _hout _hlo hhi _D => linarith only [hangle0,hle,hhi]
  | HO _hout hcone D =>
    have hBwide := wide_of_window_lower W (by linarith only [hcone,hleg.lam_pos])
    obtain ⟨GB⟩ := ActualHeavyClumpWeight.exists_actual_heavy_clump_weight o e he H B hB hBwide
    obtain ⟨GC⟩ := ActualHeavyClumpWeight.exists_actual_heavy_clump_weight o e he H C hC hCwide
    let b := GB.geometry.clumps.code C
    let T := ActualHeavyClumpWeight.members GB.geometry (!b)
    let d := GC.geometry.clumps.code B
    have hTsub : T ⊆ ActualHeavyClumpWeight.members GC.geometry d := by
      intro v hv
      have hvd := (Finset.mem_filter.mp hv).2
      have hvB := hvd.1
      have hcodes : GB.geometry.clumps.code v ≠ GB.geometry.clumps.code C := by
        intro heq
        exact bool_not_ne_self b (hvd.2.symm.trans heq)
      have hvC : v ≠ C := by
        intro heq
        exact hcodes (by rw [heq])
      have h2 := GB.geometry.clumps.different_angle_ge hleg v C hvB hCB hcodes
      have h3 : 3*lam ≤ ∠ (c v) (c B) (c C) := by
        by_cases hsame : D.code v = D.code C
        · have hsmall := D.same_angle_le hleg v C hvB hCB hsame
          linarith only [h2,hsmall,hscale,Real.pi_pos]
        · exact D.different_angle_ge hleg v C hvB hCB hsame
      rw [EuclideanGeometry.angle_comm (c v) (c B) (c C)] at h3
      have hcode := clump_code_eq_of_three_scale hleg hscale B C v hCB.symm hvC GC.geometry h3
      simp [ActualHeavyClumpWeight.members,hvC,hcode,d]
    have hBT : B ∉ T := by simp [T,ActualHeavyClumpWeight.members]
    have hBd : B ∈ ActualHeavyClumpWeight.members GC.geometry d := by
      simp [ActualHeavyClumpWeight.members,hCB.symm,d]
    have hsub : insert B T ⊆ ActualHeavyClumpWeight.members GC.geometry d := by
      intro q hq
      rcases Finset.mem_insert.mp hq with hqB | hq
      · rw [hqB]
        exact hBd
      · exact hTsub hq
    have hTweight : (potential lam (directionRows o e c) - 16) + 4 ≤
        originalWeight o e c lam T := by
      have hw := GB.weight_lower (!b)
      change (potential lam (directionRows o e c) - 16) + 4 ≤ originalWeight o e c lam T at hw
      exact hw
    have hother : (potential lam (directionRows o e c) - 16) + 4 ≤ originalWeight o e c lam
        (ActualHeavyClumpWeight.members GC.geometry (!d)) := by
      have hw := GC.weight_lower (!d)
      change (potential lam (directionRows o e c) - 16) + 4 ≤
        originalWeight o e c lam (ActualHeavyClumpWeight.members GC.geometry (!d)) at hw
      exact hw
    have hinsert : originalWeight o e c lam (insert B T) = 4 + originalWeight o e c lam T := by
      rw [weight_insert o e c lam B T hBT,hB]
      norm_num
    have hmono := weight_mono o e c lam hsub
    rw [hinsert] at hmono
    have htotal := clump_weights_sum o e GC.geometry d
    have hmass := original_weight_erase_heavy o e C hC
    have hover := H.over_cap
    omega

#print axioms actual_obtuse_heavy_other_nonacute_false

end Jsp404.ActualF17ObtuseHeavyExclusion
