import Jsp000404.DiameterFan
import Jsp000404.WeightedCircleSeparation
import Jsp000404.TriangleRestriction
import Mathlib.Data.Finset.Sort

/-! Actual positive rows admit a circle budget. A longest pair supplies
two refined windows, and every other point supplies the positive-row window. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404
namespace PositiveRowCount

/-- Explicit actual inward bisectors have a weighted circle budget. -/
lemma actual_bisector_turn_budget {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 2 ≤ s)
    (c m : Fin s → Plane₂) (hm : ∀ i, m i ≠ 0) (a : Fin s → ℝ)
    (hbound : ∀ i j, j ≠ i →
      InnerProductGeometry.angle (m i) (c j-c i) ≤ a i/2) :
    ∑ i, (Real.pi-a i) ≤ 2*Real.pi := by
  apply weighted_circle_separation_bound o hs m hm (fun i => Real.pi-a i)
  intro i j hij
  have hi := hbound i j hij.symm
  have hj := hbound j i hij
  have hneg : InnerProductGeometry.angle (m j) (c j-c i) =
      Real.pi-InnerProductGeometry.angle (m j) (c i-c j) := by
    rw [show c j-c i = -(c i-c j) by abel, InnerProductGeometry.angle_neg_right]
  have ht := InnerProductGeometry.angle_le_angle_add_angle (m j) (m i) (c j-c i)
  rw [hneg, InnerProductGeometry.angle_comm (m j) (m i)] at ht
  linarith

/-- Actual finite ray windows supply inward bisectors and their circle budget. -/
lemma turn_budget_of_ray_windows {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 2 ≤ s)
    (c : Fin s → Plane₂) (hinj : Function.Injective c)
    (a : Fin s → ℝ) (ha : ∀ i, 0 ≤ a i) (hapi : ∀ i, a i < Real.pi)
    (e : Fin s → Plane₂) (he : ∀ i, e i ≠ 0)
    (theta : (i : Fin s) → {j : Fin s // j ≠ i} → ℝ)
    (htheta : ∀ i j, theta i j ∈ Set.Icc 0 (a i) ∧
      o.oangle (e i) (c j-c i) = (theta i j : Real.Angle)) :
    ∑ i, (Real.pi-a i) ≤ 2*Real.pi := by
  classical
  have hlocal (i : Fin s) : ∃ m : Plane₂, m ≠ 0 ∧
      ∀ j : Fin s, j ≠ i →
        InnerProductGeometry.angle m (c j-c i) ≤ a i/2 := by
    let u : {j : Fin s // j ≠ i} → Plane₂ := fun j => c j-c i
    have hu (j : {j : Fin s // j ≠ i}) : u j ≠ 0 :=
      sub_ne_zero.mpr (hinj.ne j.property)
    obtain ⟨m, hm, hb⟩ := exists_inward_bisector_of_ray_window o u hu
      (ha i) (hapi i) (e i) (he i) (theta i) (htheta i)
    exact ⟨m, hm, fun j hj => hb ⟨j, hj⟩⟩
  choose m hm hb using hlocal
  exact actual_bisector_turn_budget o hs c m hm a hb

/-- A longest actual pair is distinct and controls both endpoint fans. -/
lemma exists_diameter_pair {s : ℕ} (hs : 2 ≤ s)
    (c : Fin s → Plane₂) (hinj : Function.Injective c) :
    ∃ A B : Fin s, A ≠ B ∧
      (∀ P, ‖c P-c B‖ ≤ ‖c A-c B‖) ∧
      (∀ P, ‖c P-c A‖ ≤ ‖c B-c A‖) := by
  classical
  let z : Fin s := ⟨0, by omega⟩
  let t : Fin s := ⟨1, by omega⟩
  let S := (Finset.univ : Finset (Fin s)).product (Finset.univ : Finset (Fin s))
  have hS : S.Nonempty := ⟨(z,t), by simp [S]⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image S (fun p => ‖c p.1-c p.2‖) hS
  have hne : p.1 ≠ p.2 := by
    intro hh
    have h0 := hp (z,t) (by simp [S])
    rw [hh, sub_self, norm_zero] at h0
    have hzt : z ≠ t := by intro he; have := congrArg Fin.val he; simp [z,t] at this
    have hpos := norm_pos_iff.mpr (sub_ne_zero.mpr (hinj.ne hzt))
    linarith
  refine ⟨p.1, p.2, hne, ?_, ?_⟩
  · intro P
    exact hp (P,p.2) (by simp [S])
  · intro P
    have hh := hp (P,p.1) (by simp [S])
    simpa only [norm_sub_rev (c p.1) (c p.2)] using hh

/-- Positive actual rows at all points satisfy a weighted diameter budget. -/
theorem all_positive_diameter_turn_budget {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hquarter : Real.pi/4 < lam)
    (hpos : ∀ i, 0 < rowScore lam (directionRow o e c i))
    {A B : Fin s} (hAB : A ≠ B)
    (hA : ∀ P, ‖c P-c B‖ ≤ ‖c A-c B‖)
    (hB : ∀ P, ‖c P-c A‖ ≤ ‖c B-c A‖) :
    ((s : ℝ)+rowScore lam (directionRow o e c A)+
      rowScore lam (directionRow o e c B))*lam ≤ 2*Real.pi := by
  classical
  let k (i : Fin s) := rowScore lam (directionRow o e c i)
  let a (i : Fin s) :=
    if i = A then Real.pi-(k A+1 : ℕ)*lam else
    if i = B then Real.pi-(k B+1 : ℕ)*lam else Real.pi-lam
  have hlocal (i : Fin s) : ∃ f : Plane₂, f ≠ 0 ∧
      ∃ theta : {j : Fin s // j ≠ i} → ℝ, ∀ j,
        theta j ∈ Set.Icc 0 (a i) ∧ o.oangle f (c j-c i) = (theta j : Real.Angle) := by
    by_cases hiA : i = A
    · subst i
      simpa [a, k] using
        DiameterFan.diameter_endpoint_exists_directed_ray_window o e he hleg.inj
          hleg.lam_pos hquarter hAB hA (hpos A)
    · by_cases hiB : i = B
      · subst i
        simpa [a, k, hAB.symm] using
          DiameterFan.diameter_endpoint_exists_directed_ray_window o e he hleg.inj
            hleg.lam_pos hquarter hAB.symm hB (hpos B)
      · simpa [a, hiA, hiB] using
          PositiveRowFan.positive_row_exists_directed_ray_window o e he hleg hquarter i (hpos i)
  choose f hf theta ht using hlocal
  have ha (i : Fin s) : 0 ≤ a i := by
    let z : Fin s := ⟨0, by omega⟩
    let t : Fin s := ⟨1, by omega⟩
    have hex : ∃ j : Fin s, j ≠ i := by
      by_cases hz : z = i
      · exact ⟨t, by intro hh; have heq := congrArg Fin.val (hh.trans hz.symm); simp [z,t] at heq⟩
      · exact ⟨z, hz⟩
    obtain ⟨j,hj⟩ := hex
    exact (ht i ⟨j,hj⟩).1.1.trans (ht i ⟨j,hj⟩).1.2
  have hapi (i : Fin s) : a i < Real.pi := by
    have hka : (0 : ℝ) ≤ k A := Nat.cast_nonneg _
    have hkb : (0 : ℝ) ≤ k B := Nat.cast_nonneg _
    dsimp [a]
    split_ifs <;> push_cast <;> nlinarith [hleg.lam_pos]
  have hbudget := turn_budget_of_ray_windows o hs c hleg.inj a ha hapi f hf theta ht
  have hw (i : Fin s) : Real.pi-a i = lam+
      (if i = A then (k A : ℝ)*lam else 0)+
      (if i = B then (k B : ℝ)*lam else 0) := by
    dsimp [a]
    by_cases hiA : i = A
    · have hiB : i ≠ B := hiA ▸ hAB
      simp only [ite_eq_left hiA, ite_eq_right hiB]
      push_cast
      ring
    · by_cases hiB : i = B
      · simp only [ite_eq_right hiA, ite_eq_left hiB]
        push_cast
        ring
      · simp only [ite_eq_right hiA, ite_eq_right hiB]
        ring
  have hsum : (∑ i : Fin s, (Real.pi-a i)) = ((s : ℝ)+k A+k B)*lam := by
    rw [Finset.sum_congr rfl (fun i _ => hw i)]
    simp only [Finset.sum_add_distrib]
    simp
    ring
  rw [hsum] at hbudget
  exact hbudget

/-- Every actual all-positive configuration spends at least two extra
lambda units at the endpoints of its longest pair. -/
theorem all_positive_card_budget {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 2 ≤ s) {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hquarter : Real.pi/4 < lam)
    (hpos : ∀ i, 0 < rowScore lam (directionRow o e c i)) :
    ((s : ℝ)+2)*lam ≤ 2*Real.pi := by
  obtain ⟨A,B,hAB,hA,hB⟩ := exists_diameter_pair hs c hleg.inj
  have hb := all_positive_diameter_turn_budget o e he hs hleg hquarter hpos hAB hA hB
  have hkA : (1 : ℝ) ≤ rowScore lam (directionRow o e c A) := by exact_mod_cast hpos A
  have hkB : (1 : ℝ) ≤ rowScore lam (directionRow o e c B) := by exact_mod_cast hpos B
  nlinarith [hleg.lam_pos]

/-- At lambda>pi/4, at most five actual rows can all be positive. -/
theorem all_positive_card_le_five {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hquarter : Real.pi/4 < lam)
    (hpos : ∀ i, 0 < rowScore lam (directionRow o e c i)) : s ≤ 5 := by
  by_contra hh
  have hs : 6 ≤ s := by omega
  have hb := all_positive_card_budget o e he (by omega) hleg hquarter hpos
  have hs' : (6 : ℝ) ≤ s := by exact_mod_cast hs
  nlinarith [hleg.lam_pos, Real.pi_pos]

/-- In the low third strip, at most four actual rows can all be positive. -/
theorem all_positive_card_le_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlow : 2*Real.pi/7 < lam)
    (hpos : ∀ i, 0 < rowScore lam (directionRow o e c i)) : s ≤ 4 := by
  by_contra hh
  have hs : 5 ≤ s := by omega
  have hb := all_positive_card_budget o e he (by omega) hleg (by linarith [Real.pi_pos]) hpos
  have hs' : (5 : ℝ) ≤ s := by exact_mod_cast hs
  nlinarith [hleg.lam_pos, Real.pi_pos]

private theorem subperm_map_of_subperm {α β : Type*} (f : α → β)
    {small large : List α} (h : small.Subperm large) :
    (small.map f).Subperm (large.map f) := by
  obtain ⟨middle, hperm, hsub⟩ := h
  exact ⟨middle.map f, hperm.map f, hsub.map f⟩

/-- Restricting actual points retains a sublist of each projective row,
with all direction multiplicities. -/
lemma directionRow_restrict_sublist {s t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (pick : Fin t → Fin s) (hpick : Function.Injective pick) (i : Fin t) :
    (directionRow o e (c ∘ pick) i).Sublist (directionRow o e c (pick i)) := by
  classical
  have hind : (((List.finRange t).erase i).map pick).Subperm
      ((List.finRange s).erase (pick i)) := by
    apply List.subperm_of_subset
      (List.Nodup.map hpick ((List.nodup_finRange t).erase i))
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    rw [(List.nodup_finRange t).mem_erase_iff] at hj
    rw [(List.nodup_finRange s).mem_erase_iff]
    exact ⟨fun h => hj.1 (hpick h), List.mem_finRange _⟩
  have hraw := subperm_map_of_subperm (dirRep o e c (pick i)) hind
  have hraw' : (((List.finRange t).erase i).map (dirRep o e (c ∘ pick) i)).Subperm
      (((List.finRange s).erase (pick i)).map (dirRep o e c (pick i))) := by
    have hf : dirRep o e (c ∘ pick) i = (dirRep o e c (pick i)) ∘ pick := by
      funext j
      rfl
    rw [hf]
    simpa only [List.map_map] using hraw
  have hsmall := (List.perm_insertionSort (· ≤ ·)
    (((List.finRange t).erase i).map (dirRep o e (c ∘ pick) i))).subperm
  have hlarge := (List.perm_insertionSort (· ≤ ·)
    (((List.finRange s).erase (pick i)).map (dirRep o e c (pick i)))).symm.subperm
  exact List.sublist_of_subperm_of_sortedLE (hsmall.trans (hraw'.trans hlarge))
    (directionRow_sorted o e (c ∘ pick) i) (directionRow_sorted o e c (pick i))

/-- A retained center's positive score remains positive under any
injective point restriction having at least two centers. -/
lemma rowScore_le_restrict {s t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    {lam : ℝ} (hlam : 0 < lam) (ht : 2 ≤ t)
    (pick : Fin t → Fin s) (hpick : Function.Injective pick) (i : Fin t) :
    rowScore lam (directionRow o e c (pick i)) ≤ rowScore lam (directionRow o e (c ∘ pick) i) := by
  apply rowScore_le_of_sublist hlam (directionRow_restrict_sublist o e c pick hpick i)
    (directionRow_sorted o e c (pick i))
    (fun x hx => directionRow_mem_Ico o e c hx)
  apply List.ne_nil_of_length_pos
  rw [directionRow_length]
  omega

/-- At lambda>pi/4, an arbitrary actual configuration has at most five
positive rows, even if many other rows have score zero. -/
theorem positive_card_le_five {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hquarter : Real.pi/4 < lam) :
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 5 := by
  classical
  let P : Finset (Fin s) := Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))
  change P.card ≤ 5
  by_cases ht : 2 ≤ P.card
  · let pick : Fin P.card → Fin s := fun j => (P.orderIsoOfFin rfl j).val
    have hpick : Function.Injective pick :=
      Subtype.val_injective.comp (P.orderIsoOfFin rfl).injective
    apply all_positive_card_le_five o e he (hleg.restrict_injective pick hpick) hquarter
    intro i
    have hip : pick i ∈ P := (P.orderIsoOfFin rfl i).property
    have hi : 0 < rowScore lam (directionRow o e c (pick i)) := (Finset.mem_filter.mp hip).2
    exact hi.trans_le (rowScore_le_restrict o e c hleg.lam_pos ht pick hpick i)
  · omega

/-- In the low third strip, an arbitrary actual configuration has at
most four positive rows. -/
theorem positive_card_le_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlow : 2*Real.pi/7 < lam) :
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 4 := by
  classical
  let P : Finset (Fin s) := Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))
  change P.card ≤ 4
  by_cases ht : 2 ≤ P.card
  · let pick : Fin P.card → Fin s := fun j => (P.orderIsoOfFin rfl j).val
    have hpick : Function.Injective pick :=
      Subtype.val_injective.comp (P.orderIsoOfFin rfl).injective
    apply all_positive_card_le_four o e he (hleg.restrict_injective pick hpick) hlow
    intro i
    have hip : pick i ∈ P := (P.orderIsoOfFin rfl i).property
    have hi : 0 < rowScore lam (directionRow o e c (pick i)) := (Finset.mem_filter.mp hip).2
    exact hi.trans_le (rowScore_le_restrict o e c hleg.lam_pos ht pick hpick i)
  · omega

#print axioms exists_diameter_pair
#print axioms all_positive_diameter_turn_budget
#print axioms all_positive_card_le_five
#print axioms all_positive_card_le_four
#print axioms rowScore_le_restrict
#print axioms positive_card_le_five
#print axioms positive_card_le_four
end PositiveRowCount
end Jsp404
