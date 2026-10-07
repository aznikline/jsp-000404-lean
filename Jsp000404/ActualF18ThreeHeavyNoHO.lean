import Jsp000404.DevinF18TwoHeavyApex

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY original F18 three-heavy NoHO consumer.

The public actual-angle cap excludes HO without assigning it a false
two-unit exterior turn. Every apex receiver and every finite count below
is constructed internally from the original configuration. The cloud
general apex-heavy dependency requires its separate local verification.

The actual-window acute-cap argument is adapted from the reviewed
DevinF18TwoHeavyApex candidate. No private declaration is imported or used.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18ThreeHeavyNoHO

private theorem wide_of_window_lower {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p) (hlower : 2 * lam ≤ W.width) :
    ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b) :=
  ⟨W.left, W.right, W.left_ne_center, W.right_ne_center,
    W.boundary_distinct, W.width_eq_actual_angle ▸ hlower⟩

private theorem acute_heavy_cap {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (F : ActualF18Frame.Frame o e c lam)
    (g : Fin (s + 1)) (hg : rowScore lam (directionRow o e c g) = 2)
    (hnot : ¬ ∃ a b : Fin (s + 1), a ≠ g ∧ b ≠ g ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c g) (c b)) :
    ∀ a b : Fin (s + 1), a ≠ g → b ≠ g → a ≠ b →
      ∠ (c a) (c g) (c b) ≤ Real.pi - 3 * lam := by
  have hleg := H.legality
  obtain ⟨⟨W, K⟩⟩ := ActualHullSmallScoreTypes.exists_actual_hull_two_type
    H.card_ge_three o e he hleg F.scale_lower g (F.heavy_full_hull g hg) hg
  have hcap : W.width ≤ Real.pi - 3 * lam := by
    cases K with
    | HA _hout hcone => exact hcone
    | HM _hout hlo _hhi _D => exact False.elim (hnot (wide_of_window_lower W hlo))
    | HO _hout hlo _D =>
        exact False.elim (hnot (wide_of_window_lower W (by linarith [hleg.lam_pos])))
  intro a b ha hb _hab
  exact (ActualMixedRigidCardinality.actual_window_angle_le_width W hleg a b ha hb).trans hcap

/-- Original hull vertices have baseline one, the set T has one extra
actual turn unit, and its subset R has one more. This is just a finite-set
form of the checked actual selected-hull integer budget. -/
private theorem hull_set_nested_budget {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hs : 3 ≤ s + 1) (hleg : Section4Legality c lam) (hlam : 2 * Real.pi / 9 < lam)
    (S T R : Finset (Fin (s + 1))) (hST : T ⊆ S) (hRT : R ⊆ T)
    (hcard : 2 ≤ S.card) (hShull : ∀ q ∈ S, IsHullVertex c q)
    (hcap2 : ∀ q ∈ T, ∀ a b : Fin (s + 1), a ≠ q → b ≠ q → a ≠ b →
      ∠ (c a) (c q) (c b) ≤ Real.pi - 2 * lam)
    (hcap3 : ∀ q ∈ R, ∀ a b : Fin (s + 1), a ≠ q → b ≠ q → a ≠ b →
      ∠ (c a) (c q) (c b) ≤ Real.pi - 3 * lam) :
    S.card + T.card + R.card ≤ 8 := by
  classical
  let E := S.orderIsoOfFin rfl
  let pick : Fin S.card → Fin (s + 1) := fun i => (E i).val
  have hpick : Function.Injective pick := Subtype.val_injective.comp E.injective
  let kq : Fin (s + 1) → ℕ := fun q =>
    1 + (if q ∈ T then 1 else 0) + (if q ∈ R then 1 else 0)
  have hbudget := ActualHullTurnBudget.selected_hull_integer_budget_le_eight
    o hs hcard hleg hlam pick hpick (fun i => hShull _ (E i).property)
    (fun i => kq (pick i)) (by
      intro i a b ha hb hab
      by_cases hiR : pick i ∈ R
      · have hiT := hRT hiR
        have hk : kq (pick i) = 3 := by simp [kq, hiT, hiR]
        rw [hk]
        have hc := hcap3 (pick i) hiR a b ha hb hab
        push_cast
        linarith only [hc]
      · by_cases hiT : pick i ∈ T
        · have hk : kq (pick i) = 2 := by simp [kq, hiT, hiR]
          rw [hk]
          have hc := hcap2 (pick i) hiT a b ha hb hab
          push_cast
          linarith only [hc]
        · have hk : kq (pick i) = 1 := by simp [kq, hiT, hiR]
          rw [hk]
          have hc := hleg.triAngle a (pick i) b ha hb.symm hab
          push_cast
          linarith only [hc])
  have hsumS : (∑ i : Fin S.card, kq (pick i)) = ∑ q ∈ S, kq q := by
    rw [← Finset.sum_coe_sort S kq]
    exact Fintype.sum_equiv E.toEquiv _ _ (fun _ => rfl)
  have hfilterT : S.filter (fun q => q ∈ T) = T := by
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hST h, h⟩⟩
  have hfilterR : S.filter (fun q => q ∈ R) = R := by
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hST (hRT h), h⟩⟩
  have hTsum : (∑ q ∈ S, if q ∈ T then (1 : ℕ) else 0) = T.card := by
    rw [Finset.sum_ite, hfilterT]
    simp
  have hRsum : (∑ q ∈ S, if q ∈ R then (1 : ℕ) else 0) = R.card := by
    rw [Finset.sum_ite, hfilterR]
    simp
  have hsum : (∑ q ∈ S, kq q) = S.card + T.card + R.card := by
    simp only [kq, Finset.sum_add_distrib]
    rw [hTsum, hRsum]
    simp
  have hcount := hbudget.2
  rw [hsumS, hsum] at hcount
  exact hcount

/-- Original F18 with three original heavy centers and no actual heavy
angle above pi - 2*lam is impossible. Internally selected acute-heavy
apex receivers account for every original interior center. -/
theorem actual_F18_three_heavy_no_obtuse_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (ht : (ActualF18Frame.heavyIndices o e c lam).card = 3)
    (hcap : ∀ g : Fin (s + 1), rowScore lam (directionRow o e c g) = 2 →
      ∀ a b : Fin (s + 1), a ≠ g → b ≠ g → a ≠ b →
        ∠ (c a) (c g) (c b) ≤ Real.pi - 2 * lam) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  let T := ActualF18Frame.heavyIndices o e c lam
  have hTcard : T.card = 3 := ht
  have hTscore (g : Fin (s + 1)) (hg : g ∈ T) :
      rowScore lam (directionRow o e c g) = 2 := (Finset.mem_filter.mp hg).2
  have hThull (g : Fin (s + 1)) (hg : g ∈ T) : IsHullVertex c g :=
    F.heavy_full_hull g (hTscore g hg)
  have hTcap2 (g : Fin (s + 1)) (hg : g ∈ T) := hcap g (hTscore g hg)
  have hsize : s + 1 = 6 := by
    have hc := F.card_plus_heavy
    rw [ht] at hc
    omega
  by_cases hnonacute : ∃ B : Fin (s + 1),
      rowScore lam (directionRow o e c B) = 2 ∧
      ∃ a b : Fin (s + 1), a ≠ B ∧ b ≠ B ∧ a ≠ b ∧
        2 * lam ≤ ∠ (c a) (c B) (c b)
  · obtain ⟨B, hB, hBwide⟩ := hnonacute
    let S : Finset (Fin (s + 1)) := Finset.univ.filter (fun q => IsHullVertex c q)
    let I : Finset (Fin (s + 1)) := Finset.univ.filter (fun q => ¬ IsHullVertex c q)
    have hS (q : Fin (s + 1)) : q ∈ S ↔ IsHullVertex c q := by simp [S]
    have hI (q : Fin (s + 1)) : q ∈ I ↔ ¬ IsHullVertex c q := by simp [I]
    have hST : T ⊆ S := fun q hq => (hS q).mpr (hThull q hq)
    have hScard : 2 ≤ S.card := by
      have hc := Finset.card_le_card hST
      omega
    have hpartition : S.card + I.card = 6 := by
      have hc := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (s + 1)))) (fun q => IsHullVertex c q)
      simpa only [S, I, Finset.card_univ, Fintype.card_fin, hsize] using hc
    have hex (p : {q // q ∈ I}) :
        ∃ C ∈ (ActualF18InteriorApex.actualClassWeight o e he H hF p.val
          ((hI p.val).mp p.property)).classMembers 1,
          C ≠ B ∧ rowScore lam (directionRow o e c C) = 2 :=
      DevinF18TwoHeavyApex.actual_interior_apex_has_heavy_of_nonacute
        o e he H hF p.val ((hI p.val).mp p.property) B hB hBwide
    let receiver : {q // q ∈ I} → Fin (s + 1) := fun p => Classical.choose (hex p)
    have hrecv (p : {q // q ∈ I}) := Classical.choose_spec (hex p)
    have hrecv_apex (p : {q // q ∈ I}) :
        receiver p ∈ (ActualF18InteriorApex.actualClassWeight o e he H hF p.val
          ((hI p.val).mp p.property)).classMembers 1 := (hrecv p).1
    have hrecv_score (p : {q // q ∈ I}) :
        rowScore lam (directionRow o e c (receiver p)) = 2 := (hrecv p).2.2
    have hrecv_inj : Function.Injective receiver := by
      intro p q hpq
      by_contra hne
      have hvals : p.val ≠ q.val := fun h => hne (Subtype.ext h)
      have hd := ActualF18InteriorApex.actual_two_interior_apex_disjoint
        o e he H hF p.val q.val ((hI p.val).mp p.property)
        ((hI q.val).mp q.property) hvals
      exact Finset.disjoint_left.mp hd (hrecv_apex p) (by simpa only [hpq] using hrecv_apex q)
    let R : Finset (Fin (s + 1)) := I.attach.image receiver
    have hRcard : R.card = I.card := by
      change (I.attach.image receiver).card = I.card
      rw [Finset.card_image_of_injective _ hrecv_inj]
      exact Finset.card_attach
    have hRT : R ⊆ T := by
      intro g hg
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hg
      simp only [T, ActualF18Frame.heavyIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hrecv_score p
    have hRcap3 (g : Fin (s + 1)) (hg : g ∈ R) :
        ∀ a b : Fin (s + 1), a ≠ g → b ≠ g → a ≠ b →
          ∠ (c a) (c g) (c b) ≤ Real.pi - 3 * lam := by
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hg
      apply acute_heavy_cap o e he H F (receiver p) (hrecv_score p)
      intro hwide
      exact ActualF18NonacuteApex.actual_nonacute_heavy_not_in_interior_apex
        o e he H hF p.val ((hI p.val).mp p.property) (receiver p)
        (hrecv_score p) hwide (hrecv_apex p)
    have hbudget := hull_set_nested_budget o H.card_ge_three H.legality F.scale_lower
      S T R hST hRT hScard (fun q hq => (hS q).mp hq) hTcap2 hRcap3
    omega
  · have hTcap3 (g : Fin (s + 1)) (hg : g ∈ T) :
        ∀ a b : Fin (s + 1), a ≠ g → b ≠ g → a ≠ b →
          ∠ (c a) (c g) (c b) ≤ Real.pi - 3 * lam := by
      apply acute_heavy_cap o e he H F g (hTscore g hg)
      intro hwide
      exact hnonacute ⟨g, hTscore g hg, hwide⟩
    have hbudget := hull_set_nested_budget o H.card_ge_three H.legality F.scale_lower
      T T T (fun _ h => h) (fun _ h => h) (by omega : 2 ≤ T.card)
      hThull hTcap2 hTcap3
    omega

#print axioms actual_F18_three_heavy_no_obtuse_false

end Jsp404.ActualF18ThreeHeavyNoHO
