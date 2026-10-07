import Jsp000404.DevinF18TwoHeavyApex
import Jsp000404.ActualF18ThreeHeavyNoHO

/-! SOURCE_ONLY actual original F18 three-heavy consumer.

The cloud general HO lemmas and the separate original NoHO count helper
are dependencies requiring independent local verification. This candidate
is not marked compiled or a verified F18 closure. Its public inputs are
only the original actual Model, F18 mass and original heavy count three.
No subset Model, caller hull/types, window, apex receiver or budget is used.

Three private support proofs below are adapted verbatim from the reviewed
cloud candidate13caf59 (DevinF18TwoHeavyApex). They only enumerate original
hull vertices and turn original actual angle bounds into an integer budget.
HO itself receives only the legality baseline one, never an invented two.
-/

set_option autoImplicit false
set_option pp.fullNames true
open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualF18ThreeHeavy

private theorem wide_of_window_lower {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p) (hlower : 2 * lam ≤ W.width) :
    ∃ a b : Fin s, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      2 * lam ≤ ∠ (c a) (c p) (c b) :=
  ⟨W.left, W.right, W.left_ne_center, W.right_ne_center,
    W.boundary_distinct, W.width_eq_actual_angle ▸ hlower⟩

private theorem hull_set_two_point_budget {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (hs : 3 ≤ s + 1) (hleg : Section4Legality c lam) (hlam : 2 * Real.pi / 9 < lam)
    (S : Finset (Fin (s + 1))) (hShull : ∀ q ∈ S, IsHullVertex c q)
    (h1 h2 : Fin (s + 1)) (h1S : h1 ∈ S) (h2S : h2 ∈ S) (h12 : h1 ≠ h2)
    (x1 x2 : ℕ)
    (hcap1 : ∀ a b : Fin (s + 1), a ≠ h1 → b ≠ h1 → a ≠ b →
      ∠ (c a) (c h1) (c b) ≤ Real.pi - ((1 + x1 : ℕ) : ℝ) * lam)
    (hcap2 : ∀ a b : Fin (s + 1), a ≠ h2 → b ≠ h2 → a ≠ b →
      ∠ (c a) (c h2) (c b) ≤ Real.pi - ((1 + x2 : ℕ) : ℝ) * lam) :
    S.card + x1 + x2 ≤ 8 := by
  classical
  have hcard2 : 2 ≤ S.card := by
    have hsub : ({h1, h2} : Finset (Fin (s + 1))) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · rw [hx]; exact h1S
      · rw [hx]; exact h2S
    have := Finset.card_le_card hsub
    rw [Finset.card_pair h12] at this
    exact this
  let E := S.orderIsoOfFin rfl
  let pick : Fin S.card → Fin (s + 1) := fun i => (E i).val
  have hpick : Function.Injective pick := Subtype.val_injective.comp E.injective
  let kq : Fin (s + 1) → ℕ := fun q =>
    1 + (if q = h1 then x1 else 0) + (if q = h2 then x2 else 0)
  have hbudget := ActualHullTurnBudget.selected_hull_integer_budget_le_eight
    o hs hcard2 hleg hlam pick hpick (fun i => hShull _ (E i).property)
    (fun i => kq (pick i)) (by
      intro i a b ha hb hab
      by_cases hi1 : pick i = h1
      · have hk : kq (pick i) = 1 + x1 := by simp [kq, hi1, h12]
        rw [hk]
        rw [hi1] at ha hb ⊢
        exact hcap1 a b ha hb hab
      · by_cases hi2 : pick i = h2
        · have hk : kq (pick i) = 1 + x2 := by simp [kq, hi2, h12.symm]
          rw [hk]
          rw [hi2] at ha hb ⊢
          exact hcap2 a b ha hb hab
        · have hk : kq (pick i) = 1 := by simp [kq, hi1, hi2]
          rw [hk]
          have := hleg.triAngle a (pick i) b ha hb.symm hab
          push_cast
          linarith)
  have hsumS : (∑ i : Fin S.card, kq (pick i)) = ∑ q ∈ S, kq q := by
    rw [← Finset.sum_coe_sort S kq]
    exact Fintype.sum_equiv E.toEquiv _ _ (fun _ => rfl)
  have hsum : (∑ q ∈ S, kq q) = S.card + x1 + x2 := by
    simp only [kq, Finset.sum_add_distrib, Finset.sum_ite_eq', h1S, h2S, ite_true,
      Finset.sum_const, smul_eq_mul, mul_one]
  have hcount := hbudget.2
  rw [hsumS, hsum] at hcount
  exact hcount

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
      ∠ (c a) (c g) (c b) ≤ Real.pi - ((1 + 2 : ℕ) : ℝ) * lam := by
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
  have := (ActualMixedRigidCardinality.actual_window_angle_le_width W hleg a b ha hb).trans hcap
  push_cast
  linarith

/-- The original three-heavy F18 branch is impossible. The original point
count, actual HO/nonHO alternative, hull status and two acute heavy centers
are chosen internally. The HO case spends ten integer turn units; the
independently constructed NoHO apex/count consumer supplies the other case. -/
theorem actual_F18_three_heavy_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (ht : (ActualF18Frame.heavyIndices o e c lam).card = 3) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hsize : s + 1 = 6 := by
    have h := F.card_plus_heavy
    rw [ht] at h
    omega
  by_cases hobtuse : ∃ B : Fin (s + 1),
      rowScore lam (directionRow o e c B) = 2 ∧
      ∃ a b : Fin (s + 1), a ≠ B ∧ b ≠ B ∧ a ≠ b ∧
        Real.pi - 2 * lam < ∠ (c a) (c B) (c b)
  · obtain ⟨B, hB, hBwide⟩ := hobtuse
    have hallHull (q : Fin (s + 1)) : IsHullVertex c q := by
      by_contra hq
      exact DevinF18TwoHeavyApex.actual_obtuse_heavy_interior_false
        o e he H hF q hq B hB hBwide
    have hotherNotWide (q : Fin (s + 1))
        (hq : rowScore lam (directionRow o e c q) = 2) (hqB : q ≠ B) :
        ¬ ∃ a b : Fin (s + 1), a ≠ q ∧ b ≠ q ∧ a ≠ b ∧
          2 * lam ≤ ∠ (c a) (c q) (c b) := by
      intro hwide
      exact DevinF18TwoHeavyApex.actual_obtuse_heavy_other_nonacute_false
        o e he H hF B hB hBwide q hq hqB hwide
    let T := (ActualF18Frame.heavyIndices o e c lam).erase B
    have hBmem : B ∈ ActualF18Frame.heavyIndices o e c lam := by
      simp [ActualF18Frame.heavyIndices, hB]
    have hT : T.card = 2 := by
      simp only [T, Finset.card_erase_of_mem hBmem, ht]
    let E := T.orderIsoOfFin hT
    let pick : Fin 2 → Fin (s + 1) := fun i => (E i).val
    have hpick : Function.Injective pick := Subtype.val_injective.comp E.injective
    have hscore (i : Fin 2) : rowScore lam (directionRow o e c (pick i)) = 2 := by
      have hm := (Finset.mem_erase.mp (E i).property).2
      exact (Finset.mem_filter.mp hm).2
    have hne (i : Fin 2) : pick i ≠ B :=
      (Finset.mem_erase.mp (E i).property).1
    have hcap (i : Fin 2) :
        ∀ a b : Fin (s + 1), a ≠ pick i → b ≠ pick i → a ≠ b →
          ∠ (c a) (c (pick i)) (c b) ≤ Real.pi - ((1 + 2 : ℕ) : ℝ) * lam :=
      acute_heavy_cap o e he H F (pick i) (hscore i)
        (hotherNotWide (pick i) (hscore i) (hne i))
    have hbudget := hull_set_two_point_budget o H.card_ge_three H.legality F.scale_lower
      Finset.univ (fun q _ => hallHull q) (pick 0) (pick 1)
      (Finset.mem_univ _) (Finset.mem_univ _) (hpick.ne (by decide : (0 : Fin 2) ≠ 1))
      2 2 (hcap 0) (hcap 1)
    rw [Finset.card_univ, Fintype.card_fin, hsize] at hbudget
    omega
  · have hcap (g : Fin (s + 1)) (hg : rowScore lam (directionRow o e c g) = 2) :
        ∀ a b : Fin (s + 1), a ≠ g → b ≠ g → a ≠ b →
          ∠ (c a) (c g) (c b) ≤ Real.pi - 2 * lam := by
      intro a b ha hb hab
      by_contra hnot
      exact hobtuse ⟨g, hg, a, b, ha, hb, hab, lt_of_not_ge hnot⟩
    exact ActualF18ThreeHeavyNoHO.actual_F18_three_heavy_no_obtuse_false
      o e he H hF ht hcap

#print axioms actual_F18_three_heavy_false

end Jsp404.ActualF18ThreeHeavy
