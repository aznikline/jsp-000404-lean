import Jsp000404.ActualF18LightHullClumps
import Jsp000404.ActualInteriorOneClassSize
import Jsp000404.ActualMixedRigidCardinality
import Mathlib.Geometry.Euclidean.Triangle

set_option autoImplicit false

/-!
Source-only actual F18 consumer. A nonempty block of original hull light
points separated by three-scale angles at an outside original center
has at least four points. The public theorem accepts no window, clump,
gain, or budget certificate. Only the clump opposite that outside center
is proved pure light; general LI clumps may contain a heavy singleton.
No elaboration or kernel-check claim is made here.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualPureLightBlock

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

/-- Only the target is required to be an original light point. -/
private theorem light_clump_companion {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    {u : Fin (s + 1)} {W : ActualHullRayWindow.Window o c lam u}
    (D : ActualHullSmallScoreTypes.Clumps W 1 (2 * lam) (Real.pi - 3 * lam))
    (q : Fin (s + 1)) (hqu : q ≠ u)
    (hq : rowScore lam (directionRow o e c q) = 1) :
    ∃ r : Fin (s + 1), r ≠ u ∧ r ≠ q ∧ D.code r = D.code q := by
  classical
  by_contra hnone
  push_neg at hnone
  have hgain : 1 ≤ rowGain lam (directionRow o e c u) (deleteIndex o e c q u) := by
    apply rowGain_pos_of_forall_angle_ge o e c H.legality he hqu.symm H.card_ge_three
    intro j hju hjq
    have hlarge := D.different_angle_ge H.legality q j hqu hju
      (Ne.symm (hnone j hju hjq))
    linarith [H.legality.lam_pos]
  have hzero :=
    ActualInteriorOneClassSize.actual_low_four_F18_light_incoming_gain_zero
      hs o e H hF q hq u hqu.symm
  rw [hzero] at hgain
  omega

/-- The excluded center is handled separately; the cross-angle premise
is never applied with its third point equal to p. -/
private theorem outside_code_eq {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (U : Finset (Fin s)) (p : Fin s) (hp : p ∉ U)
    (u : Fin s) (hu : u ∈ U)
    {W : ActualHullRayWindow.Window o c lam u}
    (D : ActualHullSmallScoreTypes.Clumps W 1 (2 * lam) (Real.pi - 3 * lam))
    (hcross : ∀ v : Fin s, v ∉ U → v ≠ p →
      3 * lam ≤ ∠ (c u) (c p) (c v))
    (v : Fin s) (hv : v ∉ U) : D.code v = D.code p := by
  classical
  by_cases hvp : v = p
  · simpa only [hvp]
  have hpu : p ≠ u := by
    intro h
    apply hp
    simpa only [h] using hu
  have hvu : v ≠ u := by
    intro h
    apply hv
    simpa only [h] using hu
  by_contra hdiff
  have hlarge := D.different_angle_ge hleg v p hvu hpu hdiff
  rw [EuclideanGeometry.angle_comm (c v) (c u) (c p)] at hlarge
  have hsum := actual_triangle_sum hleg p u v hpu
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c v) (c u)
  have hthree := hcross v hv hvp
  linarith [Real.pi_pos]

private theorem opposite_pair {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (U : Finset (Fin (s + 1))) (p u : Fin (s + 1))
    (hlight : ∀ q ∈ U, rowScore lam (directionRow o e c q) = 1)
    {W : ActualHullRayWindow.Window o c lam u}
    (D : ActualHullSmallScoreTypes.Clumps W 1 (2 * lam) (Real.pi - 3 * lam))
    (houtside : ∀ v : Fin (s + 1), v ∉ U → D.code v = D.code p) :
    ∃ q r : Fin (s + 1), q ∈ U ∧ r ∈ U ∧ q ≠ u ∧ r ≠ u ∧ q ≠ r ∧
      ∠ (c q) (c u) (c r) ≤ Real.pi - 3 * lam := by
  classical
  obtain ⟨a, b, hau, hbu, _hab, ha, hb⟩ := D.actual_witnesses
  have hcodes : D.code a ≠ D.code b := by rw [ha, hb]; decide
  have hex : ∃ q : Fin (s + 1), q ≠ u ∧ D.code q ≠ D.code p := by
    by_cases hap : D.code a = D.code p
    · refine ⟨b, hbu, ?_⟩
      intro hbp
      exact hcodes (hap.trans hbp.symm)
    · exact ⟨a, hau, hap⟩
  obtain ⟨q, hqu, hqpcode⟩ := hex
  have hqU : q ∈ U := by
    by_contra hq
    exact hqpcode (houtside q hq)
  obtain ⟨r, hru, hrq, hrqcode⟩ :=
    light_clump_companion hs o e he H hF D q hqu (hlight q hqU)
  have hrpcode : D.code r ≠ D.code p := by
    intro hrp
    exact hqpcode (hrqcode.symm.trans hrp)
  have hrU : r ∈ U := by
    by_contra hr
    exact hrpcode (houtside r hr)
  exact ⟨q, r, hqU, hrU, hqu, hru, hrq.symm,
    D.same_angle_le H.legality q r hqu hru hrqcode.symm⟩

/-- At cardinality at most three, a pair of distinct other members
exhausts the choices at this center. -/
private theorem angle_le_of_pair_of_card_le_three {s : ℕ}
    {c : Fin s → Plane₂} {bound : ℝ}
    (U : Finset (Fin s)) (hcard : U.card ≤ 3)
    (u : Fin s) (hu : u ∈ U)
    (hpair : ∃ q r : Fin s, q ∈ U ∧ r ∈ U ∧ q ≠ u ∧ r ≠ u ∧ q ≠ r ∧
      ∠ (c q) (c u) (c r) ≤ bound)
    (a b : Fin s) (ha : a ∈ U) (hb : b ∈ U)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b) :
    ∠ (c a) (c u) (c b) ≤ bound := by
  classical
  obtain ⟨q, r, hq, hr, hqu, hru, hqr, hangle⟩ := hpair
  have hset : ({u, q, r} : Finset (Fin s)) = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hu
      · exact hq
      · exact hr
    · have hthree : ({u, q, r} : Finset (Fin s)).card = 3 := by
        simp [hqu.symm, hru.symm, hqr]
      omega
  have hamem : a ∈ ({u, q, r} : Finset (Fin s)) := by rw [hset]; exact ha
  have hbmem : b ∈ ({u, q, r} : Finset (Fin s)) := by rw [hset]; exact hb
  have haqr : a = q ∨ a = r := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hamem
    rcases hamem with h | h | h
    · exact False.elim (hau h)
    · exact Or.inl h
    · exact Or.inr h
  have hbqr : b = q ∨ b = r := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
    rcases hbmem with h | h | h
    · exact False.elim (hbu h)
    · exact Or.inl h
    · exact Or.inr h
  rcases haqr with rfl | rfl <;> rcases hbqr with rfl | rfl
  · exact False.elim (hab rfl)
  · exact hangle
  · rw [EuclideanGeometry.angle_comm (c r) (c u) (c q)]
    exact hangle
  · exact False.elim (hab rfl)

/-- The original outside center and the exclusion of v = p from the
actual cross-angle condition are explicit public premises. -/
theorem actual_F18_pure_light_block_card_ge_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (U : Finset (Fin (s + 1))) (hU : U.Nonempty)
    (p : Fin (s + 1)) (hp : p ∉ U)
    (hhull : ∀ u ∈ U, IsHullVertex c u)
    (hlight : ∀ u ∈ U, rowScore lam (directionRow o e c u) = 1)
    (hcross : ∀ u ∈ U, ∀ v : Fin (s + 1), v ∉ U → v ≠ p →
      3 * lam ≤ ∠ (c u) (c p) (c v)) :
    4 ≤ U.card := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hs : 3 ≤ s := by have := F.card_ge_six; omega
  have hpair (u : Fin (s + 1)) (hu : u ∈ U) :
      ∃ q r : Fin (s + 1), q ∈ U ∧ r ∈ U ∧ q ≠ u ∧ r ≠ u ∧ q ≠ r ∧
        ∠ (c q) (c u) (c r) ≤ Real.pi - 3 * lam := by
    obtain ⟨⟨W, D⟩⟩ :=
      ActualF18LightHullClumps.exists_actual_F18_hull_light_clumps
        o e he H hF u (hhull u hu) (hlight u hu)
    have houtside (v : Fin (s + 1)) (hv : v ∉ U) :
        D.code v = D.code p :=
      outside_code_eq H.legality F.scale_lower U p hp u hu D (hcross u hu) v hv
    exact opposite_pair hs o e he H hF U p u hlight D houtside
  by_contra hnot
  have hcard : U.card ≤ 3 := by omega
  obtain ⟨u, hu⟩ := hU
  obtain ⟨q, r, hq, hr, hqu, hru, hqr, hangleu⟩ := hpair u hu
  have hangleq : ∠ (c u) (c q) (c r) ≤ Real.pi - 3 * lam :=
    angle_le_of_pair_of_card_le_three U hcard q hq (hpair q hq)
      u r hu hr hqu.symm hqr.symm hru.symm
  have hangler : ∠ (c u) (c r) (c q) ≤ Real.pi - 3 * lam :=
    angle_le_of_pair_of_card_le_three U hcard r hr (hpair r hr)
      u q hu hq hru.symm hqr hqu.symm
  have hsum := actual_triangle_sum H.legality u q r hqu.symm
  linarith [F.scale_lower]

/-- An original F18 model with one heavy and every other original point
hull light cannot have a three-scale actual angle at that heavy.
Its HO type, the two blocks, and the original cardinality are all derived
internally; no clump or cardinality premise is accepted. -/
theorem actual_F18_one_heavy_all_hull_three_scale_angle_false {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (hF : potential lam (directionRows o e c) = 18)
    (p : Fin (s + 1)) (hp : rowScore lam (directionRow o e c p) = 2)
    (hother : ∀ q : Fin (s + 1), q ≠ p →
      IsHullVertex c q ∧ rowScore lam (directionRow o e c q) = 1)
    (hwide : ∃ a b : Fin (s + 1), a ≠ p ∧ b ≠ p ∧ a ≠ b ∧
      3 * lam ≤ ∠ (c a) (c p) (c b)) : False := by
  classical
  have F := ActualF18Frame.actual_f18_frame o e he H hF
  have hheavy : ActualF18Frame.heavyIndices o e c lam = {p} := by
    ext q
    simp only [ActualF18Frame.heavyIndices, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      by_contra hqp
      have hqone := (hother q hqp).2
      omega
    · intro hqp
      simpa only [hqp] using hp
  have hN : s + 1 = 8 := by
    have hcard := F.card_plus_heavy
    rw [hheavy, Finset.card_singleton] at hcard
    omega
  obtain ⟨⟨W, kind⟩⟩ :=
    ActualHullSmallScoreTypes.exists_actual_hull_two_type
      H.card_ge_three o e he H.legality F.scale_lower p
      (F.heavy_full_hull p hp) hp
  obtain ⟨a, b, hap, hbp, _hab, hbig⟩ := hwide
  have hwidth :=
    ActualMixedRigidCardinality.actual_window_angle_le_width W H.legality a b hap hbp
  cases kind with
  | HA _hout hcone =>
      linarith [F.scale_lower, Real.pi_pos]
  | HM _hout _hconeLo hconeHi _D =>
      linarith [F.scale_lower, Real.pi_pos]
  | HO _hout _hcone D =>
      let targets : Finset (Fin (s + 1)) := Finset.univ.erase p
      let block (k : Bool) : Finset (Fin (s + 1)) :=
        targets.filter (fun q => D.code q = k)
      have hmem (k : Bool) (q : Fin (s + 1)) :
          q ∈ block k ↔ q ≠ p ∧ D.code q = k := by
        simp [block, targets]
      obtain ⟨left, right, hlp, hrp, _hlr, hl, hr⟩ := D.actual_witnesses
      have hnonempty (k : Bool) : (block k).Nonempty := by
        cases k with
        | false => exact ⟨right, (hmem false right).2 ⟨hrp, hr⟩⟩
        | true => exact ⟨left, (hmem true left).2 ⟨hlp, hl⟩⟩
      have hfour (k : Bool) : 4 ≤ (block k).card := by
        apply actual_F18_pure_light_block_card_ge_four o e he H hF
          (block k) (hnonempty k) p
        · intro hpmem
          exact ((hmem k p).1 hpmem).1 rfl
        · intro u hu
          exact (hother u ((hmem k u).1 hu).1).1
        · intro u hu
          exact (hother u ((hmem k u).1 hu).1).2
        · intro u hu v hv hvp
          have huk := (hmem k u).1 hu
          have hvk : D.code v ≠ k := by
            intro h
            exact hv ((hmem k v).2 ⟨hvp, h⟩)
          have hdiff : D.code u ≠ D.code v := by
            rw [huk.2]
            exact Ne.symm hvk
          exact D.different_angle_ge H.legality u v huk.1 hvp hdiff
      have htargets : targets.card = s := by
        dsimp only [targets]
        rw [Finset.card_erase_of_mem (Finset.mem_univ p)]
        simp
      have hf := Finset.card_eq_sum_card_fiberwise
        (f := D.code) (s := targets) (t := Finset.univ)
        (by intro q hq; simp)
      have hsum : targets.card = (block true).card + (block false).card := by
        simpa [block, Fintype.univ_bool] using hf
      have htrue := hfour true
      have hfalse := hfour false
      omega

#print axioms actual_F18_pure_light_block_card_ge_four
#print axioms actual_F18_one_heavy_all_hull_three_scale_angle_false

end Jsp404.ActualPureLightBlock
