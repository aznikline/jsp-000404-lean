import Jsp000404.ActualInteriorZeroPartition
import Jsp000404.ActualMinimalBandCounterexample
import Jsp000404.SmallTwoClusterGeometry
import Jsp000404.FiveTwoClassPairing

set_option autoImplicit false

/-! SOURCE_ONLY. A three-scale separated block of original interior
zero-score points has at least six members. Original partitions and the
actual five-point restriction are produced internally. Neither a deleted
configuration's criticality nor its original-hull membership is assumed.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualPureInteriorZeroBlock

private theorem actual_triangle_sum {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (A B C : Fin s) (hAB : A ≠ B) :
    ∠ (c B) (c A) (c C) + ∠ (c A) (c B) (c C) +
      ∠ (c A) (c C) (c B) = Real.pi := by
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c A) (p₂ := c B) (c C) (hleg.inj.ne hAB.symm)
  rw [EuclideanGeometry.angle_comm (c B) (c C) (c A),
    EuclideanGeometry.angle_comm (c C) (c A) (c B)] at hsum
  linarith

private theorem outside_class_eq {s : ℕ}
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam)
    (U : Finset (Fin s)) (p : Fin s) (_hp : p ∉ U)
    (u : Fin s) (_hu : u ∈ U) (hpu : p ≠ u)
    (D : ActualInteriorZeroPartition.Data c lam u)
    (hcross : ∀ v, v ∉ U → v ≠ p → 3 * lam ≤ ∠ (c u) (c p) (c v))
    (v : Fin s) (hv : v ∉ U) (hvu : v ≠ u) :
    D.classOf ⟨v, hvu⟩ = D.classOf ⟨p, hpu⟩ := by
  classical
  by_cases hvp : v = p
  · subst v; rfl
  by_contra hdiff
  have hlarge := D.different_angle ⟨v, hvu⟩ ⟨p, hpu⟩ hdiff
  rw [EuclideanGeometry.angle_comm (c v) (c u) (c p)] at hlarge
  have hsum := actual_triangle_sum hleg p u v hpu
  have hthird := EuclideanGeometry.angle_nonneg (c p) (c v) (c u)
  have hthree := hcross v hv hvp
  linarith [Real.pi_pos]

/-- Only the actual deleted target is required to be zero. -/
private theorem zero_class_companion {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (u : Fin s) (D : ActualInteriorZeroPartition.Data c lam u)
    (q : {i : Fin s // i ≠ u})
    (hzero : rowGain lam (directionRow o e c u) (deleteIndex o e c q u) = 0) :
    ∃ r : {i : Fin s // i ≠ u}, r ≠ q ∧ D.classOf r = D.classOf q := by
  classical
  by_contra hnone
  push_neg at hnone
  have hgain : 1 ≤ rowGain lam (directionRow o e c u) (deleteIndex o e c q u) := by
    apply rowGain_pos_of_forall_angle_ge o e c hleg he q.property.symm hs
    intro j hju hjq
    have hne : D.classOf q ≠ D.classOf ⟨j, hju⟩ := by
      intro h
      exact (hnone ⟨j, hju⟩ (by
        intro heq
        exact hjq (congrArg Subtype.val heq))) h.symm
    have hangle := D.different_angle q ⟨j, hju⟩ hne
    linarith [hleg.lam_pos]
  rw [hzero] at hgain
  omega

private theorem two_noncentral_classes (k : Fin 3) :
    ∃ a b : Fin 3, a ≠ k ∧ b ≠ k ∧ a ≠ b := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

/-- Two witnesses in each of two noncentral classes are actual block points. -/
private theorem class_pair {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (U : Finset (Fin s)) (p u : Fin s) (hpu : p ≠ u)
    (D : ActualInteriorZeroPartition.Data c lam u)
    (houtside : ∀ v (hv : v ∉ U) (hvu : v ≠ u),
      D.classOf ⟨v, hvu⟩ = D.classOf ⟨p, hpu⟩)
    (hzero : ∀ q ∈ U, ∀ i, i ≠ q →
      rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0)
    (k : Fin 3) (hk : k ≠ D.classOf ⟨p, hpu⟩) :
    ∃ a b : Fin s, ∃ hau : a ≠ u, ∃ hbu : b ≠ u,
      a ∈ U ∧ b ∈ U ∧ a ≠ b ∧
        D.classOf ⟨a, hau⟩ = k ∧ D.classOf ⟨b, hbu⟩ = k := by
  classical
  let a := D.witness k
  have ha : D.classOf a = k := D.witness_class k
  have haU : (a : Fin s) ∈ U := by
    by_contra hnot
    exact hk (ha.symm.trans (houtside a hnot a.property))
  obtain ⟨b, hba, hb⟩ := zero_class_companion hs o e he hleg u D a
    (hzero a haU u a.property.symm)
  have hbU : (b : Fin s) ∈ U := by
    by_contra hnot
    exact hk ((hb.trans ha).symm.trans (houtside b hnot b.property))
  have hab : (a : Fin s) ≠ b := by
    intro h
    exact hba (Subtype.ext h.symm)
  exact ⟨a, b, a.property, b.property, haU, hbU, hab, ha, hb.trans ha⟩

/-- A five-point tag row with two doubleton noncentral classes has two
computed Boolean fibers of size two. Self tags are never consumed. -/
private theorem bool_code_of_two_class_pairs
    (tag : Fin 5 → Fin 3) (p : Fin 5) (kp : Fin 3) (hself : tag p = kp)
    (hpairs : ∀ k : Fin 3, k ≠ kp →
      ∃ a b : Fin 5, a ≠ p ∧ b ≠ p ∧ a ≠ b ∧ tag a = k ∧ tag b = k) :
    ∃ code : Fin 5 → Bool,
      (∀ b : Bool, ((Finset.univ.erase p).filter (fun i => code i = b)).card = 2) ∧
      (∀ i j, tag i = tag j → code i = code j) := by
  classical
  obtain ⟨k,l,hkp,hlp,hkl⟩ := two_noncentral_classes kp
  obtain ⟨a,b,hap,hbp,hab,ha,hb⟩ := hpairs k hkp
  obtain ⟨d,f,hdp,hfp,hdf,hd,hf⟩ := hpairs l hlp
  have hcross (x y : Fin 5) (hx : tag x = k) (hy : tag y = l) : x ≠ y := by
    intro h
    exact hkl (hx.symm.trans ((congrArg tag h).trans hy))
  have had := hcross a d ha hd
  have haf := hcross a f ha hf
  have hbd := hcross b d hb hd
  have hbf := hcross b f hb hf
  have hfull : ({p,a,b,d,f} : Finset (Fin 5)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hap, hbp, hdp, hfp, hab, had, haf, hbd, hbf, hdf,
      Ne.symm hap, Ne.symm hbp, Ne.symm hdp, Ne.symm hfp]
  have hall (i : Fin 5) : i = p ∨ i = a ∨ i = b ∨ i = d ∨ i = f := by
    have hm : i ∈ ({p,a,b,d,f} : Finset (Fin 5)) := by rw [hfull]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  let code : Fin 5 → Bool := fun i => decide (tag i = k)
  have htrue : ((Finset.univ.erase p).filter (fun i => code i = true)) = {a,b} := by
    ext i
    rcases hall i with rfl | rfl | rfl | rfl | rfl
    all_goals simp [code, hself, ha, hb, hd, hf, hkp, Ne.symm hkp,
      hkl, Ne.symm hkl, hap, hbp, hdp, hfp, hab, had, haf, hbd, hbf, hdf,
      Ne.symm hap, Ne.symm hbp, Ne.symm hdp, Ne.symm hfp, Ne.symm hab,
      Ne.symm had, Ne.symm haf, Ne.symm hbd, Ne.symm hbf, Ne.symm hdf]
  have hfalse : ((Finset.univ.erase p).filter (fun i => code i = false)) = {d,f} := by
    ext i
    rcases hall i with rfl | rfl | rfl | rfl | rfl
    all_goals simp [code, hself, ha, hb, hd, hf, hkp, Ne.symm hkp,
      hkl, Ne.symm hkl, hap, hbp, hdp, hfp, hab, had, haf, hbd, hbf, hdf,
      Ne.symm hap, Ne.symm hbp, Ne.symm hdp, Ne.symm hfp, Ne.symm hab,
      Ne.symm had, Ne.symm haf, Ne.symm hbd, Ne.symm hbf, Ne.symm hdf]
  refine ⟨code, ?_, ?_⟩
  · intro bit
    cases bit
    · rw [hfalse]; simp [hdf]
    · rw [htrue]; simp [hab]
  · intro i j hij
    simp only [code, hij]

private structure FiveRow (c : Fin 5 → Plane₂) (lam : ℝ) (p : Fin 5) where
  code : Fin 5 → Bool
  card : ∀ b : Bool, ((Finset.univ.erase p).filter (fun i => code i = b)).card = 2
  different : ∀ i j, i ≠ p → j ≠ p → code i ≠ code j →
    2 * lam ≤ ∠ (c i) (c p) (c j)

private theorem five_rows_false {c : Fin 5 → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) (hlo : 2 * Real.pi / 9 < lam)
    (hupper : lam ≤ Real.pi / 4)
    (D : ∀ p, FiveRow c lam p) : False := by
  classical
  let code : Fin 5 → Fin 5 → Bool := fun p => (D p).code
  have hcover (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      code i j = code i k ∨ code j i = code j k ∨ code k i = code k j := by
    by_contra hnot
    push_neg at hnot
    have h1 := (D i).different j k hij.symm hik.symm hnot.1
    have h2 := (D j).different i k hij hjk.symm hnot.2.1
    have h3 := (D k).different i j hik hjk hnot.2.2
    have hsum := actual_triangle_sum hleg i j k hij
    linarith [Real.pi_pos]
  have hsmall (p i j : Fin 5) (hip : i ≠ p) (hjp : j ≠ p)
      (hsame : code p i = code p j) :
      ∠ (c i) (c p) (c j) ≤ Real.pi - 4 * lam := by
    by_cases hij : i = j
    · subst j
      have hR : 0 ≤ Real.pi - 4 * lam := by linarith
      simpa only [EuclideanGeometry.angle_self_of_ne (hleg.inj.ne hip)] using hR
    have htwo := FiveTwoClassPairing.same_forces_other_two_different code
      (fun p b => (D p).card b) hcover p i j hip.symm hjp.symm hij hsame
    have h1 := (D i).different p j hip.symm hij.symm htwo.1
    have h2 := (D j).different p i hjp.symm hij htwo.2
    have hsum := actual_triangle_sum hleg p i j hip.symm
    linarith
  have hhalf : Real.pi - 4 * lam < lam / 2 := by linarith
  have hclumps (p : Fin 5) : SmallTwoClusterGeometry.TwoClusters c lam
      (Real.pi - 4 * lam) p := by
    refine { code := code p, same_angle := hsmall p,
      different_angle := (D p).different, companion := ?_ }
    intro q hqp
    let F := (Finset.univ.erase p).filter (fun i => code p i = code p q)
    have hqF : q ∈ F := by simp [F, hqp]
    have hcard : F.card = 2 := (D p).card (code p q)
    have hex : ∃ r ∈ F, r ≠ q := by
      by_contra hnone
      push_neg at hnone
      have hsub : F ⊆ {q} := by intro r hr; simpa using hnone r hr
      have hle := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hle
      omega
    obtain ⟨r,hr,hrq⟩ := hex
    have hmem := Finset.mem_filter.mp hr
    exact ⟨r, (Finset.mem_erase.mp hmem.1).1, hrq, hmem.2⟩
  let pick : Fin 3 → Fin 5 := fun i => ⟨i, by have := i.isLt; omega⟩
  have hpick : Function.Injective pick := by intro i j h; exact Fin.ext (congrArg Fin.val h)
  exact SmallTwoClusterGeometry.no_three_small_two_clusters hleg hhalf pick hpick
    (fun i => hclumps (pick i))

/-- Original zero-target incoming gains are sufficient. No original
potential or deleted-configuration score is an input to this geometric leaf. -/
theorem card_ge_six_of_original_zero_incoming {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (hupper : lam ≤ Real.pi / 4)
    (U : Finset (Fin s)) (hU : U.Nonempty) (p : Fin s) (hp : p ∉ U)
    (hinterior : ∀ u ∈ U, ¬ IsHullVertex c u)
    (hscore : ∀ u ∈ U, rowScore lam (directionRow o e c u) = 0)
    (hzero : ∀ q ∈ U, ∀ i, i ≠ q →
      rowGain lam (directionRow o e c i) (deleteIndex o e c q i) = 0)
    (hcross : ∀ u ∈ U, ∀ v, v ∉ U → v ≠ p →
      3 * lam ≤ ∠ (c u) (c p) (c v)) : 6 ≤ U.card := by
  classical
  have hdata (u : Fin s) (hu : u ∈ U) :
      ActualInteriorZeroPartition.Data c lam u :=
    ActualInteriorZeroPartition.actualPartition (by omega : 2 ≤ s) o e he hleg hlo
      u (hinterior u hu) (hscore u hu)
  have hpair (u : Fin s) (hu : u ∈ U) :
      let D := hdata u hu
      ∀ k, k ≠ D.classOf ⟨p, by intro h; exact hp (by simpa only [h] using hu)⟩ →
      ∃ a b : Fin s, ∃ hau : a ≠ u, ∃ hbu : b ≠ u,
        a ∈ U ∧ b ∈ U ∧ a ≠ b ∧
          D.classOf ⟨a, hau⟩ = k ∧ D.classOf ⟨b, hbu⟩ = k := by
    intro D k hk
    have hpu : p ≠ u := by intro h; exact hp (by simpa only [h] using hu)
    apply class_pair hs o e he hleg U p u hpu D _ hzero k hk
    intro v hv hvu
    exact outside_class_eq hleg hlo U p hp u hu hpu D (hcross u hu) v hv hvu
  have hcard5 : 5 ≤ U.card := by
    obtain ⟨u,hu⟩ := hU
    let D := hdata u hu
    have hpu : p ≠ u := by intro h; exact hp (by simpa only [h] using hu)
    obtain ⟨k,l,hk,hl,hkl⟩ := two_noncentral_classes (D.classOf ⟨p,hpu⟩)
    obtain ⟨a,b,hau,hbu,ha,hb,hab,hak,hbk⟩ := hpair u hu k hk
    obtain ⟨d,f,hdu,hfu,hd,hf,hdf,hdl,hfl⟩ := hpair u hu l hl
    have hcross (x y : Fin s) (hx : x ≠ u) (hy : y ≠ u)
        (htagx : D.classOf ⟨x,hx⟩ = k) (htagy : D.classOf ⟨y,hy⟩ = l) : x ≠ y := by
      intro h
      subst y
      exact hkl (htagx.symm.trans htagy)
    have had := hcross a d hau hdu hak hdl
    have haf := hcross a f hau hfu hak hfl
    have hbd := hcross b d hbu hdu hbk hdl
    have hbf := hcross b f hbu hfu hbk hfl
    have hsub : ({u,a,b,d,f} : Finset (Fin s)) ⊆ U := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hle := Finset.card_le_card hsub
    have hcount : ({u,a,b,d,f} : Finset (Fin s)).card = 5 := by
      simp [hau, hbu, hdu, hfu, hab, had, haf, hbd, hbf, hdf,
        Ne.symm hau, Ne.symm hbu, Ne.symm hdu, Ne.symm hfu]
    omega
  by_contra hnot
  have hcard : U.card = 5 := by omega
  let E : ↥U ≃ Fin 5 := Fintype.equivFinOfCardEq (by simpa using hcard)
  let pick : Fin 5 → Fin s := fun i => (E.symm i).val
  have hpick : Function.Injective pick := by
    intro i j h
    apply E.symm.injective
    exact Subtype.ext h
  have hmem (i : Fin 5) : pick i ∈ U := (E.symm i).property
  have hex (q : Fin s) (hq : q ∈ U) : ∃ i : Fin 5, pick i = q :=
    ⟨E ⟨q,hq⟩, by simp [pick]⟩
  have hrows (a : Fin 5) : Nonempty (FiveRow (c ∘ pick) lam a) := by
    let u := pick a
    let D := hdata u (hmem a)
    have hpu : p ≠ u := by intro h; exact hp (by simpa only [h] using hmem a)
    let kp := D.classOf ⟨p,hpu⟩
    let tag : Fin 5 → Fin 3 := fun i =>
      if hi : i = a then kp else D.classOf ⟨pick i, hpick.ne hi⟩
    have hself : tag a = kp := by simp [tag]
    have htag (i : Fin 5) (hi : i ≠ a) :
        tag i = D.classOf ⟨pick i, hpick.ne hi⟩ := by simp [tag,hi]
    have hpairs (k : Fin 3) (hk : k ≠ kp) :
        ∃ i j : Fin 5, i ≠ a ∧ j ≠ a ∧ i ≠ j ∧ tag i = k ∧ tag j = k := by
      obtain ⟨q,r,hqu,hru,hq,hr,hqr,hqk,hrk⟩ := hpair u (hmem a) k hk
      obtain ⟨i,hi⟩ := hex q hq
      obtain ⟨j,hj⟩ := hex r hr
      have hia : i ≠ a := by intro h; exact hqu (by simpa [h,u] using hi.symm)
      have hja : j ≠ a := by intro h; exact hru (by simpa [h,u] using hj.symm)
      have hij : i ≠ j := by intro h; exact hqr (hi.symm.trans ((congrArg pick h).trans hj))
      refine ⟨i,j,hia,hja,hij,?_,?_⟩
      · rw [htag i hia]; simpa only [hi] using hqk
      · rw [htag j hja]; simpa only [hj] using hrk
    obtain ⟨code,hcards,hrespect⟩ := bool_code_of_two_class_pairs tag a kp hself hpairs
    refine ⟨{ code := code, card := hcards, different := ?_ }⟩
    intro i j hi hj hdiff
    have htags : tag i ≠ tag j := fun h => hdiff (hrespect i j h)
    rw [htag i hi, htag j hj] at htags
    exact D.different_angle ⟨pick i,hpick.ne hi⟩ ⟨pick j,hpick.ne hj⟩ htags
  let rows : ∀ a, FiveRow (c ∘ pick) lam a := fun a => Classical.choice (hrows a)
  exact five_rows_false (hleg.restrict_injective pick hpick) hlo hupper rows

/-- The original minimal Model internally supplies incoming zero gain
for each original zero target. No restricted Model is constructed. -/
theorem actual_low_four_pure_interior_zero_block_card_ge_six {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} {lam : ℝ}
    (H : ActualMinimalBandCounterexample.Model o e
      (Real.pi / ((4 : ℝ) + 1 / 2)) (Real.pi / 4) 16 (s + 1) c lam)
    (U : Finset (Fin (s + 1))) (hU : U.Nonempty) (p : Fin (s + 1)) (hp : p ∉ U)
    (hinterior : ∀ u ∈ U, ¬ IsHullVertex c u)
    (hscore : ∀ u ∈ U, rowScore lam (directionRow o e c u) = 0)
    (hcross : ∀ u ∈ U, ∀ v, v ∉ U → v ≠ p →
      3 * lam ≤ ∠ (c u) (c p) (c v)) : 6 ≤ U.card := by
  have hlo : 2 * Real.pi / 9 < lam := by
    have hrho : Real.pi / ((4 : ℝ) + 1 / 2) = 2 * Real.pi / 9 := by ring
    simpa only [hrho] using H.scale_lower
  apply card_ge_six_of_original_zero_incoming (by omega : 3 ≤ s + 1)
    o e he H.legality hlo H.scale_upper U hU p hp hinterior hscore _ hcross
  intro q hq i hi
  have hmin (j : Fin (s + 1)) :
      rowScore lam (directionRow o e c q) ≤ rowScore lam (directionRow o e c j) := by
    rw [hscore q hq]
    exact Nat.zero_le _
  have hdiv : 2 ^ rowScore lam (directionRow o e c q) ∣ 16 := by simp [hscore q hq]
  exact (ActualMinimalBandCounterexample.actual_minimum_score_critical_form
    hs o e H q hmin hdiv).2.2.1 i hi

#print axioms card_ge_six_of_original_zero_incoming
#print axioms actual_low_four_pure_interior_zero_block_card_ge_six

end Jsp404.ActualPureInteriorZeroBlock
