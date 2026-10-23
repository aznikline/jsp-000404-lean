import Jsp000404.Integration
import Mathlib.Analysis.Convex.Radon

/-!
# The first strip of the geometric capacity theorem

The deletion induction starts at n = 2. For n = 1, every exponent is
zero, so we need cardinality bounds: two centers in the low regime and
three in the high regime. The high case is the classical fact that four
plane points cannot have all their angles acute. We use Radon's theorem:
an acute set is in convex position, and a two-versus-two Radon partition
contradicts an inner-product identity.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Jsp404

private lemma positive_average {t u a b : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hs : t + u = 1) (ha : 0 < a) (hb : 0 < b) : 0 < t * a + u * b := by
  by_cases h : t = 0
  · have : u = 1 := by linarith
    simp [h, this, hb]
  · have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    exact add_pos_of_pos_of_nonneg (mul_pos ht' ha) (mul_nonneg hu hb.le)

private lemma segments_force_nonacute (A B C D : Plane₂)
    {t u v w : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (htu : t + u = 1) (hvw : v + w = 1)
    (hjoin : t • A + u • B = v • C + w • D)
    (hA : 0 < ⟪C - A, D - A⟫) (hB : 0 < ⟪C - B, D - B⟫)
    (hC : 0 < ⟪A - C, B - C⟫) (hD : 0 < ⟪A - D, B - D⟫) : False := by
  have hleft := positive_average ht hu htu hA hB
  have hright := positive_average hv hw hvw hC hD
  have heq := congrArg (fun x : Plane₂ => ⟪A + B - C - D, x⟫) hjoin
  have hu' : u = 1 - t := by linarith
  have hw' : w = 1 - v := by linarith
  simp only [hu', hw', inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_right] at heq hleft hright
  simp only [real_inner_comm B A, real_inner_comm C A, real_inner_comm D A,
    real_inner_comm C B, real_inner_comm D B, real_inner_comm D C]
    at heq hleft hright
  nlinarith

/-- An acute configuration puts each point strictly outside the convex hull
of every collection of other points. -/
lemma acute_outside_convexHull {ι : Type*} (p : ι → Plane₂)
    (hp : Function.Injective p)
    (hacute : ∀ i j k, i ≠ j → k ≠ j → i ≠ k →
      0 < ⟪p i - p j, p k - p j⟫)
    {i : ι} {S : Set ι} (hi : i ∉ S) : p i ∉ convexHull ℝ (p '' S) := by
  intro h
  obtain ⟨j, hj⟩ := Set.image_nonempty.mp
    (convexHull_nonempty_iff.mp ⟨p i, h⟩)
  have hji : j ≠ i := fun he => hi (he ▸ hj)
  let f : Plane₂ → ℝ := fun x => ⟪p j - p i, x⟫
  have hconv : Convex ℝ {x | f (p i) < f x} :=
    convex_halfSpace_gt
      (show IsLinearMap ℝ f from
        ⟨fun x y => inner_add_right _ x y,
          fun r x => real_inner_smul_right _ x r⟩) _
  have hpoints : p '' S ⊆ {x | f (p i) < f x} := by
    rintro x ⟨k, hk, rfl⟩
    have hki : k ≠ i := fun he => hi (he ▸ hk)
    have hpos : 0 < ⟪p j - p i, p k - p i⟫ := by
      by_cases hjk : j = k
      · subst k
        exact real_inner_self_pos.mpr (sub_ne_zero.mpr (fun he => hji (hp he)))
      · exact hacute j i k hji hki hjk
    simpa only [Set.mem_ofPred_eq, f, inner_sub_right, sub_pos] using hpos
  exact (lt_irrefl (f (p i))) ((convexHull_min hpoints hconv) h)

/-- Four distinct plane points determine an angle of at least pi/2. -/
theorem four_points_nonacute (p : Fin 4 → Plane₂) (hp : Function.Injective p) :
    ∃ i j k, i ≠ j ∧ k ≠ j ∧ i ≠ k ∧ Real.pi / 2 ≤ ∠ (p i) (p j) (p k) := by
  classical
  by_contra h
  push Not at h
  have ha : ∀ i j k, i ≠ j → k ≠ j → i ≠ k →
      0 < ⟪p i - p j, p k - p j⟫ := by
    intro i j k hij hkj hik
    apply lt_of_not_ge
    intro hinner
    exact (not_le_of_gt (h i j k hij hkj hik))
      (InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mp hinner)
  have hdep : ¬ AffineIndependent ℝ p := by
    intro hind
    have hc := hind.card_le_finrank_succ
    have hd := Submodule.finrank_le (vectorSpan ℝ (Set.range p))
    have he : Module.finrank ℝ Plane₂ = 2 := by simp
    rw [he] at hd
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨S, z, hzS, hzC⟩ := Convex.radon_partition hdep
  have hcard (T : Set (Fin 4)) (hzT : z ∈ convexHull ℝ (p '' T))
      (hzTc : z ∈ convexHull ℝ (p '' Tᶜ)) : 2 ≤ T.toFinset.card := by
    by_contra hsmall
    have hle : T.toFinset.card ≤ 1 := by omega
    obtain ⟨i, hi⟩ := Set.image_nonempty.mp
      (convexHull_nonempty_iff.mp ⟨z, hzT⟩)
    have hsub : p '' T ⊆ {p i} := by
      rintro x ⟨j, hj, rfl⟩
      have he := Finset.card_le_one.mp hle j (by simpa using hj)
        i (by simpa using hi)
      simp [he]
    have hzi : z = p i := (convexHull_min hsub (convex_singleton _)) hzT
    rw [hzi] at hzTc
    exact acute_outside_convexHull p hp ha (by simpa) hzTc
  have hs := hcard S hzS hzC
  have hc := hcard Sᶜ hzC (by simpa using hzS)
  rw [Set.toFinset_compl, Finset.card_compl] at hc
  simp only [Fintype.card_fin] at hc
  have hs2 : S.toFinset.card = 2 := by omega
  have hc2 : Sᶜ.toFinset.card = 2 := by
    rw [Set.toFinset_compl, Finset.card_compl, hs2]
    decide
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hs2
  obtain ⟨c, d, hcd, hscd⟩ := Finset.card_eq_two.mp hc2
  have hsab' : S = {a, b} := by
    simpa using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) hsab
  have hscd' : Sᶜ = {c, d} := by
    simpa using congrArg (fun t : Finset (Fin 4) => (t : Set (Fin 4))) hscd
  have hne : ∀ i ∈ S, ∀ j ∈ Sᶜ, i ≠ j := by
    intro i hi j hj he
    exact hj (he ▸ hi)
  have hac := hne a (by simp [hsab']) c (by simp [hscd'])
  have had := hne a (by simp [hsab']) d (by simp [hscd'])
  have hbc := hne b (by simp [hsab']) c (by simp [hscd'])
  have hbd := hne b (by simp [hsab']) d (by simp [hscd'])
  rw [hsab', Set.image_pair, convexHull_pair] at hzS
  rw [hscd', Set.image_pair, convexHull_pair] at hzC
  obtain ⟨t, u, ht, hu, htu, heq₁⟩ := hzS
  obtain ⟨v, w, hv, hw, hvw, heq₂⟩ := hzC
  exact segments_force_nonacute (p a) (p b) (p c) (p d)
    ht hu hv hw htu hvw (heq₁.trans heq₂.symm)
    (ha c a d hac.symm had.symm hcd) (ha c b d hbc.symm hbd.symm hcd)
    (ha a c b hac hbc hab) (ha a d b had hbd hab)

/-- The triangle sum rules out three centers when every angle is < pi/3. -/
theorem Section4Legality.card_le_two {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (h : Section4Legality c lam) (hlam : 2 * Real.pi < 3 * lam) : s ≤ 2 := by
  by_contra hs
  have hs3 : 3 ≤ s := by omega
  let f : Fin 3 → Fin s := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hs3⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (congrArg (fun x : Fin s => x.val) he)
  have ht (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :=
    h.triAngle (f i) (f j) (f k)
      (fun he => hij (hf he)) (fun he => hjk (hf he)) (fun he => hik (hf he))
  have hp : c (f 0) ≠ c (f 1) := fun he =>
    (by decide : (0 : Fin 3) ≠ 1) (hf (h.inj he))
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c (f 2)) hp
  have h₀ := ht 1 0 2 (by decide) (by decide) (by decide)
  have h₁ := ht 0 2 1 (by decide) (by decide) (by decide)
  have h₂ := ht 2 1 0 (by decide) (by decide) (by decide)
  linarith

/-- A strict acute-angle bound allows at most three planar centers. -/
theorem Section4Legality.card_le_three {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (h : Section4Legality c lam) (hlam : Real.pi < 2 * lam) : s ≤ 3 := by
  by_contra hs
  have hs4 : 4 ≤ s := by omega
  let f : Fin 4 → Fin s := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hs4⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (congrArg (fun x : Fin s => x.val) he)
  obtain ⟨i, j, k, hij, hkj, hik, ha⟩ :=
    four_points_nonacute (c ∘ f) (h.inj.comp hf)
  have hb := h.triAngle (f i) (f j) (f k)
    (fun he => hij (hf he)) (fun he => hkj (hf he.symm))
    (fun he => hik (hf he))
  change Real.pi / 2 ≤ ∠ (c (f i)) (c (f j)) (c (f k)) at ha
  linarith

lemma first_strip_weight_eq_length (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 1)
    (hfN : V.forest.Nodup) :
    ((exponents V o e lam).map (2 ^ ·)).sum = V.forest.length := by
  have ht := exponents_lt_of_floor V o e hlam hn (by omega) hfN
  have hz : ∀ k ∈ exponents V o e lam, k = 0 := fun k hk => by
    have := ht k hk
    omega
  have hlist (ks : List ℕ) (hk : ∀ k ∈ ks, k = 0) :
      (ks.map (2 ^ ·)).sum = ks.length := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      have h₀ : k = 0 := hk k (by simp)
      have hrest : ∀ j ∈ ks, j = 0 := fun j hj => hk j (by simp [hj])
      simp [h₀, ih hrest, Nat.add_comm]
  rw [hlist _ hz]
  simp [exponents]

/-- The low first-strip capacity, with no selection or certificate assumption. -/
theorem first_strip_capacity_low (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) {lam : ℝ}
    (hlegal : Section4Legality
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam)
    (hfN : V.forest.Nodup) (hn : Nat.floor (Real.pi / lam) = 1)
    (hδ : Real.pi / lam - 1 < 1 / 2) :
    ((exponents V o e lam).map (2 ^ ·)).sum ≤ 2 := by
  rw [first_strip_weight_eq_length V o e hlegal.lam_pos hn hfN]
  apply hlegal.card_le_two
  have hq : Real.pi < (3 / 2 : ℝ) * lam :=
    (div_lt_iff₀ hlegal.lam_pos).mp (by linarith)
  linarith

/-- The high first-strip capacity, with no selection or certificate assumption. -/
theorem first_strip_capacity_high (V : GCfg)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) {lam : ℝ}
    (hlegal : Section4Legality
      (fun i : Fin V.forest.length => (V.forest.get i).centerOf) lam)
    (hfN : V.forest.Nodup) (hn : Nat.floor (Real.pi / lam) = 1) :
    ((exponents V o e lam).map (2 ^ ·)).sum ≤ 3 := by
  rw [first_strip_weight_eq_length V o e hlegal.lam_pos hn hfN]
  apply hlegal.card_le_three
  have hq := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn] at hq
  have hq' : Real.pi / lam < 2 := by norm_num at hq ⊢; exact hq
  exact (div_lt_iff₀ hlegal.lam_pos).mp hq'

/-- The four-point endpoint, directly in the project's configuration type. -/
theorem sendov_lower_four (C : PtCfg) (hlen : C.pts.length = 4) :
    ∃ p q r : Plane₂, p ∈ C.pts ∧ q ∈ C.pts ∧ r ∈ C.pts ∧
      p ≠ q ∧ r ≠ q ∧ p ≠ r ∧ alphaN 4 ≤ ∠ p q r := by
  let p : Fin 4 → Plane₂ := fun i => C.pts.get ⟨i.val, by omega⟩
  have hp : Function.Injective p := by
    intro i j he
    have hget := C.nodup.get_inj_iff.mp he
    exact Fin.ext (congrArg (fun x : Fin C.pts.length => x.val) hget)
  obtain ⟨i, j, k, hij, hkj, hik, ha⟩ := four_points_nonacute p hp
  refine ⟨p i, p j, p k, List.get_mem _ _, List.get_mem _ _, List.get_mem _ _,
    (fun he => hij (hp he)), (fun he => hkj (hp he)),
    (fun he => hik (hp he)), ?_⟩
  have hvalue : alphaN 4 = Real.pi / 2 := by norm_num [alphaN, Nat.clog]; ring
  rwa [hvalue]

#print axioms four_points_nonacute
#print axioms first_strip_capacity_low
#print axioms first_strip_capacity_high
#print axioms sendov_lower_four

end Jsp404
