import Jsp000404.Section4Legality
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Actual finite two-point expansion.  Each selected centre is replaced by its
original point and a nearby point on a supplied admissible axis.  The new
configuration satisfies the original geometric legality contract at every
strictly smaller positive angle parameter.
-/


open scoped EuclideanGeometry BigOperators


namespace Jsp404.ActualPairExpansion.Reindex

/-- The number of parent indices replaced by pairs. -/
def countPairs {s : ℕ} (P : Fin s → Bool) : ℕ :=
  (Finset.univ.filter (fun i => P i = true)).card

/-- One index for an unexpanded parent, and two indices for an expanded parent. -/
abbrev Index {s : ℕ} (P : Fin s → Bool) :=
  Σ i : Fin s, Fin (if P i then 2 else 1)

theorem card_index {s : ℕ} (P : Fin s → Bool) :
    Fintype.card (Index P) = s + countPairs P := by
  classical
  simp only [Index, Fintype.card_sigma, Fintype.card_fin]
  calc
    (∑ i : Fin s, if P i then 2 else 1) =
        ∑ i : Fin s, (1 + if P i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      cases P i <;> simp
    _ = s + countPairs P := by
      rw [Finset.sum_add_distrib]
      simp [countPairs, Finset.sum_boole]

/-- A finite enumeration of all children, including the surviving singletons. -/
noncomputable def indexEquivFin {s : ℕ} (P : Fin s → Bool) :
    Index P ≃ Fin (s + countPairs P) :=
  Fintype.equivFinOfCardEq (card_index P)

/-- Reindex a generic function onto a prescribed `Fin` enumeration. -/
def transport {α β : Type*} {n : ℕ} (e : α ≃ Fin n) (c : α → β) : Fin n → β :=
  c ∘ e.symm

@[simp] theorem transport_apply {α β : Type*} {n : ℕ}
    (e : α ≃ Fin n) (c : α → β) (i : Fin n) :
    transport e c i = c (e.symm i) := rfl

@[simp] theorem transport_equiv_apply {α β : Type*} {n : ℕ}
    (e : α ≃ Fin n) (c : α → β) (i : α) :
    transport e c (e i) = c i := by
  simp [transport]

theorem transport_injective {α β : Type*} {n : ℕ}
    (e : α ≃ Fin n) {c : α → β} (hc : Function.Injective c) :
    Function.Injective (transport e c) :=
  hc.comp e.symm.injective

/-- Generic injectivity and the generic triangle bound become the existing
`Fin`-indexed Section-4 legality contract after enumeration. -/
theorem transport_legality {α : Type*} {n : ℕ}
    (e : α ≃ Fin n) {c : α → Plane₂} {lam : ℝ}
    (hlam : 0 < lam) (hc : Function.Injective c)
    (htri : ∀ i j k : α, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ Real.pi - lam) :
    Section4Legality (transport e c) lam where
  lam_pos := hlam
  inj := transport_injective e hc
  triAngle := by
    intro i j k hij hjk hik
    exact htri (e.symm i) (e.symm j) (e.symm k)
      (fun h => hij (e.symm.injective h))
      (fun h => hjk (e.symm.injective h))
      (fun h => hik (e.symm.injective h))

/-- The child configuration indexed by `Fin (s + countPairs P)`. -/
noncomputable def expandedCenters {s : ℕ} (P : Fin s → Bool)
    (c : Index P → Plane₂) : Fin (s + countPairs P) → Plane₂ :=
  transport (indexEquivFin P) c

theorem expandedCenters_injective {s : ℕ} (P : Fin s → Bool)
    {c : Index P → Plane₂} (hc : Function.Injective c) :
    Function.Injective (expandedCenters P c) :=
  transport_injective (indexEquivFin P) hc

theorem expandedCenters_legality {s : ℕ} (P : Fin s → Bool)
    {c : Index P → Plane₂} {lam : ℝ}
    (hlam : 0 < lam) (hc : Function.Injective c)
    (htri : ∀ i j k : Index P, i ≠ j → j ≠ k → i ≠ k →
      ∠ (c i) (c j) (c k) ≤ Real.pi - lam) :
    Section4Legality (expandedCenters P c) lam :=
  transport_legality (indexEquivFin P) hlam hc htri

end Jsp404.ActualPairExpansion.Reindex


namespace Jsp404.ActualPairExpansion

open Filter Topology
open scoped EuclideanGeometry

abbrev Copy {s : ℕ} (P : Fin s → Bool) := Σ i : Fin s, Fin (if P i then 2 else 1)

noncomputable def point {s : ℕ} {P : Fin s → Bool} (c u : Fin s → Plane₂)
    (eps : ℝ) (x : Copy P) : Plane₂ :=
  c x.1 + eps • ((x.2.val : ℝ) • u x.1)

@[simp] theorem point_zero {s : ℕ} {P : Fin s → Bool} (c u : Fin s → Plane₂)
    (x : Copy P) : point c u 0 x = c x.1 := by simp [point]

@[fun_prop] theorem continuous_point {s : ℕ} {P : Fin s → Bool} (c u : Fin s → Plane₂)
    (x : Copy P) : Continuous (fun eps => point c u eps x) := by
  unfold point
  fun_prop

/-- Axis assumptions concern original centre rays, not the expanded points. -/
structure Axes {s : ℕ} (c : Fin s → Plane₂) (P : Fin s → Bool)
    (u : Fin s → Plane₂) (lam : ℝ) : Prop where
  nonzero : ∀ i, P i = true → u i ≠ 0
  bounds : ∀ i, P i = true → ∀ j, j ≠ i →
    InnerProductGeometry.angle (u i) (c j - c i) ≤ Real.pi - lam ∧
    InnerProductGeometry.angle (-u i) (c j - c i) ≤ Real.pi - lam

private theorem continuous_angle_eventually_lt (f g : ℝ → Plane₂)
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (hf0 : f 0 ≠ 0) (hg0 : g 0 ≠ 0) (cap : ℝ)
    (hcap : InnerProductGeometry.angle (f 0) (g 0) < cap) :
    ∀ᶠ eps in 𝓝 (0 : ℝ), InnerProductGeometry.angle (f eps) (g eps) < cap := by
  have hc : ContinuousAt (fun eps => InnerProductGeometry.angle (f eps) (g eps)) 0 :=
    ContinuousAt.comp₂ (g := f) (h := g) (x := (0 : ℝ))
      (InnerProductGeometry.continuousAt_angle (x := (f 0, g 0)) hf0 hg0) hf hg
  exact hc.eventually_lt continuousAt_const hcap

private theorem same_copy_data {s : ℕ} {P : Fin s → Bool}
    (x y : Copy P) (hxy : x ≠ y) (hb : x.1 = y.1) :
    P x.1 = true ∧ (x.2.val : ℝ) ≠ (y.2.val : ℝ) := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  dsimp at hb
  subst j
  have hab : a ≠ b := by
    intro h
    exact hxy (by cases h; rfl)
  have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
  constructor
  · by_contra hp
    have hp' : P i = false := Bool.eq_false_iff.mpr hp
    have ha := a.isLt
    have hb := b.isLt
    simp only [hp', Bool.false_eq_true, ↓reduceIte] at ha hb
    exact hval (by omega)
  · exact_mod_cast hval

private theorem same_difference {s : ℕ} {P : Fin s → Bool} (c u : Fin s → Plane₂)
    (x y : Copy P) (hb : x.1 = y.1) (eps : ℝ) :
    point c u eps x - point c u eps y =
      eps • (((x.2.val : ℝ) - (y.2.val : ℝ)) • u x.1) := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  dsimp at hb
  subst j
  unfold point
  dsimp
  module

private theorem eventually_ne {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam : ℝ} (hleg : Section4Legality c lam)
    (axes : Axes c P u lam) (x y : Copy P) (hxy : x ≠ y) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ), point c u eps x ≠ point c u eps y := by
  by_cases hb : x.1 = y.1
  · obtain ⟨hP, hval⟩ := same_copy_data x y hxy hb
    have hu := axes.nonzero x.1 hP
    have hd : ((x.2.val : ℝ) - (y.2.val : ℝ)) • u x.1 ≠ 0 :=
      smul_ne_zero (sub_ne_zero.mpr hval) hu
    filter_upwards [self_mem_nhdsWithin] with eps heps
    have he : (eps : ℝ) ≠ 0 := ne_of_gt heps
    apply sub_ne_zero.mp
    rw [same_difference c u x y hb]
    exact smul_ne_zero he hd
  · have hd : c x.1 - c y.1 ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hb)
    have hc : ContinuousAt (fun eps => point c u eps x - point c u eps y) 0 := by
      fun_prop
    have hh := hc.eventually_ne (by simpa using hd)
    exact (hh.filter_mono nhdsWithin_le_nhds).mono fun _ h => sub_ne_zero.mp h

private theorem axis_multiple_bound {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam : ℝ} (axes : Axes c P u lam)
    (i j : Fin s) (hP : P i = true) (hji : j ≠ i) {a : ℝ} (ha : a ≠ 0) :
    InnerProductGeometry.angle (a • u i) (c j - c i) ≤ Real.pi - lam := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [InnerProductGeometry.angle_smul_left_of_neg _ _ ha]
    exact (axes.bounds i hP j hji).2
  · rw [InnerProductGeometry.angle_smul_left_of_pos _ _ ha]
    exact (axes.bounds i hP j hji).1

private theorem eventually_angle_same_left {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hleg : Section4Legality c lam)
    (axes : Axes c P u lam) (hlam' : lam' < lam)
    (x y z : Copy P) (hxy : x ≠ y) (hb : x.1 = y.1) (hzc : z.1 ≠ y.1) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      ∠ (point c u eps x) (point c u eps y) (point c u eps z) ≤ Real.pi - lam' := by
  obtain ⟨hP, hval⟩ := same_copy_data x y hxy hb
  let v : Plane₂ := ((x.2.val : ℝ) - (y.2.val : ℝ)) • u x.1
  have hv : v ≠ 0 := smul_ne_zero (sub_ne_zero.mpr hval) (axes.nonzero x.1 hP)
  have hzi : z.1 ≠ x.1 := by simpa only [hb] using hzc
  have hbound := axis_multiple_bound c u axes x.1 z.1 hP hzi (sub_ne_zero.mpr hval)
  have hz0 : c z.1 - c y.1 ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hzc)
  have hf : ContinuousAt (fun eps => point c u eps z - point c u eps y) 0 := by fun_prop
  have he := continuous_angle_eventually_lt (fun _ => v)
    (fun eps => point c u eps z - point c u eps y) continuousAt_const hf hv
    (by simpa using hz0) (Real.pi - lam') (by simpa [v, hb] using (by linarith :
      InnerProductGeometry.angle v (c z.1 - c x.1) < Real.pi - lam'))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with eps ha heps
  change InnerProductGeometry.angle
    (point c u eps x - point c u eps y) (point c u eps z - point c u eps y) ≤ _
  rw [same_difference c u x y hb, InnerProductGeometry.angle_smul_left_of_pos _ _ heps]
  exact ha.le

private theorem triple_same_impossible {s : ℕ} {P : Fin s → Bool}
    (x y z : Copy P) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hbxy : x.1 = y.1) (hbyz : y.1 = z.1) : False := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  rcases z with ⟨k, d⟩
  dsimp at hbxy hbyz
  subst j
  subst k
  have hab : a.val ≠ b.val := by
    intro h
    apply hxy
    exact congrArg (Sigma.mk i) (Fin.ext h)
  have hbd : b.val ≠ d.val := by
    intro h
    apply hyz
    exact congrArg (Sigma.mk i) (Fin.ext h)
  have had : a.val ≠ d.val := by
    intro h
    apply hxz
    exact congrArg (Sigma.mk i) (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  have hd := d.isLt
  cases hp : P i <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at ha hb hd <;> omega

private theorem lam_le_pi {s : ℕ} {c : Fin s → Plane₂} {lam : ℝ}
    (hs : 3 ≤ s) (hleg : Section4Legality c lam) : lam ≤ Real.pi := by
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  let k : Fin s := ⟨2, by omega⟩
  have ht := hleg.triAngle i j k (by simp [i, j]) (by simp [j, k]) (by simp [i, k])
  change InnerProductGeometry.angle (c i - c j) (c k - c j) ≤ _ at ht
  have hn := InnerProductGeometry.angle_nonneg (c i - c j) (c k - c j)
  linarith

private theorem eventually_angle_same_ends {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hs : 3 ≤ s)
    (hleg : Section4Legality c lam) (hlam' : lam' < lam)
    (x y z : Copy P) (hb : x.1 = z.1) (hxy : x.1 ≠ y.1) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      ∠ (point c u eps x) (point c u eps y) (point c u eps z) ≤ Real.pi - lam' := by
  have hx0 : c x.1 - c y.1 ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hxy)
  have hz0 : c z.1 - c y.1 ≠ 0 := by simpa only [← hb] using hx0
  have hf : ContinuousAt (fun eps => point c u eps x - point c u eps y) 0 := by fun_prop
  have hg : ContinuousAt (fun eps => point c u eps z - point c u eps y) 0 := by fun_prop
  have hself : InnerProductGeometry.angle (c x.1 - c y.1) (c z.1 - c y.1) = 0 := by
    rw [← hb]
    exact InnerProductGeometry.angle_self hx0
  have hcap : 0 < Real.pi - lam' := by linarith [lam_le_pi hs hleg]
  have he := continuous_angle_eventually_lt (fun eps => point c u eps x - point c u eps y)
    (fun eps => point c u eps z - point c u eps y) hf hg
    (by simpa using hx0) (by simpa using hz0) (Real.pi - lam')
    (by simpa only [point_zero, hself] using hcap)
  exact (he.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le

private theorem eventually_angle_distinct_bases {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hleg : Section4Legality c lam)
    (hlam' : lam' < lam) (x y z : Copy P)
    (hxy : x.1 ≠ y.1) (hyz : y.1 ≠ z.1) (hxz : x.1 ≠ z.1) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      ∠ (point c u eps x) (point c u eps y) (point c u eps z) ≤ Real.pi - lam' := by
  have hx0 : c x.1 - c y.1 ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hxy)
  have hz0 : c z.1 - c y.1 ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hyz.symm)
  have hf : ContinuousAt (fun eps => point c u eps x - point c u eps y) 0 := by fun_prop
  have hg : ContinuousAt (fun eps => point c u eps z - point c u eps y) 0 := by fun_prop
  have hbound := hleg.triAngle x.1 y.1 z.1 hxy hyz hxz
  change InnerProductGeometry.angle (c x.1 - c y.1) (c z.1 - c y.1) ≤ _ at hbound
  have he := continuous_angle_eventually_lt (fun eps => point c u eps x - point c u eps y)
    (fun eps => point c u eps z - point c u eps y) hf hg
    (by simpa using hx0) (by simpa using hz0) (Real.pi - lam') (by simpa using
      (by linarith : InnerProductGeometry.angle (c x.1 - c y.1) (c z.1 - c y.1) < Real.pi - lam'))
  exact (he.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le

private theorem eventually_triangle {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hs : 3 ≤ s)
    (hleg : Section4Legality c lam) (axes : Axes c P u lam) (hlam' : lam' < lam)
    (x y z : Copy P) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      ∠ (point c u eps x) (point c u eps y) (point c u eps z) ≤ Real.pi - lam' := by
  by_cases hbxy : x.1 = y.1
  · by_cases hbyz : y.1 = z.1
    · exact False.elim (triple_same_impossible x y z hxy hyz hxz hbxy hbyz)
    · exact eventually_angle_same_left c u hleg axes hlam' x y z hxy hbxy (Ne.symm hbyz)
  · by_cases hbyz : y.1 = z.1
    · have he := eventually_angle_same_left c u hleg axes hlam' z y x hyz.symm hbyz.symm hbxy
      exact he.mono fun _ h => by simpa only [EuclideanGeometry.angle_comm] using h
    · by_cases hbxz : x.1 = z.1
      · exact eventually_angle_same_ends c u hs hleg hlam' x y z hbxz hbxy
      · exact eventually_angle_distinct_bases c u hleg hlam' x y z hbxy hbyz hbxz

/-- A single sufficiently small positive scale simultaneously gives
injectivity and every actual expanded triangle bound. -/
theorem eventually_expansion {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hs : 3 ≤ s)
    (hleg : Section4Legality c lam) (axes : Axes c P u lam) (hlam' : lam' < lam) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      Function.Injective (point c u eps : Copy P → Plane₂) ∧
      ∀ x y z : Copy P, x ≠ y → y ≠ z → x ≠ z →
        ∠ (point c u eps x) (point c u eps y) (point c u eps z) ≤ Real.pi - lam' := by
  have hpairs : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ x y : Copy P,
      x ≠ y → point c u eps x ≠ point c u eps y := by
    apply eventually_all.mpr
    intro x
    apply eventually_all.mpr
    intro y
    by_cases hxy : x = y
    · exact Eventually.of_forall fun _ h => False.elim (h hxy)
    · exact (eventually_ne c u hleg axes x y hxy).mono fun _ h _ => h
  have htri : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ x y z : Copy P,
      x ≠ y → y ≠ z → x ≠ z →
        ∠ (point c u eps x) (point c u eps y) (point c u eps z) ≤ Real.pi - lam' := by
    apply eventually_all.mpr
    intro x
    apply eventually_all.mpr
    intro y
    apply eventually_all.mpr
    intro z
    by_cases hxy : x = y
    · exact Eventually.of_forall fun _ h => False.elim (h hxy)
    by_cases hyz : y = z
    · exact Eventually.of_forall fun _ _ h => False.elim (h hyz)
    by_cases hxz : x = z
    · exact Eventually.of_forall fun _ _ _ h => False.elim (h hxz)
    · exact (eventually_triangle c u hs hleg axes hlam' x y z hxy hyz hxz).mono
        fun _ h _ _ _ => h
  filter_upwards [hpairs, htri] with eps hp ht
  refine ⟨?_, ht⟩
  intro x y h
  by_contra hxy
  exact hp x y hxy h

/-- Reindexing preserves the actual perturbation's legality for every
sufficiently small positive scale. -/
theorem expansion_eventually_legality {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hs : 3 ≤ s)
    (hleg : Section4Legality c lam) (axes : Axes c P u lam)
    (hlam' : 0 < lam') (hsmall : lam' < lam) :
    ∀ᶠ eps in 𝓝[>] (0 : ℝ),
      Section4Legality (Reindex.expandedCenters P (point c u eps)) lam' := by
  exact (eventually_expansion c u hs hleg axes hsmall).mono fun _ h =>
    Reindex.expandedCenters_legality P hlam' h.1 h.2

/-- There exists a concrete positive scale, not just an abstract limiting
configuration, at which the expanded actual centres are legal. -/
theorem exists_expansion_scale {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hs : 3 ≤ s)
    (hleg : Section4Legality c lam) (axes : Axes c P u lam)
    (hlam' : 0 < lam') (hsmall : lam' < lam) :
    ∃ eps : ℝ, 0 < eps ∧
      Section4Legality (Reindex.expandedCenters P (point c u eps)) lam' := by
  have he := expansion_eventually_legality c u hs hleg axes hlam' hsmall
  have hpos : ∀ᶠ eps in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
  exact (hpos.and he).exists

/-- Actual pair expansion on exactly `s + #P` distinct centres. -/
theorem exists_pair_expansion {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) {lam lam' : ℝ} (hs : 3 ≤ s)
    (hleg : Section4Legality c lam) (axes : Axes c P u lam)
    (hlam' : 0 < lam') (hsmall : lam' < lam) :
    ∃ c' : Fin (s + Reindex.countPairs P) → Plane₂, Section4Legality c' lam' := by
  obtain ⟨eps, _, hnew⟩ := exists_expansion_scale c u hs hleg axes hlam' hsmall
  exact ⟨Reindex.expandedCenters P (point c u eps), hnew⟩

/-- The expansion also accepts independently supplied original-ray axes.
The finite choice of axes is made here, before constructing actual points. -/
theorem exists_pair_expansion_of_axes {s : ℕ} {P : Fin s → Bool}
    (c : Fin s → Plane₂) {lam lam' : ℝ} (hs : 3 ≤ s)
    (hleg : Section4Legality c lam)
    (haxes : ∀ i, P i = true → ∃ u : Plane₂, u ≠ 0 ∧ ∀ j, j ≠ i →
      InnerProductGeometry.angle u (c j - c i) ≤ Real.pi - lam ∧
      InnerProductGeometry.angle (-u) (c j - c i) ≤ Real.pi - lam)
    (hlam' : 0 < lam') (hsmall : lam' < lam) :
    ∃ c' : Fin (s + Reindex.countPairs P) → Plane₂, Section4Legality c' lam' := by
  classical
  have hchoose : ∀ i : Fin s, ∃ u : Plane₂, P i = true → u ≠ 0 ∧ ∀ j, j ≠ i →
      InnerProductGeometry.angle u (c j - c i) ≤ Real.pi - lam ∧
      InnerProductGeometry.angle (-u) (c j - c i) ≤ Real.pi - lam := by
    intro i
    by_cases hp : P i = true
    · obtain ⟨u, hu, hb⟩ := haxes i hp
      exact ⟨u, fun _ => ⟨hu, hb⟩⟩
    · exact ⟨0, fun h => False.elim (hp h)⟩
  choose u hu using hchoose
  have axes : Axes c P u lam := ⟨fun i hp => (hu i hp).1, fun i hp => (hu i hp).2⟩
  exact exists_pair_expansion c u hs hleg axes hlam' hsmall

#print axioms Reindex.card_index
#print axioms eventually_expansion
#print axioms expansion_eventually_legality
#print axioms exists_expansion_scale
#print axioms exists_pair_expansion
#print axioms exists_pair_expansion_of_axes

end Jsp404.ActualPairExpansion
