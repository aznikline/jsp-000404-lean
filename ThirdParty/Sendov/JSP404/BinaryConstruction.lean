import JSP404.HierarchicalConstruction
import Mathlib.Tactic

/-!
# A multiscale binary construction

Each binary word is projected into the plane as a sum of successively smaller
direction vectors. The first differing digit controls each limiting direction.
-/

noncomputable section

open Filter Topology

namespace JSP404

abbrev BinaryWord (n : ℕ) := Fin n → Bool

def realDigit (b : Bool) : ℝ := if b then 1 else 0

theorem realDigit_injective : Function.Injective realDigit := by
  intro a b h
  cases a <;> cases b <;> norm_num [realDigit] at *

theorem realDigit_sub_ne_zero {a b : Bool} (h : a ≠ b) : realDigit a - realDigit b ≠ 0 := by
  exact sub_ne_zero.mpr (realDigit_injective.ne h)

theorem realDigit_sub_eq_sign {a b : Bool} (h : a ≠ b) :
    realDigit a - realDigit b = -1 ∨ realDigit a - realDigit b = 1 := by
  cases a <;> cases b <;> norm_num [realDigit] at *

/-- At a fixed digit of a base word, both other words give the same nonzero difference. -/
theorem realDigit_sub_same_base {a b d : Bool} (ha : a ≠ b) (hd : d ≠ b) :
    realDigit a - realDigit b = realDigit d - realDigit b := by
  cases a <;> cases b <;> cases d <;> simp_all

theorem exists_first_difference {n : ℕ} {a b : BinaryWord n} (h : a ≠ b) :
    ∃ m : Fin n, a m ≠ b m ∧ ∀ j, j < m → a j = b j := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ b i)
  have hs : s.Nonempty := by
    have hex : ∃ i, a i ≠ b i := by
      by_contra hh
      push Not at hh
      exact h (funext hh)
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [s, hi]⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, ?_⟩
  intro j hj
  by_contra hne
  have hjmem : j ∈ s := by simp [s, hne]
  exact not_le_of_gt hj (Finset.min'_le s j hjmem)

def binaryProjection {n : ℕ} (v : Fin n → Point) (t : ℝ) (a : BinaryWord n) : Point :=
  ∑ i, (realDigit (a i) * t ^ i.val) • v i

def binaryResidual {n : ℕ} (v : Fin n → Point) (a b : BinaryWord n) (m : Fin n)
    (t : ℝ) : Point :=
  ∑ i, ((realDigit (a i) - realDigit (b i)) * t ^ (i.val - m.val)) • v i

theorem binaryProjection_sub {n : ℕ} (v : Fin n → Point) (t : ℝ) (a b : BinaryWord n) :
    binaryProjection v t a - binaryProjection v t b =
      ∑ i, ((realDigit (a i) - realDigit (b i)) * t ^ i.val) • v i := by
  simp only [binaryProjection, ← Finset.sum_sub_distrib, sub_mul, sub_smul]

/-- Factor out the scale of the first differing digit. -/
theorem binaryProjection_sub_factor {n : ℕ} (v : Fin n → Point) (t : ℝ)
    (a b : BinaryWord n) (m : Fin n) (hearlier : ∀ j, j < m → a j = b j) :
    binaryProjection v t a - binaryProjection v t b = t ^ m.val • binaryResidual v a b m t := by
  rw [binaryProjection_sub, binaryResidual, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i < m
  · simp [hearlier i hi]
  · have hle : m.val ≤ i.val := le_of_not_gt hi
    rw [smul_smul]
    congr 1
    calc
      (realDigit (a i) - realDigit (b i)) * t ^ i.val =
          (realDigit (a i) - realDigit (b i)) * (t ^ m.val * t ^ (i.val - m.val)) := by
        rw [← pow_add, Nat.add_sub_of_le hle]
      _ = t ^ m.val * ((realDigit (a i) - realDigit (b i)) * t ^ (i.val - m.val)) := by ring

theorem binaryResidual_zero {n : ℕ} (v : Fin n → Point) (a b : BinaryWord n) (m : Fin n)
    (hearlier : ∀ j, j < m → a j = b j) :
    binaryResidual v a b m 0 = (realDigit (a m) - realDigit (b m)) • v m := by
  unfold binaryResidual
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _ him
    by_cases hi : i < m
    · simp [hearlier i hi]
    · have hmilt : m.val < i.val := lt_of_le_of_ne (le_of_not_gt hi)
        (fun heq => him (Fin.ext heq.symm))
      have hpos : 0 < i.val - m.val := Nat.sub_pos_of_lt hmilt
      simp [zero_pow (Nat.ne_zero_of_lt hpos)]
  · simp

theorem tendsto_binaryResidual {n : ℕ} (v : Fin n → Point) (a b : BinaryWord n) (m : Fin n)
    (hearlier : ∀ j, j < m → a j = b j) :
    Tendsto (binaryResidual v a b m) (𝓝 0)
      (𝓝 ((realDigit (a m) - realDigit (b m)) • v m)) := by
  have hcont : Continuous (binaryResidual v a b m) := by
    unfold binaryResidual
    fun_prop
  simpa only [binaryResidual_zero v a b m hearlier] using hcont.continuousAt.tendsto (x := 0)

theorem eventually_injective_binaryProjection {n : ℕ} (v : Fin n → Point)
    (hv : ∀ i, v i ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (binaryProjection v t) := by
  have hpairs : ∀ a b : BinaryWord n, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      a ≠ b → binaryProjection v t a ≠ binaryProjection v t b := by
    intro a b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (by simp [hab])
    obtain ⟨m, hdiff, hearlier⟩ := exists_first_difference hab
    have hres := (tendsto_binaryResidual v a b m hearlier).eventually_ne
      (smul_ne_zero (realDigit_sub_ne_zero hdiff) (hv m))
    filter_upwards [hres.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos _ hsame
    have hzero := sub_eq_zero.mpr hsame
    rw [binaryProjection_sub_factor v t a b m hearlier] at hzero
    exact (smul_ne_zero (pow_ne_zero _ (ne_of_gt htpos)) ht) hzero
  filter_upwards [Filter.eventually_all.mpr (fun a =>
    Filter.eventually_all.mpr (hpairs a))] with t ht a b hab
  by_contra hne
  exact ht a b hne hab

/-- The limiting angle of two binary difference vectors is controlled by their first differing bits. -/
theorem tendsto_binaryProjection_angle {n : ℕ} (v : Fin n → Point) (hv : ∀ i, v i ≠ 0)
    (a b d : BinaryWord n) (m q : Fin n)
    (hm : a m ≠ b m) (hem : ∀ j, j < m → a j = b j)
    (hq : d q ≠ b q) (heq : ∀ j, j < q → d j = b j) :
    Tendsto (fun t : ℝ => EuclideanGeometry.angle
      (binaryProjection v t a) (binaryProjection v t b) (binaryProjection v t d))
      (𝓝[>] 0) (𝓝 (InnerProductGeometry.angle
        ((realDigit (a m) - realDigit (b m)) • v m)
        ((realDigit (d q) - realDigit (b q)) • v q))) := by
  have hpair := (tendsto_binaryResidual v a b m hem).prodMk_nhds
    (tendsto_binaryResidual v d b q heq)
  have hang : ContinuousAt (fun z : Point × Point => InnerProductGeometry.angle z.1 z.2)
      (((realDigit (a m) - realDigit (b m)) • v m),
        ((realDigit (d q) - realDigit (b q)) • v q)) :=
    InnerProductGeometry.continuousAt_angle
      (smul_ne_zero (realDigit_sub_ne_zero hm) (hv m))
      (smul_ne_zero (realDigit_sub_ne_zero hq) (hv q))
  have hlim := (Tendsto.comp
    (g := fun z : Point × Point => InnerProductGeometry.angle z.1 z.2)
    (f := fun t : ℝ => (binaryResidual v a b m t, binaryResidual v d b q t))
    hang.tendsto hpair).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  apply Tendsto.congr' (h := hlim)
  filter_upwards [self_mem_nhdsWithin] with t ht
  change _ = InnerProductGeometry.angle
    (binaryProjection v t a - binaryProjection v t b)
    (binaryProjection v t d - binaryProjection v t b)
  rw [binaryProjection_sub_factor v t a b m hem, binaryProjection_sub_factor v t d b q heq,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (pow_pos ht _),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (pow_pos ht _)]
  rfl

/-- Any separated family of `n` unoriented lines yields the multiscale `2^n`-point upper bound. -/
theorem alpha_two_pow_le_of_signed_directions {n : ℕ} (v : Fin n → Point)
    (hv : ∀ i, v i ≠ 0) (hn : 3 ≤ 2 ^ n) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsep : ∀ i j, i ≠ j → ∀ r s : ℝ,
      (r = -1 ∨ r = 1) → (s = -1 ∨ s = 1) →
      InnerProductGeometry.angle (r • v i) (s • v j) ≤ θ) :
    alpha (2 ^ n) ≤ θ := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  have htriples : ∀ a b d : BinaryWord n, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      a ≠ b → d ≠ b → EuclideanGeometry.angle
        (binaryProjection v t a) (binaryProjection v t b) (binaryProjection v t d) < θ + ε := by
    intro a b d
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (by simp [hab])
    by_cases hdb : d = b
    · exact Filter.Eventually.of_forall (by simp [hdb])
    obtain ⟨m, hm, hem⟩ := exists_first_difference hab
    obtain ⟨q, hq, heq⟩ := exists_first_difference hdb
    have hlimbound : InnerProductGeometry.angle
        ((realDigit (a m) - realDigit (b m)) • v m)
        ((realDigit (d q) - realDigit (b q)) • v q) ≤ θ := by
      by_cases hmq : m = q
      · subst q
        rw [realDigit_sub_same_base hm hq]
        rw [InnerProductGeometry.angle_self (smul_ne_zero (realDigit_sub_ne_zero hq) (hv m))]
        exact hθ
      · exact hsep m q hmq _ _ (realDigit_sub_eq_sign hm) (realDigit_sub_eq_sign hq)
    have hh := (tendsto_binaryProjection_angle v hv a b d m q hm hem hq heq).eventually_lt
      tendsto_const_nhds (hlimbound.trans_lt (lt_add_of_pos_right θ hε))
    filter_upwards [hh] with t ht _ _
    exact ht
  have hall := Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr
    (fun b => Filter.eventually_all.mpr (htriples a b)))
  obtain ⟨t, htinj, htangles⟩ := ((eventually_injective_binaryProjection v hv).and hall).exists
  let s : Finset Point := Finset.univ.image (binaryProjection v t)
  have hs : s.card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ htinj]
    simp [BinaryWord]
  apply alpha_le_of_configuration hn hs
  intro a ha b hb d hd hab _ hbd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hd
  exact (htangles i j k (fun h => hab (congrArg _ h))
    (fun h => hbd (congrArg _ h.symm))).le

end JSP404
