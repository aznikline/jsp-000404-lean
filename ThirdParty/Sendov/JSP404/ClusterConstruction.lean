import JSP404.BinaryConstruction
import Mathlib.Tactic

/-!
# Joining finite binary clusters

This module turns bounds on center angles, internal line angles, and angles
between internal lines and center-to-center vectors into an ordinary planar
configuration. The number of points is the sum of the binary cluster sizes.
-/

noncomputable section

open Filter Topology

set_option maxHeartbeats 1200000

namespace JSP404

theorem tendsto_binaryProjection_direction_angle {n : ℕ} (v : Fin n → Point)
    (a b : BinaryWord n) (m : Fin n) (hm : a m ≠ b m)
    (hem : ∀ j, j < m → a j = b j) (hv : v m ≠ 0) (u : Point) (hu : u ≠ 0) :
    Tendsto (fun t : ℝ => InnerProductGeometry.angle
      (binaryProjection v t a - binaryProjection v t b) u)
      (𝓝[>] 0) (𝓝 (InnerProductGeometry.angle
        ((realDigit (a m) - realDigit (b m)) • v m) u)) := by
  have hpair := (tendsto_binaryResidual v a b m hem).prodMk_nhds
    (tendsto_const_nhds (x := u))
  have hang : ContinuousAt (fun z : Point × Point => InnerProductGeometry.angle z.1 z.2)
      (((realDigit (a m) - realDigit (b m)) • v m), u) :=
    InnerProductGeometry.continuousAt_angle
      (smul_ne_zero (realDigit_sub_ne_zero hm) hv) hu
  have hlim := (Tendsto.comp
    (g := fun z : Point × Point => InnerProductGeometry.angle z.1 z.2)
    (f := fun t : ℝ => (binaryResidual v a b m t, u))
    hang.tendsto hpair).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  apply Tendsto.congr' (h := hlim)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [binaryProjection_sub_factor v t a b m hem,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (pow_pos ht _)]
  rfl

theorem eventually_binaryProjection_angle_lt {n : ℕ} (v : Fin n → Point)
    (hv : ∀ i, v i ≠ 0) {θ ε : ℝ} (hθ : 0 ≤ θ) (hε : 0 < ε)
    (hsep : ∀ i j, i ≠ j → ∀ r s : ℝ,
      (r = -1 ∨ r = 1) → (s = -1 ∨ s = 1) →
      InnerProductGeometry.angle (r • v i) (s • v j) ≤ θ)
    (a b d : BinaryWord n) (hab : a ≠ b) (hdb : d ≠ b) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), EuclideanGeometry.angle
      (binaryProjection v t a) (binaryProjection v t b) (binaryProjection v t d) < θ + ε := by
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
  exact (tendsto_binaryProjection_angle v hv a b d m q hm hem hq heq).eventually_lt
    tendsto_const_nhds (hlimbound.trans_lt (lt_add_of_pos_right θ hε))

abbrev ClusterWord {κ : Type*} (dims : κ → ℕ) := (i : κ) × BinaryWord (dims i)

def clusterProjection {κ : Type*} {dims : κ → ℕ}
    (v : (i : κ) → Fin (dims i) → Point) (t : ℝ) (a : ClusterWord dims) : Point :=
  binaryProjection (v a.1) t a.2

theorem eventually_injective_center_cluster {κ : Type*} [Fintype κ]
    {dims : κ → ℕ} (c : κ → Point) (hc : Function.Injective c)
    (v : (i : κ) → Fin (dims i) → Point) (hv : ∀ i j, v i j ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective
      (fun a : ClusterWord dims => (c a.1, clusterProjection v t a)) := by
  have hall := Filter.eventually_all.mpr (fun i => eventually_injective_binaryProjection (v i) (hv i))
  filter_upwards [hall] with t ht
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := hc (congrArg Prod.fst h)
  subst j
  have hab : a = b := ht i (congrArg Prod.snd h)
  subst b
  rfl

theorem clusterWord_card {κ : Type*} [Fintype κ] (dims : κ → ℕ) :
    Fintype.card (ClusterWord dims) = ∑ i, 2 ^ dims i := by
  simp [ClusterWord, BinaryWord, Fintype.card_sigma]

/-- A finite family of binary clusters produces the sum of their power-of-two sizes. -/
theorem alpha_sum_two_pow_le_of_cluster_directions {κ : Type*} [Fintype κ]
    {dims : κ → ℕ} (c : κ → Point) (hc : Function.Injective c)
    (v : (i : κ) → Fin (dims i) → Point) (hv : ∀ i j, v i j ≠ 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hn : 3 ≤ ∑ i, 2 ^ dims i)
    (hcenters : ∀ i j k, i ≠ j → k ≠ j → EuclideanGeometry.angle (c i) (c j) (c k) ≤ θ)
    (hinternal : ∀ i p q, p ≠ q → ∀ r s : ℝ,
      (r = -1 ∨ r = 1) → (s = -1 ∨ s = 1) →
      InnerProductGeometry.angle (r • v i p) (s • v i q) ≤ θ)
    (hcross : ∀ i j, i ≠ j → ∀ (p : Fin (dims i)) (r : ℝ), (r = -1 ∨ r = 1) →
      InnerProductGeometry.angle (r • v i p) (c j - c i) ≤ θ) :
    alpha (∑ i, 2 ^ dims i) ≤ θ := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let cc : ClusterWord dims → Point := fun a => c a.1
  have htriples : ∀ a b d : ClusterWord dims, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      a ≠ b → d ≠ b → clusterAngle cc (clusterProjection v t) a b d < θ + ε := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, d⟩
    by_cases hij : i = j <;> by_cases hkj : k = j
    · subst j
      subst k
      by_cases hab : a = b
      · exact Filter.Eventually.of_forall (by simp [hab])
      by_cases hdb : d = b
      · exact Filter.Eventually.of_forall (by simp [hdb])
      have hh := eventually_binaryProjection_angle_lt (v i) (hv i) hθ hε (hinternal i) a b d hab hdb
      filter_upwards [hh] with t ht _ _
      simpa [clusterAngle, clusterDirection, cc, clusterProjection, EuclideanGeometry.angle,
        vsub_eq_sub] using ht
    · subst j
      by_cases hab : a = b
      · exact Filter.Eventually.of_forall (by simp [hab])
      obtain ⟨m, hm, hem⟩ := exists_first_difference hab
      have hne : c k ≠ c i := hc.ne hkj
      have hh := (tendsto_binaryProjection_direction_angle (v i) a b m hm hem (hv i m)
        (c k - c i) (sub_ne_zero.mpr hne)).eventually_lt tendsto_const_nhds
        ((hcross i k (Ne.symm hkj) m (realDigit (a m) - realDigit (b m)) (realDigit_sub_eq_sign hm)).trans_lt
          (lt_add_of_pos_right θ hε))
      filter_upwards [hh] with t ht _ _
      simpa [clusterAngle, clusterDirection, cc, clusterProjection, hne] using ht
    · subst k
      by_cases hdb : d = b
      · exact Filter.Eventually.of_forall (by simp [hdb])
      obtain ⟨m, hm, hem⟩ := exists_first_difference hdb
      have hne : c i ≠ c j := hc.ne hij
      have hh := (tendsto_binaryProjection_direction_angle (v j) d b m hm hem (hv j m)
        (c i - c j) (sub_ne_zero.mpr hne)).eventually_lt tendsto_const_nhds
        ((hcross j i (Ne.symm hij) m (realDigit (d m) - realDigit (b m)) (realDigit_sub_eq_sign hm)).trans_lt
          (lt_add_of_pos_right θ hε))
      filter_upwards [hh] with t ht _ _
      simpa [clusterAngle, clusterDirection, cc, clusterProjection, hne,
        InnerProductGeometry.angle_comm] using ht
    · have hneij : c i ≠ c j := hc.ne hij
      have hnekj : c k ≠ c j := hc.ne hkj
      apply Filter.Eventually.of_forall
      intro t _ _
      simpa [clusterAngle, clusterDirection, cc, hneij, hnekj, EuclideanGeometry.angle,
        vsub_eq_sub] using (hcenters i j k hij hkj).trans_lt (lt_add_of_pos_right θ hε)
  have hall := Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr
    (fun b => Filter.eventually_all.mpr (htriples a b)))
  obtain ⟨t, htinj, htangles⟩ := ((eventually_injective_center_cluster c hc v hv).and hall).exists
  rw [← clusterWord_card dims]
  apply alpha_le_of_cluster_angles cc (clusterProjection v t) htinj
    (by rwa [clusterWord_card])
  intro a b d hab _ hbd
  exact (htangles a b d hab (Ne.symm hbd)).le

end JSP404
