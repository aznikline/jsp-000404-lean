import JSP404.Basic
import Mathlib.Tactic

/-!
# Shrinking a finite family of point clusters

These lemmas justify a single level of the hierarchical realization used in
Sendov's upper-bound constructions. They do not assert the full angle formula.
-/

noncomputable section

open Filter Topology

set_option maxHeartbeats 400000

namespace JSP404

variable {ι : Type*}

/-- Place a local point `x i` into a cluster centered at `c i`, at scale `t`. -/
def perturb (c x : ι → Point) (t : ℝ) (i : ι) : Point := c i + t • x i

theorem perturb_sub (c x : ι → Point) (t : ℝ) (i j : ι) :
    perturb c x t i - perturb c x t j = c i - c j + t • (x i - x j) := by
  simp only [perturb, smul_sub]
  abel

theorem perturb_sub_of_same_center (c x : ι → Point) (t : ℝ) {i j : ι}
    (h : c i = c j) :
    perturb c x t i - perturb c x t j = t • (x i - x j) := by
  rw [perturb_sub, h, sub_self, zero_add]

theorem tendsto_perturb_sub (c x : ι → Point) (i j : ι) :
    Tendsto (fun t : ℝ => perturb c x t i - perturb c x t j)
      (𝓝 0) (𝓝 (c i - c j)) := by
  have h : Continuous (fun t : ℝ => perturb c x t i - perturb c x t j) := by
    unfold perturb
    fun_prop
  simpa [perturb] using h.continuousAt.tendsto (x := 0)

/-- Distinct center/local-position pairs stay distinct at all sufficiently small positive scales. -/
theorem eventually_injective_perturb [Finite ι] (c x : ι → Point)
    (h : Function.Injective (fun i => (c i, x i))) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (perturb c x t) := by
  have hpairs : ∀ i j, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      i ≠ j → perturb c x t i ≠ perturb c x t j := by
    intro i j
    by_cases hc : c i = c j
    · filter_upwards [self_mem_nhdsWithin] with t ht hij hsame
      have ht' : 0 < t := ht
      have hlocal : x i = x j := by
        have heq : t • (x i - x j) = 0 := by
          rw [← perturb_sub_of_same_center c x t hc, hsame, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp heq).resolve_left (ne_of_gt ht'))
      exact hij (h (Prod.ext hc hlocal))
    · have hn := (tendsto_perturb_sub c x i j).eventually_ne (sub_ne_zero.mpr hc)
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with t ht _ hsame
      exact ht (sub_eq_zero.mpr hsame)
  filter_upwards [Filter.eventually_all.mpr (fun i =>
    Filter.eventually_all.mpr (hpairs i))] with t ht i j hij
  by_contra hne
  exact ht i j hne hij

/-- A three-point angle entirely inside one cluster is unchanged by shrinking. -/
theorem perturb_angle_same_cluster (c x : ι → Point) {t : ℝ} (ht : 0 < t)
    {i j k : ι} (hij : c i = c j) (hkj : c k = c j) :
    EuclideanGeometry.angle (perturb c x t i) (perturb c x t j) (perturb c x t k) =
      EuclideanGeometry.angle (x i) (x j) (x k) := by
  change InnerProductGeometry.angle
      (perturb c x t i - perturb c x t j)
      (perturb c x t k - perturb c x t j) = _
  rw [perturb_sub_of_same_center c x t hij,
    perturb_sub_of_same_center c x t hkj,
    InnerProductGeometry.angle_smul_smul (ne_of_gt ht)]
  rfl

theorem tendsto_angle_affine (u v p q : Point) (hu : u ≠ 0) (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => InnerProductGeometry.angle (u + t • p) (v + t • q))
      (𝓝 0) (𝓝 (InnerProductGeometry.angle u v)) := by
  have hup : Tendsto (fun t : ℝ => u + t • p) (𝓝 0) (𝓝 u) := by
    have hp : Tendsto (fun t : ℝ => t • p) (𝓝 0) (𝓝 ((0 : ℝ) • p)) :=
      tendsto_id.smul_const p
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add hp
  have hvq : Tendsto (fun t : ℝ => v + t • q) (𝓝 0) (𝓝 v) := by
    have hq : Tendsto (fun t : ℝ => t • q) (𝓝 0) (𝓝 ((0 : ℝ) • q)) :=
      tendsto_id.smul_const q
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add hq
  have hp := hup.prodMk_nhds hvq
  have hang : ContinuousAt (fun z : Point × Point => InnerProductGeometry.angle z.1 z.2) (u, v) :=
    InnerProductGeometry.continuousAt_angle hu hv
  exact Tendsto.comp (g := fun z : Point × Point => InnerProductGeometry.angle z.1 z.2)
    (f := fun t : ℝ => (u + t • p, v + t • q)) hang.tendsto hp

/-- The limiting direction uses the local displacement precisely when the two centers coincide. -/
def clusterDirection (c x : ι → Point) (i j : ι) : Point :=
  if c i = c j then x i - x j else c i - c j

def clusterAngle (c x : ι → Point) (i j k : ι) : ℝ :=
  InnerProductGeometry.angle (clusterDirection c x i j) (clusterDirection c x k j)

/-- Each angle converges to the angle between the first nonvanishing directions. -/
theorem tendsto_perturb_angle (c x : ι → Point)
    (hinj : Function.Injective (fun i => (c i, x i)))
    {i j k : ι} (hij : i ≠ j) (hkj : k ≠ j) :
    Tendsto (fun t : ℝ => EuclideanGeometry.angle
      (perturb c x t i) (perturb c x t j) (perturb c x t k))
      (𝓝[>] 0) (𝓝 (clusterAngle c x i j k)) := by
  have hlocal {a b : ι} (hab : a ≠ b) (hc : c a = c b) : x a - x b ≠ 0 := by
    intro hzero
    exact hab (hinj (Prod.ext hc (sub_eq_zero.mp hzero)))
  by_cases hcij : c i = c j <;> by_cases hckj : c k = c j
  · have heq : (fun _t : ℝ => EuclideanGeometry.angle (x i) (x j) (x k)) =ᶠ[𝓝[>] 0]
        (fun t => EuclideanGeometry.angle
          (perturb c x t i) (perturb c x t j) (perturb c x t k)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (perturb_angle_same_cluster c x ht hcij hckj).symm
    have hh := Tendsto.congr' heq tendsto_const_nhds
    simpa [clusterAngle, clusterDirection, hcij, hckj, EuclideanGeometry.angle,
      vsub_eq_sub] using hh
  · have hh := (tendsto_angle_affine (x i - x j) (c k - c j) 0 (x k - x j)
      (hlocal hij hcij) (sub_ne_zero.mpr hckj)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have heq : (fun t : ℝ => InnerProductGeometry.angle
        ((x i - x j) + t • (0 : Point)) ((c k - c j) + t • (x k - x j))) =ᶠ[𝓝[>] 0]
        (fun t => EuclideanGeometry.angle
          (perturb c x t i) (perturb c x t j) (perturb c x t k)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change _ = InnerProductGeometry.angle
        (perturb c x t i - perturb c x t j) (perturb c x t k - perturb c x t j)
      rw [perturb_sub_of_same_center c x t hcij, perturb_sub,
        InnerProductGeometry.angle_smul_left_of_pos _ _ ht]
      simp
    simpa [clusterAngle, clusterDirection, hcij, hckj] using Tendsto.congr' heq hh
  · have hh := (tendsto_angle_affine (c i - c j) (x k - x j) (x i - x j) 0
      (sub_ne_zero.mpr hcij) (hlocal hkj hckj)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have heq : (fun t : ℝ => InnerProductGeometry.angle
        ((c i - c j) + t • (x i - x j)) ((x k - x j) + t • (0 : Point))) =ᶠ[𝓝[>] 0]
        (fun t => EuclideanGeometry.angle
          (perturb c x t i) (perturb c x t j) (perturb c x t k)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change _ = InnerProductGeometry.angle
        (perturb c x t i - perturb c x t j) (perturb c x t k - perturb c x t j)
      rw [perturb_sub_of_same_center c x t hckj, perturb_sub,
        InnerProductGeometry.angle_smul_right_of_pos _ _ ht]
      simp
    simpa [clusterAngle, clusterDirection, hcij, hckj] using Tendsto.congr' heq hh
  · have hh := (tendsto_angle_affine (c i - c j) (c k - c j) (x i - x j) (x k - x j)
      (sub_ne_zero.mpr hcij) (sub_ne_zero.mpr hckj)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [clusterAngle, clusterDirection, hcij, hckj, EuclideanGeometry.angle,
      vsub_eq_sub, perturb_sub] using hh

/-- Realize every finite one-level cluster configuration with arbitrarily small angle error. -/
theorem exists_configuration_of_cluster_angles [Fintype ι] (c x : ι → Point)
    (hinj : Function.Injective (fun i => (c i, x i))) {θ ε : ℝ} (hε : 0 < ε)
    (hangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → clusterAngle c x i j k ≤ θ) :
    ∃ s : Finset Point, s.card = Fintype.card ι ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ d ∈ s, a ≠ b → a ≠ d → b ≠ d →
        EuclideanGeometry.angle a b d < θ + ε := by
  classical
  have htriples : ∀ i j k, ∀ᶠ t in 𝓝[>] (0 : ℝ), i ≠ j → i ≠ k → j ≠ k →
      EuclideanGeometry.angle (perturb c x t i) (perturb c x t j) (perturb c x t k) < θ + ε := by
    intro i j k
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    by_cases hik : i = k
    · exact Filter.Eventually.of_forall (by simp [hik])
    by_cases hjk : j = k
    · exact Filter.Eventually.of_forall (by simp [hjk])
    have hh := (tendsto_perturb_angle c x hinj hij (Ne.symm hjk)).eventually_lt
      tendsto_const_nhds ((hangle i j k hij hik hjk).trans_lt (lt_add_of_pos_right θ hε))
    filter_upwards [hh] with t ht _ _ _
    exact ht
  have hall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr
    (fun j => Filter.eventually_all.mpr (htriples i j)))
  obtain ⟨t, htinj, htangles⟩ := ((eventually_injective_perturb c x hinj).and hall).exists
  refine ⟨Finset.univ.image (perturb c x t), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ htinj]
    simp
  · intro a ha b hb d hd hab had hbd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hd
    exact htangles i j k (fun h => hab (congrArg _ h))
      (fun h => had (congrArg _ h)) (fun h => hbd (congrArg _ h))

/-- A generalized one-level configuration gives a bound on the ordinary Euclidean problem. -/
theorem alpha_le_of_cluster_angles [Fintype ι] (c x : ι → Point)
    (hinj : Function.Injective (fun i => (c i, x i))) (hn : 3 ≤ Fintype.card ι) {θ : ℝ}
    (hangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → clusterAngle c x i j k ≤ θ) :
    alpha (Fintype.card ι) ≤ θ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨s, hs, hang⟩ := exists_configuration_of_cluster_angles c x hinj hε hangle
  exact alpha_le_of_configuration hn hs (fun a ha b hb d hd hab had hbd =>
    (hang a ha b hb d hd hab had hbd).le)

end JSP404
