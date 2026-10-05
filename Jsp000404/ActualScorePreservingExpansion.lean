import Jsp000404.ActualPairExpansion
import Jsp000404.GapSplitFloorStability
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Necessary actual-ray and finite-gap stability foundations for exact
score-preserving expansion. The projective multiset sorting/cluster bridge
is not yet proved, and no full row-score or capacity theorem is asserted.
-/

open Filter Topology
open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualScorePreservingExpansion

/-- A projective angle chart is genuinely continuous off both real-axis
directions. The excluded imaginary-zero locus is exactly the chart seam
for this argument; no continuity at that seam is asserted. -/
theorem continuousAt_projective_arg {f : ℝ → ℂ}
    (hf : ContinuousAt f 0) (him : (f 0).im ≠ 0) :
    ContinuousAt (fun eps => linRep ((f eps).arg : Real.Angle)) 0 := by
  have hslit : f 0 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr him)
  have harg : ContinuousAt (fun eps => (f eps).arg) 0 :=
    (Complex.continuousAt_arg hslit).comp hf
  have harg0 : (f 0).arg ≠ 0 := by
    intro h
    exact him (Complex.arg_eq_zero_iff.mp h).2
  have hargpi : (f 0).arg ≠ Real.pi := by
    intro h
    exact him (Complex.arg_eq_pi_iff.mp h).2
  by_cases hneg : (f 0).arg < 0
  · have hevent : ∀ᶠ eps in 𝓝 (0 : ℝ), (f eps).arg < 0 :=
      harg.eventually_lt continuousAt_const hneg
    have hc : ContinuousAt (fun eps => (f eps).arg + Real.pi) 0 :=
      harg.add continuousAt_const
    apply hc.congr
    filter_upwards [hevent] with eps heps
    simp [linRep, Complex.arg_coe_angle_toReal_eq_arg, heps]
  · have hpos : 0 < (f 0).arg :=
      lt_of_le_of_ne (le_of_not_gt hneg) harg0.symm
    have hpositive : ∀ᶠ eps in 𝓝 (0 : ℝ), 0 < (f eps).arg :=
      continuousAt_const.eventually_lt harg hpos
    have hnotpi : ∀ᶠ eps in 𝓝 (0 : ℝ), (f eps).arg ≠ Real.pi :=
      harg.eventually_ne hargpi
    apply harg.congr
    filter_upwards [hpositive, hnotpi] with eps hp hpi
    simp [linRep, Complex.arg_coe_angle_toReal_eq_arg, not_lt.mpr hp.le, hpi]

/-- Actual external rays have continuous real chart coordinates whenever
the supplied reference avoids their limiting projective class. The value
at zero is the old-parent ray, not a zero sibling vector. -/
theorem continuousAt_external_projective_ray {s : ℕ} {P : Fin s → Bool}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c u : Fin s → Plane₂) (x y : ActualPairExpansion.Copy P)
    (hseam : (o.kahler e (c y.1 - c x.1)).im ≠ 0) :
    ContinuousAt (fun eps => linRep (o.oangle e
      (ActualPairExpansion.point c u eps y - ActualPairExpansion.point c u eps x)))
      0 := by
  have hv : Continuous (fun eps =>
      ActualPairExpansion.point c u eps y - ActualPairExpansion.point c u eps x) :=
    (ActualPairExpansion.continuous_point c u y).sub
      (ActualPairExpansion.continuous_point c u x)
  have hk : Continuous (o.kahler e) :=
    (o.kahler e).continuous_of_finiteDimensional
  have hc : ContinuousAt (fun eps => o.kahler e
      (ActualPairExpansion.point c u eps y - ActualPairExpansion.point c u eps x)) 0 :=
    (hk.comp hv).continuousAt
  have him : (o.kahler e
      (ActualPairExpansion.point c u 0 y - ActualPairExpansion.point c u 0 x)).im ≠ 0 := by
    simpa only [ActualPairExpansion.point_zero] using hseam
  simpa only [Orientation.oangle] using continuousAt_projective_arg hc him

/-- The same-parent difference is an exact scalar multiple of its axis. -/
theorem same_parent_difference {s : ℕ} {P : Fin s → Bool}
    (c u : Fin s → Plane₂) (x y : ActualPairExpansion.Copy P)
    (hb : x.1 = y.1) (eps : ℝ) :
    ActualPairExpansion.point c u eps y - ActualPairExpansion.point c u eps x =
      eps • (((y.2.val : ℝ) - (x.2.val : ℝ)) • u x.1) := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  dsimp at hb
  subst j
  unfold ActualPairExpansion.point
  dsimp
  module

/-- The actual sibling ray has a constant normalized projective direction
at every positive scale. This avoids feeding its zero vector at epsilon=0
to a false angle-continuity claim. -/
theorem sibling_projective_ray_eq {s : ℕ} {P : Fin s → Bool}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c u : Fin s → Plane₂) (x y : ActualPairExpansion.Copy P)
    (hb : x.1 = y.1) {eps : ℝ} (heps : 0 < eps) :
    linRep (o.oangle e
      (ActualPairExpansion.point c u eps y - ActualPairExpansion.point c u eps x)) =
    linRep (o.oangle e (((y.2.val : ℝ) - (x.2.val : ℝ)) • u x.1)) := by
  rw [same_parent_difference c u x y hb eps,
    o.oangle_smul_right_of_pos _ _ heps]

/-- Distinct limiting chart classes retain their relative order. Equal
classes impose no ordering condition, so collisions within a cluster are
fully retained. -/
theorem eventually_intercluster_order {m : ℕ} (a : Fin m → ℝ → ℝ)
    (hcont : ∀ i, ContinuousAt (a i) 0) :
    ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ i j,
      a i 0 < a j 0 → a i eps < a j eps := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hij : a i 0 < a j 0
  · exact ((hcont i).eventually_lt (hcont j) hij).mono fun _ h _ => h
  · exact Eventually.of_forall fun _ h => False.elim (hij h)

/-- Every permutation that sorts the actual nearby chart coordinates
already sorts the limiting coordinates. This gives a finite-permutation
route to gap stability without assuming that collided labels keep one
fixed ordering. -/
theorem eventually_sorted_limit_of_sorted {m : ℕ} (a : Fin m → ℝ → ℝ)
    (hcont : ∀ i, ContinuousAt (a i) 0) :
    ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ perm : Equiv.Perm (Fin m),
      (List.ofFn (fun i => a (perm i) eps)).SortedLE →
        (List.ofFn (fun i => a (perm i) 0)).SortedLE := by
  filter_upwards [eventually_intercluster_order a hcont] with eps heps
  intro perm hsort
  rw [List.sortedLE_ofFn_iff] at hsort ⊢
  intro i j hij
  by_contra h
  have hrev : a (perm j) 0 < a (perm i) 0 := lt_of_not_ge h
  exact (not_lt_of_ge (hsort hij)) (heps (perm j) (perm i) hrev)

/-- The genuine linear chart gap formula, including its full-circle wrap,
is continuous along each fixed finite ray enumeration. This is not an
assertion that the global cut representatives or a changing sorted row
are continuous. -/
theorem continuousAt_gapAfter_ofFn {m : ℕ} (a : Fin (m + 1) → ℝ → ℝ)
    (hcont : ∀ i, ContinuousAt (a i) 0) (i : Fin (m + 1)) :
    ContinuousAt (fun eps => gapAfter (List.ofFn (fun j => a j eps))
      (Fin.cast (by simp) i)) 0 := by
  by_cases hi : i.val + 1 < m + 1
  · have hc : ContinuousAt (fun eps => a ⟨i.val + 1, hi⟩ eps - a i eps) 0 :=
      (hcont ⟨i.val + 1, hi⟩).sub (hcont i)
    simpa only [gapAfter, List.get_eq_getElem, List.length_ofFn,
      List.getElem_ofFn, Fin.cast, hi, ↓reduceDIte, Fin.eta] using hc
  · have hc : ContinuousAt (fun eps => a ⟨0, Nat.succ_pos m⟩ eps + Real.pi - a i eps) 0 :=
      ((hcont ⟨0, Nat.succ_pos m⟩).add (show ContinuousAt (fun _ : ℝ => Real.pi) 0 from
        continuousAt_const)).sub (hcont i)
    simpa only [gapAfter, List.get_eq_getElem, List.length_ofFn,
      List.getElem_ofFn, Fin.cast, hi, ↓reduceDIte, Fin.eta] using hc

/-- Continuous finite gap trajectories retain every old natural floor at
one strictly smaller parameter and every sufficiently small perturbation.
Zero gaps are allowed; their perturbed values need not be nonnegative for
the natural-floor conclusion. This is proved from continuity and strict
arithmetic margins, rather than assumed as a score-stability hypothesis. -/
theorem exists_eventual_floor_stability {m : ℕ}
    (gs : Fin m → ℝ) (pert : Fin m → ℝ → ℝ)
    (hnonneg : ∀ i, 0 ≤ gs i)
    (hcont : ∀ i, ContinuousAt (pert i) 0)
    (hzero : ∀ i, pert i 0 = gs i)
    {lam tau : ℝ} (hlam : 0 < lam) (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∀ᶠ eps in 𝓝 (0 : ℝ), ∀ i,
        ⌊pert i eps / lam'⌋₊ = ⌊gs i / lam⌋₊ := by
  obtain ⟨lam', htau', hsmall, hm⟩ :=
    GapSplitFloorStability.exists_floor_stable_scale_with_margins
      (List.ofFn gs) hlam
      (fun g hg => by
        rcases List.mem_ofFn.mp hg with ⟨i, rfl⟩
        exact hnonneg i) htau0 htau
  have hlam' : 0 < lam' := htau0.trans htau'
  refine ⟨lam', htau', hsmall, eventually_all.mpr ?_⟩
  intro i
  have hmargin := hm (gs i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hupper0 : pert i 0 < ((⌊gs i / lam⌋₊ : ℝ) + 1) * lam' := by
    rw [hzero i]
    exact hmargin.2.1
  have hupper : ∀ᶠ eps in 𝓝 (0 : ℝ),
      pert i eps < ((⌊gs i / lam⌋₊ : ℝ) + 1) * lam' :=
    (hcont i).eventually_lt continuousAt_const hupper0
  by_cases hq : 0 < ⌊gs i / lam⌋₊
  · have hlower0 : (⌊gs i / lam⌋₊ : ℝ) * lam' < pert i 0 := by
      rw [hzero i]
      exact hmargin.2.2 hq
    have hlower : ∀ᶠ eps in 𝓝 (0 : ℝ),
        (⌊gs i / lam⌋₊ : ℝ) * lam' < pert i eps :=
      continuousAt_const.eventually_lt (hcont i) hlower0
    filter_upwards [hupper, hlower] with eps hu hl
    apply (Nat.floor_eq_iff' (ne_of_gt hq)).mpr
    exact ⟨(le_div_iff₀ hlam').mpr hl.le, (div_lt_iff₀ hlam').mpr hu⟩
  · have hz : ⌊gs i / lam⌋₊ = 0 := Nat.eq_zero_of_not_pos hq
    filter_upwards [hupper] with eps hu
    rw [hz]
    apply Nat.floor_eq_zero.mpr
    apply (div_lt_one hlam').mpr
    simpa only [hz, Nat.cast_zero, zero_add, one_mul] using hu

/-- The derived finite floor-stability event and the existing actual
legality event admit the same positive epsilon. The missing cluster/sort
bridge must still identify the continuous trajectories with each actual
row's cyclic gaps before this lemma can assert row-score preservation. -/
theorem exists_legal_expansion_with_floor_stability {s m : ℕ}
    {P : Fin s → Bool} (c u : Fin s → Plane₂)
    {lam tau : ℝ} (hs : 3 ≤ s) (hleg : Section4Legality c lam)
    (axes : ActualPairExpansion.Axes c P u lam)
    (gs : Fin m → ℝ) (pert : Fin m → ℝ → ℝ)
    (hnonneg : ∀ i, 0 ≤ gs i)
    (hcont : ∀ i, ContinuousAt (pert i) 0)
    (hzero : ∀ i, pert i 0 = gs i)
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∃ eps : ℝ, 0 < eps ∧
        Section4Legality
          (ActualPairExpansion.Reindex.expandedCenters P
            (ActualPairExpansion.point c u eps)) lam' ∧
        ∀ i, ⌊pert i eps / lam'⌋₊ = ⌊gs i / lam⌋₊ := by
  obtain ⟨lam', htau', hsmall, hfloor⟩ :=
    exists_eventual_floor_stability gs pert hnonneg hcont hzero hleg.lam_pos htau0 htau
  have hlam' : 0 < lam' := htau0.trans htau'
  have hlegal := ActualPairExpansion.expansion_eventually_legality
    c u hs hleg axes hlam' hsmall
  have hpositive : ∀ᶠ eps in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
  have hfloor' : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ i,
      ⌊pert i eps / lam'⌋₊ = ⌊gs i / lam⌋₊ :=
    hfloor.filter_mono nhdsWithin_le_nhds
  obtain ⟨eps, heps, hleg', hfloors⟩ := (hpositive.and (hlegal.and hfloor')).exists
  exact ⟨lam', htau', hsmall, eps, heps, hleg', hfloors⟩

#print axioms continuousAt_projective_arg
#print axioms continuousAt_external_projective_ray
#print axioms same_parent_difference
#print axioms sibling_projective_ray_eq
#print axioms eventually_intercluster_order
#print axioms eventually_sorted_limit_of_sorted
#print axioms continuousAt_gapAfter_ofFn
#print axioms exists_eventual_floor_stability
#print axioms exists_legal_expansion_with_floor_stability

end Jsp404.ActualScorePreservingExpansion
