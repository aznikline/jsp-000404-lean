import Jsp000404.RowGainCyclicIncident
import Jsp000404.GeomSkeleton
import Jsp000404.SaturatedNesting

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY actual outgoing-emission degree at an original observer.
All targets are actual original centers and their ordinal indices are
constructed internally. The indexed cyclic-incidence dependency must
pass its own strict and genuine normal checks before this consumer is
verified. No zero-row, minimum Model, merge arc or gain budget is assumed.
-/

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualPositiveGainTargetBudget

private theorem merged_span_ge_two_scale {lam x y : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hg : 1 ≤ mergeGain lam x y) :
    2 * lam ≤ x + y := by
  have hscore : 1 ≤ gapScore lam (x + y) := by
    unfold mergeGain at hg
    omega
  have hfloor : 2 ≤ ⌊(x + y) / lam⌋₊ := by
    unfold gapScore at hscore
    omega
  have hcast : (2 : ℝ) ≤ (⌊(x + y) / lam⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hreal : (2 : ℝ) ≤ (x + y) / lam :=
    hcast.trans (Nat.floor_le (div_nonneg (add_nonneg hx hy) hlam.le))
  exact (le_div_iff₀ hlam).mp hreal

private theorem emitting_positions_card_le_four {lam : ℝ} (hlam : 0 < lam)
    (hlo : Real.pi / 5 < lam) {l : List ℝ}
    (hs : l.SortedLE) (hnd : l.Nodup)
    (hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi) (h2 : 2 ≤ l.length)
    (T : Finset (Fin l.length))
    (hgain : ∀ k ∈ T, 1 ≤ rowGain lam l k.val) : T.card ≤ 4 := by
  classical
  have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
  let arc : Fin l.length → ℝ := fun k =>
    gapAfter l ((finRotate l.length).symm k) + gapAfter l k
  have hnonneg (k : Fin l.length) : 0 ≤ arc k :=
    add_nonneg (gapAfter_nonneg hs hall hne _) (gapAfter_nonneg hs hall hne _)
  have hlarge (k : Fin l.length) (hk : k ∈ T) : 2 * lam ≤ arc k := by
    have hg := hgain k hk
    rw [RowGainCyclicIncident.rowGain_eq_mergeGain_gapAfter hlam hs hnd hall h2 k] at hg
    exact merged_span_ge_two_scale hlam
      (gapAfter_nonneg hs hall hne _) (gapAfter_nonneg hs hall hne _) hg
  have htotal : (∑ k : Fin l.length, arc k) = 2 * Real.pi := by
    simp only [arc, Finset.sum_add_distrib]
    rw [(finRotate l.length).symm.sum_comp (gapAfter l)]
    simp only [gapAfter_sum hne]
    ring
  have hlower : (T.card : ℝ) * (2 * lam) ≤ ∑ k ∈ T, arc k := by
    calc
      _ = ∑ _k ∈ T, (2 * lam) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k hk => hlarge k hk)
  have hupper : (∑ k ∈ T, arc k) ≤ 2 * Real.pi := by
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun k _ _ => hnonneg k)
  by_contra hnot
  have hfive : 5 ≤ T.card := by omega
  have hfiveR : (5 : ℝ) ≤ T.card := by exact_mod_cast hfive
  have hm := mul_le_mul_of_nonneg_right hfiveR (by positivity : 0 ≤ 2 * lam)
  linarith only [hm, hlower, hupper, hlo, Real.pi_pos]

private theorem actual_dirRep_ne {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    {z a b : Fin s} (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) :
    dirRep o e c z a ≠ dirRep o e c z b := by
  intro heq
  have hang := angle_eq_dirRep o e c hs he hleg.inj z a b
  simp only [selfIdx_of_ne hs hza.symm, selfIdx_of_ne hs hzb.symm] at hang
  rw [heq, sub_self, abs_zero] at hang
  have hpos := EuclideanGeometry.angle_pos_of_not_collinear
    (legal_triple_not_collinear hleg hza.symm hab hzb)
  have hcap := hleg.triAngle a z b hza.symm hzb hab
  split_ifs at hang <;> linarith [hleg.lam_pos]

private theorem actual_directionRow_nodup {s : ℕ} (hs : 2 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (z : Fin s) : (directionRow o e c z).Nodup := by
  rw [← fanOrder_map_eq o e c z]
  apply List.Nodup.map_on ?_ (fanOrder_nodup o e c z)
  intro a ha b hb heq
  by_contra hab
  exact actual_dirRep_ne hs o e he hleg
    ((mem_fanOrder o e c).mp ha).symm ((mem_fanOrder o e c).mp hb).symm hab heq

/-- In an actual legal configuration above pi/5, any fixed original
observer emits toward at most four distinct original targets. This is
stronger than the original zero-observer/light-target subcase: no row
score, potential, minimum Model, direction order or incident arcs are
caller inputs. The actual target-to-row-index map is produced internally. -/
theorem actual_positive_gain_targets_card_le_four {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : Real.pi / 5 < lam) (z : Fin s) :
    ((Finset.univ.erase z).filter (fun q =>
      1 ≤ rowGain lam (directionRow o e c z) (deleteIndex o e c q z))).card ≤ 4 := by
  classical
  let T : Finset (Fin s) := (Finset.univ.erase z).filter (fun q =>
    1 ≤ rowGain lam (directionRow o e c z) (deleteIndex o e c q z))
  change T.card ≤ 4
  by_cases hs5 : s ≤ 5
  · have hsub : T ⊆ Finset.univ.erase z := fun _ hq => (Finset.mem_filter.mp hq).1
    have hc := Finset.card_le_card hsub
    have herase : (Finset.univ.erase z).card = s - 1 := by simp
    omega
  · have hs6 : 6 ≤ s := by omega
    let l := directionRow o e c z
    have hlength : l.length = s - 1 := directionRow_length o e c z
    have h2 : 2 ≤ l.length := by omega
    have hsort : l.SortedLE := directionRow_sorted o e c z
    have hmem : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi := fun b hb =>
      directionRow_mem_Ico o e c hb
    have hnd : l.Nodup := actual_directionRow_nodup (by omega : 2 ≤ s) o e he hleg z
    have hqz (q : {q : Fin s // q ∈ T}) : q.val ≠ z :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp q.property).1).1
    let ordinal : {q : Fin s // q ∈ T} → Fin l.length := fun q =>
      ⟨deleteIndex o e c q.val z, deleteIndex_lt o e c (hqz q).symm⟩
    have hord : Function.Injective ordinal := by
      intro a b hab
      apply Subtype.ext
      have hidx := congrArg Fin.val hab
      change (directionRow o e c z).idxOf (dirRep o e c z a.val) =
        (directionRow o e c z).idxOf (dirRep o e c z b.val) at hidx
      have hdirs := (List.idxOf_inj
        ((mem_directionRow o e c).mpr ⟨a.val, hqz a, rfl⟩)).mp hidx
      by_contra hne
      exact actual_dirRep_ne (by omega : 2 ≤ s) o e he hleg
        (hqz a).symm (hqz b).symm hne hdirs
    let S : Finset (Fin l.length) := T.attach.image ordinal
    have hScard : S.card = T.card := by
      change (T.attach.image ordinal).card = T.card
      rw [Finset.card_image_of_injective _ hord]
      exact Finset.card_attach
    have hgain (k : Fin l.length) (hk : k ∈ S) : 1 ≤ rowGain lam l k.val := by
      obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_filter.mp q.property).2
    have hbound := emitting_positions_card_le_four hleg.lam_pos hlo hsort hnd hmem h2 S hgain
    omega

#print axioms actual_positive_gain_targets_card_le_four

end Jsp404.ActualPositiveGainTargetBudget
