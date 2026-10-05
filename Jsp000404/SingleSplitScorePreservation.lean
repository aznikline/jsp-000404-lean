import Jsp000404.SafeFanReference
import Jsp000404.UniformFanScoreStability
import Jsp000404.Reindex
import Jsp000404.ChartInvariance
import Jsp000404.PositiveRowFan

/-! Genuine single-positive-parent splitting with exact potential preservation.
The endpoint axis, references, normalized actual fan families, and their
limiting old-star/old-star-plus-axis identities are constructed internally.
An arbitrary admissible-axis helper preserves limiting scores only; the
complete positive-row theorem chooses the end-lambda axis and proves the
two one-unit score decrements before the actual potential equality.
-/

open Filter Topology
open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.SingleSplitScorePreservation

def selected {s : ℕ} (v : Fin s) (i : Fin s) : Bool := decide (i = v)

abbrev Copies {s : ℕ} (v : Fin s) := ActualPairExpansion.Copy (selected v)

theorem countPairs_selected {s : ℕ} (v : Fin s) :
    ActualPairExpansion.Reindex.countPairs (selected v) = 1 := by
  classical
  have hfilter : (Finset.univ.filter (fun i => selected v i = true)) = {v} := by
    ext i
    simp [selected]
  rw [ActualPairExpansion.Reindex.countPairs, hfilter]
  simp

/-- Exactly the selected original parent has two children; all others have one. -/
noncomputable def index {s : ℕ} (v : Fin s) : Copies v ≃ Fin (s + 1) :=
  Fintype.equivFinOfCardEq (by
    simpa only [countPairs_selected] using ActualPairExpansion.Reindex.card_index (selected v))

/-- A genuine single-parent perturbation, enumerated on exactly s+1 points. -/
noncomputable def points {s : ℕ} (v : Fin s) (c : Fin s → Plane₂)
    (u : Plane₂) (eps : ℝ) : Fin (s + 1) → Plane₂ :=
  ActualPairExpansion.Reindex.transport (index v)
    (ActualPairExpansion.point c (fun _ => u) eps)

/-- Sibling rays are normalized by removing the positive perturbation
scale; external rays keep their actual difference trajectory. -/
noncomputable def normalizedDifference {s : ℕ} {P : Fin s → Bool}
    (c : Fin s → Plane₂) (u : Plane₂) (eps : ℝ)
    (x y : ActualPairExpansion.Copy P) : Plane₂ :=
  if x.1 = y.1 then ((y.2.val : ℝ) - (x.2.val : ℝ)) • u
  else ActualPairExpansion.point c (fun _ => u) eps y -
    ActualPairExpansion.point c (fun _ => u) eps x

theorem continuous_normalizedDifference {s : ℕ} {P : Fin s → Bool}
    (c : Fin s → Plane₂) (u : Plane₂) (x y : ActualPairExpansion.Copy P) :
    Continuous (fun eps => normalizedDifference c u eps x y) := by
  by_cases hb : x.1 = y.1
  · have hc : Continuous (fun _ : ℝ => ((y.2.val : ℝ) - (x.2.val : ℝ)) • u) :=
      continuous_const
    simpa only [normalizedDifference, ite_eq_left hb] using hc
  · have hc : Continuous (fun eps => ActualPairExpansion.point c (fun _ => u) eps y -
        ActualPairExpansion.point c (fun _ => u) eps x) :=
      (ActualPairExpansion.continuous_point c (fun _ => u) y).sub
        (ActualPairExpansion.continuous_point c (fun _ => u) x)
    simpa only [normalizedDifference, ite_eq_right hb] using hc

/-- Every limiting normalized outgoing ray is genuinely nonzero. A sibling
uses a nonzero child-value difference, not its zero actual vector at eps=0. -/
theorem normalizedDifference_zero_ne {s : ℕ} {P : Fin s → Bool}
    (c : Fin s → Plane₂) (hinj : Function.Injective c) (u : Plane₂) (hu : u ≠ 0)
    (x y : ActualPairExpansion.Copy P) (hxy : x ≠ y) :
    normalizedDifference c u 0 x y ≠ 0 := by
  by_cases hb : x.1 = y.1
  · rw [normalizedDifference, ite_eq_left hb]
    rcases x with ⟨i, a⟩
    rcases y with ⟨j, b⟩
    dsimp at hb
    subst j
    have hab : a ≠ b := fun h => hxy (congrArg (Sigma.mk i) h)
    have hval : b.val ≠ a.val := fun h => hab (Fin.ext h.symm)
    have hvalR : (b.val : ℝ) ≠ (a.val : ℝ) := by exact_mod_cast hval
    exact smul_ne_zero (sub_ne_zero.mpr hvalR) hu
  · rw [normalizedDifference, ite_eq_right hb,
      ActualPairExpansion.point_zero, ActualPairExpansion.point_zero]
    exact sub_ne_zero.mpr (hinj.ne (Ne.symm hb))

/-- At every positive actual scale, normalization preserves the actual
projective ray. No fan-identification hypothesis is supplied by the caller. -/
theorem normalizedDifference_projective_eq {s : ℕ} {P : Fin s → Bool}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) (u : Plane₂) (x y : ActualPairExpansion.Copy P)
    {eps : ℝ} (heps : 0 < eps) :
    linRep (o.oangle e (normalizedDifference c u eps x y)) =
      linRep (o.oangle e (ActualPairExpansion.point c (fun _ => u) eps y -
        ActualPairExpansion.point c (fun _ => u) eps x)) := by
  by_cases hb : x.1 = y.1
  · simpa only [normalizedDifference, ite_eq_left hb] using
      (ActualScorePreservingExpansion.sibling_projective_ray_eq
        o e c (fun _ => u) x y hb heps).symm
  · simp only [normalizedDifference, ite_eq_right hb]

/-- The same fixed label count s enumerates every new row's outgoing rays. -/
noncomputable def outgoing {s : ℕ} (v : Fin s) (c : Fin s → Plane₂)
    (u : Plane₂) (eps : ℝ) (r : Fin (s + 1)) (j : Fin s) : Plane₂ :=
  normalizedDifference c u eps ((index v).symm r) ((index v).symm (r.succAbove j))

noncomputable def coordinates {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (v : Fin s) (c : Fin s → Plane₂) (u : Plane₂)
    (ref : Fin (s + 1) → Plane₂) (eps : ℝ) (r : Fin (s + 1)) (j : Fin s) : ℝ :=
  linRep (o.oangle (ref r) (outgoing v c u eps r j))

/-- The internally sorted tuple equals the ordinary multiplicity-preserving
list sort. This does not require distinct coordinate values. -/
theorem sortedFan_eq_insertionSort {n : ℕ} (a : Fin n → ℝ) :
    FiniteFanScoreStability.sortedFan a = (List.ofFn a).insertionSort (· ≤ ·) := by
  apply List.Perm.eq_of_sortedLE (FiniteFanScoreStability.sortedFan_sorted a)
    List.sortedLE_insertionSort
  exact ((Tuple.sort a).ofFn_comp_perm a).trans (List.perm_insertionSort _ _).symm

/-- Reference changes act on any nonzero vector ray, including a normalized
sibling vector. They do not require a realized point-star configuration. -/
theorem vector_reference_shift (o : Orientation ℝ Plane₂ (Fin 2))
    (e f w : Plane₂) (he : e ≠ 0) (hf : f ≠ 0) (hw : w ≠ 0) :
    linRep (o.oangle f w) =
      projectiveShift (linRep (o.oangle e f)) (linRep (o.oangle e w)) := by
  rw [projectiveShift_eq_cyclicDiff, cyclicDiff_linRep, o.oangle_sub_left he hf hw]

/-- A finite nonzero ray family's sorted cyclic score is reference invariant.
All multiplicities remain; no fake point difference at epsilon zero is used. -/
theorem nonzero_ray_family_score_reference_eq {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e f : Plane₂)
    (he : e ≠ 0) (hf : f ≠ 0) (V : Fin n → Plane₂) (hV : ∀ i, V i ≠ 0)
    (lam : ℝ) :
    rowScore lam (FiniteFanScoreStability.sortedFan (fun i => linRep (o.oangle f (V i)))) =
      rowScore lam (FiniteFanScoreStability.sortedFan (fun i => linRep (o.oangle e (V i)))) := by
  classical
  let xe : Fin n → ℝ := fun i => linRep (o.oangle e (V i))
  let xf : Fin n → ℝ := fun i => linRep (o.oangle f (V i))
  let cut := linRep (o.oangle e f)
  let shift : ℝ → ℝ := projectiveShift cut
  have htuple : xf = shift ∘ xe := by
    funext i
    exact vector_reference_shift o e f (V i) he hf (hV i)
  have hlist : List.ofFn xf = (List.ofFn xe).map shift := by
    rw [htuple]
    exact List.ofFn_comp' xe shift
  have pf : (FiniteFanScoreStability.sortedFan xf).Perm (List.ofFn xf) :=
    (Tuple.sort xf).ofFn_comp_perm xf
  rw [hlist] at pf
  have pe : (List.ofFn xe).Perm (FiniteFanScoreStability.sortedFan xe) :=
    ((Tuple.sort xe).ofFn_comp_perm xe).symm
  have hsort : FiniteFanScoreStability.sortedFan xf =
      ((FiniteFanScoreStability.sortedFan xe).map shift).insertionSort (· ≤ ·) := by
    apply List.Perm.eq_of_sortedLE (FiniteFanScoreStability.sortedFan_sorted xf)
      List.sortedLE_insertionSort
    exact (pf.trans (pe.map shift)).trans (List.perm_insertionSort _ _).symm
  change rowScore lam (FiniteFanScoreStability.sortedFan xf) =
    rowScore lam (FiniteFanScoreStability.sortedFan xe)
  rw [hsort]
  apply rowScore_sort_projectiveShift lam cut _ (FiniteFanScoreStability.sortedFan_sorted xe)
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
  exact linRep_mem_Ico _

/-- Membership in the internally sorted fan retains every original label. -/
theorem mem_sortedFan_iff {n : ℕ} (a : Fin n → ℝ) (x : ℝ) :
    x ∈ FiniteFanScoreStability.sortedFan a ↔ ∃ i, x = a i := by
  rw [sortedFan_eq_insertionSort, List.mem_insertionSort, List.mem_ofFn]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, h.symm⟩
  · rintro ⟨i, h⟩
    exact ⟨i, h.symm⟩

/-- Zero-gap multiplicities do not change a sorted cyclic score. This is
the proved dedup invariance, applied only after genuine fan membership is
identified; it does not deduplicate centers or rows of the potential. -/
theorem rowScore_eq_of_sorted_mem_iff (lam : ℝ) (l k : List ℝ)
    (hl : l.SortedLE) (hk : k.SortedLE) (hmem : ∀ x, x ∈ l ↔ x ∈ k) :
    rowScore lam l = rowScore lam k := by
  classical
  have hld : l.dedup.SortedLT :=
    (hl.pairwise.sublist l.dedup_sublist).sortedLE.sortedLT_of_nodup (List.nodup_dedup l)
  have hkd : k.dedup.SortedLT :=
    (hk.pairwise.sublist k.dedup_sublist).sortedLE.sortedLT_of_nodup (List.nodup_dedup k)
  have hd : l.dedup = k.dedup :=
    List.SortedLT.eq_of_mem_iff hld hkd (fun x => by simpa only [List.mem_dedup] using hmem x)
  rw [← rowScore_dedup lam hl, ← rowScore_dedup lam hk, hd]

/-- Both signs of any nonzero scalar give the same projective ray. -/
theorem projective_smul_eq (o : Orientation ℝ Plane₂ (Fin 2)) (e u : Plane₂)
    (he : e ≠ 0) (hu : u ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    linRep (o.oangle e (a • u)) = linRep (o.oangle e u) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · rw [o.oangle_smul_right_of_neg _ _ hneg, o.oangle_neg_right he hu, linRep_add_pi]
  · rw [o.oangle_smul_right_of_pos _ _ hpos]

/-- Every original center has its surviving zero-valued child. -/
noncomputable def originalCopy {s : ℕ} (v i : Fin s) : Copies v :=
  ⟨i, ⟨0, by cases selected v i <;> simp⟩⟩

noncomputable def extraCopy {s : ℕ} (v : Fin s) : Copies v :=
  ⟨v, ⟨1, by simp [selected]⟩⟩

/-- Unselected parents have only one child, so equal parents force equal
children. This is the actual single-split index structure, not a fan premise. -/
theorem same_parent_eq_of_not_selected {s : ℕ} {v : Fin s} {x y : Copies v}
    (hb : x.1 = y.1) (hv : x.1 ≠ v) : x = y := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  dsimp at hb hv
  subst j
  have hp : selected v i = false := by simp [selected, hv]
  have ha : a.val < 1 := by simpa only [hp, Bool.false_eq_true, ↓reduceIte] using a.isLt
  have hb' : b.val < 1 := by simpa only [hp, Bool.false_eq_true, ↓reduceIte] using b.isLt
  exact congrArg (Sigma.mk i) (Fin.ext (by omega : a.val = b.val))

/-- A cloned parent has a genuine other child along its axis. -/
theorem exists_sibling {s : ℕ} (v : Fin s) (x : Copies v) (hx : x.1 = v) :
    ∃ y : Copies v, y.1 = x.1 ∧ y ≠ x := by
  by_cases hval : x.2.val = 0
  · refine ⟨extraCopy v, hx.symm, ?_⟩
    intro h
    have h' := congrArg (fun z : Copies v => z.2.val) h
    simp [extraCopy, hval] at h'
  · refine ⟨originalCopy v v, hx.symm, ?_⟩
    intro h
    have h' := congrArg (fun z : Copies v => z.2.val) h
    apply hval
    simpa only [originalCopy] using h'.symm

/-- The outgoing enumeration covers each and only each other actual child. -/
theorem exists_outgoing_label {s : ℕ} (v : Fin s) (r : Fin (s + 1))
    (y : Copies v) (hy : y ≠ (index v).symm r) :
    ∃ j : Fin s, (index v).symm (r.succAbove j) = y := by
  have hneq : index v y ≠ r := by
    intro h
    apply hy
    simpa only [Equiv.symm_apply_apply] using congrArg (index v).symm h
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hneq
  refine ⟨j, ?_⟩
  rw [hj]
  exact (index v).symm_apply_apply y

/-- Distinct children of one parent have a nonzero axis coefficient. -/
theorem child_coefficient_ne {s : ℕ} {P : Fin s → Bool}
    (x y : ActualPairExpansion.Copy P) (hxy : x ≠ y) (hb : x.1 = y.1) :
    (y.2.val : ℝ) - (x.2.val : ℝ) ≠ 0 := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  dsimp at hb
  subst j
  have hab : a ≠ b := fun h => hxy (congrArg (Sigma.mk i) h)
  have hval : b.val ≠ a.val := fun h => hab (Fin.ext h.symm)
  apply sub_ne_zero.mpr
  exact_mod_cast hval

/-- A sibling's limiting normalized direction is exactly the supplied axis,
including the child whose normalized coefficient is negative. -/
theorem normalized_sibling_direction {s : ℕ} {P : Fin s → Bool}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin s → Plane₂) (u : Plane₂) (hu : u ≠ 0)
    (x y : ActualPairExpansion.Copy P) (hxy : x ≠ y) (hb : x.1 = y.1) :
    linRep (o.oangle e (normalizedDifference c u 0 x y)) = linRep (o.oangle e u) := by
  rw [normalizedDifference, ite_eq_left hb]
  exact projective_smul_eq o e u he hu (child_coefficient_ne x y hxy hb)

/-- At an unselected surviving center the limiting fan is exactly the old
star up to zero-gap direction multiplicities. The second copy of v is not
dropped as a point; only proved score-dedup invariance is used. -/
theorem limiting_other_row_score {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (v : Fin s)
    (c : Fin s → Plane₂) (u : Plane₂) (r : Fin (s + 1))
    (hv : ((index v).symm r).1 ≠ v) (lam : ℝ) :
    rowScore lam (FiniteFanScoreStability.sortedFan
      (fun j => linRep (o.oangle e (outgoing v c u 0 r j)))) =
      rowScore lam (directionRow o e c ((index v).symm r).1) := by
  classical
  apply rowScore_eq_of_sorted_mem_iff lam _ _
    (FiniteFanScoreStability.sortedFan_sorted _) (directionRow_sorted o e c _)
  intro t
  rw [mem_sortedFan_iff, mem_directionRow]
  constructor
  · rintro ⟨j, ht⟩
    let x := (index v).symm r
    let y := (index v).symm (r.succAbove j)
    have hxy : x ≠ y := (index v).symm.injective.ne (Fin.ne_succAbove r j)
    have hb : x.1 ≠ y.1 := fun h => hxy (same_parent_eq_of_not_selected h hv)
    refine ⟨y.1, Ne.symm hb, ?_⟩
    change t = linRep (o.oangle e (normalizedDifference c u 0 x y)) at ht
    rw [normalizedDifference, ite_eq_right hb,
      ActualPairExpansion.point_zero, ActualPairExpansion.point_zero] at ht
    exact ht
  · rintro ⟨k, hk, ht⟩
    let x := (index v).symm r
    let y := originalCopy v k
    have hy : y ≠ x := by
      intro h
      exact hk (congrArg (fun z : Copies v => z.1) h)
    obtain ⟨j, hj⟩ := exists_outgoing_label v r y hy
    refine ⟨j, ?_⟩
    change t = linRep (o.oangle e (normalizedDifference c u 0 x
      ((index v).symm (r.succAbove j))))
    rw [hj]
    have hb : x.1 ≠ y.1 := Ne.symm hk
    rw [normalizedDifference, ite_eq_right hb,
      ActualPairExpansion.point_zero, ActualPairExpansion.point_zero]
    exact ht

/-- At either cloned center the true normalized limiting star is the old
star plus the supplied axis, retaining all original directions. No caller
supplies the star identity, and no endpoint score decrement is assumed. -/
theorem limiting_cloned_row_score {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0) (v : Fin s)
    (c : Fin s → Plane₂) (u : Plane₂) (hu : u ≠ 0) (r : Fin (s + 1))
    (hv : ((index v).symm r).1 = v) (lam : ℝ) :
    rowScore lam (FiniteFanScoreStability.sortedFan
      (fun j => linRep (o.oangle e (outgoing v c u 0 r j)))) =
      rowScore lam ((directionRow o e c v ++ [linRep (o.oangle e u)]).insertionSort (· ≤ ·)) := by
  classical
  apply rowScore_eq_of_sorted_mem_iff lam _ _
    (FiniteFanScoreStability.sortedFan_sorted _) List.sortedLE_insertionSort
  intro t
  rw [mem_sortedFan_iff, List.mem_insertionSort, List.mem_append, List.mem_singleton,
    mem_directionRow]
  constructor
  · rintro ⟨j, ht⟩
    let x := (index v).symm r
    let y := (index v).symm (r.succAbove j)
    have hxy : x ≠ y := (index v).symm.injective.ne (Fin.ne_succAbove r j)
    change t = linRep (o.oangle e (normalizedDifference c u 0 x y)) at ht
    by_cases hb : x.1 = y.1
    · right
      rw [normalized_sibling_direction o e he c u hu x y hxy hb] at ht
      exact ht

    · left
      have hyv : y.1 ≠ v := by
        intro h
        exact hb (hv.trans h.symm)
      refine ⟨y.1, hyv, ?_⟩
      rw [normalizedDifference, ite_eq_right hb,
        ActualPairExpansion.point_zero, ActualPairExpansion.point_zero, hv] at ht
      exact ht
  · rintro (⟨k, hk, ht⟩ | ht)
    · let x := (index v).symm r
      let y := originalCopy v k
      have hy : y ≠ x := by
        intro h
        apply hk
        exact (congrArg (fun z : Copies v => z.1) h).trans hv
      obtain ⟨j, hj⟩ := exists_outgoing_label v r y hy
      refine ⟨j, ?_⟩
      change t = linRep (o.oangle e (normalizedDifference c u 0 x
        ((index v).symm (r.succAbove j))))
      rw [hj]
      have hb : x.1 ≠ y.1 := by
        intro h
        exact hk (h.symm.trans hv)
      rw [normalizedDifference, ite_eq_right hb,
        ActualPairExpansion.point_zero, ActualPairExpansion.point_zero, hv]
      exact ht
    · let x := (index v).symm r
      obtain ⟨y, hyparent, hy⟩ := exists_sibling v x hv
      obtain ⟨j, hj⟩ := exists_outgoing_label v r y hy
      refine ⟨j, ?_⟩
      change t = linRep (o.oangle e (normalizedDifference c u 0 x
        ((index v).symm (r.succAbove j))))
      rw [hj, normalized_sibling_direction o e he c u hu x y (Ne.symm hy) hyparent.symm]
      exact ht

/-- The actual full-circle wrap formula includes the all-equal case. -/
theorem wrapGap_eq_head_add_pi_sub_last {l : List ℝ} (hs : l.SortedLE) (hne : l ≠ []) :
    wrapGap l hne = l.head hne + Real.pi - l.getLast hne := by
  classical
  by_cases hall : ∀ x ∈ l, x = l.head hne
  · have hlast := hall _ (List.getLast_mem hne)
    rw [wrapGap, ite_eq_left hall, hlast]
    ring
  · have hle : l.head hne ≤ l.getLast hne := hs.pairwise.rel_head (List.getLast_mem hne)
    have hneq : l.head hne ≠ l.getLast hne := by
      intro h
      apply hall
      intro x hx
      have hlo := hs.pairwise.rel_head hx
      have hhi := hs.pairwise.rel_getLast hx
      rw [← h] at hhi
      exact le_antisymm hhi hlo
    rw [wrapGap, ite_eq_right hall]
    unfold cyclicDiff
    rw [ite_eq_right (Ne.symm hneq), ite_eq_right (not_lt_of_ge hle)]
    ring

/-- Insert the end-lambda axis into the genuine wrap of a sorted fan.
The old first coordinate a may be strictly inside the empty gap. Both
incident gaps are exactly H-lambda and lambda, even when H=pi. -/
theorem end_split_rowScore {l : List ℝ} {lam a : ℝ}
    (hlam : 0 < lam) (ha0 : 0 ≤ a) (halam : a < lam)
    (hs : l.SortedLE) (hne : l ≠ []) (hhead : l.head hne = a)
    (hb : ∀ x ∈ l, a ≤ x ∧ x ≤ a + Real.pi - 2 * lam) :
    rowScore lam (l ++ [a + Real.pi - lam]) + 1 = rowScore lam l := by
  classical
  let H := a + Real.pi - l.getLast hne
  let axis := a + Real.pi - lam
  have hlast := hb _ (List.getLast_mem hne)
  have hpi : 2 * lam ≤ Real.pi := by linarith [hlast.1, hlast.2]
  have haxis0 : 0 < axis := by dsimp [axis]; linarith
  have haxispi : axis < Real.pi := by dsimp [axis]; linarith
  have haxislast : l.getLast hne < axis := by dsimp [axis]; linarith [hlast.2]
  have hlast0 : 0 ≤ l.getLast hne := ha0.trans hlast.1
  have hlastpi : l.getLast hne < Real.pi := by linarith [hlast.2]
  have hapi : a < Real.pi := by linarith
  have hH : 2 * lam ≤ H := by dsimp [H]; linarith [hlast.2]
  have hwold : wrapGap l hne = H := by
    rw [wrapGap_eq_head_add_pi_sub_last hs hne, hhead]
  have hnotall : ¬∀ x ∈ axis :: l, x = (axis :: l).head (List.cons_ne_nil _ _) := by
    intro hall
    have hh := hall (l.head hne) (List.mem_cons.mpr (Or.inr (List.head_mem hne)))
    simp only [List.head_cons, hhead] at hh
    dsimp [axis] at hh
    linarith
  have hwnew : wrapGap (axis :: l) (List.cons_ne_nil _ _) = H - lam := by
    rw [wrapGap, ite_eq_right hnotall, List.getLast_cons hne, List.head_cons]
    unfold cyclicDiff
    rw [ite_eq_right (ne_of_lt haxislast), ite_eq_left haxislast]
    dsimp [axis, H]
    ring
  have hout : cyclicDiff axis (l.head hne) = lam := by
    rw [hhead]
    have haa : a < axis := by dsimp [axis]; linarith
    unfold cyclicDiff
    rw [ite_eq_right (Ne.symm (ne_of_lt haa)), ite_eq_right (not_lt_of_ge haa.le)]
    dsimp [axis]
    ring
  have hmerge : wrapGap l hne =
      wrapGap (axis :: l) (List.cons_ne_nil _ _) + cyclicDiff axis (l.head hne) := by
    rw [hwold, hwnew, hout]
    ring
  have hgain : mergeGain lam (H - lam) lam = 1 := by
    have hsplit := GapSplitFloorStability.floor_score_end_split hlam hH
    change gapScore lam lam + gapScore lam (H - lam) + 1 = gapScore lam H at hsplit
    unfold mergeGain
    rw [show (H - lam) + lam = H by ring]
    omega
  have herase := rowScore_erase_head' hlam hne haxis0.le haxispi
    (by rw [hhead]; exact ha0) (by rw [hhead]; exact hapi) hlast0 hlastpi hmerge
  rw [hwnew, hout, hgain] at herase
  have hrot : (axis :: l).rotate 1 = l ++ [axis] := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, List.rotate_cons_succ, List.rotate_zero]
  have hscore : rowScore lam (l ++ [axis]) = rowScore lam (axis :: l) := by
    simpa only [hrot] using rowScore_rotate lam (axis :: l) 1
  change rowScore lam (l ++ [axis]) + 1 = rowScore lam l
  rw [hscore]
  exact herase.symm

noncomputable def endAxis (o : Orientation ℝ Plane₂ (Fin 2))
    (r : Plane₂) (lam : ℝ) : Plane₂ :=
  o.rotation ((Real.pi - lam : ℝ) : Real.Angle) r

theorem endAxis_ne_zero (o : Orientation ℝ Plane₂ (Fin 2))
    {r : Plane₂} (hr : r ≠ 0) (lam : ℝ) : endAxis o r lam ≠ 0 := by
  intro h
  exact hr ((o.rotation ((Real.pi - lam : ℝ) : Real.Angle)).injective
    (by simpa only [endAxis, map_zero] using h))

/-- The specifically constructed end axis has both caps against a ray in
the complementary occupied window. This is not a midpoint-axis claim. -/
theorem endAxis_angle_bounds (o : Orientation ℝ Plane₂ (Fin 2))
    {r w : Plane₂} (hr : r ≠ 0) (hw : w ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hwindow : linRep (o.oangle r w) ∈ Set.Icc 0 (Real.pi - 2 * lam)) :
    lam ≤ InnerProductGeometry.angle (endAxis o r lam) w ∧
      InnerProductGeometry.angle (endAxis o r lam) w ≤ Real.pi - lam := by
  let phi := linRep (o.oangle r w)
  have hphi : phi ∈ Set.Icc 0 (Real.pi - 2 * lam) := hwindow
  have hu : endAxis o r lam ≠ 0 := endAxis_ne_zero o hr lam
  have haxis : o.oangle r (endAxis o r lam) = ((Real.pi - lam : ℝ) : Real.Angle) :=
    o.oangle_rotation_self_right hr _
  have ha : Real.pi - lam ∈ Set.Ico 0 Real.pi := by
    constructor <;> linarith [hphi.1, hphi.2]
  have hp : phi ∈ Set.Ico 0 Real.pi := ⟨hphi.1, by linarith [hphi.2]⟩
  have hdirect (z : Plane₂) (hz : z ≠ 0) (hdir : o.oangle r z = (phi : Real.Angle)) :
      lam ≤ InnerProductGeometry.angle (endAxis o r lam) z ∧
        InnerProductGeometry.angle (endAxis o r lam) z ≤ Real.pi - lam := by
    rw [angle_eq_abs_of_half_plane_chart o hr hu hz ha hp haxis hdir,
      abs_of_nonpos (by linarith [hphi.2])]
    constructor <;> linarith [hphi.1, hphi.2]
  rcases linRep_class (o.oangle r w) with hdir | hdir
  · exact hdirect w hw hdir.symm
  · have hn : o.oangle r (-w) = (phi : Real.Angle) := by
      rw [o.oangle_neg_right hr hw]
      exact hdir.symm
    have h := hdirect (-w) (neg_ne_zero.mpr hw) hn
    rw [InnerProductGeometry.angle_neg_right] at h
    constructor <;> linarith [h.1, h.2]

/-- An actual positive row internally supplies its end axis and a static
post-gap calculation reference. That reference is used only to calculate
scores; the continuity argument uses the separately constructed safe refs. -/
theorem exists_endpoint_split_data {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin s → Plane₂) {lam : ℝ} (hleg : Section4Legality c lam)
    (v : Fin s) (hpos : 0 < rowScore lam (directionRow o e c v)) :
    ∃ r u : Plane₂, r ≠ 0 ∧ u ≠ 0 ∧
      (∀ x ∈ directionRow o r c v, 0 ≤ x ∧ x ≤ Real.pi - 2 * lam) ∧
      0 ∈ directionRow o r c v ∧
      linRep (o.oangle r u) = Real.pi - lam ∧
      ∀ j, j ≠ v → InnerProductGeometry.angle u (c j - c v) ≤ Real.pi - lam ∧
        InnerProductGeometry.angle (-u) (c j - c v) ≤ Real.pi - lam := by
  obtain ⟨G, hG, hbig⟩ := PositiveRowFan.exists_big_gap_of_rowScore_pos hleg.lam_pos hpos
  obtain ⟨cut, hcut, hwindow⟩ := PositiveRowFan.exists_shift_window_of_gap
    (directionRow_sorted o e c v) (fun _ hx => directionRow_mem_Ico o e c hx) hG
  obtain ⟨z, hz, hcutz⟩ := (mem_directionRow o e c).mp hcut
  let r := c z - c v
  have hr : r ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hz)
  have hw (j : Fin s) (hj : j ≠ v) :
      linRep (o.oangle r (c j - c v)) ∈ Set.Icc 0 (Real.pi - 2 * lam) := by
    have h := (hwindow _ ((mem_directionRow o e c).mpr ⟨j, hj, rfl⟩)).2
    rw [hcutz] at h
    have hshift := dirRep_reference_shift o e r he hr c hleg.inj hj.symm
    change dirRep o r c v j ∈ _
    refine ⟨(linRep_mem_Ico _).1, ?_⟩
    rw [hshift]
    change projectiveShift (dirRep o e c v z) (dirRep o e c v j) ≤ _
    linarith
  let u := endAxis o r lam
  have hu : u ≠ 0 := endAxis_ne_zero o hr lam
  have hperiod : 2 * lam ≤ Real.pi := by
    have h := hw z hz
    linarith [h.1, h.2]
  have hdir : linRep (o.oangle r u) = Real.pi - lam := by
    have hangle : o.oangle r u = ((Real.pi - lam : ℝ) : Real.Angle) :=
      o.oangle_rotation_self_right hr _
    rw [hangle]
    apply (eq_linRep_of_int_pi
      (by constructor <;> linarith [hleg.lam_pos] : Real.pi - lam ∈ Set.Ico 0 Real.pi)
      ⟨0, by simp⟩).symm
  refine ⟨r, u, hr, hu, ?_, ?_, hdir, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_directionRow o r c).mp hx
    exact hw j hj
  · apply (mem_directionRow o r c).mpr
    refine ⟨z, hz, ?_⟩
    change 0 = linRep (o.oangle r r)
    rw [o.oangle_self]
    simp [linRep]
  · intro j hj
    have h := endAxis_angle_bounds o hr (sub_ne_zero.mpr (hleg.inj.ne hj))
      hleg.lam_pos (hw j hj)
    exact ⟨h.2, by rw [InnerProductGeometry.angle_neg_left]; linarith [h.1]⟩

/-- A sorted actual row is exactly the internally sorted outgoing tuple;
the proof retains each outgoing point and all repeated direction values. -/
theorem directionRow_eq_sortedOutgoing {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (p : Fin (s + 1) → Plane₂) (r : Fin (s + 1)) :
    directionRow o e p r = FiniteFanScoreStability.sortedFan
      (fun j : Fin s => dirRep o e p r (r.succAbove j)) := by
  classical
  let q : Fin s → ℝ := fun j => dirRep o e p r (r.succAbove j)
  unfold directionRow
  rw [← finRange_map_succAbove r, List.map_map, ← List.ofFn_eq_map]
  apply List.Perm.eq_of_sortedLE List.sortedLE_insertionSort
    (FiniteFanScoreStability.sortedFan_sorted q)
  exact (List.perm_insertionSort _ _).trans ((Tuple.sort q).ofFn_comp_perm q).symm

/-- Actual positive-epsilon rows coincide with the internally constructed
continuous normalized fan, rather than merely sharing its direction set. -/
theorem normalizedFan_eq_actual_directionRow {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (v : Fin s)
    (c : Fin s → Plane₂) (u : Plane₂) (ref : Fin (s + 1) → Plane₂)
    (r : Fin (s + 1)) {eps : ℝ} (heps : 0 < eps) :
    directionRow o (ref r) (points v c u eps) r =
      FiniteFanScoreStability.sortedFan (coordinates o v c u ref eps r) := by
  rw [directionRow_eq_sortedOutgoing]
  have htuple : (fun j : Fin s => dirRep o (ref r) (points v c u eps) r (r.succAbove j)) =
      coordinates o v c u ref eps r := by
    funext j
    simpa only [dirRep, points, ActualPairExpansion.Reindex.transport,
      Function.comp_apply, coordinates, outgoing] using
      (normalizedDifference_projective_eq o (ref r) c u
        ((index v).symm r) ((index v).symm (r.succAbove j)) heps).symm
  rw [htuple]

/-- Every row's safe reference, limiting strict range, and coordinate
continuity are constructed from its actual normalized vector family. -/
theorem exists_safe_normalized_coordinates {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (v : Fin s) (hs : 0 < s)
    (c : Fin s → Plane₂) (hinj : Function.Injective c) (u : Plane₂) (hu : u ≠ 0) :
    ∃ ref : Fin (s + 1) → Plane₂,
      (∀ r, ref r ≠ 0) ∧
      (∀ r j, coordinates o v c u ref 0 r j ∈ Set.Ioo 0 Real.pi) ∧
      ∀ r j, ContinuousAt (fun eps => coordinates o v c u ref eps r j) 0 := by
  classical
  let : NeZero s := ⟨by omega⟩
  have hrow (r : Fin (s + 1)) : ∃ e : Plane₂, e ≠ 0 ∧
      (∀ j, linRep (o.oangle e (outgoing v c u 0 r j)) ∈ Set.Ioo 0 Real.pi) ∧
      ∀ j, ContinuousAt (fun eps => linRep (o.oangle e (outgoing v c u eps r j))) 0 := by
    apply SafeFanReference.exists_safe_continuous_coordinates o
      (fun eps j => outgoing v c u eps r j)
    · intro j
      exact (continuous_normalizedDifference c u
        ((index v).symm r) ((index v).symm (r.succAbove j))).continuousAt
    · intro j
      exact normalizedDifference_zero_ne c hinj u hu
        ((index v).symm r) ((index v).symm (r.succAbove j))
        ((index v).symm.injective.ne (Fin.ne_succAbove r j))
  choose ref href hrange hcont using hrow
  exact ⟨ref, href, hrange, hcont⟩

/-- Genuine actual single-parent split with all rows sharing a legal
positive scale and one parameter. Their scores equal the internally built
limiting normalized fan scores. This theorem does not claim those limiting
scores are old-score-minus-one for an arbitrary admissible axis. -/
theorem exists_legal_split_with_limit_scores {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (v : Fin s) (hs : 3 ≤ s)
    (c : Fin s → Plane₂) {lam tau : ℝ} (hleg : Section4Legality c lam)
    (u : Plane₂) (hu : u ≠ 0)
    (hcap : ∀ j, j ≠ v →
      InnerProductGeometry.angle u (c j - c v) ≤ Real.pi - lam ∧
        InnerProductGeometry.angle (-u) (c j - c v) ≤ Real.pi - lam)
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ ref : Fin (s + 1) → Plane₂, (∀ r, ref r ≠ 0) ∧
      ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
        ∃ eps : ℝ, 0 < eps ∧ Section4Legality (points v c u eps) lam' ∧
          ∀ r, rowScore lam' (directionRow o (ref r) (points v c u eps) r) =
            rowScore lam (FiniteFanScoreStability.sortedFan (coordinates o v c u ref 0 r)) := by
  obtain ⟨ref, href, hrange, hcont⟩ :=
    exists_safe_normalized_coordinates o v (by omega) c hleg.inj u hu
  obtain ⟨lam', htau', hsmall, hscore⟩ :=
    UniformFanScoreStability.exists_uniform_sorted_score_stability (by omega : 0 < s)
      (coordinates o v c u ref) hcont hrange hleg.lam_pos htau0 htau
  have hlam' : 0 < lam' := htau0.trans htau'
  have axes : ActualPairExpansion.Axes c (selected v) (fun _ => u) lam := {
    nonzero := fun _ _ => hu
    bounds := by
      intro i hi j hji
      have hiv : i = v := by simpa only [selected, decide_eq_true_eq] using hi
      subst i
      exact hcap j hji }
  have hexp := ActualPairExpansion.eventually_expansion c (fun _ => u) hs hleg axes hsmall
  have hlegal : ∀ᶠ eps in 𝓝[>] (0 : ℝ), Section4Legality (points v c u eps) lam' :=
    hexp.mono fun _ h => ActualPairExpansion.Reindex.transport_legality (index v) hlam' h.1 h.2
  have hscores : ∀ᶠ eps in 𝓝[>] (0 : ℝ), ∀ r,
      rowScore lam' (FiniteFanScoreStability.sortedFan (coordinates o v c u ref eps r)) =
        rowScore lam (FiniteFanScoreStability.sortedFan (coordinates o v c u ref 0 r)) :=
    hscore.filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ eps in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
  obtain ⟨eps, heps, hleg', hsc⟩ := (hpositive.and (hlegal.and hscores)).exists
  refine ⟨ref, href, lam', htau', hsmall, eps, heps, hleg', ?_⟩
  intro r
  rw [normalizedFan_eq_actual_directionRow o v c u ref r heps]
  exact hsc r

/-- Complete genuine single-positive-row split. The endpoint axis, safe
references, actual fan identification, common scale, and all limiting score
identities are constructed internally. One new distinct point is added and
the original potential is preserved exactly. -/
theorem exists_single_positive_split_preserving_potential {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs : 3 ≤ s) (c : Fin s → Plane₂) {lam tau : ℝ}
    (hleg : Section4Legality c lam) (v : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c v))
    (htau0 : 0 < tau) (htau : tau < lam) :
    ∃ lam' : ℝ, tau < lam' ∧ lam' < lam ∧
      ∃ c' : Fin (s + 1) → Plane₂, Section4Legality c' lam' ∧
        potential lam' (directionRows o e c') = potential lam (directionRows o e c) := by
  classical
  obtain ⟨calcRef, u, hcalc, hu, hbounds, hzero, haxis, hcap⟩ :=
    exists_endpoint_split_data o e he c hleg v hpos
  let l := directionRow o calcRef c v
  have hsorted : l.SortedLE := directionRow_sorted o calcRef c v
  have hne : l ≠ [] := List.ne_nil_of_mem hzero
  have hhead : l.head hne = 0 := by
    exact le_antisymm (hsorted.pairwise.rel_head hzero) (hbounds _ (List.head_mem hne)).1
  have happ : (l ++ [Real.pi - lam]).SortedLE := by
    apply List.sortedLE_append.mpr
    refine ⟨hsorted, by simpa [List.sortedLE_cons] using (List.sortedLE_nil : ([] : List ℝ).SortedLE), ?_⟩
    intro x hx y hy
    have hy' : y = Real.pi - lam := List.mem_singleton.mp hy
    subst y
    have h := (hbounds x hx).2
    linarith [hleg.lam_pos]
  have hsortEq : (l ++ [Real.pi - lam]).insertionSort (· ≤ ·) = l ++ [Real.pi - lam] :=
    List.Perm.eq_of_sortedLE List.sortedLE_insertionSort happ (List.perm_insertionSort _ _)
  have hend : rowScore lam (l ++ [Real.pi - lam]) + 1 = rowScore lam l := by
    simpa only [zero_add] using end_split_rowScore hleg.lam_pos (le_refl (0 : ℝ))
      hleg.lam_pos hsorted hne hhead (by simpa only [zero_add] using hbounds)
  obtain ⟨ref, href, lam', htau', hsmall, eps, heps, hleg', hactual⟩ :=
    exists_legal_split_with_limit_scores o v hs c hleg u hu hcap htau0 htau
  let k : Fin s → ℕ := fun i => rowScore lam (directionRow o e c i)
  have hold : rowScore lam l = k v :=
    (rowScore_directionRow_reference_eq o e calcRef he hcalc c hleg.inj v lam).symm
  rw [hold] at hend
  have hV (r : Fin (s + 1)) (j : Fin s) : outgoing v c u 0 r j ≠ 0 :=
    normalizedDifference_zero_ne c hleg.inj u hu
      ((index v).symm r) ((index v).symm (r.succAbove j))
      ((index v).symm.injective.ne (Fin.ne_succAbove r j))
  have htable (r : Fin (s + 1)) :
      rowScore lam' (directionRow o e (points v c u eps) r) =
        if ((index v).symm r).1 = v then k v - 1 else k ((index v).symm r).1 := by
    have hg := (rowScore_directionRow_reference_eq o e (ref r) he (href r)
      (points v c u eps) hleg'.inj r lam').trans (hactual r)
    change rowScore lam' (directionRow o e (points v c u eps) r) =
      rowScore lam (FiniteFanScoreStability.sortedFan
        (fun j => linRep (o.oangle (ref r) (outgoing v c u 0 r j)))) at hg
    by_cases hv : ((index v).symm r).1 = v
    · have hswap := nonzero_ray_family_score_reference_eq o calcRef (ref r) hcalc (href r)
        (outgoing v c u 0 r) (hV r) lam
      rw [hswap, limiting_cloned_row_score o calcRef hcalc v c u hu r hv lam,
        haxis, hsortEq] at hg
      rw [ite_eq_left hv]
      omega
    · have hswap := nonzero_ray_family_score_reference_eq o e (ref r) he (href r)
        (outgoing v c u 0 r) (hV r) lam
      rw [hswap, limiting_other_row_score o e v c u r hv lam] at hg
      rw [ite_eq_right hv]
      exact hg
  let W : Copies v → ℕ := fun x => if x.1 = v then 2 ^ (k v - 1) else 2 ^ k x.1
  have hk : 1 ≤ k v := by dsimp [k]; omega
  have hpow : 2 * 2 ^ (k v - 1) = 2 ^ k v := by
    calc
      2 * 2 ^ (k v - 1) = 2 ^ (k v - 1) * 2 := Nat.mul_comm _ _
      _ = 2 ^ ((k v - 1) + 1) := (pow_succ _ _).symm
      _ = 2 ^ k v := by rw [Nat.sub_add_cancel hk]
  have hmass : (∑ x : Copies v, W x) = potential lam (directionRows o e c) := by
    rw [Fintype.sum_sigma]
    change (∑ i : Fin s, ∑ _ : Fin (if selected v i then 2 else 1),
      if i = v then 2 ^ (k v - 1) else 2 ^ k i) = ∑ i : Fin s, 2 ^ k i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = v
    · subst i
      simpa [selected] using hpow
    · simp [selected, hi]
  refine ⟨lam', htau', hsmall, points v c u eps, hleg', ?_⟩
  calc
    potential lam' (directionRows o e (points v c u eps)) =
        ∑ r : Fin (s + 1), W ((index v).symm r) := by
      unfold potential exponentAt directionRows
      apply Finset.sum_congr rfl
      intro r _
      rw [htable r]
      dsimp [W]
      split_ifs <;> rfl
    _ = ∑ x : Copies v, W x := (index v).symm.sum_comp W
    _ = potential lam (directionRows o e c) := hmass

#print axioms countPairs_selected
#print axioms continuous_normalizedDifference
#print axioms normalizedDifference_zero_ne
#print axioms normalizedDifference_projective_eq
#print axioms sortedFan_eq_insertionSort
#print axioms vector_reference_shift
#print axioms nonzero_ray_family_score_reference_eq
#print axioms mem_sortedFan_iff
#print axioms rowScore_eq_of_sorted_mem_iff
#print axioms projective_smul_eq
#print axioms same_parent_eq_of_not_selected
#print axioms exists_sibling
#print axioms exists_outgoing_label
#print axioms child_coefficient_ne
#print axioms normalized_sibling_direction
#print axioms limiting_other_row_score
#print axioms limiting_cloned_row_score
#print axioms wrapGap_eq_head_add_pi_sub_last
#print axioms end_split_rowScore
#print axioms endAxis_ne_zero
#print axioms endAxis_angle_bounds
#print axioms exists_endpoint_split_data
#print axioms directionRow_eq_sortedOutgoing
#print axioms normalizedFan_eq_actual_directionRow
#print axioms exists_safe_normalized_coordinates
#print axioms exists_legal_split_with_limit_scores
#print axioms exists_single_positive_split_preserving_potential

end Jsp404.SingleSplitScorePreservation
