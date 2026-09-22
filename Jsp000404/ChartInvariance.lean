import Jsp000404.GeometricDeletion
import Mathlib.Data.List.TakeWhile

/-!
# Reference changes on the projective direction circle

A change of nonzero reference vector cuts the direction circle at a new
origin. The projective shift preserves each cyclic gap, including repeated
directions and the full-circle wrap gap of a constant row.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

noncomputable def projectiveShift (cut x : ℝ) : ℝ :=
  if x < cut then x - cut + Real.pi else x - cut

lemma projectiveShift_mem_Ico {cut x : ℝ}
    (hc : cut ∈ Set.Ico 0 Real.pi) (hx : x ∈ Set.Ico 0 Real.pi) :
    projectiveShift cut x ∈ Set.Ico 0 Real.pi := by
  unfold projectiveShift
  split_ifs <;> constructor <;> linarith [hc.1, hc.2, hx.1, hx.2]

lemma projectiveShift_injOn (cut : ℝ) :
    Set.InjOn (projectiveShift cut) (Set.Ico 0 Real.pi) := by
  intro x hx y hy h
  unfold projectiveShift at h
  split_ifs at h <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma projectiveShift_eq_cyclicDiff (cut x : ℝ) :
    projectiveShift cut x = cyclicDiff cut x := by
  by_cases h : cut = x
  · subst x; simp [projectiveShift, cyclicDiff]
  have h' : cut < x ∨ x < cut := lt_or_gt_of_ne h
  rcases h' with h' | h'
  · simp [projectiveShift, cyclicDiff, h, h', not_lt_of_ge h'.le]
  · simp [projectiveShift, cyclicDiff, h, h', not_lt_of_ge h'.le]
    ring

lemma cyclicDiff_projectiveShift {cut x y : ℝ}
    (hx : x ∈ Set.Ico 0 Real.pi) (hy : y ∈ Set.Ico 0 Real.pi) :
    cyclicDiff (projectiveShift cut x) (projectiveShift cut y) = cyclicDiff x y := by
  by_cases hxy : x = y
  · subst y; simp [cyclicDiff]
  have hxy' : projectiveShift cut x ≠ projectiveShift cut y :=
    fun h => hxy (projectiveShift_injOn cut hx hy h)
  simp only [cyclicDiff, ite_eq_right hxy, ite_eq_right hxy']
  unfold projectiveShift
  split_ifs <;>
    linarith [hx.1, hx.2, hy.1, hy.2]

lemma dirRep_reference_shift {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e f : Plane₂) (he : e ≠ 0) (hf : f ≠ 0) (c : Fin s → Plane₂)
    (hc : Function.Injective c) {i j : Fin s} (hij : i ≠ j) :
    dirRep o f c i j =
      projectiveShift (linRep (o.oangle e f)) (dirRep o e c i j) := by
  rw [projectiveShift_eq_cyclicDiff]
  unfold dirRep
  rw [cyclicDiff_linRep, o.oangle_sub_left he hf
    (sub_ne_zero.mpr (fun h => hij (hc h).symm))]

lemma wrapGap_projectiveShift {cut : ℝ} {l : List ℝ} (hl : l ≠ [])
    (hx : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) :
    wrapGap (l.map (projectiveShift cut)) (by simpa using hl) = wrapGap l hl := by
  have hh : l.head hl ∈ Set.Ico 0 Real.pi := hx _ (List.head_mem hl)
  have ht : l.getLast hl ∈ Set.Ico 0 Real.pi := hx _ (List.getLast_mem hl)
  have heq : (∀ x ∈ l.map (projectiveShift cut),
      x = (l.map (projectiveShift cut)).head (by simpa using hl)) ↔
      ∀ x ∈ l, x = l.head hl := by
    simp only [List.head_map, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro h x hx'
      exact projectiveShift_injOn cut (hx x hx') hh (h _ x hx' rfl)
    · intro h y x hx' hy
      rw [← hy, h x hx']
  unfold wrapGap
  by_cases h : ∀ x ∈ l, x = l.head hl
  · rw [ite_eq_left h, ite_eq_left (heq.mpr h)]
  · rw [ite_eq_right h, ite_eq_right ((not_congr heq).mpr h)]
    simp only [List.getLast_map, List.head_map]
    exact cyclicDiff_projectiveShift ht hh

lemma cycGaps_projectiveShift {cut : ℝ} (l : List ℝ)
    (hx : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) :
    cycGaps (l.map (projectiveShift cut)) = cycGaps l := by
  by_cases hl : l = []
  · simp [hl]
  rw [cycGaps_eq_map_append_wrap _ (by simpa using hl),
    cycGaps_eq_map_append_wrap _ hl, wrapGap_projectiveShift hl hx]
  congr 1
  rw [← List.map_dropLast, ← List.map_tail, List.zip_map, List.map_map]
  apply List.map_congr_left
  intro z hz
  exact cyclicDiff_projectiveShift
    (hx z.1 (List.mem_of_mem_dropLast (List.of_mem_zip hz).1))
    (hx z.2 (List.mem_of_mem_tail (List.of_mem_zip hz).2))

theorem rowScore_projectiveShift (lam cut : ℝ) (l : List ℝ)
    (hx : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) :
    rowScore lam (l.map (projectiveShift cut)) = rowScore lam l := by
  rw [rowScore, rowScore, cycGaps_projectiveShift l hx]

lemma insertionSort_projectiveShift (cut : ℝ) (l : List ℝ)
    (hs : l.SortedLE) (hrange : ∀ a ∈ l, a ∈ Set.Ico 0 Real.pi) :
    (l.map (projectiveShift cut)).insertionSort (· ≤ ·) =
      (l.rotate (l.takeWhile (fun a => decide (a < cut))).length).map
        (projectiveShift cut) := by
  classical
  let q : ℝ → Bool := fun a => decide (a < cut)
  let lo := l.takeWhile q
  let hi := l.dropWhile q
  have hsplit : lo ++ hi = l := List.takeWhile_append_dropWhile
  have hrot : l.rotate lo.length = hi ++ lo := by
    calc
      l.rotate lo.length = (lo ++ hi).rotate lo.length := by rw [hsplit]
      _ = hi ++ lo := List.rotate_append_length_eq lo hi
  have hlo : lo.Pairwise (· ≤ ·) :=
    hs.pairwise.sublist (List.takeWhile_sublist q)
  have hhi : hi.Pairwise (· ≤ ·) :=
    hs.pairwise.sublist (List.dropWhile_sublist q)
  have hlow {a : ℝ} (ha : a ∈ lo) : a < cut := by
    simpa [q] using (List.mem_takeWhile_imp (p := q) ha)
  have hhigh {a : ℝ} (ha : a ∈ hi) : cut ≤ a := by
    have hhead : cut ≤ hi.head (List.ne_nil_of_mem ha) := by
      simpa [hi, q] using
        (List.head_dropWhile_not q (l := l) (List.ne_nil_of_mem ha))
    exact hhead.trans (hhi.rel_head ha)
  have hlowShift {a : ℝ} (ha : a ∈ lo) :
      projectiveShift cut a = a - cut + Real.pi := by
    simp [projectiveShift, hlow ha]
  have hhighShift {a : ℝ} (ha : a ∈ hi) :
      projectiveShift cut a = a - cut := by
    simp [projectiveShift, not_lt.mpr (hhigh ha)]
  have hmlo : (lo.map (projectiveShift cut)).SortedLE := by
    apply List.Pairwise.sortedLE
    apply List.pairwise_map.mpr
    apply hlo.imp_of_mem
    intro a b ha hb hab
    rw [hlowShift ha, hlowShift hb]
    linarith
  have hmhi : (hi.map (projectiveShift cut)).SortedLE := by
    apply List.Pairwise.sortedLE
    apply List.pairwise_map.mpr
    apply hhi.imp_of_mem
    intro a b ha hb hab
    rw [hhighShift ha, hhighShift hb]
    linarith
  have hsorted : ((l.rotate lo.length).map (projectiveShift cut)).SortedLE := by
    rw [hrot, List.map_append]
    apply List.sortedLE_append.mpr
    refine ⟨hmhi, hmlo, ?_⟩
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    rw [hhighShift hx, hlowShift hy]
    have hxpi := (hrange x (List.dropWhile_subset q hx)).2
    have hy0 := (hrange y (List.takeWhile_subset q hy)).1
    linarith
  have hperm : ((l.rotate lo.length).map (projectiveShift cut)).Perm
      (l.map (projectiveShift cut)) := (List.rotate_perm l lo.length).map _
  exact List.Perm.eq_of_sortedLE List.sortedLE_insertionSort hsorted
    ((List.perm_insertionSort (· ≤ ·) (l.map (projectiveShift cut))).trans hperm.symm)

theorem rowScore_sort_projectiveShift (lam cut : ℝ) (l : List ℝ)
    (hs : l.SortedLE) (hx : ∀ x ∈ l, x ∈ Set.Ico 0 Real.pi) :
    rowScore lam ((l.map (projectiveShift cut)).insertionSort (· ≤ ·)) =
      rowScore lam l := by
  rw [insertionSort_projectiveShift cut l hs hx, List.map_rotate,
    rowScore_rotate, rowScore_projectiveShift lam cut l hx]

lemma directionRow_reference_shift {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (e f : Plane₂) (he : e ≠ 0) (hf : f ≠ 0) (c : Fin s → Plane₂)
    (hc : Function.Injective c) (i : Fin s) :
    directionRow o f c i =
      ((directionRow o e c i).map
        (projectiveShift (linRep (o.oangle e f)))).insertionSort (· ≤ ·) := by
  classical
  let shift := projectiveShift (linRep (o.oangle e f))
  have hraw : (((List.finRange s).erase i).map (fun j => dirRep o f c i j)) =
      (((List.finRange s).erase i).map (fun j => dirRep o e c i j)).map shift := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have hji := ((List.nodup_finRange s).mem_erase_iff.mp hj).1
    exact dirRep_reference_shift o e f he hf c hc hji.symm
  have hperm : (directionRow o f c i).Perm ((directionRow o e c i).map shift) := by
    unfold directionRow
    exact (List.perm_insertionSort _ _).trans
      (hraw ▸ ((List.perm_insertionSort _ _).map shift).symm)
  exact List.Perm.eq_of_sortedLE (directionRow_sorted o f c i)
    List.sortedLE_insertionSort
    (hperm.trans (List.perm_insertionSort _ _).symm)

/-- The actual cyclic gap score does not depend on the nonzero reference vector. -/
theorem rowScore_directionRow_reference_eq {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e f : Plane₂)
    (he : e ≠ 0) (hf : f ≠ 0) (c : Fin s → Plane₂)
    (hc : Function.Injective c) (i : Fin s) (lam : ℝ) :
    rowScore lam (directionRow o e c i) = rowScore lam (directionRow o f c i) := by
  rw [directionRow_reference_shift o e f he hf c hc i,
    rowScore_sort_projectiveShift lam _ _ (directionRow_sorted o e c i)
      (fun x hx => directionRow_mem_Ico o e c hx)]

theorem potential_directionRows_reference_eq {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e f : Plane₂)
    (he : e ≠ 0) (hf : f ≠ 0) (c : Fin s → Plane₂)
    (hc : Function.Injective c) (lam : ℝ) :
    potential lam (directionRows o e c) = potential lam (directionRows o f c) := by
  unfold potential exponentAt directionRows
  apply Finset.sum_congr rfl
  intro i _
  rw [rowScore_directionRow_reference_eq o e f he hf c hc i lam]

#print axioms dirRep_reference_shift
#print axioms rowScore_projectiveShift
#print axioms insertionSort_projectiveShift
#print axioms rowScore_directionRow_reference_eq
#print axioms potential_directionRows_reference_eq

end Jsp404
