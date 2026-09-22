import Jsp000404.ConeCorridor
import Jsp000404.IntervalPacking

/-! # The cyclic-to-linear row bridge for a separated anchor direction -/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

lemma wrapGap_sorted_formula {l : List ℝ} (hs : l.SortedLE) (hne : l ≠ []) :
    wrapGap l hne = l.head hne + Real.pi - l.getLast hne := by
  unfold wrapGap
  split_ifs with hflat
  · have he := hflat (l.getLast hne) (List.getLast_mem hne)
    rw [he]
    ring
  · have hdiff : l.head hne ≠ l.getLast hne := by
      intro he
      exact hflat (fun x hx => eq_head_of_sortedLE hs hne he hx)
    have hle : l.head hne ≤ l.getLast hne := by
      rw [List.head_eq_getElem hne, List.getLast_eq_getElem hne]
      exact getElem_mono_of_sortedLE hs (Nat.zero_le _) (by
        have := List.length_pos_iff.mpr hne
        omega)
    unfold cyclicDiff
    rw [if_neg hdiff.symm, if_neg (not_lt.mpr hle)]
    ring

private lemma adjacent_scores_eq (lam : ℝ) : ∀ l : List ℝ, l.SortedLE →
    ((l.dropLast.zip l.tail).map (fun p => gapScore lam (cyclicDiff p.1 p.2))) =
      ((l.dropLast.zip l.tail).map (fun p => gapScore lam (p.2 - p.1))) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    cases l with
    | nil => intro _; rfl
    | cons b bs =>
      intro hs
      have hrest := (List.sortedLE_cons.mp hs).2
      have hab : a ≤ b := (List.sortedLE_cons.mp hs).1 b (by simp)
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b bs), List.tail_cons,
        List.zip_cons_cons, List.map_cons, List.map_cons,
        cyclicDiff_eq_sub_of_le hab]
      congr 1
      exact ih hrest

private lemma linearGapScore_eq_adjacent (lam right : ℝ) :
    ∀ (xs : List ℝ) (x : ℝ),
    linearGapScore lam x right xs =
      (((x :: xs).dropLast.zip (x :: xs).tail).map
        (fun p => gapScore lam (p.2 - p.1))).sum +
      gapScore lam (right - (x :: xs).getLast (List.cons_ne_nil _ _)) := by
  intro xs
  induction xs with
  | nil => intro x; simp [linearGapScore]
  | cons y ys ih =>
    intro x
    rw [linearGapScore, ih y,
      List.dropLast_cons_of_ne_nil (List.cons_ne_nil y ys)]
    simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons,
      List.getLast_cons (List.cons_ne_nil y ys)]
    omega

/-- The cyclic score of a sorted row starting at its anchor is exactly
the linear score closed at anchor + pi, including constant rows. -/
theorem rowScore_cons_eq_linear {xs : List ℝ} {x lam : ℝ}
    (hs : (x :: xs).SortedLE) :
    rowScore lam (x :: xs) = linearGapScore lam x (x + Real.pi) xs := by
  rw [rowScore, cycGaps_eq_map_append_wrap _ (List.cons_ne_nil _ _),
    List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  simp only [List.map_map, Function.comp_def]
  rw [adjacent_scores_eq lam _ hs, wrapGap_sorted_formula hs]
  rw [linearGapScore_eq_adjacent]
  simp

/-- In the constructed chart the anchor line is the first direction in
each remaining center's row. Removing it gives the actual subconfiguration. -/
theorem directionRow_anchor_cons {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin (s + 1) → Plane₂) (hc : Function.Injective c)
    (v : Fin (s + 1)) {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (theta : Fin s → ℝ)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (lam / 2) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hdir : ∀ i j : Fin s, i ≠ j →
      lam ≤ dirRep o e (c ∘ v.succAbove) i j) (i : Fin s) :
    directionRow o e c (v.succAbove i) =
      theta i :: directionRow o e (c ∘ v.succAbove) i := by
  classical
  have hne : c (v.succAbove i) - c v ≠ 0 :=
    sub_ne_zero.mpr (fun h => Fin.succAbove_ne v i (hc h))
  have hthetaPi : theta i ∈ Set.Ico 0 Real.pi :=
    ⟨(htheta i).1.1, by linarith [(htheta i).1.2]⟩
  have hanchor : dirRep o e c (v.succAbove i) v = theta i := by
    unfold dirRep
    rw [show c v - c (v.succAbove i) = -(c (v.succAbove i) - c v) by abel,
      o.oangle_neg_right he hne, linRep_add_pi, (htheta i).2]
    exact (eq_linRep_of_int_pi hthetaPi ⟨0, by simp⟩).symm
  have hmem : theta i ∈ directionRow o e c (v.succAbove i) :=
    (mem_directionRow o e c).mpr ⟨v, Fin.ne_succAbove v i, hanchor.symm⟩
  have herase : (directionRow o e c (v.succAbove i)).erase (theta i) =
      directionRow o e (c ∘ v.succAbove) i := by
    simpa only [hanchor] using (erase_directionRow o e (c' := c) v i).symm
  have hperm := List.perm_cons_erase hmem
  rw [herase] at hperm
  apply hperm.eq_of_sortedLE (directionRow_sorted o e c _)
  rw [List.sortedLE_cons]
  refine ⟨?_, directionRow_sorted o e _ _⟩
  intro x hx
  obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e (c ∘ v.succAbove)).mp hx
  have hlow := hdir i j hji.symm
  linarith [(htheta i).1.2]

theorem anchored_rowScore_eq_linear {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (c : Fin (s + 1) → Plane₂) (hc : Function.Injective c)
    (v : Fin (s + 1)) {lam : ℝ} (hlam : 0 < lam) (hlampi : lam < Real.pi)
    (theta : Fin s → ℝ)
    (htheta : ∀ i, theta i ∈ Set.Icc 0 (lam / 2) ∧
      o.oangle e (c (v.succAbove i) - c v) = (theta i : Real.Angle))
    (hdir : ∀ i j : Fin s, i ≠ j →
      lam ≤ dirRep o e (c ∘ v.succAbove) i j) (i : Fin s) :
    rowScore lam (directionRow o e c (v.succAbove i)) =
      linearGapScore lam (theta i) (theta i + Real.pi)
        (directionRow o e (c ∘ v.succAbove) i) := by
  have hrow := directionRow_anchor_cons o e he c hc v hlam hlampi theta htheta hdir i
  have hsort := directionRow_sorted o e c (v.succAbove i)
  rw [hrow] at hsort ⊢
  exact rowScore_cons_eq_linear hsort

#print axioms rowScore_cons_eq_linear
#print axioms anchored_rowScore_eq_linear

end Jsp404
