import Jsp000404.AnchoredRows
import Jsp000404.BinGraphs

/-!
# Row and interval counting between two anchor directions

If the two anchor directions are the first and last entries of a sorted
row, their outside wrap gap contributes no score when its size is less
than two lambda. The remaining score is exactly the linear gap score
between those anchors, so the existing empty-bin bound applies unchanged.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

lemma linearGapScore_append_singleton (lam left right last : ℝ) (xs : List ℝ) :
    linearGapScore lam left right (xs ++ [last]) =
      linearGapScore lam left last xs + gapScore lam (right - last) := by
  induction xs generalizing left with
  | nil => simp [linearGapScore]
  | cons x xs ih => simp [linearGapScore, ih, Nat.add_assoc]

/-- The two extreme anchor directions close the linear row. Their wrap
gap has score zero; the result also covers an empty intervening row. -/
theorem rowScore_two_anchors_eq_linear {lam a b : ℝ} {ds : List ℝ}
    (hlam : 0 < lam) (hwrap : a + b < 2 * lam)
    (hs : (a :: (ds ++ [Real.pi - b])).SortedLE) :
    rowScore lam (a :: (ds ++ [Real.pi - b])) =
      linearGapScore lam a (Real.pi - b) ds := by
  rw [rowScore_cons_eq_linear hs, linearGapScore_append_singleton]
  have hzero : gapScore lam (a + b) = 0 := by
    have h := gapScore_le_of_lt_mul hlam 0 (by simpa using hwrap)
    omega
  rw [show a + Real.pi - (Real.pi - b) = a + b by ring, hzero, Nat.add_zero]

/-- A two-anchor row is bounded by the unoccupied bins of its middle
directions. Closed endpoints and repeated directions are allowed. -/
theorem rowScore_two_anchors_le_empty_bins {lam a b start width : ℝ} {m : ℕ}
    (hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hwrap : a + b < 2 * lam)
    (hleft : start - a ≤ lam)
    (hright : (Real.pi - b) - (start + (m : ℝ) * width) ≤ lam)
    (ds : List ℝ) (hs : (a :: (ds ++ [Real.pi - b])).SortedLE)
    (hpos : ∀ x ∈ ds, x ∈ Set.Icc start (start + (m : ℝ) * width)) :
    rowScore lam (a :: (ds ++ [Real.pi - b])) ≤
      m - (ds.map (uniformBin start width m)).toFinset.card := by
  rw [rowScore_two_anchors_eq_linear (hw.trans hwidth) hwrap hs]
  apply linearGapScore_le_empty_of_interval hm hw hwidth hleft hright ds _ hpos
  exact ((hs.pairwise.of_cons).sublist (List.sublist_append_left ds [Real.pi - b])).sortedLE

/-- The actual weights of the remaining centers fit in the binary cube
provided their full rows have the stated two-anchor endpoints. The bin
graphs and their colorings are constructed from the original geometry. -/
theorem weighted_two_anchored_rows {s t m : ℕ} {lam start width : ℝ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (c : Fin s → Plane₂)
    (he : e ≠ 0) (hleg : Section4Legality c lam)
    (pick : Fin t → Fin s) (hpick : Function.Injective pick)
    (a b : Fin t → ℝ)
    (hrow : ∀ i, directionRow o e c (pick i) =
      a i :: (directionRow o e (c ∘ pick) i ++ [Real.pi - b i]))
    (hwrap : ∀ i, a i + b i < 2 * lam)
    (hm : 0 < m) (hw : 0 < width) (hwidth : width < lam)
    (hstart : 0 ≤ start) (hend : start + (m : ℝ) * width < Real.pi)
    (hleft : ∀ i, start - a i ≤ lam)
    (hright : ∀ i, (Real.pi - b i) - (start + (m : ℝ) * width) ≤ lam)
    (hpos : ∀ i j, i ≠ j → dirRep o e (c ∘ pick) i j ∈
      Set.Icc start (start + (m : ℝ) * width)) :
    ∑ i, 2 ^ rowScore lam (directionRow o e c (pick i)) ≤ 2 ^ m := by
  have hangle : ∀ i j k : Fin t, i ≠ j → i ≠ k → j ≠ k →
      ∠ ((c ∘ pick) i) ((c ∘ pick) j) ((c ∘ pick) k) ≤ Real.pi - lam := by
    intro i j k hij hik hjk
    exact hleg.triAngle _ _ _ (hpick.ne hij) (hpick.ne hjk) (hpick.ne hik)
  have hbins := directionBinGraph_row_weighted_bound o e (c ∘ pick) he
    (hleg.inj.comp hpick) hm hw hwidth hstart hend hangle hpos
  have hlocal (i : Fin t) : rowScore lam (directionRow o e c (pick i)) ≤
      m - ((directionRow o e (c ∘ pick) i).map (uniformBin start width m)).toFinset.card := by
    have hsort := directionRow_sorted o e c (pick i)
    rw [hrow i] at hsort ⊢
    apply rowScore_two_anchors_le_empty_bins hm hw hwidth (hwrap i)
      (hleft i) (hright i) _ hsort
    intro x hx
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e (c ∘ pick)).mp hx
    exact hpos i j hji.symm
  exact (Finset.sum_le_sum (fun i _ =>
    Nat.pow_le_pow_right (by omega) (hlocal i))).trans hbins

#print axioms rowScore_two_anchors_eq_linear
#print axioms rowScore_two_anchors_le_empty_bins
#print axioms weighted_two_anchored_rows

end Jsp404
