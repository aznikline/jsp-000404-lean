import Jsp000404.CircleSeparation

/-!
# Weighted packing of separated directions

When the angle between directions i and j is at least half the sum of
their weights, consecutive directions contribute half of each endpoint's
weight. Adding the wrap inequality counts every weight exactly once.
Sorting the indices keeps each weight attached to its own direction.
-/

namespace Jsp404

open scoped EuclideanGeometry EuclideanSpace

private theorem weighted_separated_list_span {ι : Type*} (theta w : ι → ℝ) :
    ∀ (xs : List ι) (x : ι),
    (x :: xs).Pairwise (fun a b => (w a + w b) / 2 ≤ theta b - theta a) →
    ((x :: xs).map w).sum - (w x + w ((x :: xs).getLast (List.cons_ne_nil _ _))) / 2 ≤
      theta ((x :: xs).getLast (List.cons_ne_nil _ _)) - theta x := by
  intro xs
  induction xs with
  | nil => intro x _; simp
  | cons y ys ih =>
    intro x hp
    have hxy := (List.pairwise_cons.mp hp).1 y (by simp)
    have ht := ih y (List.pairwise_cons.mp hp).2
    rw [List.getLast_cons (List.cons_ne_nil _ _), List.map_cons, List.sum_cons]
    linarith

theorem weighted_circle_separation_list_bound {ι : Type*}
    (theta w : ι → ℝ) {l : List ι} (hlen : 2 ≤ l.length)
    (hs : l.Pairwise (fun a b => theta a ≤ theta b))
    (hp : l.Pairwise (fun a b =>
      (w a + w b) / 2 ≤ |theta b - theta a| ∧
      (w a + w b) / 2 ≤ 2 * Real.pi - |theta b - theta a|)) :
    (l.map w).sum ≤ 2 * Real.pi := by
  cases l with
  | nil => simp at hlen
  | cons x xs =>
    have hxsn : xs ≠ [] := by intro h; simp [h] at hlen
    have hlin : (x :: xs).Pairwise
        (fun a b => (w a + w b) / 2 ≤ theta b - theta a) := by
      have hboth := List.pairwise_and_iff.mpr ⟨hs, hp⟩
      apply List.Pairwise.imp _ hboth
      intro a b hab
      simpa only [abs_of_nonneg (sub_nonneg.mpr hab.1)] using hab.2.1
    have hspan := weighted_separated_list_span theta w xs x hlin
    have hlast : xs.getLast hxsn ∈ xs := List.getLast_mem hxsn
    have hwrap := ((List.pairwise_cons.mp hp).1 _ hlast).2
    have hle := (List.pairwise_cons.mp hs).1 _ hlast
    rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hwrap
    rw [List.getLast_cons hxsn] at hspan
    linarith

/-- Pairwise angular separation by the mean endpoint weight bounds the
total weight by the circumference. No sign assumption on the weights is needed. -/
theorem weighted_circle_separation_bound {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 2 ≤ s)
    (m : Fin s → Plane₂) (hm : ∀ i, m i ≠ 0) (w : Fin s → ℝ)
    (hsep : ∀ i j, i ≠ j →
      (w i + w j) / 2 ≤ InnerProductGeometry.angle (m i) (m j)) :
    ∑ i, w i ≤ 2 * Real.pi := by
  classical
  let z : Fin s := ⟨0, by omega⟩
  let theta (i : Fin s) : ℝ := (o.oangle (m z) (m i)).toReal
  let R : Fin s → Fin s → Prop := fun i j => theta i ≤ theta j
  let Sep : Fin s → Fin s → Prop := fun i j =>
    (w i + w j) / 2 ≤ |theta j - theta i| ∧
      (w i + w j) / 2 ≤ 2 * Real.pi - |theta j - theta i|
  have hp (i j : Fin s) (hij : i ≠ j) : Sep i j := by
    have hti := Real.Angle.toReal_mem_Ioc (o.oangle (m z) (m i))
    have htj := Real.Angle.toReal_mem_Ioc (o.oangle (m z) (m j))
    have hr : |theta j - theta i| ≤ 2 * Real.pi := by
      apply abs_le.mpr
      dsimp [theta]
      constructor <;> linarith [hti.1, hti.2, htj.1, htj.2]
    have ha : InnerProductGeometry.angle (m i) (m j) =
        |((theta j - theta i : ℝ) : Real.Angle).toReal| := by
      rw [o.angle_eq_abs_oangle_toReal (hm i) (hm j),
        ← o.oangle_sub_left (hm z) (hm i) (hm j)]
      simp only [theta, Real.Angle.coe_sub, Real.Angle.coe_toReal]
    have hb := abs_angle_rep_le_both hr
    rw [← ha] at hb
    exact ⟨(hsep i j hij).trans hb.1, (hsep i j hij).trans hb.2⟩
  let : Std.Total R := ⟨fun i j => le_total (theta i) (theta j)⟩
  let : IsTrans (Fin s) R := ⟨fun _ _ _ hij hjk => hij.trans hjk⟩
  let sorted := (List.finRange s).insertionSort R
  have hsort : sorted.Pairwise R := List.pairwise_insertionSort R _
  have hraw : (List.finRange s).Pairwise Sep :=
    (List.nodup_finRange s).imp (fun {i j} hij => hp i j hij)
  have hsorted : sorted.Pairwise Sep := hraw.perm
    (List.perm_insertionSort _ _).symm (by
      intro i j hij
      simpa only [Sep, add_comm, abs_sub_comm] using hij)
  have hlen : sorted.length = s := by simp [sorted]
  have h := weighted_circle_separation_list_bound theta w (by omega) hsort hsorted
  have hsum : (sorted.map w).sum = ∑ i, w i := by
    calc (sorted.map w).sum = ((List.finRange s).map w).sum :=
          ((List.perm_insertionSort _ _).map w).sum_eq
      _ = ∑ i, w i := by rw [← List.ofFn_eq_map, List.sum_ofFn]
  rwa [hsum] at h

#print axioms weighted_circle_separation_list_bound
#print axioms weighted_circle_separation_bound

end Jsp404
