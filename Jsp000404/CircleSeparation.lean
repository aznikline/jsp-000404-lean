import Jsp000404.ConeCorridor

/-! # Packing separated vector directions on the full circle -/

namespace Jsp404

open scoped EuclideanGeometry EuclideanSpace

private theorem abs_angle_rep_le_both_nonneg {x : ℝ}
    (hx : 0 ≤ x) (hxpi : x ≤ 2 * Real.pi) :
    |(x : Real.Angle).toReal| ≤ x ∧
      |(x : Real.Angle).toReal| ≤ 2 * Real.pi - x := by
  by_cases h : x ≤ Real.pi
  · rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], h⟩,
      abs_of_nonneg hx]
    constructor <;> linarith
  · have hp : Real.pi < x := lt_of_not_ge h
    rw [Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr
      ⟨hp, by linarith [Real.pi_pos]⟩, abs_of_nonpos (by linarith)]
    constructor <;> linarith

theorem abs_angle_rep_le_both {x : ℝ} (hx : |x| ≤ 2 * Real.pi) :
    |(x : Real.Angle).toReal| ≤ |x| ∧
      |(x : Real.Angle).toReal| ≤ 2 * Real.pi - |x| := by
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0] at hx ⊢
    exact abs_angle_rep_le_both_nonneg hx0 hx
  · have hxn : x < 0 := lt_of_not_ge hx0
    rw [abs_of_neg hxn] at hx ⊢
    have h := abs_angle_rep_le_both_nonneg (neg_nonneg.mpr hxn.le) hx
    simpa only [Real.Angle.coe_neg, Real.Angle.abs_toReal_neg] using h

private theorem separated_list_span {gamma : ℝ} : ∀ (xs : List ℝ) (x : ℝ),
    (x :: xs).Pairwise (fun a b => gamma ≤ b-a) →
    (xs.length : ℝ) * gamma ≤ (x :: xs).getLast (List.cons_ne_nil _ _) - x := by
  intro xs
  induction xs with
  | nil => intro x _; simp
  | cons y ys ih =>
    intro x hp
    have hxy : gamma ≤ y-x := (List.pairwise_cons.mp hp).1 y (by simp)
    have ht := ih y (List.pairwise_cons.mp hp).2
    rw [List.getLast_cons (List.cons_ne_nil _ _), List.length_cons, Nat.cast_add,
      Nat.cast_one]
    nlinarith

/-- A finite list of full-circle representatives whose shorter circular
separations are all at least gamma occupies at least length*gamma. -/
theorem circle_separation_list_bound {gamma : ℝ} {l : List ℝ}
    (hlen : 2 ≤ l.length) (hs : l.SortedLE)
    (hp : l.Pairwise (fun a b => gamma ≤ |b-a| ∧ gamma ≤ 2*Real.pi-|b-a|)) :
    (l.length : ℝ) * gamma ≤ 2 * Real.pi := by
  cases l with
  | nil => simp at hlen
  | cons x xs =>
    have hxsn : xs ≠ [] := by intro h; simp [h] at hlen
    have hlin : (x :: xs).Pairwise (fun a b => gamma ≤ b-a) := by
      have hc := List.pairwise_and_iff.mpr ⟨hs.pairwise, hp⟩
      apply List.Pairwise.imp _ hc
      intro a b hab
      simpa only [abs_of_nonneg (sub_nonneg.mpr hab.1)] using hab.2.1
    have hspan := separated_list_span xs x hlin
    have hlast : xs.getLast hxsn ∈ xs := List.getLast_mem hxsn
    have hwrap := ((List.pairwise_cons.mp hp).1 _ hlast).2
    have hle := (List.sortedLE_cons.mp hs).1 _ hlast
    rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hwrap
    rw [List.getLast_cons hxsn] at hspan
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- Pairwise angular separation of s nonzero planar vectors costs at
least s*gamma around the full circle. -/
theorem circle_separation_bound {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 2 ≤ s)
    (m : Fin s → Plane₂) (hm : ∀ i, m i ≠ 0) {gamma : ℝ}
    (hsep : ∀ i j, i ≠ j → gamma ≤ InnerProductGeometry.angle (m i) (m j)) :
    (s : ℝ) * gamma ≤ 2 * Real.pi := by
  classical
  let z : Fin s := ⟨0, by omega⟩
  let theta : Fin s → ℝ := fun i => (o.oangle (m z) (m i)).toReal
  let R : ℝ → ℝ → Prop := fun a b =>
    gamma ≤ |b-a| ∧ gamma ≤ 2*Real.pi-|b-a|
  have hp (i j : Fin s) (hij : i ≠ j) : R (theta i) (theta j) := by
    have hti := Real.Angle.toReal_mem_Ioc (o.oangle (m z) (m i))
    have htj := Real.Angle.toReal_mem_Ioc (o.oangle (m z) (m j))
    have hr : |theta j - theta i| ≤ 2*Real.pi := by
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
  let raw := (List.finRange s).map theta
  let sorted := raw.insertionSort (· ≤ ·)
  have hpraw : raw.Pairwise R := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange s).imp (fun {i j} hij => hp i j hij)
  have hpsorted : sorted.Pairwise R := hpraw.perm
    (List.perm_insertionSort _ _).symm (by
      intro a b hab
      simpa only [R, abs_sub_comm] using hab)
  have hsorted : sorted.SortedLE := by
    exact (List.pairwise_insertionSort _ _).sortedLE
  have hlen : sorted.length = s := by simp [sorted, raw]
  have h := circle_separation_list_bound (by omega) hsorted hpsorted
  rwa [hlen] at h

#print axioms circle_separation_bound

end Jsp404
