import Jsp000404.Induction
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
set_option pp.fullNames true

/-!
SOURCE_ONLY indexed cyclic-incidence bridge. The two gaps actually merged
by an indexed erasure are the gap before and the gap after that position.
The predecessor is a genuine permutation of the full list index type.
No caller incidence identity, merged arc or gain conclusion is assumed.
-/

namespace Jsp404.RowGainCyclicIncident

private theorem wrapGap_eq_cyclicDiff_of_nodup {l : List ℝ} (hne : l ≠ [])
    (hnd : l.Nodup) (h2 : 2 ≤ l.length) :
    wrapGap l hne = cyclicDiff (l.getLast hne) (l.head hne) := by
  have hnot : ¬ ∀ x ∈ l, x = l.head hne := by
    intro hall
    cases l with
    | nil => exact hne rfl
    | cons a rest =>
      cases rest with
      | nil => simp at h2
      | cons b bs =>
        have hba : b = a := hall b (by simp)
        have ha := (List.nodup_cons.mp hnd).1
        exact ha (by rw [← hba]; simp)
  rw [wrapGap, ite_eq_right hnot]

private theorem predecessor_zero {m : ℕ} (h2 : 2 ≤ m) :
    (finRotate m).symm ⟨0, by omega⟩ = ⟨m - 1, by omega⟩ := by
  letI : NeZero m := ⟨by omega⟩
  apply (finRotate m).symm_apply_eq.mpr
  apply Fin.ext
  rw [finRotate_apply]
  change ((m - 1) + (1 % m)) % m = 0
  rw [Nat.mod_eq_of_lt (by omega : 1 < m),
    show m - 1 + 1 = m by omega, Nat.mod_self]

/-- Exact positional form of the actual list-erasure merge. In particular
the full wrap gap keeps its index and its multiplicity. This applies to
the original sorted list; the rotated list is not assumed sorted. -/
theorem rowGain_eq_mergeGain_gapAfter {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.SortedLE) (hnd : l.Nodup)
    (hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi) (h2 : 2 ≤ l.length)
    (K : Fin l.length) :
    rowGain lam l K.val = mergeGain lam
      (gapAfter l ((finRotate l.length).symm K)) (gapAfter l K) := by
  classical
  rcases K with ⟨k, hk⟩
  letI : NeZero l.length := ⟨by omega⟩
  have hlne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
  let rest := l.drop (k + 1) ++ l.take k
  have hrest_len : rest.length = l.length - 1 := by
    simp only [rest, List.length_append, List.length_drop, List.length_take,
      Nat.min_eq_left hk.le]
    omega
  have hrest_ne : rest ≠ [] := by
    intro heq
    rw [heq] at hrest_len
    simp only [List.length_nil] at hrest_len
    omega
  have hrot : l.rotate k = l[k] :: rest := by
    rw [List.rotate_eq_rotate', List.rotate'_eq_drop_append_take hk.le,
      List.drop_eq_getElem_cons hk, List.cons_append]
  have hrot_nd : (l[k] :: rest).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr hnd
  have hrot_two : 2 ≤ (l[k] :: rest).length := by
    rw [← hrot, List.length_rotate]
    exact h2
  have hwrap : wrapGap (l[k] :: rest) (List.cons_ne_nil _ _) =
      cyclicDiff (rest.getLast hrest_ne) l[k] := by
    rw [wrapGap_eq_cyclicDiff_of_nodup (List.cons_ne_nil _ _) hrot_nd hrot_two,
      List.getLast_cons hrest_ne, List.head_cons]
  have hinj := List.nodup_iff_injective_get.mp hnd
  have hleft : wrapGap (l[k] :: rest) (List.cons_ne_nil _ _) =
      gapAfter l ((finRotate l.length).symm ⟨k, hk⟩) := by
    by_cases hk0 : k = 0
    · subst k
      have hA : rest.getLast hrest_ne = l[l.length - 1]'(by omega) := by
        change (l.drop (0 + 1) ++ l.take 0).getLast hrest_ne = _
        rw [List.getLast_eq_getElem,
          List.getElem_append_left (by
            simp only [List.length_append, List.length_drop, List.length_take,
              Nat.min_eq_left (Nat.zero_le l.length)]
            omega), List.getElem_drop]
        congr 1
        simp only [List.length_append, List.length_drop, List.length_take,
          Nat.min_eq_left (Nat.zero_le l.length)]
        omega
      have hne : l[l.length - 1]'(by omega) ≠ l[0]'hk := by
        intro heq
        have hidx : (⟨l.length - 1, by omega⟩ : Fin l.length) = ⟨0, hk⟩ :=
          hinj heq
        have := congrArg Fin.val hidx
        omega
      have hnotlt : ¬ l[l.length - 1]'(by omega) < l[0]'hk :=
        not_lt.mpr (getElem_mono_of_sortedLE hs (by omega) (by omega))
      rw [hwrap, hA, predecessor_zero h2]
      rw [cyclicDiff, ite_eq_right hne, ite_eq_right hnotlt]
      unfold gapAfter
      rw [dite_eq_right (by omega : ¬ l.length - 1 + 1 < l.length)]
      simp only [List.get_eq_getElem]
      ring
    · have hkpos : 0 < k := by omega
      have htk : l.take k ≠ [] := by
        intro heq
        rw [List.take_eq_nil_iff] at heq
        rcases heq with heq | heq
        · omega
        · exact hlne heq
      have hA : rest.getLast hrest_ne = l[k - 1]'(by omega) := by
        change (l.drop (k + 1) ++ l.take k).getLast hrest_ne = _
        rw [List.getLast_append_of_right_ne_nil _ _ htk, List.getLast_eq_getElem]
        simp only [List.length_take, Nat.min_eq_left hk.le, List.getElem_take]
      have hKzero : (⟨k, hk⟩ : Fin l.length) ≠ 0 := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_zero] at this
        omega
      have hpred : (finRotate l.length).symm ⟨k, hk⟩ =
          ⟨k - 1, by omega⟩ := Fin.ext (coe_finRotate_symm_of_ne_zero hKzero)
      rw [hwrap, hA, hpred,
        cyclicDiff_eq_sub_of_le (getElem_mono_of_sortedLE hs (by omega) hk)]
      unfold gapAfter
      rw [dite_eq_left (by omega : k - 1 + 1 < l.length)]
      have hi : (⟨k - 1 + 1, by omega⟩ : Fin l.length) = ⟨k, hk⟩ :=
        Fin.ext (by omega)
      rw [hi]
      rfl
  have hright : cyclicDiff l[k] (rest.head hrest_ne) = gapAfter l ⟨k, hk⟩ := by
    by_cases hk1 : k + 1 < l.length
    · have hB : rest.head hrest_ne = l[k + 1] := by
        change (l.drop (k + 1) ++ l.take k).head hrest_ne = _
        rw [List.head_append_left (by
            intro heq
            rw [List.drop_eq_nil_iff] at heq
            omega), List.head_drop]
      rw [hB, cyclicDiff_eq_sub_of_le (getElem_mono_of_sortedLE hs (by omega) hk1)]
      unfold gapAfter
      rw [dite_eq_left hk1]
      rfl
    · have hkpos : 0 < k := by omega
      have htk : l.take k ≠ [] := by
        intro heq
        rw [List.take_eq_nil_iff] at heq
        rcases heq with heq | heq
        · omega
        · exact hlne heq
      have hB : rest.head hrest_ne = l[0]'(by omega) := by
        change (l.drop (k + 1) ++ l.take k).head hrest_ne = _
        rw [List.head_append_right _ (by rw [List.drop_eq_nil_iff]; omega),
          List.head_take htk, List.head_eq_getElem]
      have hne : l[k] ≠ l[0]'(by omega) := by
        intro heq
        have hidx : (⟨k, hk⟩ : Fin l.length) = ⟨0, by omega⟩ := hinj heq
        have := congrArg Fin.val hidx
        omega
      have hnotlt : ¬ l[k] < l[0]'(by omega) :=
        not_lt.mpr (getElem_mono_of_sortedLE hs (by omega) hk)
      rw [hB, cyclicDiff, ite_eq_right hne, ite_eq_right hnotlt]
      unfold gapAfter
      rw [dite_eq_right hk1]
      simp only [List.get_eq_getElem]
      ring
  rw [rowGain_eq_mergeGain hlam hs hall hk h2 (rfl : rest = _) hrest_ne, hleft, hright]

#print axioms rowGain_eq_mergeGain_gapAfter

end Jsp404.RowGainCyclicIncident
