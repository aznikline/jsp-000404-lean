import Jsp000404.ActualZeroPairDeletionBudget
import Jsp000404.ActualHullSmallScoreTypes

/-!
Actual outside-gap plateau after two original zero-score deletions.

Let `H` be an actual n4 LOW minimum-counter `Model` with cap 16 whose
potential is 17 (derived internally), let `p` and `p.succAbove q` be two
distinct original zero-score targets, and let `A` be a surviving original
full-hull point of positive original score. The original actual hull Window
at `A` and the restricted actual hull Window at the same point after both
deletions are constructed internally. In the original Window chart, the
two deletions are two actual list erasures of physical boundary/interior
rays; each has zero actual row gain. An endpoint erasure merges the outside
gap with an internal gap, and zero gain forces its outside score to stay
unchanged. Hence the restricted physical outside gap `E = pi - W'.width`
has the original outside score `t`, so `E < (t + 2) * lam`.

No gap budget, score bound, synthetic class or restricted minimum-counter
Model is supplied by the caller.
-/

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.DevinF17HullGap

/-! ### Pure list layer -/

theorem wrapGap_congr {l₁ l₂ : List ℝ} (h : l₁ = l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    wrapGap l₁ h₁ = wrapGap l₂ h₂ := by
  subst h
  rfl

theorem wrapGap_eq_of_head_lt_getLast {l : List ℝ} (hl : l ≠ [])
    (hlt : l.head hl < l.getLast hl) :
    wrapGap l hl = Real.pi + l.head hl - l.getLast hl := by
  unfold wrapGap
  split_ifs with h
  · have := h _ (List.getLast_mem hl)
    linarith
  · unfold cyclicDiff
    split_ifs <;> linarith

theorem wrapGap_eq_of_getLast_lt_head {l : List ℝ} (hl : l ≠ [])
    (hlt : l.getLast hl < l.head hl) :
    wrapGap l hl = l.head hl - l.getLast hl := by
  unfold wrapGap
  split_ifs with h
  · have := h _ (List.getLast_mem hl)
    linarith
  · unfold cyclicDiff
    split_ifs <;> linarith

/-- Zero merge gain against a gap of length at least `lam` keeps that gap's
score: the other merged gap is shorter than `lam`. -/
theorem gapScore_add_right_of_mergeGain_zero {lam w h : ℝ} (hlam : 0 < lam)
    (hw : lam ≤ w) (hh : 0 ≤ h) (hz : mergeGain lam w h = 0) :
    gapScore lam (w + h) = gapScore lam w := by
  have hhlt : h < lam := by
    by_contra hnot
    have := mergeGain_pos_of_ge hlam hw (le_of_not_gt hnot)
    omega
  have hspec := mergeGain_spec hlam (hlam.le.trans hw) hh
  have hzero : gapScore lam h = 0 := by
    unfold gapScore
    have : ⌊h / lam⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hlam).mpr hhlt)
    omega
  omega

theorem gapScore_add_left_of_mergeGain_zero {lam w h : ℝ} (hlam : 0 < lam)
    (hw : lam ≤ w) (hh : 0 ≤ h) (hz : mergeGain lam h w = 0) :
    gapScore lam (h + w) = gapScore lam w := by
  have hhlt : h < lam := by
    by_contra hnot
    have := mergeGain_pos_of_ge hlam (le_of_not_gt hnot) hw
    omega
  have hspec := mergeGain_spec hlam hh (hlam.le.trans hw)
  have hzero : gapScore lam h = 0 := by
    unfold gapScore
    have : ⌊h / lam⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hlam).mpr hhlt)
    omega
  omega

/-- One actual erasure from a strictly sorted chart row whose wrap is the
outside gap. If the row score does not change, the outside gap cannot
shrink and its score is unchanged. Endpoint erasures are merges with the
outside gap; interior erasures leave it fixed. -/
theorem wrap_step {lam : ℝ} (hlam : 0 < lam) {l : List ℝ}
    (hs : l.Pairwise (· < ·)) (hall : ∀ b ∈ l, 0 ≤ b ∧ b < Real.pi)
    (h3 : 3 ≤ l.length) (hne : l ≠ []) (hwrap : lam ≤ wrapGap l hne)
    {x : ℝ} (hx : x ∈ l) {l' : List ℝ} (hl' : l' = l.erase x) (hne' : l' ≠ [])
    (heq : rowScore lam l' = rowScore lam l) :
    wrapGap l hne ≤ wrapGap l' hne' ∧
      gapScore lam (wrapGap l' hne') = gapScore lam (wrapGap l hne) := by
  subst hl'
  obtain ⟨y, m, rfl⟩ : ∃ y m, l = y :: m := by
    cases l with
    | nil => exact absurd rfl hne
    | cons y m => exact ⟨y, m, rfl⟩
  have hm : m ≠ [] := by rintro rfl; simp at h3
  obtain ⟨m0, L, rfl⟩ : ∃ m0 L, m = m0 ++ [L] :=
    ⟨_, _, (List.dropLast_append_getLast hm).symm⟩
  have hm0 : m0 ≠ [] := by rintro rfl; simp at h3
  have hy_m0 : ∀ b ∈ m0, y < b := fun b hb =>
    (List.pairwise_cons.mp hs).1 b (by simp [hb])
  have hyL : y < L := (List.pairwise_cons.mp hs).1 L (by simp)
  have hm0L : ∀ b ∈ m0, b < L := by
    have h := (List.pairwise_cons.mp hs).2
    rw [List.pairwise_append] at h
    exact fun b hb => h.2.2 b hb L (by simp)
  have hLm0 : L ∉ m0 := fun h => lt_irrefl _ (hm0L L h)
  have hyπ := hall y (by simp)
  have hLπ := hall L (by simp)
  have hwl : wrapGap (y :: (m0 ++ [L])) hne = Real.pi + y - L := by
    rw [wrapGap_eq_of_head_lt_getLast hne (by simpa using hyL)]
    simp
  rw [hwl] at hwrap ⊢
  by_cases hxy : x = y
  · subst hxy
    have hn : m0 ++ [L] ≠ [] := by simp
    have herase : (x :: (m0 ++ [L])).erase x = m0 ++ [L] := List.erase_cons_head _ _
    rw [wrapGap_congr herase hne' hn]
    rw [herase] at heq
    set z := m0.head hm0 with hz
    have hzm : z ∈ m0 := List.head_mem hm0
    have hhead : (m0 ++ [L]).head hn = z := List.head_append_of_ne_nil hm0
    have hxz : x < z := hy_m0 z hzm
    have hzL : z < L := hm0L z hzm
    have hwn : wrapGap (m0 ++ [L]) hn = Real.pi + z - L := by
      rw [wrapGap_eq_of_head_lt_getLast hn (by rw [hhead]; simpa using hzL), hhead]
      simp
    have hcd : cyclicDiff x ((m0 ++ [L]).head hn) = z - x := by
      rw [hhead]
      unfold cyclicDiff
      split_ifs <;> linarith
    have hzπ := hall z (by simp [hzm])
    have hscore := rowScore_erase_head' hlam (x := x) (l := m0 ++ [L]) hn
      hyπ.1 hyπ.2 (by rw [hhead]; exact hzπ.1) (by rw [hhead]; exact hzπ.2)
      (by simpa using hLπ.1) (by simpa using hLπ.2)
      (by rw [hwn, hwl, hcd]; ring)
    rw [hwl, hcd] at hscore
    have hz0 : mergeGain lam (Real.pi + x - L) (z - x) = 0 := by omega
    have hg := gapScore_add_right_of_mergeGain_zero hlam hwrap (by linarith) hz0
    rw [hwn]
    refine ⟨by linarith, ?_⟩
    rw [show Real.pi + z - L = (Real.pi + x - L) + (z - x) by ring]
    exact hg
  · by_cases hxL : x = L
    · subst hxL
      have hn : y :: m0 ≠ [] := by simp
      have herase : (y :: (m0 ++ [x])).erase x = y :: m0 := by
        rw [List.erase_cons_tail (by simpa using (ne_of_lt hyL)),
          List.erase_append_right _ hLm0]
        simp
      rw [wrapGap_congr herase hne' hn]
      rw [herase] at heq
      set w := m0.getLast hm0 with hw
      have hwm : w ∈ m0 := List.getLast_mem hm0
      have hlast : (y :: m0).getLast hn = w := List.getLast_cons hm0
      have hyw : y < w := hy_m0 w hwm
      have hwx : w < x := hm0L w hwm
      have hwπ := hall w (by simp [hwm])
      have hwn : wrapGap (y :: m0) hn = Real.pi + y - w := by
        rw [wrapGap_eq_of_head_lt_getLast hn (by rw [hlast]; simpa using hyw), hlast]
        simp
      have hn2 : x :: y :: m0 ≠ [] := by simp
      have hwx' : wrapGap (x :: y :: m0) hn2 = x - w := by
        have hlast2 : (x :: y :: m0).getLast hn2 = w := by
          rw [List.getLast_cons hn, hlast]
        rw [wrapGap_eq_of_getLast_lt_head hn2 (by rw [hlast2]; simpa using hwx), hlast2]
        simp
      have hcd : cyclicDiff x ((y :: m0).head hn) = Real.pi + y - x := by
        simp only [List.head_cons]
        unfold cyclicDiff
        split_ifs <;> linarith
      have hscore := rowScore_erase_head' hlam (x := x) (l := y :: m0) hn
        hLπ.1 hLπ.2 (by simpa using hyπ.1) (by simpa using hyπ.2)
        (by rw [hlast]; exact hwπ.1) (by rw [hlast]; exact hwπ.2)
        (by rw [hwn, hwx', hcd]; ring)
      rw [hwx', hcd] at hscore
      have hrot : rowScore lam (y :: (m0 ++ [x])) = rowScore lam (x :: y :: m0) := by
        have h1 : y :: (m0 ++ [x]) = (y :: m0) ++ [x] := rfl
        rw [h1, ← rowScore_rotate lam ((y :: m0) ++ [x]) (y :: m0).length,
          List.rotate_append_length_eq]
        rfl
      rw [hrot] at heq
      have hz0 : mergeGain lam (x - w) (Real.pi + y - x) = 0 := by omega
      have hg := gapScore_add_left_of_mergeGain_zero hlam hwrap (by linarith) hz0
      rw [hwn]
      refine ⟨by linarith, ?_⟩
      rw [show Real.pi + y - w = (x - w) + (Real.pi + y - x) by ring]
      exact hg
    · have hxm0 : x ∈ m0 := by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
        rcases hx with h | h | h
        · exact absurd h hxy
        · exact h
        · exact absurd h hxL
      have herase : (y :: (m0 ++ [L])).erase x = y :: (m0.erase x ++ [L]) := by
        rw [List.erase_cons_tail (by simpa using (Ne.symm hxy)),
          List.erase_append_left _ hxm0]
      have hn : y :: (m0.erase x ++ [L]) ≠ [] := by simp
      rw [wrapGap_congr herase hne' hn]
      have hwn : wrapGap (y :: (m0.erase x ++ [L])) hn = Real.pi + y - L := by
        rw [wrapGap_eq_of_head_lt_getLast hn (by simpa using hyL)]
        simp
      rw [hwn]
      exact ⟨le_rfl, rfl⟩

/-! ### Actual window charts -/

section Geometry

variable {o : Orientation ℝ Plane₂ (Fin 2)}

/-- In the reference direction of an actual Window, every actual direction
representative is the Window coordinate. -/
theorem dirRep_window {m : ℕ} {c : Fin m → Plane₂} {lam : ℝ} {P : Fin m}
    (W : ActualHullRayWindow.Window o c lam P) (j : Fin m) (hj : j ≠ P) :
    dirRep o W.base c P j = W.theta j := by
  unfold dirRep
  rw [W.actual_direction j hj]
  exact (eq_linRep_of_int_pi
    ⟨(W.theta_mem j hj).1, ((W.theta_mem j hj).2).trans_lt W.width_lt_pi⟩
    ⟨0, by simp⟩).symm

/-- The actual row in an original Window chart is strictly increasing:
legality forbids two other centers on one ray from the Window vertex. -/
theorem row_pairwise_lt {m : ℕ} {c : Fin m → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c lam) {P : Fin m}
    (W : ActualHullRayWindow.Window o c lam P) :
    (directionRow o W.base c P).Pairwise (· < ·) := by
  have hnd : (directionRow o W.base c P).Nodup := by
    unfold directionRow
    refine (List.perm_insertionSort _ _).nodup_iff.mpr ?_
    refine List.Nodup.map_on ?_ ((List.nodup_finRange m).erase P)
    intro j hj k hk hjk
    have hjP := ((List.nodup_finRange m).mem_erase_iff.mp hj).1
    have hkP := ((List.nodup_finRange m).mem_erase_iff.mp hk).1
    by_contra hne
    rw [dirRep_window W j hjP, dirRep_window W k hkP] at hjk
    have hy : c j - c P ≠ 0 := sub_ne_zero.mpr (fun h => hjP (hleg.inj h))
    have hz : c k - c P ≠ 0 := sub_ne_zero.mpr (fun h => hkP (hleg.inj h))
    have hadd := o.oangle_add W.base_ne_zero hy hz
    rw [W.actual_direction j hjP, W.actual_direction k hkP, hjk] at hadd
    have h0 : o.oangle (c j - c P) (c k - c P) = 0 := by
      have := congrArg (fun x => x - ((W.theta k : ℝ) : Real.Angle)) hadd
      simpa using this
    have hangle := (o.oangle_eq_zero_iff_angle_eq_zero hy hz).mp h0
    have hpos := EuclideanGeometry.angle_pos_of_not_collinear
      (legal_triple_not_collinear hleg hjP hne (Ne.symm hkP))
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hangle] at hpos
    exact lt_irrefl _ hpos
  have hsort := (directionRow_sorted o W.base c P).pairwise
  exact (List.Pairwise.and hsort (hnd : List.Pairwise (fun a b => a ≠ b) _)).imp
    (fun h => lt_of_le_of_ne h.1 h.2)

/-- Coordinates of a subconfiguration Window are the original Window
coordinates shifted by the original coordinate of its left boundary ray. -/
theorem theta_transport {m r : ℕ} {c : Fin m → Plane₂} {lam lam' : ℝ}
    (hinj : Function.Injective c) {c' : Fin r → Plane₂} {φ : Fin r → Fin m}
    (hφ : Function.Injective φ) (hc' : ∀ j, c' j = c (φ j)) {a : Fin r}
    (W : ActualHullRayWindow.Window o c lam (φ a))
    (W' : ActualHullRayWindow.Window o c' lam' a) (j : Fin r) (hj : j ≠ a) :
    W'.theta j = W.theta (φ j) - W.theta (φ W'.left) := by
  have hjφ : φ j ≠ φ a := fun h => hj (hφ h)
  have hlφ : φ W'.left ≠ φ a := fun h => W'.left_ne_center (hφ h)
  have hz : c' j - c' a ≠ 0 := by
    rw [hc', hc']
    exact sub_ne_zero.mpr (fun h => hjφ (hinj h))
  have hadd := o.oangle_add W.base_ne_zero W'.base_ne_zero hz
  have hyb : W'.base = c (φ W'.left) - c (φ a) := by rw [W'.base_eq_left, hc', hc']
  rw [W'.actual_direction j hj, hyb, W.actual_direction _ hlφ, hc' j, hc' a,
    W.actual_direction _ hjφ] at hadd
  have hang : ((W'.theta j : ℝ) : Real.Angle) =
      ((W.theta (φ j) - W.theta (φ W'.left) : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, ← hadd]
    abel
  have h1 := W'.theta_mem j hj
  have h2 := W.theta_mem _ hjφ
  have h3 := W.theta_mem _ hlφ
  have e1 : ((W'.theta j : ℝ) : Real.Angle).toReal = W'.theta j :=
    Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [Real.pi_pos, h1.1], by linarith [h1.2, W'.width_lt_pi]⟩
  have e2 : ((W.theta (φ j) - W.theta (φ W'.left) : ℝ) : Real.Angle).toReal =
      W.theta (φ j) - W.theta (φ W'.left) :=
    Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [h2.1, h3.2, W.width_lt_pi], by linarith [h2.2, h3.1, W.width_lt_pi]⟩
  rw [← e1, ← e2, hang]

/-- In the original Window chart, the actual row of a retained point of any
subconfiguration lies in `[0, π)`, and its wrap gap is the physical outside
gap `π - W'.width` of the subconfiguration Window. -/
theorem row_wrap {m r : ℕ} {c : Fin m → Plane₂} {lam lam' : ℝ}
    (hinj : Function.Injective c) {c' : Fin r → Plane₂} {φ : Fin r → Fin m}
    (hφ : Function.Injective φ) (hc' : ∀ j, c' j = c (φ j)) {a : Fin r}
    (W : ActualHullRayWindow.Window o c lam (φ a))
    (W' : ActualHullRayWindow.Window o c' lam' a)
    (hne : directionRow o W.base c' a ≠ []) :
    (∀ x ∈ directionRow o W.base c' a, 0 ≤ x ∧ x < Real.pi) ∧
      wrapGap (directionRow o W.base c' a) hne = Real.pi - W'.width := by
  have hval : ∀ j, j ≠ a → dirRep o W.base c' a j = W.theta (φ j) := by
    intro j hj
    have : dirRep o W.base c' a j = dirRep o W.base c (φ a) (φ j) := by
      unfold dirRep
      rw [hc', hc']
    rw [this, dirRep_window W _ (fun h => hj (hφ h))]
  have hmem : ∀ x ∈ directionRow o W.base c' a, ∃ j, j ≠ a ∧ x = W.theta (φ j) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_directionRow o W.base c').mp hx
    exact ⟨j, hj, hval j hj⟩
  have hin : ∀ j, j ≠ a → W.theta (φ j) ∈ directionRow o W.base c' a := fun j hj =>
    (mem_directionRow o W.base c').mpr ⟨j, hj, (hval j hj).symm⟩
  have htr := theta_transport hinj hφ hc' W W'
  have hsort := (directionRow_sorted o W.base c' a).pairwise
  have hhead : (directionRow o W.base c' a).head hne = W.theta (φ W'.left) := by
    apply le_antisymm
    · simpa using hsort.rel_head (hin _ W'.left_ne_center)
    · obtain ⟨j, hj, hx⟩ := hmem _ (List.head_mem hne)
      have := (W'.theta_mem j hj).1
      rw [htr j hj] at this
      rw [hx]
      linarith
  have hlast : (directionRow o W.base c' a).getLast hne =
      W.theta (φ W'.left) + W'.width := by
    apply le_antisymm
    · obtain ⟨j, hj, hx⟩ := hmem _ (List.getLast_mem hne)
      have := (W'.theta_mem j hj).2
      rw [htr j hj] at this
      rw [hx]
      linarith
    · have h : W.theta (φ W'.right) ≤ (directionRow o W.base c' a).getLast hne := by
        simpa using hsort.rel_getLast (hin _ W'.right_ne_center)
      have hr := htr _ W'.right_ne_center
      rw [W'.right_coordinate] at hr
      linarith
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := hmem x hx
    have := W.theta_mem _ (fun h => hj (hφ h))
    exact ⟨this.1, this.2.trans_lt W.width_lt_pi⟩
  · rw [wrapGap_eq_of_head_lt_getLast hne
      (by rw [hhead, hlast]; linarith [W'.width_pos]), hhead, hlast]
    ring

/-- Original full-hull membership persists in every subconfiguration that
retains the point. Newly exposed subset hull vertices are not used. -/
theorem isHullVertex_restrict {m r : ℕ} {c : Fin m → Plane₂} {c' : Fin r → Plane₂}
    {φ : Fin r → Fin m} (hc' : ∀ j, c' j = c (φ j)) {a : Fin r}
    (h : IsHullVertex c (φ a)) : IsHullVertex c' a := by
  have hsub : Set.range c' ⊆ Set.range c := by
    rintro _ ⟨j, rfl⟩
    exact ⟨φ j, (hc' j).symm⟩
  unfold IsHullVertex at h ⊢
  apply inter_extremePoints_subset_extremePoints_of_subset (convexHull_mono hsub)
  refine ⟨subset_convexHull ℝ _ (Set.mem_range_self a), ?_⟩
  rw [hc']
  exact h

end Geometry

/-! ### Outside-gap plateau after two original zero deletions -/

section Plateau

variable {o : Orientation ℝ Plane₂ (Fin 2)}

/-- The two original zero targets `p` and `p.succAbove q` are distinct, and the
observer `p.succAbove (q.succAbove a)` survives both deletions. -/
theorem targets_and_observer_distinct {s : ℕ} (p : Fin (s + 2)) (q : Fin (s + 1))
    (a : Fin s) :
    p.succAbove q ≠ p ∧ p.succAbove (q.succAbove a) ≠ p ∧
      p.succAbove (q.succAbove a) ≠ p.succAbove q :=
  ⟨Fin.succAbove_ne p q, Fin.succAbove_ne p _,
    fun h => Fin.succAbove_ne q a (Fin.succAbove_right_injective h)⟩

/-- **Actual outside-gap plateau, window form.** For any actual hull Window `W`
of the surviving observer in the original configuration and any actual hull
Window `W'` of the same observer after deleting the two original zero targets,
the restricted physical outside gap `E = π - W'.width` has the original outside
score `t = gapScore lam (π - W.width)`, does not shrink, and `E < (t + 2) * lam`. -/
theorem actual_zero_pair_outside_gap_plateau_of_windows {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) (he : e ≠ 0) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0)
    (hqzero : rowScore lam (directionRow o e c (p.succAbove q)) = 0)
    (a : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))))
    (W : ActualHullRayWindow.Window o c lam (p.succAbove (q.succAbove a)))
    (W' : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam a) :
    gapScore lam (Real.pi - W'.width) = gapScore lam (Real.pi - W.width) ∧
      Real.pi - W.width ≤ Real.pi - W'.width ∧
      Real.pi - W'.width < ((gapScore lam (Real.pi - W.width) : ℕ) + 2 : ℝ) * lam := by
  classical
  have hlam : 0 < lam := H.legality.lam_pos
  have hleg1 : Section4Legality (c ∘ p.succAbove) lam := H.legality.erase p
  have hleg2 : Section4Legality ((c ∘ p.succAbove) ∘ q.succAbove) lam := hleg1.erase q
  have hAp : p ≠ p.succAbove (q.succAbove a) := (Fin.succAbove_ne p _).symm
  have ha1q : q ≠ q.succAbove a := (Fin.succAbove_ne q a).symm
  -- Budget inputs, in the caller's reference direction `e`.
  have hmin : ∀ i : Fin (s + 2),
      rowScore lam (directionRow o e c p) ≤ rowScore lam (directionRow o e c i) := by
    intro i
    rw [hpzero]
    exact Nat.zero_le _
  have hdiv : 2 ^ rowScore lam (directionRow o e c p) ∣ 16 := by
    rw [hpzero, pow_zero]
    exact one_dvd _
  obtain ⟨-, -, -, hrows⟩ :=
    ActualMinimalBandCounterexample.actual_minimum_score_critical_form
      (s := s + 1) (by omega) o e H p hmin hdiv
  obtain ⟨-, -, -, -, hposg, -⟩ :=
    ActualZeroPairDeletionBudget.actual_zero_pair_deletion_budget hs o e H p q hpzero hqzero
  have hg : rowGain lam (directionRow o e (c ∘ p.succAbove) (q.succAbove a))
      (deleteIndex o e (c ∘ p.succAbove) q (q.succAbove a)) = 0 :=
    hposg (q.succAbove a) ha1q.symm hpos
  have hstep1e : rowScore lam (directionRow o e (c ∘ p.succAbove) (q.succAbove a)) =
      rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))) :=
    hrows (q.succAbove a)
  have hstep2e : rowScore lam
        (directionRow o e ((c ∘ p.succAbove) ∘ q.succAbove) a) =
      rowScore lam (directionRow o e (c ∘ p.succAbove) (q.succAbove a)) := by
    have hle := rowScore_le_of_sublist hlam
      (small := directionRow o e ((c ∘ p.succAbove) ∘ q.succAbove) a)
      (large := directionRow o e (c ∘ p.succAbove) (q.succAbove a))
      (by rw [erase_directionRow o e (c' := c ∘ p.succAbove) q a]
          exact List.erase_sublist)
      (directionRow_sorted _ _ _ _)
      (fun x hx => directionRow_mem_Ico o e _ hx)
      (by
        apply List.ne_nil_of_length_pos
        rw [directionRow_length]
        omega)
    unfold rowGain at hg
    rw [← eraseIdx_directionRow o e (c' := c ∘ p.succAbove) q a] at hg
    omega
  -- Transport both zero-gain steps to the original actual Window chart.
  have hW0 := W.base_ne_zero
  have hstep1 : rowScore lam (directionRow o W.base (c ∘ p.succAbove) (q.succAbove a)) =
      rowScore lam (directionRow o W.base c (p.succAbove (q.succAbove a))) := by
    rw [← rowScore_directionRow_reference_eq o e W.base he hW0 _ hleg1.inj,
      ← rowScore_directionRow_reference_eq o e W.base he hW0 _ H.legality.inj]
    exact hstep1e
  have hstep2 : rowScore lam
        (directionRow o W.base ((c ∘ p.succAbove) ∘ q.succAbove) a) =
      rowScore lam (directionRow o W.base (c ∘ p.succAbove) (q.succAbove a)) := by
    rw [← rowScore_directionRow_reference_eq o e W.base he hW0 _ hleg2.inj,
      ← rowScore_directionRow_reference_eq o e W.base he hW0 _ hleg1.inj]
    exact hstep2e
  -- The physical deletions are erasures of actual rays from the chart rows.
  have h1 : directionRow o W.base (c ∘ p.succAbove) (q.succAbove a) =
      (directionRow o W.base c (p.succAbove (q.succAbove a))).erase
        (dirRep o W.base c (p.succAbove (q.succAbove a)) p) :=
    erase_directionRow o W.base (c' := c) p (q.succAbove a)
  have h2 : directionRow o W.base ((c ∘ p.succAbove) ∘ q.succAbove) a =
      (directionRow o W.base (c ∘ p.succAbove) (q.succAbove a)).erase
        (dirRep o W.base (c ∘ p.succAbove) (q.succAbove a) q) :=
    erase_directionRow o W.base (c' := c ∘ p.succAbove) q a
  have hlen0 := directionRow_length o W.base c (p.succAbove (q.succAbove a))
  have hlen1 := directionRow_length o W.base (c ∘ p.succAbove) (q.succAbove a)
  have hlen2 := directionRow_length o W.base ((c ∘ p.succAbove) ∘ q.succAbove) a
  have hne0 : directionRow o W.base c (p.succAbove (q.succAbove a)) ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hne1 : directionRow o W.base (c ∘ p.succAbove) (q.succAbove a) ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hne2 : directionRow o W.base ((c ∘ p.succAbove) ∘ q.succAbove) a ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  -- Original and restricted wrap gaps are the physical outside gaps.
  obtain ⟨hall0, hwrap0⟩ := row_wrap (φ := fun i => i) H.legality.inj
    (fun _ _ h => h) (fun _ => rfl) W W hne0
  obtain ⟨-, hwrap2⟩ := row_wrap (c' := (c ∘ p.succAbove) ∘ q.succAbove)
    (φ := fun i => p.succAbove (q.succAbove i)) H.legality.inj
    (fun _ _ h => Fin.succAbove_right_injective (Fin.succAbove_right_injective h))
    (fun _ => rfl) W W' hne2
  have hs0 := row_pairwise_lt H.legality W
  have hlamwrap : lam ≤ wrapGap (directionRow o W.base c (p.succAbove (q.succAbove a))) hne0 := by
    rw [hwrap0]
    linarith [W.width_le_legality]
  -- First actual deletion.
  have hx0 : dirRep o W.base c (p.succAbove (q.succAbove a)) p ∈
      directionRow o W.base c (p.succAbove (q.succAbove a)) :=
    (mem_directionRow o W.base c).mpr ⟨p, hAp, rfl⟩
  obtain ⟨hle1, hsc1⟩ := wrap_step hlam hs0 hall0 (by omega) hne0 hlamwrap hx0 h1 hne1 hstep1
  -- Second actual deletion.
  have hsub1 := (List.erase_sublist (l := directionRow o W.base c (p.succAbove (q.succAbove a)))
    (a := dirRep o W.base c (p.succAbove (q.succAbove a)) p))
  rw [← h1] at hsub1
  have hs1 := hs0.sublist hsub1
  have hall1 : ∀ b ∈ directionRow o W.base (c ∘ p.succAbove) (q.succAbove a),
      0 ≤ b ∧ b < Real.pi := fun b hb => hall0 b (hsub1.subset hb)
  have hx1 : dirRep o W.base (c ∘ p.succAbove) (q.succAbove a) q ∈
      directionRow o W.base (c ∘ p.succAbove) (q.succAbove a) :=
    (mem_directionRow o W.base _).mpr ⟨q, ha1q, rfl⟩
  obtain ⟨hle2, hsc2⟩ := wrap_step hlam hs1 hall1 (by omega) hne1
    (hlamwrap.trans hle1) hx1 h2 hne2 hstep2
  rw [hwrap2, hsc1, hwrap0] at hsc2
  rw [hwrap2] at hle2
  rw [hwrap0] at hle1
  refine ⟨hsc2, hle1.trans hle2, ?_⟩
  -- Floor arithmetic: score `t` with floor at least one gives `E < (t+2) lam`.
  set t := gapScore lam (Real.pi - W.width) with ht
  have hge : 1 ≤ ⌊(Real.pi - W'.width) / lam⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hlam]
    linarith [W.width_le_legality]
  have hfl : ⌊(Real.pi - W'.width) / lam⌋₊ = t + 1 := by
    unfold gapScore at hsc2
    omega
  have hlt := Nat.lt_floor_add_one ((Real.pi - W'.width) / lam)
  rw [hfl, div_lt_iff₀ hlam] at hlt
  push_cast at hlt ⊢
  linarith

/-- **Actual outside-gap plateau.** Original actual n4 LOW minimum-counter
Model with cap 16 (its potential is 17), two distinct original zero-score
targets `p` and `p.succAbove q`, and a surviving original full-hull observer
of positive original score. The original and restricted actual hull Windows
are constructed internally; the restricted physical outside gap has the
original outside score `t` and is strictly below `(t + 2) * lam`. -/
theorem actual_zero_pair_outside_gap_plateau {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) (he : e ≠ 0) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0)
    (hqzero : rowScore lam (directionRow o e c (p.succAbove q)) = 0)
    (a : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))))
    (hhull : IsHullVertex c (p.succAbove (q.succAbove a))) :
    potential lam (directionRows o e c) = 17 ∧
      ∃ (W : ActualHullRayWindow.Window o c lam (p.succAbove (q.succAbove a)))
        (W' : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam a),
        gapScore lam (Real.pi - W'.width) = gapScore lam (Real.pi - W.width) ∧
          Real.pi - W.width ≤ Real.pi - W'.width ∧
          Real.pi - W'.width <
            ((gapScore lam (Real.pi - W.width) : ℕ) + 2 : ℝ) * lam := by
  have hleg2 : Section4Legality ((c ∘ p.succAbove) ∘ q.succAbove) lam :=
    (H.legality.erase p).erase q
  have hhull2 : IsHullVertex ((c ∘ p.succAbove) ∘ q.succAbove) a :=
    isHullVertex_restrict (φ := fun i => p.succAbove (q.succAbove i)) (fun _ => rfl) hhull
  obtain ⟨W⟩ := ActualHullRayWindow.exists_actual_hull_ray_window o (by omega)
    H.legality _ hhull
  obtain ⟨W'⟩ := ActualHullRayWindow.exists_actual_hull_ray_window o hs hleg2 a hhull2
  exact ⟨(ActualZeroPairDeletionBudget.actual_zero_pair_deletion_budget
      hs o e H p q hpzero hqzero).1,
    W, W', actual_zero_pair_outside_gap_plateau_of_windows hs e he H p q hpzero hqzero a
      hpos W W'⟩

end Plateau

#print axioms wrap_step
#print axioms row_pairwise_lt
#print axioms theta_transport
#print axioms row_wrap
#print axioms isHullVertex_restrict
#print axioms actual_zero_pair_outside_gap_plateau_of_windows
#print axioms actual_zero_pair_outside_gap_plateau

end Jsp404.DevinF17HullGap
