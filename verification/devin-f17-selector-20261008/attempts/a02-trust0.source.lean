import Jsp000404.DevinF17HullGap

/-!
Retained original hull boundary events after two original zero deletions.

Let `H` be an actual n4 LOW minimum-counter `Model` with cap 16, and let
`p` and `p.succAbove q` be two distinct original zero-score targets. For a
retained original hull observer `a`, write `E` for its actual restricted
outside gap `π - W'.width`, where `W'` is any actual hull Window of the
twice-deleted configuration at `a`, and `t` for its original outside score.

A *boundary event* at `a` is `(t + 2) * lam ≤ E`. This module proves, from
the original Model alone:

* positive original observers have no boundary event (via the outside-gap
  plateau of `DevinF17HullGap`);
* a zero original hull observer has `t = 0` and `E < 3 * lam`;
* at most one retained original hull observer has a boundary event.

No gap budget, score bound, cover, partition or restricted Model is supplied
by the caller. The existence of a target pair producing two events (the F17
selector) is NOT proved here.
-/

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.DevinF17Selector

open Jsp404.DevinF17HullGap

variable {o : Orientation ℝ Plane₂ (Fin 2)}

/-- The wrap gap is one of the cyclic gaps, so its score is a lower bound
for the row score. -/
theorem gapScore_wrapGap_le_rowScore (lam : ℝ) {l : List ℝ} (hne : l ≠ []) :
    gapScore lam (wrapGap l hne) ≤ rowScore lam l := by
  unfold rowScore
  apply List.le_sum_of_mem
  apply List.mem_map_of_mem
  unfold cycGaps
  simp [hne]

/-- At an actual hull Window of any injective configuration, the outside
gap score `gapScore lam (π - W.width)` is at most the actual row score, in
every nonzero reference direction. -/
theorem outside_score_le_rowScore {r : ℕ} {c : Fin r → Plane₂} {lam lam' : ℝ}
    (hinj : Function.Injective c) {a : Fin r}
    (W : ActualHullRayWindow.Window o c lam' a) (e : Plane₂) (he : e ≠ 0) :
    gapScore lam (Real.pi - W.width) ≤ rowScore lam (directionRow o e c a) := by
  have hne : directionRow o W.base c a ≠ [] :=
    List.ne_nil_of_mem ((mem_directionRow o W.base c).mpr ⟨W.left, W.left_ne_center, rfl⟩)
  obtain ⟨-, hwrap⟩ := row_wrap (φ := fun i => i) hinj (fun _ _ h => h) (fun _ => rfl)
    W W hne
  rw [rowScore_directionRow_reference_eq o e W.base he W.base_ne_zero c hinj a lam,
    ← hwrap]
  exact gapScore_wrapGap_le_rowScore lam hne

/-- Exact restricted score ledger: the twice-deleted row score of a retained
point is its original score plus the actual second-deletion gain. -/
theorem restricted_score_eq {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0) (a : Fin s) :
    rowScore lam (directionRow o e ((c ∘ p.succAbove) ∘ q.succAbove) a) =
      rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))) +
        rowGain lam (directionRow o e (c ∘ p.succAbove) (q.succAbove a))
          (deleteIndex o e (c ∘ p.succAbove) q (q.succAbove a)) := by
  classical
  have hlam : 0 < lam := H.legality.lam_pos
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
  have h1 := hrows (q.succAbove a)
  unfold rowGain
  rw [← eraseIdx_directionRow o e (c' := c ∘ p.succAbove) q a]
  omega

/-- A retained original zero-score hull observer has restricted outside gap
strictly below `3 * lam` for every actual restricted hull Window. -/
theorem zero_observer_outside_lt_three {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) (he : e ≠ 0) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0)
    (hqzero : rowScore lam (directionRow o e c (p.succAbove q)) = 0)
    (a : Fin s)
    (hazero : rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))) = 0)
    (W' : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam a) :
    Real.pi - W'.width < 3 * lam := by
  classical
  have hlam : 0 < lam := H.legality.lam_pos
  have hinj2 := ((H.legality.erase p).erase q).inj
  obtain ⟨-, -, -, -, -, hg1, -⟩ :=
    ActualZeroPairDeletionBudget.actual_zero_pair_deletion_budget hs o e H p q hpzero hqzero
  have hg := hg1 (q.succAbove a) (Fin.succAbove_ne q a)
  have heq := restricted_score_eq hs e H p q hpzero a
  have hout := outside_score_le_rowScore (lam := lam) hinj2 W' e he
  have hle : gapScore lam (Real.pi - W'.width) ≤ 1 := by
    simp only at hg
    omega
  have hfl : ⌊(Real.pi - W'.width) / lam⌋₊ < 3 := by
    unfold gapScore at hle
    omega
  have := (Nat.floor_lt (div_nonneg (by linarith [W'.width_lt_pi]) hlam.le)).mp hfl
  rw [div_lt_iff₀ hlam] at this
  push_cast at this
  linarith

/-- Two distinct retained original zero-score hull observers cannot both
have restricted outside gap at least `2 * lam`. -/
theorem two_zero_observers_not_both_wide {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) (he : e ≠ 0) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0)
    (hqzero : rowScore lam (directionRow o e c (p.succAbove q)) = 0)
    (a b : Fin s) (hab : a ≠ b)
    (hazero : rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))) = 0)
    (hbzero : rowScore lam (directionRow o e c (p.succAbove (q.succAbove b))) = 0)
    (Wa : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam a)
    (Wb : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam b) :
    ¬ (2 * lam ≤ Real.pi - Wa.width ∧ 2 * lam ≤ Real.pi - Wb.width) := by
  classical
  rintro ⟨ha, hb⟩
  have hlam : 0 < lam := H.legality.lam_pos
  have hinj2 := ((H.legality.erase p).erase q).inj
  obtain ⟨-, -, -, -, -, -, hcard, -⟩ :=
    ActualZeroPairDeletionBudget.actual_zero_pair_deletion_budget hs o e H p q hpzero hqzero
  have wide : ∀ x : Fin s,
      rowScore lam (directionRow o e c (p.succAbove (q.succAbove x))) = 0 →
      ∀ Wx : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam x,
      2 * lam ≤ Real.pi - Wx.width →
      1 ≤ rowGain lam (directionRow o e (c ∘ p.succAbove) (q.succAbove x))
        (deleteIndex o e (c ∘ p.succAbove) q (q.succAbove x)) := by
    intro x hx Wx hwx
    have heq := restricted_score_eq hs e H p q hpzero x
    have hout := outside_score_le_rowScore (lam := lam) hinj2 Wx e he
    have hge : 1 ≤ gapScore lam (Real.pi - Wx.width) := by
      unfold gapScore
      have : 2 ≤ ⌊(Real.pi - Wx.width) / lam⌋₊ := by
        apply Nat.le_floor
        rw [le_div_iff₀ hlam]
        push_cast
        linarith
      omega
    omega
  have hsub : ({q.succAbove a, q.succAbove b} : Finset (Fin (s + 1))) ⊆
      (Finset.univ.erase q).filter (fun i =>
        1 ≤ rowGain lam (directionRow o e (c ∘ p.succAbove) i)
          (deleteIndex o e (c ∘ p.succAbove) q i)) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Fin.succAbove_ne q a,
        Finset.mem_univ _⟩, wide a hazero Wa ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Fin.succAbove_ne q b,
        Finset.mem_univ _⟩, wide b hbzero Wb hb⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair (fun h => hab (Fin.succAbove_right_injective h))] at h2
  simp only at hcard
  omega

/-- **Boundary-event classification.** Let `W` be an actual original hull
Window and `W'` an actual restricted hull Window at a retained observer. If
`E = π - W'.width` reaches `(t + 2) * lam`, where `t` is the original outside
score, then the observer has original score zero, `t = 0`, and `E < 3 * lam`. -/
theorem boundary_event_zero {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) (he : e ≠ 0) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0)
    (hqzero : rowScore lam (directionRow o e c (p.succAbove q)) = 0)
    (a : Fin s)
    (W : ActualHullRayWindow.Window o c lam (p.succAbove (q.succAbove a)))
    (W' : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam a)
    (hev : ((gapScore lam (Real.pi - W.width) : ℕ) + 2 : ℝ) * lam ≤
      Real.pi - W'.width) :
    rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))) = 0 ∧
      gapScore lam (Real.pi - W.width) = 0 ∧ Real.pi - W'.width < 3 * lam := by
  have hzero : rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))) = 0 := by
    by_contra hne
    have hpos : 0 < rowScore lam (directionRow o e c (p.succAbove (q.succAbove a))) :=
      Nat.pos_of_ne_zero hne
    have := (actual_zero_pair_outside_gap_plateau_of_windows hs e he H p q hpzero hqzero a
      hpos W W').2.2
    linarith
  have ht : gapScore lam (Real.pi - W.width) = 0 := by
    have := outside_score_le_rowScore (lam := lam) H.legality.inj W e he
    omega
  exact ⟨hzero, ht, zero_observer_outside_lt_three hs e he H p q hpzero hqzero a hzero W'⟩

/-- **At most one boundary event.** Two retained original hull observers
whose restricted outside gaps both reach their original outside thresholds
`(t + 2) * lam` are the same observer. -/
theorem boundary_event_unique {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) (he : e ≠ 0) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1))
    (hpzero : rowScore lam (directionRow o e c p) = 0)
    (hqzero : rowScore lam (directionRow o e c (p.succAbove q)) = 0)
    (a b : Fin s)
    (Wa : ActualHullRayWindow.Window o c lam (p.succAbove (q.succAbove a)))
    (Wa' : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam a)
    (Wb : ActualHullRayWindow.Window o c lam (p.succAbove (q.succAbove b)))
    (Wb' : ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam b)
    (hea : ((gapScore lam (Real.pi - Wa.width) : ℕ) + 2 : ℝ) * lam ≤
      Real.pi - Wa'.width)
    (heb : ((gapScore lam (Real.pi - Wb.width) : ℕ) + 2 : ℝ) * lam ≤
      Real.pi - Wb'.width) :
    a = b := by
  by_contra hab
  obtain ⟨hza, hta, -⟩ := boundary_event_zero hs e he H p q hpzero hqzero a Wa Wa' hea
  obtain ⟨hzb, htb, -⟩ := boundary_event_zero hs e he H p q hpzero hqzero b Wb Wb' heb
  rw [hta] at hea
  rw [htb] at heb
  norm_num at hea heb
  exact two_zero_observers_not_both_wide hs e he H p q hpzero hqzero a b hab hza hzb Wa' Wb'
    ⟨by linarith, by linarith⟩

/-- Every retained original full-hull observer has actual original and
restricted hull Windows, so the event lemmas above apply to it. -/
theorem hull_observer_windows {s : ℕ} (hs : 3 ≤ s)
    (e : Plane₂) {rho upper lam : ℝ} {c : Fin (s + 2) → Plane₂}
    (H : ActualMinimalBandCounterexample.Model o e rho upper 16 (s + 2) c lam)
    (p : Fin (s + 2)) (q : Fin (s + 1)) (a : Fin s) (hhull : IsHullVertex c (p.succAbove (q.succAbove a))) :
    Nonempty (ActualHullRayWindow.Window o c lam (p.succAbove (q.succAbove a))) ∧
      Nonempty (ActualHullRayWindow.Window o ((c ∘ p.succAbove) ∘ q.succAbove) lam a) := by
  have hleg2 : Section4Legality ((c ∘ p.succAbove) ∘ q.succAbove) lam :=
    (H.legality.erase p).erase q
  exact ⟨ActualHullRayWindow.exists_actual_hull_ray_window o (by omega) H.legality _ hhull,
    ActualHullRayWindow.exists_actual_hull_ray_window o hs hleg2 a
      (isHullVertex_restrict (φ := fun i => p.succAbove (q.succAbove i)) (fun _ => rfl) hhull)⟩

#print axioms gapScore_wrapGap_le_rowScore
#print axioms outside_score_le_rowScore
#print axioms restricted_score_eq
#print axioms zero_observer_outside_lt_three
#print axioms two_zero_observers_not_both_wide
#print axioms boundary_event_zero
#print axioms boundary_event_unique
#print axioms hull_observer_windows

end Jsp404.DevinF17Selector
