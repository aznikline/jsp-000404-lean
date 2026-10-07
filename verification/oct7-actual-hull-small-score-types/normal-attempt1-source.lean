import Jsp000404.ActualHullRayWindow
import Jsp000404.ChartInvariance
import Jsp000404.Induction
import Mathlib.Data.List.Pairwise

set_option autoImplicit false

/-!
Actual small-score types at vertices of the full original hull.

The public producers choose their physical Window internally. The full
direction row, its two extrema, its wrap gap, and its internal gap cut
are all derived from the original centers. No caller supplies a cone,
an angular array, or a partition.

This source is prepared statically. Its check state is recorded separately.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.ActualHullSmallScoreTypes

private noncomputable def innerGaps (l : List ℝ) : List ℝ :=
  (l.dropLast.zip l.tail).map (fun ab => cyclicDiff ab.1 ab.2)

private theorem cyclicDiff_eq_sub_of_le {a b : ℝ} (hab : a ≤ b) :
    cyclicDiff a b = b - a := by
  by_cases h : a = b
  · simp [cyclicDiff, h]
  · have hlt : a < b := lt_of_le_of_ne hab h
    simp [cyclicDiff, h, hlt]

private theorem innerGaps_cons (a b : ℝ) (l : List ℝ) :
    innerGaps (a :: b :: l) = cyclicDiff a b :: innerGaps (b :: l) := by
  simp [innerGaps, List.dropLast_cons_cons]

/-- A positive internal list gap has actual adjacent endpoints. The
no-middle conclusion ranges over the complete list, not a subset. -/
private theorem innerGap_spec (l : List ℝ) :
    l.SortedLE → ∀ g, g ∈ innerGaps l →
      ∃ a b : ℝ, a ∈ l ∧ b ∈ l ∧ a ≤ b ∧ g = b - a ∧
        ∀ z ∈ l, z ≤ a ∨ b ≤ z := by
  induction l with
  | nil =>
      intro hs g hg
      simp [innerGaps] at hg
  | cons a l ih =>
      intro hs g hg
      cases l with
      | nil => simp [innerGaps] at hg
      | cons b bs =>
          have hp := List.pairwise_cons.mp hs.pairwise
          have ht : (b :: bs).SortedLE := hp.2.sortedLE
          have hab : a ≤ b := hp.1 b (by simp)
          rw [innerGaps_cons, List.mem_cons] at hg
          rcases hg with hg | hg
          · refine ⟨a, b, by simp, by simp, hab,
              hg.trans (cyclicDiff_eq_sub_of_le hab), ?_⟩
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inl le_rfl
            · exact Or.inr (by simpa using ht.pairwise.rel_head hz)
          · obtain ⟨u, v, hu, hv, huv, hgap, hcut⟩ := ih ht g hg
            refine ⟨u, v, List.mem_cons_of_mem _ hu,
              List.mem_cons_of_mem _ hv, huv, hgap, ?_⟩
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inl (hp.1 u hu)
            · exact hcut z hz

private theorem innerGaps_nonneg {l : List ℝ} (hs : l.SortedLE) :
    ∀ g ∈ innerGaps l, 0 ≤ g := by
  intro g hg
  obtain ⟨a, b, _, _, hab, rfl, _⟩ := innerGap_spec l hs g hg
  exact sub_nonneg.mpr hab

private theorem linRep_coe_of_mem {x : ℝ} (hx : x ∈ Set.Ico 0 Real.pi) :
    linRep (x : Real.Angle) = x :=
  (eq_linRep_of_int_pi hx ⟨0, by simp⟩).symm

private theorem window_dirRep {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (j : Fin s) (hj : j ≠ p) :
    dirRep o W.base c p j = W.theta j := by
  unfold dirRep
  rw [W.actual_direction j hj]
  exact linRep_coe_of_mem
    ⟨(W.theta_mem j hj).1, ((W.theta_mem j hj).2).trans_lt W.width_lt_pi⟩

private theorem window_row_mem {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p) :
    ∀ x ∈ directionRow o W.base c p, x ∈ Set.Icc 0 W.width := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := (mem_directionRow o W.base c).mp hx
  rw [window_dirRep W j hj]
  exact W.theta_mem j hj

private theorem window_zero_mem {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p) :
    (0 : ℝ) ∈ directionRow o W.base c p := by
  apply (mem_directionRow o W.base c).mpr
  refine ⟨W.left, W.left_ne_center, ?_⟩
  rw [window_dirRep W W.left W.left_ne_center, W.left_coordinate]

private theorem window_width_mem {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p) :
    W.width ∈ directionRow o W.base c p := by
  apply (mem_directionRow o W.base c).mpr
  refine ⟨W.right, W.right_ne_center, ?_⟩
  rw [window_dirRep W W.right W.right_ne_center, W.right_coordinate]

private theorem window_row_ne_nil {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p) :
    directionRow o W.base c p ≠ [] :=
  List.ne_nil_of_mem (window_zero_mem W)

private theorem window_row_head {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (hne : directionRow o W.base c p ≠ []) :
    (directionRow o W.base c p).head hne = 0 := by
  have h0 := (window_row_mem W _ (List.head_mem hne)).1
  have hle : (directionRow o W.base c p).head hne ≤ 0 := by
    simpa using (directionRow_sorted o W.base c p).pairwise.rel_head
      (window_zero_mem W)
  exact le_antisymm hle h0

private theorem window_row_last {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (hne : directionRow o W.base c p ≠ []) :
    (directionRow o W.base c p).getLast hne = W.width := by
  have hle := (window_row_mem W _ (List.getLast_mem hne)).2
  have hge : W.width ≤ (directionRow o W.base c p).getLast hne := by
    simpa using (directionRow_sorted o W.base c p).pairwise.rel_getLast
      (window_width_mem W)
  exact le_antisymm hle hge

private theorem window_wrap {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (hne : directionRow o W.base c p ≠ []) :
    wrapGap (directionRow o W.base c p) hne = Real.pi - W.width := by
  have hnot : ¬ ∀ x ∈ directionRow o W.base c p,
      x = (directionRow o W.base c p).head hne := by
    intro h
    have hwidth := h W.width (window_width_mem W)
    rw [window_row_head W hne] at hwidth
    linarith [W.width_pos]
  rw [wrapGap, if_neg hnot, window_row_head W hne, window_row_last W hne]
  simp [cyclicDiff, ne_of_gt W.width_pos, not_lt_of_ge W.width_pos.le]

private theorem window_wrap_mem {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p) :
    Real.pi - W.width ∈ cycGaps (directionRow o W.base c p) := by
  have hne := window_row_ne_nil W
  rw [cycGaps_eq_map_append_wrap _ hne, window_wrap W hne]
  exact List.mem_append_right _ (by simp)

private theorem window_inner_sum {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p) :
    (innerGaps (directionRow o W.base c p)).sum = W.width := by
  have hne := window_row_ne_nil W
  have h := cycGaps_sum_eq_pi (directionRow_sorted o W.base c p) hne
  rw [cycGaps_eq_map_append_wrap _ hne, List.sum_append,
    List.sum_cons, List.sum_nil, window_wrap W hne] at h
  change (innerGaps (directionRow o W.base c p)).sum +
    (Real.pi - W.width + 0) = Real.pi at h
  linarith

private theorem window_score_split {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p) :
    rowScore lam (directionRow o W.base c p) =
      ((innerGaps (directionRow o W.base c p)).map (gapScore lam)).sum +
        gapScore lam (Real.pi - W.width) := by
  have hne := window_row_ne_nil W
  unfold rowScore
  rw [cycGaps_eq_map_append_wrap _ hne, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, window_wrap W hne]
  rfl

/-- The smallest actual full-list support consumed by the classification. -/
structure Support {s : ℕ} (o : Orientation ℝ Plane₂ (Fin 2))
    (c : Fin s → Plane₂) (lam : ℝ) (p : Fin s) where
  window : ActualHullRayWindow.Window o c lam p
  nonempty : directionRow o window.base c p ≠ []
  dirRep_eq : ∀ j, j ≠ p → dirRep o window.base c p j = window.theta j
  head_eq : (directionRow o window.base c p).head nonempty = 0
  last_eq : (directionRow o window.base c p).getLast nonempty = window.width
  wrap_eq : wrapGap (directionRow o window.base c p) nonempty =
    Real.pi - window.width
  wrap_mem : Real.pi - window.width ∈ cycGaps (directionRow o window.base c p)
  outside_ge_scale : lam ≤ Real.pi - window.width
  outside_floor_pos : 1 ≤ ⌊(Real.pi - window.width) / lam⌋₊

theorem exists_actual_hull_full_row_support {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (hs : 3 ≤ s)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hp : IsHullVertex c p) :
    Nonempty (Support o c lam p) := by
  obtain ⟨W⟩ := ActualHullRayWindow.exists_actual_hull_ray_window o hs hleg p hp
  exact ⟨{
    window := W
    nonempty := window_row_ne_nil W
    dirRep_eq := window_dirRep W
    head_eq := window_row_head W _
    last_eq := window_row_last W _
    wrap_eq := window_wrap W _
    wrap_mem := window_wrap_mem W
    outside_ge_scale := by linarith [W.width_le_legality]
    outside_floor_pos := (one_le_floor_iff_ge lam _ hleg.lam_pos).mpr
      (by linarith [W.width_le_legality]) }⟩

private theorem score_mul_lower {lam g : ℝ} (hlam : 0 < lam) (hg : 0 ≤ g)
    {k : ℕ} (hk : 1 ≤ k) (hscore : k ≤ gapScore lam g) :
    ((k + 1 : ℕ) : ℝ) * lam ≤ g := by
  have hf : k + 1 ≤ ⌊g / lam⌋₊ := by
    unfold gapScore at hscore
    omega
  have hf' : ((k + 1 : ℕ) : ℝ) ≤ (⌊g / lam⌋₊ : ℝ) := by exact_mod_cast hf
  exact (le_div_iff₀ hlam).mp
    (hf'.trans (Nat.floor_le (div_nonneg hg hlam.le)))

private theorem score_zero_gap_lt_two {lam g : ℝ} (hlam : 0 < lam)
    (hscore : gapScore lam g = 0) : g < 2 * lam := by
  have hf : ⌊g / lam⌋₊ ≤ 1 := by unfold gapScore at hscore; omega
  have hf' : (⌊g / lam⌋₊ : ℝ) ≤ 1 := by exact_mod_cast hf
  have hlt := Nat.lt_floor_add_one (g / lam)
  apply (div_lt_iff₀ hlam).mp
  linarith

private theorem exists_positive (l : List ℕ) :
    0 < l.sum → ∃ a ∈ l, 0 < a := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro h
      by_cases ha : 0 < a
      · exact ⟨a, by simp, ha⟩
      · have ha0 : a = 0 := by omega
        obtain ⟨b, hb, hbp⟩ := ih (by simpa [ha0] using h)
        exact ⟨b, by simp [hb], hbp⟩

private theorem exists_gap_score_one {lam : ℝ} {l : List ℝ}
    (hsum : (l.map (gapScore lam)).sum = 1) :
    ∃ g ∈ l, gapScore lam g = 1 := by
  obtain ⟨a, ha, hapos⟩ := exists_positive (l.map (gapScore lam)) (by omega)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
  have hle : gapScore lam g ≤ (l.map (gapScore lam)).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨g, hg, rfl⟩)
  exact ⟨g, hg, by omega⟩

private theorem twice_mul_score_sum_le (lam : ℝ) (hlam : 0 < lam)
    (l : List ℝ) :
    (∀ g ∈ l, 0 ≤ g) → (∀ g ∈ l, gapScore lam g ≤ 1) →
      (2 * lam) * ((l.map (gapScore lam)).sum : ℝ) ≤ l.sum := by
  induction l with
  | nil => simp
  | cons g l ih =>
      intro hnonneg hsmall
      have hg0 := hnonneg g (by simp)
      have hg1 := hsmall g (by simp)
      have hper : (2 * lam) * (gapScore lam g : ℝ) ≤ g := by
        have hc : gapScore lam g = 0 ∨ gapScore lam g = 1 := by omega
        rcases hc with hc | hc
        · simpa [hc] using hg0
        · have h := score_mul_lower hlam hg0 (by omega : 1 ≤ 1) (by omega)
          simpa [hc] using h
      have ht := ih
        (fun x hx => hnonneg x (List.mem_cons_of_mem _ hx))
        (fun x hx => hsmall x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add]
      linarith

private theorem exists_gap_score_two {lam : ℝ} (hlam : 0 < lam)
    {l : List ℝ} (hnonneg : ∀ g ∈ l, 0 ≤ g)
    (hsum : (l.map (gapScore lam)).sum = 2) (hwidth : l.sum < 4 * lam) :
    ∃ g ∈ l, gapScore lam g = 2 := by
  by_contra hnot
  push_neg at hnot
  have hsmall : ∀ g ∈ l, gapScore lam g ≤ 1 := by
    intro g hg
    have hle : gapScore lam g ≤ (l.map (gapScore lam)).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨g, hg, rfl⟩)
    have hne := hnot g hg
    omega
  have hmass := twice_mul_score_sum_le lam hlam l hnonneg hsmall
  rw [hsum] at hmass
  norm_num at hmass
  linarith

private theorem window_angle {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    (hleg : Section4Legality c lam) (i j : Fin s) (hi : i ≠ p) (hj : j ≠ p) :
    ∠ (c i) (c p) (c j) = |W.theta j - W.theta i| := by
  have hui : c i - c p ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hi)
  have huj : c j - c p ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hj)
  change InnerProductGeometry.angle (c i - c p) (c j - c p) = _
  rw [o.angle_eq_abs_oangle_toReal hui huj,
    ← o.oangle_sub_left W.base_ne_zero hui huj,
    W.actual_direction i hi, W.actual_direction j hj, ← Real.Angle.coe_sub]
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr
    ⟨by linarith [(W.theta_mem j hj).1, (W.theta_mem i hi).2, W.width_lt_pi],
      by linarith [(W.theta_mem j hj).2, (W.theta_mem i hi).1, W.width_lt_pi]⟩]

/-- A cut at an internally selected actual adjacent gap. -/
structure Clumps {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p)
    (score : ℕ) (separation bound : ℝ) where
  leftRay : Fin s
  rightRay : Fin s
  left_ne_center : leftRay ≠ p
  right_ne_center : rightRay ≠ p
  left_lt_right : W.theta leftRay < W.theta rightRay
  no_middle : ∀ i, i ≠ p →
    W.theta i ≤ W.theta leftRay ∨ W.theta rightRay ≤ W.theta i
  actual_gap : W.theta rightRay - W.theta leftRay ∈
    cycGaps (directionRow o W.base c p)
  gap_score : gapScore lam (W.theta rightRay - W.theta leftRay) = score
  gap_lower : separation ≤ W.theta rightRay - W.theta leftRay
  remaining_width : W.theta leftRay + (W.width - W.theta rightRay) ≤ bound

noncomputable def Clumps.code {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    {W : ActualHullRayWindow.Window o c lam p}
    {score : ℕ} {separation bound : ℝ}
    (D : Clumps W score separation bound) (i : Fin s) : Bool := by
  classical
  exact if W.theta i ≤ W.theta D.leftRay then true else false

theorem Clumps.actual_witnesses {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    {W : ActualHullRayWindow.Window o c lam p}
    {score : ℕ} {separation bound : ℝ} (D : Clumps W score separation bound) :
    ∃ i j : Fin s, i ≠ p ∧ j ≠ p ∧ i ≠ j ∧
      D.code i = true ∧ D.code j = false := by
  refine ⟨D.leftRay, D.rightRay, D.left_ne_center, D.right_ne_center, ?_, ?_, ?_⟩
  · intro h
    have hlt := D.left_lt_right
    simpa only [h, lt_self_iff_false] using hlt
  · simp [Clumps.code]
  · simp [Clumps.code, not_le.mpr D.left_lt_right]

theorem Clumps.same_angle_le {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    {W : ActualHullRayWindow.Window o c lam p}
    {score : ℕ} {separation bound : ℝ} (D : Clumps W score separation bound)
    (hleg : Section4Legality c lam) (i j : Fin s) (hi : i ≠ p) (hj : j ≠ p)
    (hsame : D.code i = D.code j) : ∠ (c i) (c p) (c j) ≤ bound := by
  classical
  have hleft0 := (W.theta_mem D.leftRay D.left_ne_center).1
  have hright := (W.theta_mem D.rightRay D.right_ne_center).2
  rw [window_angle W hleg i j hi hj]
  by_cases hci : W.theta i ≤ W.theta D.leftRay <;>
    by_cases hcj : W.theta j ≤ W.theta D.leftRay
  · apply abs_sub_le_iff.mpr
    constructor <;> linarith [(W.theta_mem i hi).1, (W.theta_mem j hj).1,
      D.remaining_width]
  · simp [Clumps.code, hci, hcj] at hsame
  · simp [Clumps.code, hci, hcj] at hsame
  · have hbi := (D.no_middle i hi).resolve_left hci
    have hbj := (D.no_middle j hj).resolve_left hcj
    apply abs_sub_le_iff.mpr
    constructor <;> linarith [(W.theta_mem i hi).2, (W.theta_mem j hj).2,
      D.remaining_width]

theorem Clumps.different_angle_ge {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    {W : ActualHullRayWindow.Window o c lam p}
    {score : ℕ} {separation bound : ℝ} (D : Clumps W score separation bound)
    (hleg : Section4Legality c lam) (i j : Fin s) (hi : i ≠ p) (hj : j ≠ p)
    (hdiff : D.code i ≠ D.code j) : separation ≤ ∠ (c i) (c p) (c j) := by
  classical
  rw [window_angle W hleg i j hi hj]
  by_cases hci : W.theta i ≤ W.theta D.leftRay <;>
    by_cases hcj : W.theta j ≤ W.theta D.leftRay
  · simp [Clumps.code, hci, hcj] at hdiff
  · have hbj := (D.no_middle j hj).resolve_left hcj
    rw [abs_of_nonneg (by linarith [D.left_lt_right] :
      0 ≤ W.theta j - W.theta i)]
    linarith [D.gap_lower]
  · have hbi := (D.no_middle i hi).resolve_left hci
    rw [abs_of_nonpos (by linarith [D.left_lt_right] :
      W.theta j - W.theta i ≤ 0)]
    linarith [D.gap_lower]
  · simp [Clumps.code, hci, hcj] at hdiff

private theorem clumps_of_internal_gap {s : ℕ}
    {o : Orientation ℝ Plane₂ (Fin 2)} {c : Fin s → Plane₂}
    {lam : ℝ} {p : Fin s} (W : ActualHullRayWindow.Window o c lam p)
    {g separation bound : ℝ} {score : ℕ}
    (hg : g ∈ innerGaps (directionRow o W.base c p))
    (hscore : gapScore lam g = score) (hsep : 0 < separation)
    (hgap : separation ≤ g) (hbound : W.width - g ≤ bound) :
    Nonempty (Clumps W score separation bound) := by
  obtain ⟨a, b, ha, hb, hab, hgab, hcut⟩ :=
    innerGap_spec _ (directionRow_sorted o W.base c p) g hg
  obtain ⟨i, hi, hai⟩ := (mem_directionRow o W.base c).mp ha
  obtain ⟨j, hj, hbj⟩ := (mem_directionRow o W.base c).mp hb
  have hia : W.theta i = a := (hai.trans (window_dirRep W i hi)).symm
  have hjb : W.theta j = b := (hbj.trans (window_dirRep W j hj)).symm
  have hlt : W.theta i < W.theta j := by rw [hia, hjb]; linarith
  refine ⟨{
    leftRay := i
    rightRay := j
    left_ne_center := hi
    right_ne_center := hj
    left_lt_right := hlt
    no_middle := ?_
    actual_gap := ?_
    gap_score := ?_
    gap_lower := ?_
    remaining_width := ?_ }⟩
  · intro k hk
    have hmem : W.theta k ∈ directionRow o W.base c p := by
      rw [← window_dirRep W k hk]
      exact (mem_directionRow o W.base c).mpr ⟨k, hk, rfl⟩
    simpa only [hia, hjb] using hcut (W.theta k) hmem
  · rw [hia, hjb, ← hgab,
      cycGaps_eq_map_append_wrap _ (window_row_ne_nil W)]
    exact List.mem_append_left _ hg
  · rw [hia, hjb, ← hgab]
    exact hscore
  · rw [hia, hjb, ← hgab]
    exact hgap
  · rw [hia, hjb]
    linarith

inductive LightKind {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p) : Type
  | LB (outside_score : gapScore lam (Real.pi - W.width) = 1)
      (cone : W.width ≤ Real.pi - 2 * lam) : LightKind W
  | LI (outside_score : gapScore lam (Real.pi - W.width) = 0)
      (cone : Real.pi - 2 * lam < W.width)
      (clumps : Clumps W 1 (2 * lam) (Real.pi - 3 * lam)) : LightKind W

inductive HeavyKind {s : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)}
    {c : Fin s → Plane₂} {lam : ℝ} {p : Fin s}
    (W : ActualHullRayWindow.Window o c lam p) : Type
  | HA (outside_score : gapScore lam (Real.pi - W.width) = 2)
      (cone : W.width ≤ Real.pi - 3 * lam) : HeavyKind W
  | HM (outside_score : gapScore lam (Real.pi - W.width) = 1)
      (cone_lower : 2 * lam ≤ W.width)
      (cone_upper : W.width ≤ Real.pi - 2 * lam)
      (clumps : Clumps W 1 (2 * lam) (Real.pi - 4 * lam)) : HeavyKind W
  | HO (outside_score : gapScore lam (Real.pi - W.width) = 0)
      (cone : 3 * lam ≤ W.width)
      (clumps : Clumps W 2 (3 * lam) (Real.pi - 4 * lam)) : HeavyKind W

/-- The caller supplies the original score, not an outside-gap type or cut. -/
theorem exists_actual_hull_one_type {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (p : Fin s) (hp : IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 1) :
    Nonempty (Sigma fun W : ActualHullRayWindow.Window o c lam p => LightKind W) := by
  obtain ⟨W⟩ := ActualHullRayWindow.exists_actual_hull_ray_window o hs hleg p hp
  have hscoreW : rowScore lam (directionRow o W.base c p) = 1 :=
    (rowScore_directionRow_reference_eq o e W.base he W.base_ne_zero c hleg.inj p lam).symm.trans hscore
  have hsplit := window_score_split W
  have hout : gapScore lam (Real.pi - W.width) ≤ 1 := by omega
  have hE : lam ≤ Real.pi - W.width := by linarith [W.width_le_legality]
  have hE0 : 0 ≤ Real.pi - W.width := hleg.lam_pos.le.trans hE
  have hc : gapScore lam (Real.pi - W.width) = 0 ∨
      gapScore lam (Real.pi - W.width) = 1 := by omega
  rcases hc with hc | hc
  · have hsum : ((innerGaps (directionRow o W.base c p)).map (gapScore lam)).sum = 1 := by omega
    obtain ⟨g, hg, hgs⟩ := exists_gap_score_one hsum
    have hnonneg := innerGaps_nonneg (directionRow_sorted o W.base c p)
    have hg0 := hnonneg g hg
    have hbig : 2 * lam ≤ g := by
      have h := score_mul_lower hleg.lam_pos hg0 (by omega : 1 ≤ 1) (by omega)
      simpa using h
    have hbound : W.width - g ≤ Real.pi - 3 * lam := by
      linarith [W.width_le_legality]
    obtain ⟨D⟩ := clumps_of_internal_gap W hg hgs (by linarith [hleg.lam_pos]) hbig hbound
    have hcone : Real.pi - 2 * lam < W.width := by
      have h := score_zero_gap_lt_two hleg.lam_pos hc
      linarith
    exact ⟨⟨W, LightKind.LI hc hcone D⟩⟩
  · have hbig : 2 * lam ≤ Real.pi - W.width := by
      have h := score_mul_lower hleg.lam_pos hE0 (by omega : 1 ≤ 1) (by omega)
      simpa using h
    exact ⟨⟨W, LightKind.LB hc (by linarith)⟩⟩

/-- Score two is classified from its actual wrap and actual internal sum.
The HO branch rules out two score-one internal gaps using alpha < 4*lam. -/
theorem exists_actual_hull_two_type {s : ℕ} (hs : 3 ≤ s)
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hlo : 2 * Real.pi / 9 < lam) (p : Fin s) (hp : IsHullVertex c p)
    (hscore : rowScore lam (directionRow o e c p) = 2) :
    Nonempty (Sigma fun W : ActualHullRayWindow.Window o c lam p => HeavyKind W) := by
  obtain ⟨W⟩ := ActualHullRayWindow.exists_actual_hull_ray_window o hs hleg p hp
  have hscoreW : rowScore lam (directionRow o W.base c p) = 2 :=
    (rowScore_directionRow_reference_eq o e W.base he W.base_ne_zero c hleg.inj p lam).symm.trans hscore
  have hsplit := window_score_split W
  have hout : gapScore lam (Real.pi - W.width) ≤ 2 := by omega
  have hE : lam ≤ Real.pi - W.width := by linarith [W.width_le_legality]
  have hE0 : 0 ≤ Real.pi - W.width := hleg.lam_pos.le.trans hE
  have hc : gapScore lam (Real.pi - W.width) = 0 ∨
      gapScore lam (Real.pi - W.width) = 1 ∨
      gapScore lam (Real.pi - W.width) = 2 := by omega
  rcases hc with hc | hc | hc
  · have hsum : ((innerGaps (directionRow o W.base c p)).map (gapScore lam)).sum = 2 := by omega
    have hnonneg := innerGaps_nonneg (directionRow_sorted o W.base c p)
    have hwidth : (innerGaps (directionRow o W.base c p)).sum < 4 * lam := by
      rw [window_inner_sum W]
      have hpi : Real.pi < 5 * lam := by linarith [Real.pi_pos]
      linarith [W.width_le_legality]
    obtain ⟨g, hg, hgs⟩ := exists_gap_score_two hleg.lam_pos hnonneg hsum hwidth
    have hg0 := hnonneg g hg
    have hbig : 3 * lam ≤ g := by
      have h := score_mul_lower hleg.lam_pos hg0 (by omega : 1 ≤ 2) (by omega)
      simpa using h
    have hle : g ≤ W.width := by
      have h := le_sum_of_mem_of_nonneg _ hnonneg hg
      simpa only [window_inner_sum W] using h
    have hbound : W.width - g ≤ Real.pi - 4 * lam := by
      linarith [W.width_le_legality]
    obtain ⟨D⟩ := clumps_of_internal_gap W hg hgs (by linarith [hleg.lam_pos]) hbig hbound
    exact ⟨⟨W, HeavyKind.HO hc (hbig.trans hle) D⟩⟩
  · have hsum : ((innerGaps (directionRow o W.base c p)).map (gapScore lam)).sum = 1 := by omega
    obtain ⟨g, hg, hgs⟩ := exists_gap_score_one hsum
    have hnonneg := innerGaps_nonneg (directionRow_sorted o W.base c p)
    have hg0 := hnonneg g hg
    have hbig : 2 * lam ≤ g := by
      have h := score_mul_lower hleg.lam_pos hg0 (by omega : 1 ≤ 1) (by omega)
      simpa using h
    have hle : g ≤ W.width := by
      have h := le_sum_of_mem_of_nonneg _ hnonneg hg
      simpa only [window_inner_sum W] using h
    have houter : 2 * lam ≤ Real.pi - W.width := by
      have h := score_mul_lower hleg.lam_pos hE0 (by omega : 1 ≤ 1) (by omega)
      simpa using h
    have hbound : W.width - g ≤ Real.pi - 4 * lam := by linarith
    obtain ⟨D⟩ := clumps_of_internal_gap W hg hgs (by linarith [hleg.lam_pos]) hbig hbound
    exact ⟨⟨W, HeavyKind.HM hc (hbig.trans hle) (by linarith) D⟩⟩
  · have houter : 3 * lam ≤ Real.pi - W.width := by
      have h := score_mul_lower hleg.lam_pos hE0 (by omega : 1 ≤ 2) (by omega)
      simpa using h
    exact ⟨⟨W, HeavyKind.HA hc (by linarith)⟩⟩

#print axioms exists_actual_hull_full_row_support
#print axioms Clumps.actual_witnesses
#print axioms Clumps.same_angle_le
#print axioms Clumps.different_angle_ge
#print axioms exists_actual_hull_one_type
#print axioms exists_actual_hull_two_type

end Jsp404.ActualHullSmallScoreTypes
