import Jsp000404.NoSatFiveGeometry
import Jsp000404.GlobalFiveLowFloorBudget
import Jsp000404.GlobalFiveLowEndpointTerminal

/-!
Actual five-centre LOW exclusion, retaining all three triangle caps and the
four genuine cyclic row gaps. The wrap gap is pi plus minimum minus maximum.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.GlobalFiveLowEndpointGeometry

open GlobalFiveLowFloorBudget GlobalFiveLowEndpointTerminal



/-- The genuine four cyclic gaps of the sorted four-entry direction row.
The final entry is the whole wrap gap, with no cut at zero. -/
noncomputable def fourGaps (a b c d : ℝ) : Fin 4 → ℝ :=
  ![b - a, c - b, d - c, Real.pi + a - d]

/-- The four genuine cyclic gaps measured in units of `lam`. -/
noncomputable def normalizedGaps (lam a b c d : ℝ) : Fin 4 → ℝ :=
  fun j => fourGaps a b c d j / lam

theorem normalizedGaps_eq_vector (lam a b c d : ℝ) :
    normalizedGaps lam a b c d =
      ![(b - a) / lam, (c - b) / lam, (d - c) / lam,
        (Real.pi + a - d) / lam] := by
  funext j
  fin_cases j <;> simp [normalizedGaps, fourGaps]

theorem fourGaps_sum (a b c d : ℝ) :
    (∑ j : Fin 4, fourGaps a b c d j) = Real.pi := by
  simp [fourGaps, Fin.sum_univ_succ]

theorem normalizedGaps_sum (lam a b c d : ℝ) :
    (∑ j : Fin 4, normalizedGaps lam a b c d j) = Real.pi / lam := by
  unfold normalizedGaps
  rw [← Finset.sum_div, fourGaps_sum]

theorem gapAfter_four (a b c d : ℝ) (j : Fin 4) :
    gapAfter [a, b, c, d] j = fourGaps a b c d j := by
  fin_cases j <;> norm_num [gapAfter, fourGaps]
  all_goals ring

theorem cycGaps_four {a b c d : ℝ} (hs : [a, b, c, d].SortedLE) :
    cycGaps [a, b, c, d] = [b - a, c - b, d - c, Real.pi + a - d] := by
  rw [cycGaps_eq_ofFn_gapAfter hs]
  have hfun : (fun j : Fin [a, b, c, d].length => gapAfter [a, b, c, d] j) =
      fourGaps a b c d := by
    funext j
    exact gapAfter_four a b c d j
  rw [hfun]
  simp [fourGaps, List.ofFn_succ]

theorem normalizedGaps_nonneg {lam a b c d : ℝ} (hlam : 0 < lam)
    (hs : [a, b, c, d].SortedLE)
    (hmem : ∀ x ∈ [a, b, c, d], x ∈ Set.Ico 0 Real.pi) (j : Fin 4) :
    0 ≤ normalizedGaps lam a b c d j := by
  apply div_nonneg _ hlam.le
  rw [← gapAfter_four]
  exact gapAfter_nonneg hs hmem (by simp) j

theorem rowCells_four {lam a b c d : ℝ} (hs : [a, b, c, d].SortedLE) :
    rowCells lam [a, b, c, d] =
      ∑ j : Fin 4, ⌊normalizedGaps lam a b c d j⌋₊ := by
  rw [rowCells_eq_sum_floor hs]
  apply Finset.sum_congr rfl
  intro j _
  rw [gapAfter_four]
  rfl

theorem rowBig_four {lam a b c d : ℝ} (hlam : 0 < lam)
    (hs : [a, b, c, d].SortedLE) :
    rowBig lam [a, b, c, d] =
      ∑ j : Fin 4, if 1 ≤ ⌊normalizedGaps lam a b c d j⌋₊ then 1 else 0 := by
  classical
  unfold rowBig
  rw [← sum_ite_eq_length_filter]
  rw [cycGaps_eq_ofFn_gapAfter hs, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply, gapAfter_four, normalizedGaps,
    one_le_floor_iff_ge lam _ hlam]

theorem rowDefect_four {n : ℕ} {lam a b c d : ℝ} (hlam : 0 < lam)
    (hs : [a, b, c, d].SortedLE) :
    rowDefect n lam [a, b, c, d] =
      (∑ j : Fin 4, if 1 ≤ ⌊normalizedGaps lam a b c d j⌋₊ then 1 else 0) +
        (n - ∑ j : Fin 4, ⌊normalizedGaps lam a b c d j⌋₊) := by
  rw [rowDefect, rowCells_four hs, rowBig_four hlam hs]

theorem rowResidual_four (lam a b c d : ℝ) :
    rowResidual lam [a, b, c, d] =
      ∑ j : Fin 4, (normalizedGaps lam a b c d j -
        (⌊normalizedGaps lam a b c d j⌋₊ : ℝ)) := by
  unfold rowResidual
  apply Finset.sum_congr rfl
  intro j _
  rw [gapAfter_four]
  rfl

/-- Finite packaging of the one-large-gap / two-active-gap coarse budget. -/
theorem gapBudget_of_coarseBudget (n : ℕ) (p a b c d : ℝ)
    (h : CoarseBudget n ![b-a,c-b,d-c,p+a-d]) :
    GapBudget (n : ℝ) p a b c d := by
  rcases h with ⟨i, hi⟩ | ⟨i,j,hne,hi,hj,hij⟩
  · fin_cases i
    · change (n : ℝ)-1 ≤ b-a at hi
      unfold GapBudget
      left; exact hi
    · change (n : ℝ)-1 ≤ c-b at hi
      unfold GapBudget
      right; left; exact hi
    · change (n : ℝ)-1 ≤ d-c at hi
      unfold GapBudget
      right; right; left; exact hi
    · change (n : ℝ)-1 ≤ p+a-d at hi
      unfold GapBudget
      right; right; right; left; exact hi
  · fin_cases i <;> fin_cases j
    · exact False.elim (hne rfl)
    · change 1 ≤ b-a at hi
      change 1 ≤ c-b at hj
      change (n : ℝ) ≤ (b-a)+(c-b) at hij
      unfold GapBudget
      right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 1 ≤ b-a at hi
      change 1 ≤ d-c at hj
      change (n : ℝ) ≤ (b-a)+(d-c) at hij
      unfold GapBudget
      right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 1 ≤ b-a at hi
      change 1 ≤ p+a-d at hj
      change (n : ℝ) ≤ (b-a)+(p+a-d) at hij
      unfold GapBudget
      right; right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 1 ≤ c-b at hi
      change 1 ≤ b-a at hj
      change (n : ℝ) ≤ (c-b)+(b-a) at hij
      unfold GapBudget
      right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · exact False.elim (hne rfl)
    · change 1 ≤ c-b at hi
      change 1 ≤ d-c at hj
      change (n : ℝ) ≤ (c-b)+(d-c) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 1 ≤ c-b at hi
      change 1 ≤ p+a-d at hj
      change (n : ℝ) ≤ (c-b)+(p+a-d) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 1 ≤ d-c at hi
      change 1 ≤ b-a at hj
      change (n : ℝ) ≤ (d-c)+(b-a) at hij
      unfold GapBudget
      right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · change 1 ≤ d-c at hi
      change 1 ≤ c-b at hj
      change (n : ℝ) ≤ (d-c)+(c-b) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · exact False.elim (hne rfl)
    · change 1 ≤ d-c at hi
      change 1 ≤ p+a-d at hj
      change (n : ℝ) ≤ (d-c)+(p+a-d) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; right
      exact ⟨hi,hj,hij⟩
    · change 1 ≤ p+a-d at hi
      change 1 ≤ b-a at hj
      change (n : ℝ) ≤ (p+a-d)+(b-a) at hij
      unfold GapBudget
      right; right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · change 1 ≤ p+a-d at hi
      change 1 ≤ c-b at hj
      change (n : ℝ) ≤ (p+a-d)+(c-b) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · change 1 ≤ p+a-d at hi
      change 1 ≤ d-c at hj
      change (n : ℝ) ≤ (p+a-d)+(d-c) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; right
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · exact False.elim (hne rfl)

/-- A given sorted neighbor permutation is exactly the actual direction row;
no independently assigned chord or gap array is introduced. -/
theorem directionRow_eq_four
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hlam : 0 < lam)
    (i a b d f : Fin 5)
    (hp : [a,b,d,f].Perm ((List.finRange 5).erase i))
    (hab : dirRep o e c i a / lam ≤ dirRep o e c i b / lam)
    (hbd : dirRep o e c i b / lam ≤ dirRep o e c i d / lam)
    (hdf : dirRep o e c i d / lam ≤ dirRep o e c i f / lam) :
    directionRow o e c i =
      [dirRep o e c i a,dirRep o e c i b,dirRep o e c i d,dirRep o e c i f] := by
  have hs : [dirRep o e c i a,dirRep o e c i b,dirRep o e c i d,dirRep o e c i f].Pairwise (· ≤ ·) := by
    simp only [List.pairwise_cons_cons_iff_of_trans, List.pairwise_singleton, and_true]
    exact ⟨(div_le_div_iff_of_pos_right hlam).mp hab,
      (div_le_div_iff_of_pos_right hlam).mp hbd,
      (div_le_div_iff_of_pos_right hlam).mp hdf⟩
  have hp1 : (directionRow o e c i).Perm
      (((List.finRange 5).erase i).map (dirRep o e c i)) := List.perm_insertionSort _ _
  have hp2 := hp.map (dirRep o e c i)
  exact List.Perm.eq_of_pairwise' (directionRow_sorted o e c i).pairwise hs
    (hp1.trans (by simpa only [List.map_cons, List.map_nil] using hp2.symm))

/-- The terminal's coarse row budget comes from the actual cyclic floor count
and actual row defect, including the whole wrap gap. -/
theorem actual_row_gapBudget
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (i a b d f : Fin 5)
    (hdef : rowDefect n lam (directionRow o e c i) = 2)
    (hp : [a,b,d,f].Perm ((List.finRange 5).erase i))
    (hab : dirRep o e c i a / lam ≤ dirRep o e c i b / lam)
    (hbd : dirRep o e c i b / lam ≤ dirRep o e c i d / lam)
    (hdf : dirRep o e c i d / lam ≤ dirRep o e c i f / lam) :
    GapBudget (n : ℝ) (Real.pi/lam) (dirRep o e c i a/lam)
      (dirRep o e c i b/lam) (dirRep o e c i d/lam) (dirRep o e c i f/lam) := by
  have hrow := directionRow_eq_four o e hlam i a b d f hp hab hbd hdf
  have hs : [dirRep o e c i a,dirRep o e c i b,dirRep o e c i d,dirRep o e c i f].SortedLE := by
    rw [← hrow]
    exact directionRow_sorted o e c i
  have hmem : ∀ x ∈ [dirRep o e c i a,dirRep o e c i b,dirRep o e c i d,dirRep o e c i f],
      x ∈ Set.Ico 0 Real.pi := by
    rw [← hrow]
    exact fun x hx => directionRow_mem_Ico o e c hx
  let g := normalizedGaps lam (dirRep o e c i a) (dirRep o e c i b)
    (dirRep o e c i d) (dirRep o e c i f)
  have hg : ∀ j, 0 ≤ g j := normalizedGaps_nonneg hlam hs hmem
  have hc : (∑ j : Fin 4, ⌊g j⌋₊) ≤ n := by
    rw [← rowCells_four hs, ← hrow]
    exact rowCells_directionRow_le_of_floor_eq o e c hlam i (by decide) hn
  have hd : (∑ j : Fin 4, if 1 ≤ ⌊g j⌋₊ then (1 : ℕ) else 0) +
      (n-(∑ j : Fin 4, ⌊g j⌋₊)) = 2 := by
    rw [hrow, rowDefect_four hlam hs] at hdef
    exact hdef
  have hb := coarseBudget_of_floor hn3 g hg hc hd
  have hvec : g = ![dirRep o e c i b/lam-dirRep o e c i a/lam,
      dirRep o e c i d/lam-dirRep o e c i b/lam,
      dirRep o e c i f/lam-dirRep o e c i d/lam,
      Real.pi/lam+dirRep o e c i a/lam-dirRep o e c i f/lam] := by
    dsimp only [g]
    rw [normalizedGaps_eq_vector]
    simp only [sub_div, add_div]
  rw [hvec] at hb
  exact gapBudget_of_coarseBudget n (Real.pi/lam) _ _ _ _ hb

/-- Full necessary scalar model extracted from the actual five-point geometry.
Only the four genuine nonzero-index row defects are constrained. -/
noncomputable def model
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (hdef : ∀ i : Fin 5, i ≠ 0 → rowDefect n lam (directionRow o e c i) = 2) :
    FiveModel (n : ℝ) (Real.pi/lam-(n : ℝ)) where
  hn := by exact_mod_cast hn3
  hdelta := by
    have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hleg.lam_pos.le)
    rw [hn] at hfloor
    exact ⟨by linarith, hlow⟩
  d i j := dirRep o e c i j / lam
  symm i j := by
    by_cases hij : i = j
    · simp [hij]
    · rw [dirRep_comm o e c he (hleg.inj.ne hij)]
  range i j _ := by
    have hr : 0 ≤ dirRep o e c i j ∧ dirRep o e c i j < Real.pi := linRep_mem_Ico _
    constructor
    · exact div_nonneg hr.1 hleg.lam_pos.le
    · have hh := (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr hr.2
      linarith
  triangle i j k hij hjk := by
    have ht := NoSatFiveGeometry.ordered_triangle o e he hleg hup hij hjk
    rcases ht with ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4,h5⟩
    · apply Or.inl
      refine ⟨?_, (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h2,
        (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h3, ?_, ?_⟩
      · simpa only [add_div, div_self hleg.lam_pos.ne'] using
          (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h1
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h4
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h5
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
    · apply Or.inr
      refine ⟨?_, (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h2,
        (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h3, ?_, ?_⟩
      · simpa only [add_div, div_self hleg.lam_pos.ne'] using
          (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h1
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h4
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h5
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
  budget i hi a b d f hp hab hbd hdf := by
    have h := actual_row_gapBudget o e hleg.lam_pos hn3 hn i a b d f (hdef i hi) hp hab hbd hdf
    simpa only [add_sub_cancel] using h

/-- Actual ordered five-centre exclusion, uniform in every strip n≥3.
The fifth centre's row is unrestricted. -/
theorem ordered_five_centres_four_defect_two_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (hdef : ∀ i : Fin 5, i ≠ 0 → rowDefect n lam (directionRow o e c i) = 2) : False :=
  endpoint_model_impossible (model o e he hleg hn3 hn hlow hup hdef)

/-- The same genuine cyclic budget holds for a row of defect at most two. -/
theorem actual_row_gapBudget_le_two
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (i a b d f : Fin 5)
    (hdef : rowDefect n lam (directionRow o e c i) ≤ 2)
    (hp : [a,b,d,f].Perm ((List.finRange 5).erase i))
    (hab : dirRep o e c i a / lam ≤ dirRep o e c i b / lam)
    (hbd : dirRep o e c i b / lam ≤ dirRep o e c i d / lam)
    (hdf : dirRep o e c i d / lam ≤ dirRep o e c i f / lam) :
    GapBudget (n : ℝ) (Real.pi/lam) (dirRep o e c i a/lam)
      (dirRep o e c i b/lam) (dirRep o e c i d/lam) (dirRep o e c i f/lam) := by
  have hrow := directionRow_eq_four o e hlam i a b d f hp hab hbd hdf
  have hs : [dirRep o e c i a,dirRep o e c i b,dirRep o e c i d,dirRep o e c i f].SortedLE := by
    rw [← hrow]
    exact directionRow_sorted o e c i
  have hmem : ∀ x ∈ [dirRep o e c i a,dirRep o e c i b,dirRep o e c i d,dirRep o e c i f],
      x ∈ Set.Ico 0 Real.pi := by
    rw [← hrow]
    exact fun x hx => directionRow_mem_Ico o e c hx
  let g := normalizedGaps lam (dirRep o e c i a) (dirRep o e c i b)
    (dirRep o e c i d) (dirRep o e c i f)
  have hg : ∀ j, 0 ≤ g j := normalizedGaps_nonneg hlam hs hmem
  have hc : (∑ j : Fin 4, ⌊g j⌋₊) ≤ n := by
    rw [← rowCells_four hs, ← hrow]
    exact rowCells_directionRow_le_of_floor_eq o e c hlam i (by decide) hn
  have hd : (∑ j : Fin 4, if 1 ≤ ⌊g j⌋₊ then (1 : ℕ) else 0) +
      (n-(∑ j : Fin 4, ⌊g j⌋₊)) ≤ 2 := by
    rw [hrow, rowDefect_four hlam hs] at hdef
    exact hdef
  have hb := coarseBudget_of_floor_le_two hn3 g hg hc hd
  have hvec : g = ![dirRep o e c i b/lam-dirRep o e c i a/lam,
      dirRep o e c i d/lam-dirRep o e c i b/lam,
      dirRep o e c i f/lam-dirRep o e c i d/lam,
      Real.pi/lam+dirRep o e c i a/lam-dirRep o e c i f/lam] := by
    dsimp only [g]
    rw [normalizedGaps_eq_vector]
    simp only [sub_div, add_div]
  rw [hvec] at hb
  exact gapBudget_of_coarseBudget n (Real.pi/lam) _ _ _ _ hb


/-- Model extraction permitting saturated rows among the four constrained rows. -/
noncomputable def model_le_two
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (hdef : ∀ i : Fin 5, i ≠ 0 → rowDefect n lam (directionRow o e c i) ≤ 2) :
    FiveModel (n : ℝ) (Real.pi/lam-(n : ℝ)) where
  hn := by exact_mod_cast hn3
  hdelta := by
    have hfloor := Nat.floor_le (div_nonneg Real.pi_pos.le hleg.lam_pos.le)
    rw [hn] at hfloor
    exact ⟨by linarith, hlow⟩
  d i j := dirRep o e c i j / lam
  symm i j := by
    by_cases hij : i = j
    · simp [hij]
    · rw [dirRep_comm o e c he (hleg.inj.ne hij)]
  range i j _ := by
    have hr : 0 ≤ dirRep o e c i j ∧ dirRep o e c i j < Real.pi := linRep_mem_Ico _
    constructor
    · exact div_nonneg hr.1 hleg.lam_pos.le
    · have hh := (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr hr.2
      linarith
  triangle i j k hij hjk := by
    have ht := NoSatFiveGeometry.ordered_triangle o e he hleg hup hij hjk
    rcases ht with ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4,h5⟩
    · apply Or.inl
      refine ⟨?_, (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h2,
        (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h3, ?_, ?_⟩
      · simpa only [add_div, div_self hleg.lam_pos.ne'] using
          (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h1
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h4
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h5
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
    · apply Or.inr
      refine ⟨?_, (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h2,
        (div_lt_div_iff_of_pos_right hleg.lam_pos).mpr h3, ?_, ?_⟩
      · simpa only [add_div, div_self hleg.lam_pos.ne'] using
          (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h1
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h4
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
      · have hh := (div_le_div_iff_of_pos_right hleg.lam_pos).mpr h5
        simpa only [sub_div, div_self hleg.lam_pos.ne', add_sub_cancel] using hh
  budget i hi a b d f hp hab hbd hdf := by
    have h := actual_row_gapBudget_le_two o e hleg.lam_pos hn3 hn i a b d f (hdef i hi) hp hab hbd hdf
    simpa only [add_sub_cancel] using h


/-- Uniform LOW exclusion when all four non-endpoint rows have defect at most two. -/
theorem ordered_five_centres_four_defect_le_two_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (hdef : ∀ i : Fin 5, i ≠ 0 → rowDefect n lam (directionRow o e c i) ≤ 2) : False :=
  endpoint_model_impossible (model_le_two o e he hleg hn3 hn hlow hup hdef)

/-- Five actual LOW centres cannot all have defect at most two. The required
projection order is constructed from the original legality contract. -/
theorem five_centres_all_defect_le_two_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (hdef : ∀ i : Fin 5, rowDefect n lam (directionRow o e c i) ≤ 2) : False := by
  obtain ⟨sigma, hsigma, hup⟩ := ActualProjectionOrder.exists_ordered_config o e he hleg
  have hleg' := hleg.restrict_injective sigma hsigma.1
  apply ordered_five_centres_four_defect_le_two_impossible o e he hleg' hn3 hn hlow
    (fun i j hij => hup i j hij)
  intro i _
  have hco := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos (sigma i) (by decide) hn
  have hcn := rowCells_directionRow_le_of_floor_eq o e (c ∘ sigma) hleg.lam_pos i (by decide) hn
  have hso := rowScore_eq_sub_defect lam hleg.lam_pos n _ hco
  have hsn := rowScore_eq_sub_defect lam hleg.lam_pos n _ hcn
  have hd := hdef (sigma i)
  have hnle := rowDefect_le lam hleg.lam_pos n _ hcn
  have hs := PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos (by decide) sigma hsigma.1 i
  omega

#print axioms actual_row_gapBudget_le_two
#print axioms ordered_five_centres_four_defect_le_two_impossible
#print axioms five_centres_all_defect_le_two_impossible

#print axioms actual_row_gapBudget
#print axioms model
#print axioms ordered_five_centres_four_defect_two_impossible

end Jsp404.GlobalFiveLowEndpointGeometry
