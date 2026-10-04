import Jsp000404.GlobalFiveLowEndpointGeometry
import Jsp000404.GlobalFiveLowTerminal

/-!
Actual five-centre LOW exclusion with four low rows and an arbitrary fifth
row. The strong cyclic budget is extracted from actual natural gap floors.
-/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.GlobalFiveLowGeometry

open GlobalFiveLowEndpointGeometry GlobalFiveLowFloorBudget GlobalFiveLowTerminal

/-- Package the genuine strong four-gap floor budget into the scalar terminal's
finite ten-way row budget. -/
theorem gapBudget_of_strongBudget (n : ℕ) (p a b c d : ℝ)
    (h : StrongBudget n ![b-a,c-b,d-c,p+a-d]) :
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
    · change 2 ≤ b-a at hi
      change 2 ≤ c-b at hj
      change (n : ℝ) ≤ (b-a)+(c-b) at hij
      unfold GapBudget
      right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 2 ≤ b-a at hi
      change 2 ≤ d-c at hj
      change (n : ℝ) ≤ (b-a)+(d-c) at hij
      unfold GapBudget
      right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 2 ≤ b-a at hi
      change 2 ≤ p+a-d at hj
      change (n : ℝ) ≤ (b-a)+(p+a-d) at hij
      unfold GapBudget
      right; right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 2 ≤ c-b at hi
      change 2 ≤ b-a at hj
      change (n : ℝ) ≤ (c-b)+(b-a) at hij
      unfold GapBudget
      right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · exact False.elim (hne rfl)
    · change 2 ≤ c-b at hi
      change 2 ≤ d-c at hj
      change (n : ℝ) ≤ (c-b)+(d-c) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 2 ≤ c-b at hi
      change 2 ≤ p+a-d at hj
      change (n : ℝ) ≤ (c-b)+(p+a-d) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; left
      exact ⟨hi,hj,hij⟩
    · change 2 ≤ d-c at hi
      change 2 ≤ b-a at hj
      change (n : ℝ) ≤ (d-c)+(b-a) at hij
      unfold GapBudget
      right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · change 2 ≤ d-c at hi
      change 2 ≤ c-b at hj
      change (n : ℝ) ≤ (d-c)+(c-b) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · exact False.elim (hne rfl)
    · change 2 ≤ d-c at hi
      change 2 ≤ p+a-d at hj
      change (n : ℝ) ≤ (d-c)+(p+a-d) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; right
      exact ⟨hi,hj,hij⟩
    · change 2 ≤ p+a-d at hi
      change 2 ≤ b-a at hj
      change (n : ℝ) ≤ (p+a-d)+(b-a) at hij
      unfold GapBudget
      right; right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · change 2 ≤ p+a-d at hi
      change 2 ≤ c-b at hj
      change (n : ℝ) ≤ (p+a-d)+(c-b) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; left
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · change 2 ≤ p+a-d at hi
      change 2 ≤ d-c at hj
      change (n : ℝ) ≤ (p+a-d)+(d-c) at hij
      unfold GapBudget
      right; right; right; right; right; right; right; right; right
      exact ⟨hj,hi,by simpa only [add_comm] using hij⟩
    · exact False.elim (hne rfl)

/-- Actual row defect at most two yields the strong cyclic budget. Any pair
branch has both gap floors at least two; a floor equal to one is absorbed
into the single-large-gap branch by exact integer arithmetic. -/
theorem actual_row_strongGapBudget
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
  have hb := strongBudget_of_floor_le_two hn3 g hg hc hd
  have hvec : g = ![dirRep o e c i b/lam-dirRep o e c i a/lam,
      dirRep o e c i d/lam-dirRep o e c i b/lam,
      dirRep o e c i f/lam-dirRep o e c i d/lam,
      Real.pi/lam+dirRep o e c i a/lam-dirRep o e c i f/lam] := by
    dsimp only [g]
    rw [normalizedGaps_eq_vector]
    simp only [sub_div, add_div]
  rw [hvec] at hb
  exact gapBudget_of_strongBudget n (Real.pi/lam) _ _ _ _ hb


/-- Every field of the shared scalar model follows from actual point geometry
and the actual four constrained row defects. The fifth row is unrestricted. -/
noncomputable def modelStrong
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (q : Fin 5)
    (hdef : ∀ i : Fin 5, i ≠ q → rowDefect n lam (directionRow o e c i) ≤ 2) :
    FiveModel (n : ℝ) (Real.pi/lam-(n : ℝ)) q where
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
    have h := actual_row_strongGapBudget o e hleg.lam_pos hn3 hn i a b d f (hdef i hi) hp hab hbd hdf
    simpa only [add_sub_cancel] using h



/-- Four actual low-defect rows are impossible among any five ordered centres;
the unconstrained fifth row may occur at any ordered index. -/
theorem ordered_five_centres_four_defect_le_two_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (q : Fin 5)
    (hdef : ∀ i : Fin 5, i ≠ q → rowDefect n lam (directionRow o e c i) ≤ 2) : False :=
  GlobalFiveLowTerminal.model_impossible (modelStrong o e he hleg hn3 hn hlow hup q hdef)

/-- Actual five-point exclusion in every LOW strip n≥3, with four constrained
rows and an arbitrary fifth row. The actual projection order and the free
row's new index are constructed inside the proof. -/
theorem five_centres_four_defect_le_two_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam) {n : ℕ}
    (hn3 : 3 ≤ n) (hn : ⌊Real.pi/lam⌋₊ = n)
    (hlow : Real.pi/lam-(n : ℝ) < 1/2)
    (q : Fin 5)
    (hdef : ∀ i : Fin 5, i ≠ q → rowDefect n lam (directionRow o e c i) ≤ 2) : False := by
  obtain ⟨sigma, hsigma, hup⟩ := ActualProjectionOrder.exists_ordered_config o e he hleg
  obtain ⟨q', hq⟩ := hsigma.2 q
  have hleg' := hleg.restrict_injective sigma hsigma.1
  apply ordered_five_centres_four_defect_le_two_impossible o e he hleg' hn3 hn hlow
    (fun i j hij => hup i j hij) q'
  intro i hi
  have hqi : sigma i ≠ q := by
    intro h
    exact hi (hsigma.1 (h.trans hq.symm))
  have hco := rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos (sigma i) (by decide) hn
  have hcn := rowCells_directionRow_le_of_floor_eq o e (c ∘ sigma) hleg.lam_pos i (by decide) hn
  have hso := rowScore_eq_sub_defect lam hleg.lam_pos n _ hco
  have hsn := rowScore_eq_sub_defect lam hleg.lam_pos n _ hcn
  have hd := hdef (sigma i) hqi
  have hnle := rowDefect_le lam hleg.lam_pos n _ hcn
  have hs := PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos (by decide) sigma hsigma.1 i
  omega

#print axioms ordered_five_centres_four_defect_le_two_impossible
#print axioms five_centres_four_defect_le_two_impossible

#print axioms actual_row_strongGapBudget
#print axioms modelStrong
end Jsp404.GlobalFiveLowGeometry
