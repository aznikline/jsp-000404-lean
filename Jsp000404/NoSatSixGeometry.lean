import Jsp000404.NoSatFiveGeometry
import Jsp000404.NoSatSixTerminal

/-! Actual extraction for the six-point five-positive terminal. The
complete triangle constraints and occupied projective cuts are extracted
from actual points. The caller supplies no scalar-coordinate premises. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.NoSatSixGeometry

/-- Actual ordered points give the complete three-cap six-point model. -/
noncomputable def model
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 6 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3)
    (hup : ∀ i j : Fin 6, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle)) :
    NoSatSixTerminal.SixModel lam Real.pi where
  hlam := hleg.lam_pos
  hp := by
    have h := Nat.floor_le (div_nonneg Real.pi_pos.le hleg.lam_pos.le)
    rw [hn] at h
    have hnle := (le_div_iff₀ hleg.lam_pos).mp h
    have hh := Nat.lt_floor_add_one (Real.pi/lam)
    rw [hn] at hh
    have hnlt := (div_lt_iff₀ hleg.lam_pos).mp hh
    norm_num at hnle hnlt
    exact ⟨hnle, hnlt⟩
  d := dirRep o e c
  hsymm := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · exact dirRep_comm o e c he (hleg.inj.ne hij)
  hrange := fun _ _ _ => linRep_mem_Ico _
  htr := fun _ _ _ hij hjk => NoSatFiveGeometry.ordered_triangle o e he hleg hup hij hjk

/-- Positive actual rows supply the occupied cuts of the model. -/
theorem model_positive_cuts
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 6 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3)
    (hup : ∀ i j : Fin 6, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (q : Fin 6) (hpos : ∀ i, i ≠ q → 0 < rowScore lam (directionRow o e c i)) :
    ∀ i : Fin 6, i ≠ q → ∃ j : Fin 6, j ≠ i ∧ ∀ k : Fin 6, k ≠ i →
      (if (model o e he hleg hn hup).d i k < (model o e he hleg hn hup).d i j
       then (model o e he hleg hn hup).d i k+Real.pi-(model o e he hleg hn hup).d i j
       else (model o e he hleg hn hup).d i k-(model o e he hleg hn hup).d i j) ≤
      Real.pi-2*lam := by
  intro i hi
  obtain ⟨j, hj, hcut⟩ := NoSatFiveGeometry.positive_projective_cut o e c hleg.lam_pos i (hpos i hi)
  refine ⟨j, hj, ?_⟩
  intro k hk
  have h := hcut k hk
  dsimp only [model]
  unfold projectiveShift at h
  split_ifs with hh
  · simp only [hh, ite_true] at h ⊢
    ring_nf at h ⊢
    exact h
  · simp only [hh, ite_false] at h ⊢
    ring_nf at h ⊢
    exact h

/-- Ordered actual six-point exclusion in the entire third strip. -/
theorem ordered_six_centres_five_positive_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 6 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3)
    (hup : ∀ i j : Fin 6, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (q : Fin 6) (hpos : ∀ i, i ≠ q → 0 < rowScore lam (directionRow o e c i)) : False :=
  NoSatSixTerminal.six_model_impossible (model o e he hleg hn hup) q
    (model_positive_cuts o e he hleg hn hup q hpos)

/-- The actual half-plane order is constructed internally. Five positive
rows in an actual six-point third-strip configuration are impossible. -/
theorem six_centres_five_positive_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 6 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3)
    (q : Fin 6) (hpos : ∀ i, i ≠ q → 0 < rowScore lam (directionRow o e c i)) : False := by
  classical
  obtain ⟨sigma, hsigma, hup⟩ := ActualProjectionOrder.exists_ordered_config o e he hleg
  obtain ⟨q', hq⟩ := hsigma.2 q
  have hleg' := hleg.restrict_injective sigma hsigma.1
  apply ordered_six_centres_five_positive_impossible o e he hleg' hn
    (fun i j hij => hup i j hij) q'
  intro i hi
  have hqi : sigma i ≠ q := by
    intro hh
    apply hi
    exact hsigma.1 (hh.trans hq.symm)
  exact (hpos (sigma i) hqi).trans_le
    (PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos (by omega) sigma hsigma.1 i)

/-- Every actual six-point third-strip configuration has at most four
positive rows, regardless of the sixth row's defect. -/
theorem six_positive_card_le_four
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 6 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3) :
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 4 := by
  classical
  let P : Finset (Fin 6) := Finset.univ.filter
    (fun i => 0 < rowScore lam (directionRow o e c i))
  change P.card ≤ 4
  by_contra hh
  have hquarter : Real.pi/4 < lam := by
    have h := Nat.lt_floor_add_one (Real.pi/lam)
    rw [hn] at h
    have hlt := (div_lt_iff₀ hleg.lam_pos).mp h
    norm_num at hlt
    linarith
  have hle : P.card ≤ 5 := PositiveRowCount.positive_card_le_five o e he hleg hquarter
  have hcard : P.card = 5 := by omega
  have hex : ∃ q : Fin 6, q ∉ P := by
    by_contra hnmem
    push Not at hnmem
    have hpall : P = Finset.univ := Finset.ext (fun i => by simp [hnmem i])
    rw [hpall] at hcard
    norm_num at hcard
  obtain ⟨q, hq⟩ := hex
  have hp : P ⊆ Finset.univ.erase q := by
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hiq
    exact hq (hiq ▸ hi)
  have heq : P = Finset.univ.erase q := Finset.eq_of_subset_of_card_le hp
    (by simp [hcard])
  apply six_centres_five_positive_impossible o e he hleg hn q
  intro i hi
  have hip : i ∈ P := by rw [heq]; simp [hi]
  exact (Finset.mem_filter.mp hip).2

#print axioms six_centres_five_positive_impossible
#print axioms six_positive_card_le_four
end Jsp404.NoSatSixGeometry
