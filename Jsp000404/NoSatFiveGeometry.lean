import Jsp000404.PositiveRowCount
import Jsp000404.ActualProjectionOrder
import Jsp000404.NoSatFiveTerminal

/-! Actual occupied-cut extraction for the low third-strip five-point terminal.
The reference and cut rays come from the actual direction row. -/

open scoped EuclideanGeometry EuclideanSpace
namespace Jsp404.NoSatFiveGeometry

/-- A positive actual row has an occupied projective cut whose complementary
window has width at most pi minus two lambda. Repeated directions are retained. -/
theorem positive_projective_cut {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin s → Plane₂) {lam : ℝ} (hlam : 0 < lam) (i : Fin s)
    (hpos : 0 < rowScore lam (directionRow o e c i)) :
    ∃ j : Fin s, j ≠ i ∧ ∀ k : Fin s, k ≠ i →
      projectiveShift (dirRep o e c i j) (dirRep o e c i k) ≤ Real.pi - 2*lam := by
  obtain ⟨G, hG, hbig⟩ :=
    PositiveRowFan.exists_big_gap_of_rowScore_pos hlam hpos
  obtain ⟨cut, hcut, hwindow⟩ := PositiveRowFan.exists_shift_window_of_gap
    (directionRow_sorted o e c i) (fun _ hx => directionRow_mem_Ico o e c hx) hG
  obtain ⟨j, hj, hcutj⟩ := (mem_directionRow o e c).mp hcut
  refine ⟨j, hj, ?_⟩
  intro k hk
  have hw := (hwindow _ ((mem_directionRow o e c).mpr ⟨k, hk, rfl⟩)).2
  rw [hcutj] at hw
  linarith

#print axioms positive_projective_cut

/-- Both endpoint caps of an ordered actual triangle. These are independent
of the middle-angle separation and are needed by the scalar exclusion. -/
theorem endpoint_caps {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hup : ∀ i j : Fin s, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    {i j k : Fin s} (hij : i < j) (hjk : j < k) :
    |dirRep o e c i k - dirRep o e c i j| ≤ Real.pi-lam ∧
      |dirRep o e c j k - dirRep o e c i k| ≤ Real.pi-lam := by
  have hik := hij.trans hjk
  have hnij : c j-c i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hij.ne.symm)
  have hnik : c k-c i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hik.ne.symm)
  have hnjk : c k-c j ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hjk.ne.symm)
  have hai := angle_eq_abs_of_half_plane_chart o he hnij hnik
    (linRep_mem_Ico _) (linRep_mem_Ico _) (hup i j hij) (hup i k hik)
  have hak := angle_eq_abs_of_half_plane_chart o he hnik hnjk
    (linRep_mem_Ico _) (linRep_mem_Ico _) (hup i k hik) (hup j k hjk)
  have hci := hleg.triAngle j i k hij.ne.symm hik.ne hjk.ne
  have hck := hleg.triAngle i k j hik.ne hjk.ne.symm hij.ne
  change InnerProductGeometry.angle (c j-c i) (c k-c i) ≤ _ at hci
  change InnerProductGeometry.angle (c i-c k) (c j-c k) ≤ _ at hck
  rw [show c i-c k = -(c k-c i) by abel,
    show c j-c k = -(c k-c j) by abel,
    InnerProductGeometry.angle_neg_neg] at hck
  rw [hai] at hci
  rw [hak] at hck
  exact ⟨hci, hck⟩

#print axioms endpoint_caps

/-- An actual triangle supplies the middle separation, strict chord
betweenness, and both endpoint caps of the finite scalar model. -/
theorem ordered_triangle {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin s → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hup : ∀ i j : Fin s, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    {i j k : Fin s} (hij : i < j) (hjk : j < k) :
    (dirRep o e c i j + lam ≤ dirRep o e c j k ∧
      dirRep o e c i j < dirRep o e c i k ∧
      dirRep o e c i k < dirRep o e c j k ∧
      dirRep o e c i k-dirRep o e c i j ≤ Real.pi-lam ∧
      dirRep o e c j k-dirRep o e c i k ≤ Real.pi-lam) ∨
    (dirRep o e c j k + lam ≤ dirRep o e c i j ∧
      dirRep o e c j k < dirRep o e c i k ∧
      dirRep o e c i k < dirRep o e c i j ∧
      dirRep o e c i k-dirRep o e c j k ≤ Real.pi-lam ∧
      dirRep o e c i j-dirRep o e c i k ≤ Real.pi-lam) := by
  have hik := hij.trans hjk
  have hmid := ActualProjectionOrder.up_cap o e he hleg hij.ne hjk.ne hik.ne
    (hup i j hij) (hup j k hjk)
  have hbetween := ActualProjectionOrder.triangle_between o e he hleg
    hij.ne hjk.ne hik.ne (hup i j hij) (hup j k hjk)
  obtain ⟨hcap1, hcap2⟩ := endpoint_caps o e he hleg hup hij hjk
  rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith)] at hmid
    rw [abs_of_nonneg (by linarith)] at hcap1
    rw [abs_of_nonneg (by linarith)] at hcap2
    exact Or.inl ⟨by linarith, h1, h2, hcap1, hcap2⟩
  · rw [abs_of_nonpos (by linarith)] at hmid
    rw [abs_of_nonpos (by linarith)] at hcap1
    rw [abs_of_nonpos (by linarith)] at hcap2
    exact Or.inr ⟨by linarith, h1, h2, by linarith, by linarith⟩

/-- The model is obtained from actual ordered points; in particular all
three triangle-angle bounds are retained. -/
noncomputable def model
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3) (hlow : 2*Real.pi/7 < lam)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle)) :
    NoSatFiveTerminal.FiveModel lam Real.pi where
  hlam := hleg.lam_pos
  hp := by
    have h := Nat.floor_le (div_nonneg Real.pi_pos.le hleg.lam_pos.le)
    rw [hn] at h
    have hnle := (le_div_iff₀ hleg.lam_pos).mp h
    norm_num at hnle
    constructor <;> linarith
  d := dirRep o e c
  hsymm := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · exact dirRep_comm o e c he (hleg.inj.ne hij)
  hrange := fun _ _ _ => linRep_mem_Ico _
  htr := fun _ _ _ hij hjk => ordered_triangle o e he hleg hup hij hjk

/-- The occupied cuts needed by the scalar terminal are extracted from
the actual four positive rows, with no assumption about the remaining row. -/
theorem model_positive_cuts
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3) (hlow : 2*Real.pi/7 < lam)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (q : Fin 5) (hpos : ∀ i, i ≠ q → 0 < rowScore lam (directionRow o e c i)) :
    ∀ i : Fin 5, i ≠ q → ∃ j : Fin 5, j ≠ i ∧ ∀ k : Fin 5, k ≠ i →
      (if (model o e he hleg hn hlow hup).d i k < (model o e he hleg hn hlow hup).d i j
       then (model o e he hleg hn hlow hup).d i k+Real.pi-(model o e he hleg hn hlow hup).d i j
       else (model o e he hleg hn hlow hup).d i k-(model o e he hleg hn hlow hup).d i j) ≤
      Real.pi-2*lam := by
  intro i hi
  obtain ⟨j, hj, hcut⟩ := positive_projective_cut o e c hleg.lam_pos i (hpos i hi)
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

/-- Actual five-point exclusion in the low third strip. The fifth point's
score is unrestricted; the four positive rows suffice for contradiction. -/
theorem ordered_five_centres_four_positive_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3) (hlow : 2*Real.pi/7 < lam)
    (hup : ∀ i j : Fin 5, i < j →
      o.oangle e (c j-c i) = (dirRep o e c i j : Real.Angle))
    (q : Fin 5) (hpos : ∀ i, i ≠ q → 0 < rowScore lam (directionRow o e c i)) : False :=
  NoSatFiveTerminal.five_model_impossible (model o e he hleg hn hlow hup) q
    (model_positive_cuts o e he hleg hn hlow hup q hpos)

/-- The actual directed half-plane order is constructed from legality.
No ordered-coordinate or cut-window hypothesis is supplied by the caller. -/
theorem five_centres_four_positive_impossible
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3) (hlow : 2*Real.pi/7 < lam)
    (q : Fin 5) (hpos : ∀ i, i ≠ q → 0 < rowScore lam (directionRow o e c i)) : False := by
  classical
  obtain ⟨sigma, hsigma, hup⟩ := ActualProjectionOrder.exists_ordered_config o e he hleg
  obtain ⟨q', hq⟩ := hsigma.2 q
  have hleg' := hleg.restrict_injective sigma hsigma.1
  apply ordered_five_centres_four_positive_impossible o e he hleg' hn hlow
    (fun i j hij => hup i j hij) q'
  intro i hi
  have hqi : sigma i ≠ q := by
    intro hh
    apply hi
    exact hsigma.1 (hh.trans hq.symm)
  exact (hpos (sigma i) hqi).trans_le
    (PositiveRowCount.rowScore_le_restrict o e c hleg.lam_pos (by omega) sigma hsigma.1 i)

#print axioms ordered_triangle
#print axioms five_centres_four_positive_impossible

/-- In an actual five-point low-third-strip configuration, at most three
rows are positive. This strengthens the earlier general bound of four. -/
theorem five_positive_card_le_three
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {c : Fin 5 → Plane₂} {lam : ℝ} (hleg : Section4Legality c lam)
    (hn : Nat.floor (Real.pi/lam) = 3) (hlow : 2*Real.pi/7 < lam) :
    (Finset.univ.filter (fun i => 0 < rowScore lam (directionRow o e c i))).card ≤ 3 := by
  classical
  let P : Finset (Fin 5) := Finset.univ.filter
    (fun i => 0 < rowScore lam (directionRow o e c i))
  change P.card ≤ 3
  by_contra hh
  have hle : P.card ≤ 4 := PositiveRowCount.positive_card_le_four o e he hleg hlow
  have hcard : P.card = 4 := by omega
  have hex : ∃ q : Fin 5, q ∉ P := by
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
  apply five_centres_four_positive_impossible o e he hleg hn hlow q
  intro i hi
  have hip : i ∈ P := by rw [heq]; simp [hi]
  exact (Finset.mem_filter.mp hip).2

#print axioms five_positive_card_le_three
end Jsp404.NoSatFiveGeometry
