import Jsp000404.R2N4FiniteReduction
import Jsp000404.ActualMinimumDeletionNormalForm

/-! SOURCE_ONLY conditional assembly for actual strip-four HIGH R2 capacity.

The only unfinished mathematical inputs are the two explicitly named actual
critical exclusions below. They concern original legal point configurations,
not scalar words or accepted certificates. The finite induction uses an actual
minimum-score point in the current configuration and one deletion bound from
the smaller R2 instance; no global minimum-counterexample model is an input.
The existing finite-eight consumer supplies the arbitrary-size induction.
This module does not certify either critical input or the original theorem.
-/

set_option autoImplicit false

open scoped EuclideanGeometry EuclideanSpace BigOperators

namespace Jsp404.ActualN4R2CapacityAssembly

/-- The actual potential-21 exclusion at the fixed original scale.
The floor-four and HIGH hypotheses are fixed by the assembly's outer context
when the actual critical producer is supplied. -/
def NamedNoCrit21 (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (lam : ℝ) : Prop :=
  ∀ {s : ℕ}, 6 ≤ s → ∀ c : Fin s → Plane₂, Section4Legality c lam →
    ∀ {v a b : Fin s}, v ≠ a → v ≠ b → a ≠ b →
      rowScore lam (directionRow o e c v) = 3 →
      rowScore lam (directionRow o e c a) = 2 →
      rowScore lam (directionRow o e c b) = 2 →
      potential lam (directionRows o e c) = 21 → False

/-- The remaining actual six-point potential-22 profile. All three other
rows have score one. There is no minimum-model or capacity hypothesis. -/
def NamedNoCrit22Six (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (lam : ℝ) : Prop :=
  ∀ c : Fin 6 → Plane₂, Section4Legality c lam →
    ∀ {v a b : Fin 6}, v ≠ a → v ≠ b → a ≠ b →
      rowScore lam (directionRow o e c v) = 3 →
      rowScore lam (directionRow o e c a) = 2 →
      rowScore lam (directionRow o e c b) = 2 →
      (∀ i : Fin 6, i ≠ v → i ≠ a → i ≠ b →
        rowScore lam (directionRow o e c i) = 1) →
      potential lam (directionRows o e c) = 22 → False

private theorem exists_outside_three {t : ℕ} (ht : 4 ≤ t) (v a b : Fin t) :
    ∃ i : Fin t, i ≠ v ∧ i ≠ a ∧ i ≠ b := by
  classical
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Fin t)) ⊆ {v, a, b} := by
    intro i _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hiv : i = v
    · exact Or.inl hiv
    by_cases hia : i = a
    · exact Or.inr (Or.inl hia)
    exact Or.inr (Or.inr (h i hiv hia))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hthree : ({v, a, b} : Finset (Fin t)).card ≤ 3 := by
    have h1 := Finset.card_insert_le v ({a, b} : Finset (Fin t))
    have h2 := Finset.card_insert_le a ({b} : Finset (Fin t))
    rw [Finset.card_singleton] at h2
    omega
  omega

/-- In an actual overfull R2 configuration, all unprotected scores are at
most one: a second SAT would already close the HIGH cap, and a third heavy
row is excluded by the existing uniform actual five-point lift. -/
private theorem tail_score_le_one {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (ht5 : 5 ≤ t) {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin t → Plane₂} (hleg : Section4Legality c lam)
    (v a b : Fin t) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2)
    (hover : 20 < potential lam (directionRows o e c)) :
    ∀ i : Fin t, i ≠ v → i ≠ a → i ≠ b →
      rowScore lam (directionRow o e c i) ≤ 1 := by
  classical
  have hcells (i : Fin t) : rowCells lam (directionRow o e c i) ≤ 4 :=
    rowCells_directionRow_le_of_floor_eq o e c hleg.lam_pos i (by omega) hn
  have hcount := defect_two_rows_le_two o e he ht5 (by omega : 3 ≤ 4)
    hleg.lam_pos hn hleg v hsat
  intro i hiv hia hib
  have hnot1 : rowDefect 4 lam (directionRow o e c i) ≠ 1 := by
    intro hi
    have hcap := potential_le_high_of_two_saturated o e he (by omega : 3 ≤ t)
      (by omega : 2 ≤ 4) hleg.lam_pos hn hleg hiv.symm hsat hi
    norm_num at hcap
    omega
  have hnot2 : rowDefect 4 lam (directionRow o e c i) ≠ 2 := by
    intro hi
    let T := (Finset.univ : Finset (Fin t)).filter
      (fun j => rowDefect 4 lam (directionRow o e c j) = 2)
    have hsub : ({a, b, i} : Finset (Fin t)) ⊆ T := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · simpa [T] using hda
      · simpa [T] using hdb
      · simpa [T] using hi
    have hane : a ∉ ({b, i} : Finset (Fin t)) := by simp [hab, hia.symm]
    have hthree : ({a, b, i} : Finset (Fin t)).card = 3 := by
      rw [Finset.card_insert_of_notMem hane, Finset.card_pair hib.symm]
    have hge := Finset.card_le_card hsub
    change T.card ≤ 2 at hcount
    omega
  have hge1 := one_le_rowDefect lam hleg.lam_pos 4 (directionRow o e c i)
    (by omega : 1 ≤ 4) (hcells i)
  have hscore := rowScore_eq_sub_defect lam hleg.lam_pos 4 (directionRow o e c i) (hcells i)
  omega

private theorem potential_eq_two_card_add_ten {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin t → Plane₂) (lam : ℝ) (v a b : Fin t)
    (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hv : rowScore lam (directionRow o e c v) = 3)
    (ha : rowScore lam (directionRow o e c a) = 2)
    (hb : rowScore lam (directionRow o e c b) = 2)
    (htail : ∀ i : Fin t, i ≠ v → i ≠ a → i ≠ b →
      rowScore lam (directionRow o e c i) = 1) :
    potential lam (directionRows o e c) = 2 * t + 10 := by
  classical
  have hweight (i : Fin t) :
      2 ^ rowScore lam (directionRow o e c i) =
        2 + (if i = v then 6 else 0) + (if i = a then 2 else 0) +
          (if i = b then 2 else 0) := by
    by_cases hiv : i = v
    · subst i
      simp [hv, hav.symm, hbv.symm]
    by_cases hia : i = a
    · subst i
      simp [ha, hav, hab]
    by_cases hib : i = b
    · subst i
      simp [hb, hbv, hab.symm]
    simp [htail i hiv hia hib, hiv, hia, hib]
  unfold potential exponentAt directionRows
  simp_rw [hweight]
  simp [Finset.sum_add_distrib, Nat.mul_comm] <;> omega

/-- Actual finite R2 capacities from three through eight points, conditional
only on the two concrete original critical exclusions. HIGH is retained in
the interface for their eventual actual producers at this fixed scale. -/
theorem finite_capacity_of_critical_exclusions
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    (_hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    (h21 : NamedNoCrit21 o e lam) (h22 : NamedNoCrit22Six o e lam)
    {t : ℕ} (ht3 : 3 ≤ t) (ht8 : t ≤ 8)
    {c : Fin t → Plane₂} (hleg : Section4Legality c lam)
    (v a b : Fin t) (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2) :
    potential lam (directionRows o e c) ≤ 20 := by
  classical
  have finite : ∀ u : ℕ, 3 ≤ u → u ≤ 8 →
      ∀ d : Fin u → Plane₂, Section4Legality d lam →
      ∀ v a b : Fin u, a ≠ v → b ≠ v → a ≠ b →
      rowDefect 4 lam (directionRow o e d v) = 1 →
      rowDefect 4 lam (directionRow o e d a) = 2 →
      rowDefect 4 lam (directionRow o e d b) = 2 →
      potential lam (directionRows o e d) ≤ 20 := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u IH =>
      intro hu3 hu8 d hd v a b hav hbv hab hsat hda hdb
      by_cases hu5 : u ≤ 5
      · have hcap := potential_le_high_cap_of_le_five o e he hu3 hu5
          (by omega : 3 ≤ 4) hd.lam_pos hn hd
        norm_num at hcap
        exact hcap
      have hu6 : 6 ≤ u := by omega
      obtain ⟨s, rfl⟩ : ∃ s : ℕ, u = s + 1 := ⟨u - 1, by omega⟩
      by_contra hnot
      have hover : 20 < potential lam (directionRows o e d) := by omega
      let score (i : Fin (s + 1)) : ℕ := rowScore lam (directionRow o e d i)
      have hcells (i : Fin (s + 1)) : rowCells lam (directionRow o e d i) ≤ 4 :=
        rowCells_directionRow_le_of_floor_eq o e d hd.lam_pos i (by omega) hn
      have hv3 : score v = 3 := by
        dsimp [score]
        rw [rowScore_eq_sub_defect lam hd.lam_pos 4 _ (hcells v), hsat]
      have ha2 : score a = 2 := by
        dsimp [score]
        rw [rowScore_eq_sub_defect lam hd.lam_pos 4 _ (hcells a), hda]
      have hb2 : score b = 2 := by
        dsimp [score]
        rw [rowScore_eq_sub_defect lam hd.lam_pos 4 _ (hcells b), hdb]
      have htail : ∀ i : Fin (s + 1), i ≠ v → i ≠ a → i ≠ b → score i ≤ 1 :=
        tail_score_le_one o e he (by omega) hn hd v a b hav hbv hab hsat hda hdb hover
      obtain ⟨z, hzv, hza, hzb⟩ := exists_outside_three (by omega : 4 ≤ s + 1) v a b
      obtain ⟨q, hmin⟩ := Finite.exists_min score
      have hqle : score q ≤ 1 := (hmin z).trans (htail z hzv hza hzb)
      have hqv : q ≠ v := by
        intro hq
        rw [hq, hv3] at hqle
        omega
      have hqa : q ≠ a := by
        intro hq
        rw [hq, ha2] at hqle
        omega
      have hqb : q ≠ b := by
        intro hq
        rw [hq, hb2] at hqle
        omega
      have hqcases : score q = 0 ∨ score q = 1 := by omega
      have hdiv : 2 ^ score q ∣ 20 := by
        rcases hqcases with hq0 | hq1
        · norm_num [hq0]
        · norm_num [hq1]
      obtain ⟨a0, ha0⟩ := Fin.exists_succAbove_eq hav
      obtain ⟨b0, hb0⟩ := Fin.exists_succAbove_eq hbv
      obtain ⟨q0, hq0⟩ := Fin.exists_succAbove_eq hqv
      have hab0 : a0 ≠ b0 := by
        intro h
        apply hab
        rw [← ha0, ← hb0, h]
      have hqa0 : q0 ≠ a0 := by
        intro h
        apply hqa
        rw [← hq0, ← ha0, h]
      have hqb0 : q0 ≠ b0 := by
        intro h
        apply hqb
        rw [← hq0, ← hb0, h]
      obtain ⟨v', hv', hsat', a', b', ha', hb', hda', hdb', _⟩ :=
        r2_tail_delete_closed o e he (by omega : 5 ≤ s) (by omega : 3 ≤ 4)
          hd.lam_pos hn hd v hsat hab0 (ha0.symm ▸ hda) (hb0.symm ▸ hdb)
          q0 hqa0 hqb0
      have hvq' : q.succAbove v' = v := by simpa [hq0] using hv'
      have haq' : q.succAbove a' = a := by simpa [hq0, ha0] using ha'
      have hbq' : q.succAbove b' = b := by simpa [hq0, hb0] using hb'
      have hav' : a' ≠ v' := by
        intro h
        apply hav
        rw [← haq', ← hvq', h]
      have hbv' : b' ≠ v' := by
        intro h
        apply hbv
        rw [← hbq', ← hvq', h]
      have hab' : a' ≠ b' := by
        intro h
        apply hab
        rw [← haq', ← hbq', h]
      have hsatq' : rowDefect 4 lam (directionRow o e (d ∘ q.succAbove) v') = 1 := by
        simpa [hq0] using hsat'
      have hdaq' : rowDefect 4 lam (directionRow o e (d ∘ q.succAbove) a') = 2 := by
        simpa [hq0] using hda'
      have hdbq' : rowDefect 4 lam (directionRow o e (d ∘ q.succAbove) b') = 2 := by
        simpa [hq0] using hdb'
      have hdelete : potential lam (directionRows o e (d ∘ q.succAbove)) ≤ 20 :=
        IH s (by omega) (by omega) (by omega) (d ∘ q.succAbove) (hd.erase q)
          v' a' b' hav' hbv' hab' hsatq' hdaq' hdbq'
      obtain ⟨hF, _, _, _⟩ :=
        ActualMinimumDeletionNormalForm.actual_minimum_delete_normal_form
          (by omega : 2 ≤ s) o e hd q 20 hmin hdiv hover hdelete
      change potential lam (directionRows o e d) = 20 + 2 ^ score q at hF
      rcases hqcases with hqzero | hqone
      · have hF21 : potential lam (directionRows o e d) = 21 := by
          simpa [hqzero] using hF
        exact h21 (by omega : 6 ≤ s + 1) d hd hav.symm hbv.symm hab hv3 ha2 hb2 hF21
      · have hF22 : potential lam (directionRows o e d) = 22 := by
          simpa [hqone] using hF
        have htailOne : ∀ i : Fin (s + 1), i ≠ v → i ≠ a → i ≠ b → score i = 1 := by
          intro i hiv hia hib
          have hlo := hmin i
          have hhi := htail i hiv hia hib
          omega
        have hcount := potential_eq_two_card_add_ten o e d lam v a b hav hbv hab
          hv3 ha2 hb2 htailOne
        have hs5 : s = 5 := by omega
        subst s
        exact h22 d hd hav.symm hbv.symm hab hv3 ha2 hb2 htailOne hF22
  exact finite t ht3 ht8 c hleg v a b hav hbv hab hsat hda hdb

/-- Conditional actual R2 capacity at every point count. The existing
finite-eight consumer performs the arbitrary-size deletion induction. -/
theorem actual_r2_capacity_of_critical_exclusions
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hn : Nat.floor (Real.pi / lam) = 4)
    (hhigh : (1 / 2 : ℝ) ≤ Real.pi / lam - 4)
    (h21 : NamedNoCrit21 o e lam) (h22 : NamedNoCrit22Six o e lam)
    {t : ℕ} {c : Fin t → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin t) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    {a b : Fin t} (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2) :
    potential lam (directionRows o e c) ≤ 20 := by
  exact r2_n4_capacity_of_finite_eight_capacity o e he hleg.lam_pos hn
    (fun {u} hu3 hu8 {d} hd v' a' b' hav' hbv' hab' hsat' hda' hdb' =>
      finite_capacity_of_critical_exclusions o e he hn hhigh h21 h22
        hu3 hu8 hd v' a' b' hav' hbv' hab' hsat' hda' hdb')
    hleg v hsat hav hbv hab hda hdb

#print axioms finite_capacity_of_critical_exclusions
#print axioms actual_r2_capacity_of_critical_exclusions
end Jsp404.ActualN4R2CapacityAssembly
