import Jsp000404.FivePointCapacity

/-!
# Actual n=4 R2 reduction to finite capacities

The point configuration, legality, floor equation, reference vector, row
defects, and potential in this file are the original geometric objects.
An eight-centre R2 capacity bound is an explicit hypothesis, not a proved
kernel or an axiom.  Deleting a tail keeps the anchor and two low rows by
`r2_tail_delete_closed`, so this finite hypothesis excludes every R2
configuration with at least eight centres.  A finite capacity premise for
three through eight centres therefore gives arbitrary-size R2 capacity.
The scalar UNSAT diagnostics are not used as proofs here.
-/

set_option autoImplicit false

namespace Jsp404

open scoped EuclideanSpace

private theorem r2_n4_exists_ne_and_ne {s : ℕ} (hs : 3 ≤ s)
    (a b : Fin s) : ∃ q : Fin s, q ≠ a ∧ q ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin s)) ⊆ {a, b} := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (h x hxa)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hc : ({a, b} : Finset (Fin s)).card ≤ 2 := by
    have g := Finset.card_insert_le a ({b} : Finset (Fin s))
    rw [Finset.card_singleton] at g
    omega
  omega

/-- At n=4, an actual saturated row contributes 8 and two actual
defect-2 rows contribute 4 each; every other natural score contributes
at least 1.  Thus the original potential is at least `t+13`.
Legality and the nonzero reference vector are retained in the interface;
the lower bound itself only needs the row-score/floor relations. -/
theorem potential_ge_card_add_thirteen {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (_he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin t → Plane₂} (_hleg : Section4Legality c lam)
    (v : Fin t) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    {a b : Fin t} (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2) :
    t + 13 ≤ potential lam (directionRows o e c) := by
  classical
  have ht2 : 2 ≤ t := by
    have h := Finset.card_le_univ ({a, b} : Finset (Fin t))
    rw [Finset.card_pair hab, Fintype.card_fin] at h
    exact h
  have hcells := fun i : Fin t =>
    rowCells_directionRow_le_of_floor_eq o e c hlam i ht2 hn
  have hscv : rowScore lam (directionRow o e c v) = 3 := by
    rw [rowScore_eq_sub_defect lam hlam 4 _ (hcells v), hsat]
  have hsca : rowScore lam (directionRow o e c a) = 2 := by
    rw [rowScore_eq_sub_defect lam hlam 4 _ (hcells a), hda]
  have hscb : rowScore lam (directionRow o e c b) = 2 := by
    rw [rowScore_eq_sub_defect lam hlam 4 _ (hcells b), hdb]
  have hweight : ∀ i : Fin t,
      1 + (if i = v then 7 else 0) + (if i = a then 3 else 0) +
          (if i = b then 3 else 0) ≤
        2 ^ rowScore lam (directionRow o e c i) := by
    intro i
    by_cases hiv : i = v
    · subst i
      simp [hscv, hav.symm, hbv.symm]
    by_cases hia : i = a
    · subst i
      simp [hsca, hav, hab]
    by_cases hib : i = b
    · subst i
      simp [hscb, hbv, hab.symm]
    simpa [hiv, hia, hib] using
      (Nat.one_le_two_pow (n := rowScore lam (directionRow o e c i)))
  calc
    t + 13 = ∑ i : Fin t,
        (1 + (if i = v then 7 else 0) + (if i = a then 3 else 0) +
          (if i = b then 3 else 0)) := by
      simp [Finset.sum_add_distrib]
    _ ≤ potential lam (directionRows o e c) := by
      unfold potential exponentAt directionRows
      exact Finset.sum_le_sum (fun i _ => hweight i)

/-- A genuine capacity bound for actual eight-centre R2 configurations
at the given angle/floor excludes every actual R2 configuration with
at least eight centres.  The reference vector and angle do not change
in the deletion induction.  `hcap8` is the unfinished finite hypothesis. -/
theorem r2_n4_eight_plus_impossible_of_eight_capacity
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (hcap8 : ∀ {c8 : Fin 8 → Plane₂}, Section4Legality c8 lam →
      ∀ (v8 a8 b8 : Fin 8), a8 ≠ v8 → b8 ≠ v8 → a8 ≠ b8 →
        rowDefect 4 lam (directionRow o e c8 v8) = 1 →
        rowDefect 4 lam (directionRow o e c8 a8) = 2 →
        rowDefect 4 lam (directionRow o e c8 b8) = 2 →
        potential lam (directionRows o e c8) ≤ 20) :
    ∀ {t : ℕ}, 8 ≤ t → ∀ {c : Fin t → Plane₂}, Section4Legality c lam →
      ∀ (v : Fin t), rowDefect 4 lam (directionRow o e c v) = 1 →
        ∀ {a b : Fin t}, a ≠ v → b ≠ v → a ≠ b →
          rowDefect 4 lam (directionRow o e c a) = 2 →
          rowDefect 4 lam (directionRow o e c b) = 2 → False := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht c hleg v hsat a b hav hbv hab hda hdb
    rcases Nat.eq_or_lt_of_le ht with rfl | hgt
    · have hge := potential_ge_card_add_thirteen o e he hlam hn hleg
        v hsat hav hbv hab hda hdb
      have hle := hcap8 hleg v a b hav hbv hab hsat hda hdb
      omega
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      obtain ⟨a₀, ha₀⟩ := Fin.exists_succAbove_eq hav
      obtain ⟨b₀, hb₀⟩ := Fin.exists_succAbove_eq hbv
      have hab₀ : a₀ ≠ b₀ := fun h => hab (by rw [← ha₀, h, hb₀])
      obtain ⟨q, hqa, hqb⟩ := r2_n4_exists_ne_and_ne (by omega) a₀ b₀
      obtain ⟨v', hv', hv'1, a', b', ha', hb', hda', hdb', -⟩ :=
        r2_tail_delete_closed o e he (by omega) (by omega : 3 ≤ 4) hlam hn
          hleg v hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb) q hqa hqb
      have hav' : a' ≠ v' := fun h =>
        hav (by rw [← ha₀, ← ha', h, hv'])
      have hbv' : b' ≠ v' := fun h =>
        hbv (by rw [← hb₀, ← hb', h, hv'])
      have hab' : a' ≠ b' := fun h => hab₀
        (Fin.succAbove_right_injective (by rw [← ha', h, hb']))
      exact IH s (by omega) (by omega) (hleg.erase (v.succAbove q))
        v' hv'1 hav' hbv' hab' hda' hdb'

/-- Actual arbitrary-size n=4 R2 capacity, conditional only on actual
finite R2 capacities from three through eight centres.  Sizes at most
seven use the finite premise directly; sizes at least eight are
impossible by the preceding genuine deletion induction. -/
theorem r2_n4_capacity_of_finite_eight_capacity
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (hfinite : ∀ {s : ℕ}, 3 ≤ s → s ≤ 8 →
      ∀ {cs : Fin s → Plane₂}, Section4Legality cs lam →
        ∀ (vs as bs : Fin s), as ≠ vs → bs ≠ vs → as ≠ bs →
          rowDefect 4 lam (directionRow o e cs vs) = 1 →
          rowDefect 4 lam (directionRow o e cs as) = 2 →
          rowDefect 4 lam (directionRow o e cs bs) = 2 →
          potential lam (directionRows o e cs) ≤ 20)
    {t : ℕ} {c : Fin t → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin t) (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    {a b : Fin t} (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2) :
    potential lam (directionRows o e c) ≤ 20 := by
  classical
  have ht3 : 3 ≤ t := by
    have hvnot : v ∉ ({a, b} : Finset (Fin t)) := by
      simp [hav.symm, hbv.symm]
    have hcard := Finset.card_le_univ ({v, a, b} : Finset (Fin t))
    rw [Finset.card_insert_of_notMem hvnot, Finset.card_pair hab,
      Fintype.card_fin] at hcard
    exact hcard
  by_cases ht8 : 8 ≤ t
  · exact (r2_n4_eight_plus_impossible_of_eight_capacity o e he hlam hn
      (fun {c8} hleg8 => hfinite (s := 8) (by omega) (le_refl 8) hleg8)
      ht8 hleg v hsat hav hbv hab hda hdb).elim
  · exact hfinite ht3 (by omega) hleg v a b hav hbv hab hsat hda hdb

#print axioms potential_ge_card_add_thirteen
#print axioms r2_n4_eight_plus_impossible_of_eight_capacity
#print axioms r2_n4_capacity_of_finite_eight_capacity

end Jsp404
