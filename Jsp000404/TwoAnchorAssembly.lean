import Jsp000404.TwoAnchoredRows
import Jsp000404.ChartInvariance

/-! # Exact two-anchor row assembly and corridor width arithmetic

These helpers consume explicit direction endpoints and a common chord
corridor. They do not assert the existence of that geometric corridor.
-/

namespace Jsp404

open scoped EuclideanGeometry

theorem directionRow_two_anchor_perm {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin (t + 2) → Plane₂) (i : Fin t) :
    (directionRow o e c i.succ.succ).Perm
      (dirRep o e c i.succ.succ 0 :: dirRep o e c i.succ.succ 1 ::
        directionRow o e (fun j : Fin t => c j.succ.succ) i) := by
  classical
  have hm0 : dirRep o e c i.succ.succ 0 ∈ directionRow o e c i.succ.succ :=
    (mem_directionRow o e c).mpr ⟨0, by
      intro h; have := congrArg Fin.val h; simp at this, rfl⟩
  have her0 := erase_directionRow o e (c' := c) 0 i.succ
  simp only [Fin.succAbove_zero, Function.comp_def] at her0
  have hp0 := List.perm_cons_erase hm0
  rw [← her0] at hp0
  have hm1 : dirRep o e (fun j : Fin (t + 1) => c j.succ) i.succ 0 ∈
      directionRow o e (fun j : Fin (t + 1) => c j.succ) i.succ :=
    (mem_directionRow o e _).mpr ⟨0, by
      intro h; have := congrArg Fin.val h; simp at this, rfl⟩
  have her1 := erase_directionRow o e
    (c' := fun j : Fin (t + 1) => c j.succ) 0 i
  simp only [Fin.succAbove_zero, Function.comp_def] at her1
  have hp1 := List.perm_cons_erase hm1
  rw [← her1] at hp1
  exact hp0.trans (hp1.cons _)

theorem directionRow_two_anchor_eq {t : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    (c : Fin (t + 2) → Plane₂) (i : Fin t) {a b : ℝ}
    (hp : [dirRep o e c i.succ.succ 0, dirRep o e c i.succ.succ 1].Perm
      [a, Real.pi - b])
    (hab : a ≤ Real.pi - b)
    (hpos : ∀ j : Fin t, i ≠ j →
      dirRep o e (fun k : Fin t => c k.succ.succ) i j ∈ Set.Icc a (Real.pi - b)) :
    directionRow o e c i.succ.succ =
      a :: (directionRow o e (fun j : Fin t => c j.succ.succ) i ++ [Real.pi - b]) := by
  let ds := directionRow o e (fun j : Fin t => c j.succ.succ) i
  have hmem : ∀ x ∈ ds, a ≤ x ∧ x ≤ Real.pi - b := by
    intro x hx
    obtain ⟨j, hji, rfl⟩ := (mem_directionRow o e _).mp hx
    exact hpos j hji.symm
  have hp1 := (directionRow_two_anchor_perm o e c i).trans (hp.append_right ds)
  have hp2 : (a :: (Real.pi - b) :: ds).Perm (a :: (ds ++ [Real.pi - b])) :=
    by simpa only [List.singleton_append] using
      (List.perm_append_comm (l₁ := [Real.pi - b]) (l₂ := ds)).cons a
  apply (hp1.trans hp2).eq_of_sortedLE (directionRow_sorted o e c _)
  rw [List.sortedLE_cons]
  constructor
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hmem x hx).1
    · simpa only [List.mem_singleton.mp hx] using hab
  · apply List.Pairwise.sortedLE
    rw [List.pairwise_append]
    exact ⟨(directionRow_sorted o e _ i).pairwise, by simp,
      fun x hx y hy => by simpa only [List.mem_singleton.mp hy] using (hmem x hx).2⟩

/-- A corridor with the two-anchor angle margins fits into n-2 bins,
each strictly narrower than lambda. -/
theorem two_anchor_grid_width {n : ℕ} (hn3 : 3 ≤ n) {lam a b : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = n)
    (hablow : lam ≤ a + b)
    (habhigh : a + b ≤ 2 * (Real.pi - n * lam)) :
    0 < (Real.pi - 2 * lam - (a+b)) / (n-2 : ℕ) ∧
      (Real.pi - 2 * lam - (a+b)) / (n-2 : ℕ) < lam := by
  have hnpos : 0 < (n - 2 : ℕ) := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hden : (0 : ℝ) < (n - 2 : ℕ) := by exact_mod_cast hnpos
  have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor
  constructor
  · apply div_pos _ hden
    have hmul : 0 ≤ ((n : ℝ) - 3) * lam := mul_nonneg (by linarith) hlam.le
    nlinarith
  · rw [div_lt_iff₀ hden, hcast]
    nlinarith

/-- Assembly once the geometric two-anchor corridor has been supplied.
The existence of these data is a separate geometric obligation. -/
theorem potential_le_high_of_two_anchor_data {t n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e f : Plane₂)
    (he : e ≠ 0) (hf : f ≠ 0)
    (c : Fin (t + 2) → Plane₂) {lam : ℝ}
    (hleg : Section4Legality c lam) (hn3 : 3 ≤ n)
    (hn : Nat.floor (Real.pi / lam) = n)
    (h0 : rowDefect n lam (directionRow o e c 0) = 1)
    (h1 : rowDefect n lam (directionRow o e c 1) = 1)
    (a b : Fin t → ℝ) (amin bmin : ℝ)
    (ha : ∀ i, a i ≤ Real.pi - n * lam)
    (hb : ∀ i, b i ≤ Real.pi - n * lam)
    (ha0 : 0 < amin) (hb0 : 0 < bmin)
    (hmin : ∀ i, amin ≤ a i ∧ bmin ≤ b i)
    (hlow : lam ≤ amin + bmin)
    (hhigh : amin + bmin ≤ 2 * (Real.pi - n * lam))
    (hp : ∀ i, [dirRep o f c i.succ.succ 0, dirRep o f c i.succ.succ 1].Perm
      [a i, Real.pi - b i])
    (hpos : ∀ i j : Fin t, i ≠ j →
      dirRep o f (fun k : Fin t => c k.succ.succ) i j ∈
        Set.Icc (lam + amin) (Real.pi - lam - bmin)) :
    potential lam (directionRows o e c) ≤ 2 ^ n + 2 ^ (n - 2) := by
  have hlam := hleg.lam_pos
  let m := n - 2
  let width : ℝ := (Real.pi - 2 * lam - (amin+bmin)) / m
  have hm : 0 < m := by dsimp [m]; omega
  have hw : 0 < width := (two_anchor_grid_width hn3 hlam hn hlow hhigh).1
  have hwidth : width < lam := (two_anchor_grid_width hn3 hlam hn hlow hhigh).2
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hend : lam + amin + (m : ℝ) * width = Real.pi - lam - bmin := by
    dsimp [width]
    field_simp
    <;> ring
  have hfloor := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn, div_lt_iff₀ hlam] at hfloor
  have hbeta : Real.pi - n * lam < lam := by nlinarith
  have hfl := Nat.floor_le (div_nonneg Real.pi_pos.le hlam.le)
  rw [hn, le_div_iff₀ hlam] at hfl
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have htwolam : 2 * lam < Real.pi := by nlinarith
  let pick : Fin t → Fin (t + 2) := fun i => i.succ.succ
  have hinj : Function.Injective pick :=
    (Fin.succ_injective (t + 1)).comp (Fin.succ_injective t)
  have hrow (i : Fin t) : directionRow o f c (pick i) =
      a i :: (directionRow o f (c ∘ pick) i ++ [Real.pi - b i]) := by
    apply directionRow_two_anchor_eq o f c i (hp i)
    · linarith [ha i, hb i]
    · intro j hij
      obtain ⟨hl, hr⟩ := hpos i j hij
      constructor <;> linarith [ha i, hb i]
  have hrest := weighted_two_anchored_rows (start := lam + amin) (width := width) (m := m)
    o f c hf hleg pick hinj a b hrow
    (fun i => by linarith [ha i, hb i]) hm hw hwidth
    (by linarith) (by rw [hend]; linarith)
    (fun i => by linarith [(hmin i).1])
    (fun i => by rw [hend]; linarith [(hmin i).2])
    (fun i j hij => by rw [hend]; exact hpos i j hij)
  have hscore (i : Fin (t + 2))
      (hi : rowDefect n lam (directionRow o e c i) = 1) :
      rowScore lam (directionRow o f c i) = n - 1 := by
    rw [← rowScore_directionRow_reference_eq o e f he hf c hleg.inj i lam]
    rw [rowScore_eq_sub_defect lam hlam n _
      (rowCells_directionRow_le_of_floor_eq o e c hlam i (by omega) hn), hi]
  rw [potential_directionRows_reference_eq o e f he hf c hleg.inj lam]
  unfold potential exponentAt directionRows
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    show (0 : Fin (t + 1)).succ = (1 : Fin (t + 2)) by
      apply Fin.ext; simp,
    hscore 0 h0, hscore 1 h1]
  have heq : 2 ^ (n-1) + 2 ^ (n-1) = (2 : ℕ) ^ n := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  change 2 ^ (n-1) + (2 ^ (n-1) +
    ∑ i : Fin t, 2 ^ rowScore lam (directionRow o f c (pick i))) ≤ _
  dsimp [m] at hrest
  omega

#print axioms directionRow_two_anchor_eq
#print axioms two_anchor_grid_width
#print axioms potential_le_high_of_two_anchor_data

end Jsp404
