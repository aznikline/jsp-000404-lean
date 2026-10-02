import Jsp000404.FivePointCapacity

/-!
# R2 six-centre critical profile `(1,2,2,3,3,3)`

Assembly layer for the `SIX_CENTRE_122333` attack.  In a minimal
counterexample the only six-centre profile is anchor `1`, low rows
`2,2` and a pure defect-`3` tail of three rows.  This file packages
the two *real* geometric consequences already available at this
profile, with no minimality hypothesis:

* `six_centre_zero_gain_facing` — deleting any tail point `q` leaves
  every survivor's score unchanged (`r2_tail_delete_all_gains_zero`),
  and every defect-`≥ 2` survivor row sees the deleted direction
  `λ`-faced: one of the two cyclic sweeps incident to the ray
  `i → q` is `< λ` (`exists_small_facing_sweep_of_rowGain_zero`).

* `six_centre_theta_class` — the three θ-position classes of the low
  rows, specialised from `defect_two_pair_theta_cluster`: every tail
  row's `θ` lies below both, strictly between, or above both of the
  low rows.

The remaining step — combining these with the all-position residual
emission `r2_residual_tail_emission` and the `Up`/triangle caps to
force a positive gain somewhere — is the open `G6` geometry; it is
*not* proved here.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

/-- **Six-centre zero-gain facing bundle.**  In a six-centre R2
configuration whose tail is pure defect `3`, deleting any tail point
`q` and looking at any non-anchor survivor `i ≠ q` (whose defect is
then `≥ 2`), the deleted direction `i → q` is `λ`-faced: there are
centres `p`, `q'` adjacent to its cyclic neighbours with
`linRep(∠piq) < λ` or `linRep(∠qiq') < λ`.  All `rowGain = 0` data
are *theorems* here, not hypotheses. -/
theorem six_centre_zero_gain_facing {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin 6)
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    {a b : Fin 5} (hab : a ≠ b)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2)
    (htail3 : ∀ i : Fin 5, i ≠ a → i ≠ b →
      rowDefect n lam (directionRow o e c (v.succAbove i)) = 3)
    (q : Fin 5) (hqa : q ≠ a) (hqb : q ≠ b)
    (i : Fin 6) (hi : i ≠ v.succAbove q) (hiv : i ≠ v) :
    ∃ p q' : Fin 6, p ≠ i ∧ q' ≠ i ∧
      (linRep (o.oangle (c p - c i) (c (v.succAbove q) - c i)) < lam ∨
        linRep (o.oangle (c (v.succAbove q) - c i) (c q' - c i)) < lam) := by
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hiv
  have hd2 : 2 ≤ rowDefect n lam (directionRow o e c i) := by
    have hd' : rowDefect n lam (directionRow o e c i) = 2 ∨
        rowDefect n lam (directionRow o e c i) = 3 := by
      rcases eq_or_ne j a with rfl | hja
      · rw [← hj]; exact Or.inl hda
      · rcases eq_or_ne j b with rfl | hjb
        · rw [← hj]; exact Or.inl hdb
        · rw [← hj]; exact Or.inr (htail3 j hja hjb)
    rcases hd' with h | h <;> omega
  exact r2_tail_delete_facing_sweep o e he (by omega) hn3 hlam hn hleg v
    hsat hab hda hdb htail3 q hqa hqb i hi hd2

/-- **Three θ-position classes of the low rows** (six-centre
specialisation).  Renaming `defect_two_pair_theta_cluster` at `s = 5`:
there is a saturated chart `(e', θ)` with low rows `θ lo < θ hi` such
that either all tail `θ` lie below `lo`, or all lie strictly between
`lo` and `hi`, or all lie above `hi`. -/
theorem six_centre_theta_class {n : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hn3 : 3 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = n)
    {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    {v A B : Fin 6} (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect n lam (directionRow o e c v) = 1)
    (hdA : rowDefect n lam (directionRow o e c A) = 2)
    (hdB : rowDefect n lam (directionRow o e c B) = 2) :
    ∃ e' : Plane₂, e' ≠ 0 ∧ ∃ theta : Fin 5 → ℝ,
      SatChart o e' n lam c v theta ∧
      ∃ lo hi : Fin 5,
        ((v.succAbove lo = A ∧ v.succAbove hi = B) ∨
          (v.succAbove lo = B ∧ v.succAbove hi = A)) ∧
        theta lo < theta hi ∧
        ((∀ z : Fin 5, z ≠ lo → z ≠ hi → theta z < theta lo) ∨
         (∀ z : Fin 5, z ≠ lo → z ≠ hi → theta lo < theta z ∧
            theta z < theta hi) ∨
         (∀ z : Fin 5, z ≠ lo → z ≠ hi → theta hi < theta z)) :=
  defect_two_pair_theta_cluster o e he (by omega) hn3 hlam hn hleg
    hvA hvB hAB hsat hdA hdB

/-- **Six-centre `n = 3` merged-gap bound.**  At `n = 3` a defect-`3`
row has score `0`, hence every cyclic gap `< 2λ`; zero gain when
deleting another tail point then forces the two incident facing sweeps
to merge *below `2λ`*, i.e. the merged gap in the reduced five-centre
row is again `< 2λ`.  All `rowGain = 0` data are proved in-line from
the profile via `r2_tail_delete_all_gains_zero` — the all-zero-gain
premise is not assumed. -/
theorem six_centre_n3_facing_sum
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3)
    {c : Fin 6 → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin 6)
    (hsat : rowDefect 3 lam (directionRow o e c v) = 1)
    {a b : Fin 5} (hab : a ≠ b)
    (hda : rowDefect 3 lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect 3 lam (directionRow o e c (v.succAbove b)) = 2)
    (htail3 : ∀ i : Fin 5, i ≠ a → i ≠ b →
      rowDefect 3 lam (directionRow o e c (v.succAbove i)) = 3)
    (q : Fin 5) (hqa : q ≠ a) (hqb : q ≠ b)
    (i : Fin 5) (hia : i ≠ a) (hib : i ≠ b) (hiq : i ≠ q) :
    ∃ p q' : Fin 6, p ≠ v.succAbove i ∧ q' ≠ v.succAbove i ∧
      linRep (o.oangle (c p - c (v.succAbove i))
          (c (v.succAbove q) - c (v.succAbove i))) +
        linRep (o.oangle (c (v.succAbove q) - c (v.succAbove i))
          (c q' - c (v.succAbove i))) < 2 * lam := by
  have hd3 : rowDefect 3 lam (directionRow o e c (v.succAbove i)) = 3 :=
    htail3 i hia hib
  have hi' : (v.succAbove i : Fin 6) ≠ v.succAbove q :=
    fun h => hiq (Fin.succAbove_right_injective h)
  -- defect `3` at `n = 3` gives score `0`, hence all gaps `< 2λ`.
  have hscore0 : rowScore lam (directionRow o e c (v.succAbove i)) = 0 := by
    have hcells := rowCells_directionRow_le o e c hlam (v.succAbove i)
      (by omega)
    have hsub := rowScore_eq_sub_defect lam hlam 3 _ (by rwa [hn] at hcells)
    rw [hd3] at hsub; omega
  have hgap := cycGaps_lt_two_mul_of_rowScore_zero hlam hscore0
  have hgain0 : rowGain lam (directionRow o e c (v.succAbove i))
      (deleteIndex o e c (v.succAbove q) (v.succAbove i)) = 0 :=
    r2_tail_delete_all_gains_zero o e he (by omega) (by omega) hlam hn hleg
      v hsat hab hda hdb htail3 q hqa hqb _ hi'
  have hne := exists_ne_dirRep_of_two_le_rowDefect o e c hlam hn
    (by omega) hi' (by omega) (by omega)
  obtain ⟨p, q', hpi, hqi, hsum, -, -⟩ :=
    exists_facing_sweep_sum_lt_two_of_rowGain_zero o e he hleg.inj hlam
      hi' (by omega) hne hgap hgain0
  exact ⟨p, q', hpi, hqi, hsum⟩

#print axioms six_centre_zero_gain_facing
#print axioms six_centre_theta_class
#print axioms six_centre_n3_facing_sum

end Jsp404
