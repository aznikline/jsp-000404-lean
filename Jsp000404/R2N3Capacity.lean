import Jsp000404.N3Extraction
import Jsp000404.FivePointCapacity
import Jsp000404.Induction

/-!
# Arbitrary-size `R2` capacity at `n = 3`

Lifts the six-centre terminal exclusion `six_centre_n3_terminal` to an
arbitrary-size capacity statement for the `R2` profile (a saturated
anchor plus two defect-`2` rows) at `n = 3`:

* `r2_n3_six_plus_impossible`: with `≥ 6` centres the profile is
  outright impossible.  Each step deletes one high row via
  `r2_tail_delete_closed` — the anchor stays saturated and the two
  defect-`2` rows persist — until six centres remain, where
  `six_centre_n3_terminal` closes `False`.  The scalar terminal model is
  UNSAT over the whole `δ ∈ (0,1)` strip, so no `LOW`/`HIGH` band split
  is needed for the exclusion itself.

* `r2_n3_capacity`: for every size, `potential ≤ sendovCap 3 big`.  In
  the `δ < 1/2` band the stronger arbitrary-size `LOW` bound
  `potential_le_two_pow_of_saturated` applies to any profile; for
  `big = true` the `≤ 5`-centre cases are closed by
  `potential_le_high_of_saturated_small` /
  `potential_le_high_of_saturated_five`, and `≥ 6` centres is vacuous.

This is a genuine arbitrary-size sub-domain of the open capacity
premise: it does not discharge `CertExists`, and it says nothing about
`n ≥ 4`, `R0`/`R1` profiles in the `HIGH` band, or unsaturated anchors.
-/

namespace Jsp404

open scoped EuclideanSpace

section R2N3

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- `Fin s` with `s ≥ 3` contains an index distinct from any two given
indices. -/
private theorem exists_ne_and_ne {s : ℕ} (hs : 3 ≤ s) (a b : Fin s) :
    ∃ q : Fin s, q ≠ a ∧ q ≠ b := by
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

/-- **Arbitrary-size `R2` exclusion at `n = 3`, `≥ 6` centres.**  A
legal configuration of `t ≥ 6` centres at `n = 3` cannot have a
saturated anchor together with two defect-`2` rows.  Strong induction
on `t`: at `t = 6` the six-centre terminal `six_centre_n3_terminal`
applies; at `t ≥ 7` delete any third row by `r2_tail_delete_closed` —
the anchor remains saturated, the two defect-`2` rows persist, and the
reduced `t − 1`-centre configuration meets the induction hypothesis. -/
theorem r2_n3_six_plus_impossible :
    ∀ {t : ℕ} (_ht : 6 ≤ t) {lam : ℝ} (_hlam : 0 < lam)
      (_hn : Nat.floor (Real.pi / lam) = 3) {c : Fin t → Plane₂}
      (_hleg : Section4Legality c lam) (_he : e ≠ 0) (v : Fin t)
      (_hsat : rowDefect 3 lam (directionRow o e c v) = 1)
      {a b : Fin t} (_hav : a ≠ v) (_hbv : b ≠ v) (_hab : a ≠ b)
      (_hda : rowDefect 3 lam (directionRow o e c a) = 2)
      (_hdb : rowDefect 3 lam (directionRow o e c b) = 2),
      False := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht lam hlam hn c hleg he v hsat a b hav hbv hab hda hdb
    rcases Nat.eq_or_lt_of_le ht with rfl | hgt
    · -- `t = 6`: the six-centre terminal exclusion.
      exact six_centre_n3_terminal o e he hlam hn hleg hav.symm hbv.symm
        hab hsat hda hdb
    · -- `t ≥ 7`: delete a third row and induct.
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      obtain ⟨a₀, ha₀⟩ := Fin.exists_succAbove_eq hav
      obtain ⟨b₀, hb₀⟩ := Fin.exists_succAbove_eq hbv
      have hab₀ : a₀ ≠ b₀ := fun h => hab (by rw [← ha₀, h, hb₀])
      obtain ⟨q, hqa, hqb⟩ := exists_ne_and_ne (by omega) a₀ b₀
      obtain ⟨v', hv', hv'1, a', b', ha', hb', hda', hdb', -⟩ :=
        r2_tail_delete_closed o e he (by omega) (le_refl 3) hlam hn hleg v
          hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb) q hqa hqb
      have hav' : a' ≠ v' := fun h =>
        hav (by rw [← ha₀, ← ha', h, hv'])
      have hbv' : b' ≠ v' := fun h =>
        hbv (by rw [← hb₀, ← hb', h, hv'])
      have hab' : a' ≠ b' := fun h => hab₀
        (Fin.succAbove_right_injective (by rw [← ha', h, hb']))
      exact IH s (by omega) (by omega) hlam hn
        (hleg.erase (v.succAbove q)) he v' hv'1 hav' hbv' hab' hda' hdb'

/-- **Arbitrary-size `R2` capacity at `n = 3`.**  A legal configuration
with a saturated anchor `v`, two defect-`2` rows `a ≠ b`, and every
other non-anchor row of defect `≥ 2` stays under `sendovCap 3 big` in
both bands: `δ < 1/2` is covered by the unconditional `LOW` bound
`potential_le_two_pow_of_saturated`; `δ ≥ 1/2` uses the `≤ 5`-centre
`HIGH` bounds, with `≥ 6` centres vacuous by
`r2_n3_six_plus_impossible`. -/
theorem r2_n3_capacity {s : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3) (he : e ≠ 0) (big : Bool)
    (hbig : big = false → Real.pi / lam - 3 < 1 / 2)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    (v : Fin s) (hsat : rowDefect 3 lam (directionRow o e c v) = 1)
    {a b : Fin s} (hav : a ≠ v) (hbv : b ≠ v) (hab : a ≠ b)
    (hda : rowDefect 3 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 3 lam (directionRow o e c b) = 2)
    (huniq : ∀ w : Fin s, w ≠ v →
      2 ≤ rowDefect 3 lam (directionRow o e c w)) :
    potential lam (directionRows o e c) ≤ sendovCap 3 big := by
  classical
  have hs2 : 2 ≤ s := by
    have h := Finset.card_le_card
      (Finset.subset_univ ({a, b} : Finset (Fin s)))
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hab] at h
    exact h
  cases big with
  | false =>
      have h := potential_le_two_pow_of_saturated o e he hs2
        (by omega : 2 ≤ 3) hlam hn hleg v hsat (by simpa using hbig rfl)
      simpa [sendovCap] using h
  | true =>
      rcases lt_or_ge s 6 with hlt | hge
      · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | h4
        · -- `s = 5`: the five-centre HIGH bound.
          have h := potential_le_high_of_saturated_five o e he
            (le_refl 3) hlam hn hleg v hsat huniq
          simpa [sendovCap] using h
        · -- `s ≤ 4`: the small-size HIGH bound.
          have h := potential_le_high_of_saturated_small o e hs2
            (Nat.le_of_lt_succ h4)
            (by omega : 2 ≤ 3) hlam hn hleg v hsat huniq
          simpa [sendovCap] using h
      · -- `s ≥ 6`: the profile is impossible.
        exact (r2_n3_six_plus_impossible hge hlam hn hleg he v hsat
          hav hbv hab hda hdb).elim

#print axioms r2_n3_six_plus_impossible
#print axioms r2_n3_capacity

end R2N3

end Jsp404
