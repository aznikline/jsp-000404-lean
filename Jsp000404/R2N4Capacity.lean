import Jsp000404.N4Extraction
import Jsp000404.FivePointCapacity
import Jsp000404.Induction

/-!
# Arbitrary-size `R2` capacity at `n = 4`, stage 1: defect-3 count

Unlike `n = 3`, the six-centre terminal `six_centre_n4_overcap` is a
capacity bound (`potential ≤ 2^4 + 2^2`), not outright non-existence:
a weight-`21` profile such as `(1,2,2,4,4,4,4,4)` has the six-centre
sub-profile `(1,2,2,4,4,4)` strictly below the cap, so the `n = 3`
induction spine ("delete to six centres, contradiction") does not
apply verbatim.  The spine therefore goes through a *tail
classification* instead.

`r2_n4_tail_defect3_le_one`: in any `≥ 6`-centre `R2` profile at
`n = 4` there is at most one defect-`3` tail row.  Two defect-`3` rows
`x, y` together with one more tail row `z` survive every tail
deletion: `defect_three_survivor_gain_zero` keeps `x, y` defect `3`,
`r2_tail_delete_closed` keeps the anchor saturated, the two defect-`2`
rows defect `2`, and every other survivor defect `≥ 3`.  Deleting
down to six centres produces potential `≥ 8+4+4+2+2+1 = 21`,
contradicting `six_centre_n4_overcap`.

After this, over-capacity (`potential > 2^4 + 2^2`) with tail
decomposition `F = 16 + 2p + q` forces `2p + q > 4` with `p ≤ 1`, so
the only remaining supercritical profiles are the seven-centre
`(1,2,2,3,4,4,4)` and the eight-centre `(1,2,2,4,4,4,4,4)`.  Those two
terminals are the content of the next stage.
-/

namespace Jsp404

open scoped EuclideanSpace

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- `Fin t` with `t > 5` has an index distinct from five given ones. -/
private theorem exists_ne_five {t : ℕ} (ht : 5 < t)
    (v a b x y : Fin t) :
    ∃ z : Fin t, z ≠ v ∧ z ≠ a ∧ z ≠ b ∧ z ≠ x ∧ z ≠ y := by
  classical
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Fin t)) ⊆ {v, a, b, x, y} := by
    intro w _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases eq_or_ne w v with rfl | hwv
    · exact Or.inl rfl
    · rcases eq_or_ne w a with rfl | hwa
      · exact Or.inr (Or.inl rfl)
      · rcases eq_or_ne w b with rfl | hwb
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rcases eq_or_ne w x with rfl | hwx
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (h w hwv hwa hwb hwx))))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have h5 : ({v, a, b, x, y} : Finset (Fin t)).card ≤ 5 := by
    have h1 := Finset.card_insert_le v ({a, b, x, y} : Finset (Fin t))
    have h2 := Finset.card_insert_le a ({b, x, y} : Finset (Fin t))
    have h3 := Finset.card_insert_le b ({x, y} : Finset (Fin t))
    have h4 := Finset.card_insert_le x ({y} : Finset (Fin t))
    rw [Finset.card_singleton] at h4
    omega
  omega

/-- **Tail defect-`3` rows are scarce.**  In a `≥ 6`-centre `R2`
configuration at `n = 4` (saturated anchor `v`, defect-`2` rows
`a ≠ b`, every other non-anchor row of defect `≥ 3`), no two distinct
tail rows both have defect `3`.

Proof by strong induction on the size `t ≥ 6`.  Given two defect-`3`
rows `x, y`, pick a third tail row `z`.  At `t = 6` the profile's
potential is `≥ 8+4+4+2+2+1 = 21`, contradicting
`six_centre_n4_overcap`.  At `t ≥ 7` delete `z`: the reduced `R2`
profile still has defect-`3` rows at the images of `x, y` by
`defect_three_survivor_gain_zero`, so the induction hypothesis
applies. -/
theorem r2_n4_tail_defect3_le_one :
    ∀ {t : ℕ} (_ht : 6 ≤ t) {lam : ℝ} (_hlam : 0 < lam)
      (_hn : Nat.floor (Real.pi / lam) = 4) {c : Fin t → Plane₂}
      (_hleg : Section4Legality c lam) (_he : e ≠ 0) (v : Fin t)
      (_hsat : rowDefect 4 lam (directionRow o e c v) = 1)
      {a b : Fin t} (_hav : a ≠ v) (_hbv : b ≠ v) (_hab : a ≠ b)
      (_hda : rowDefect 4 lam (directionRow o e c a) = 2)
      (_hdb : rowDefect 4 lam (directionRow o e c b) = 2)
      (_htail : ∀ w : Fin t, w ≠ v → w ≠ a → w ≠ b →
        3 ≤ rowDefect 4 lam (directionRow o e c w)),
      ∀ x y : Fin t, x ≠ v → x ≠ a → x ≠ b →
        y ≠ v → y ≠ a → y ≠ b → x ≠ y →
        ¬ (rowDefect 4 lam (directionRow o e c x) = 3 ∧
          rowDefect 4 lam (directionRow o e c y) = 3) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht lam hlam hn c hleg he v hsat a b hav hbv hab hda hdb htail
      x y hxv hxa hxb hyv hya hyb hxy h3
    obtain ⟨z, hzv, hza, hzb, hzx, hzy⟩ :=
      exists_ne_five (by omega) v a b x y
    rcases Nat.eq_or_lt_of_le ht with rfl | hgt
    · -- `t = 6`: potential `≥ 21` contradicts the six-centre cap.
      have hcell : ∀ i : Fin 6,
          rowCells lam (directionRow o e c i) ≤ 4 :=
        fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i
          (by omega) hn
      have hsc : ∀ i : Fin 6, exponentAt lam (directionRows o e c) i =
          4 - rowDefect 4 lam (directionRow o e c i) :=
        fun i => rowScore_eq_sub_defect lam hlam 4 _ (hcell i)
      have hvmem : v ∉ ({a, b, x, y, z} : Finset (Fin 6)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hav.symm, hbv.symm, hxv.symm, hyv.symm, hzv.symm⟩
      have hamem : a ∉ ({b, x, y, z} : Finset (Fin 6)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, hxa.symm, hya.symm, hza.symm⟩
      have hbmem : b ∉ ({x, y, z} : Finset (Fin 6)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxb.symm, hyb.symm, hzb.symm⟩
      have hxmem : x ∉ ({y, z} : Finset (Fin 6)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxy, hzx.symm⟩
      have hymem : y ∉ ({z} : Finset (Fin 6)) := by
        simp only [Finset.mem_singleton]
        exact hzy.symm
      have huniv : ({v, a, b, x, y, z} : Finset (Fin 6)) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Fintype.card_fin]
        rw [Finset.card_insert_of_notMem hvmem,
          Finset.card_insert_of_notMem hamem,
          Finset.card_insert_of_notMem hbmem,
          Finset.card_insert_of_notMem hxmem,
          Finset.card_insert_of_notMem hymem, Finset.card_singleton]
      have hexp : ∑ i : Fin 6, 2 ^ exponentAt lam (directionRows o e c) i =
          2 ^ exponentAt lam (directionRows o e c) v +
            (2 ^ exponentAt lam (directionRows o e c) a +
              (2 ^ exponentAt lam (directionRows o e c) b +
                (2 ^ exponentAt lam (directionRows o e c) x +
                  (2 ^ exponentAt lam (directionRows o e c) y +
                    2 ^ exponentAt lam (directionRows o e c) z)))) := by
        conv_lhs => rw [← huniv]
        rw [Finset.sum_insert hvmem, Finset.sum_insert hamem,
          Finset.sum_insert hbmem, Finset.sum_insert hxmem,
          Finset.sum_insert hymem, Finset.sum_singleton]
      have hv8 : 2 ^ exponentAt lam (directionRows o e c) v = 8 := by
        rw [hsc v, hsat]; norm_num
      have ha4 : 2 ^ exponentAt lam (directionRows o e c) a = 4 := by
        rw [hsc a, hda]; norm_num
      have hb4 : 2 ^ exponentAt lam (directionRows o e c) b = 4 := by
        rw [hsc b, hdb]; norm_num
      have hx2 : 2 ^ exponentAt lam (directionRows o e c) x = 2 := by
        rw [hsc x, h3.1]; norm_num
      have hy2 : 2 ^ exponentAt lam (directionRows o e c) y = 2 := by
        rw [hsc y, h3.2]; norm_num
      have hz1 : 1 ≤ 2 ^ exponentAt lam (directionRows o e c) z :=
        Nat.one_le_two_pow
      have hover : 2 ^ 4 + 2 ^ 2 <
          potential lam (directionRows o e c) := by
        rw [potential_eq_exponent_sum, hexp]
        omega
      exact six_centre_n4_overcap o e he hlam hn hleg
        hav.symm hbv.symm hab hsat hda hdb htail hover
    · -- `t ≥ 7`: delete a third tail row `z` and induct.
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      obtain ⟨a₀, ha₀⟩ := Fin.exists_succAbove_eq hav
      obtain ⟨b₀, hb₀⟩ := Fin.exists_succAbove_eq hbv
      obtain ⟨x₀, hx₀⟩ := Fin.exists_succAbove_eq hxv
      obtain ⟨y₀, hy₀⟩ := Fin.exists_succAbove_eq hyv
      obtain ⟨z₀, hz₀⟩ := Fin.exists_succAbove_eq hzv
      have hab₀ : a₀ ≠ b₀ := fun h => hab (by rw [← ha₀, h, hb₀])
      have hza₀ : z₀ ≠ a₀ := fun h =>
        hza (by rw [← hz₀, h, ha₀])
      have hzb₀ : z₀ ≠ b₀ := fun h =>
        hzb (by rw [← hz₀, h, hb₀])
      have hxa₀ : x₀ ≠ a₀ := fun h => hxa (by rw [← hx₀, h, ha₀])
      have hxb₀ : x₀ ≠ b₀ := fun h => hxb (by rw [← hx₀, h, hb₀])
      have hxz₀ : x₀ ≠ z₀ := fun h => hzx (by rw [← hz₀, ← h, hx₀])
      have hya₀ : y₀ ≠ a₀ := fun h => hya (by rw [← hy₀, h, ha₀])
      have hyb₀ : y₀ ≠ b₀ := fun h => hyb (by rw [← hy₀, h, hb₀])
      have hyz₀ : y₀ ≠ z₀ := fun h => hzy (by rw [← hz₀, ← h, hy₀])
      obtain ⟨v', hv', hdv', a', b', ha', hb', hda', hdb', hother'⟩ :=
        r2_tail_delete_closed o e he (by omega) (by decide) hlam hn hleg v
          hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb) z₀ hza₀ hzb₀
      obtain ⟨x', hx', hdx3', -, -⟩ :=
        defect_three_survivor_gain_zero o e he (by omega) (by decide)
          hlam hn hleg v hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb)
          hza₀ hzb₀ hxa₀ hxb₀ hxz₀ (hx₀.symm ▸ h3.1)
      obtain ⟨y', hy', hdy3', -, -⟩ :=
        defect_three_survivor_gain_zero o e he (by omega) (by decide)
          hlam hn hleg v hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb)
          hza₀ hzb₀ hya₀ hyb₀ hyz₀ (hy₀.symm ▸ h3.2)
      have hav' : a' ≠ v' := fun h =>
        hav (by rw [← ha₀, ← ha', h, hv'])
      have hbv' : b' ≠ v' := fun h =>
        hbv (by rw [← hb₀, ← hb', h, hv'])
      have hab' : a' ≠ b' := fun h => hab₀
        (Fin.succAbove_right_injective (by rw [← ha', h, hb']))
      have hxv' : x' ≠ v' := fun h =>
        hxv (by rw [← hx₀, ← hx', h, hv'])
      have hxa' : x' ≠ a' := fun h =>
        hxa (by rw [← hx₀, ← hx', h, ha', ha₀])
      have hxb' : x' ≠ b' := fun h =>
        hxb (by rw [← hx₀, ← hx', h, hb', hb₀])
      have hyv' : y' ≠ v' := fun h =>
        hyv (by rw [← hy₀, ← hy', h, hv'])
      have hya' : y' ≠ a' := fun h =>
        hya (by rw [← hy₀, ← hy', h, ha', ha₀])
      have hyb' : y' ≠ b' := fun h =>
        hyb (by rw [← hy₀, ← hy', h, hb', hb₀])
      have hxy' : x' ≠ y' := fun h => hxy
        (by rw [← hx₀, ← hx', h, hy', hy₀])
      exact (IH s (by omega) (by omega) hlam hn
        (hleg.erase (v.succAbove z₀)) he v' hdv' hav' hbv' hab' hda' hdb'
        hother' x' y' hxv' hxa' hxb' hyv' hya' hyb' hxy')
        ⟨hdx3', hdy3'⟩

#print axioms r2_n4_tail_defect3_le_one

end Jsp404
