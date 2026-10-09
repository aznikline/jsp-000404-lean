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

section Defect4Reduction

/-- **The `R2` profile bundle at `n = 4`.**  Saturated anchor `v`,
defect-`2` rows `a ≠ b`, and every other non-anchor row of defect
`≥ 3`.  This is the invariant preserved by tail deletion. -/
def R2N4Profile (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {t : ℕ} (lam : ℝ) (c : Fin t → Plane₂) : Prop :=
  ∃ v a b : Fin t, v ≠ a ∧ v ≠ b ∧ a ≠ b ∧
    rowDefect 4 lam (directionRow o e c v) = 1 ∧
    rowDefect 4 lam (directionRow o e c a) = 2 ∧
    rowDefect 4 lam (directionRow o e c b) = 2 ∧
    ∀ w : Fin t, w ≠ v → w ≠ a → w ≠ b →
      3 ≤ rowDefect 4 lam (directionRow o e c w)

/-- **One tail deletion step.**  Deleting any centre `Q` distinct from
the anchor and the two defect-`2` rows produces a size-`s` `R2`
subconfiguration `c ∘ Q.succAbove` with the profile intact; moreover
every defect-`3` row `x ≠ Q` survives as a defect-`3` row of the
reduced configuration (`defect_three_survivor_gain_zero`). -/
private theorem r2_n4_delete_step {s : ℕ} (hs : 6 ≤ s)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (he : e ≠ 0)
    {c : Fin (s + 1) → Plane₂} (hleg : Section4Legality c lam)
    {v a b : Fin (s + 1)} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2)
    (htail : ∀ w : Fin (s + 1), w ≠ v → w ≠ a → w ≠ b →
      3 ≤ rowDefect 4 lam (directionRow o e c w))
    {Q : Fin (s + 1)} (hQv : Q ≠ v) (hQa : Q ≠ a) (hQb : Q ≠ b) :
    R2N4Profile o e lam (c ∘ Q.succAbove) ∧
      (∀ x : Fin (s + 1),
        rowDefect 4 lam (directionRow o e c x) = 3 → x ≠ Q →
        ∃ x' : Fin s,
          rowDefect 4 lam
            (directionRow o e (c ∘ Q.succAbove) x') = 3) := by
  classical
  obtain ⟨q₀, hq₀⟩ := Fin.exists_succAbove_eq hQv
  obtain ⟨a₀, ha₀⟩ := Fin.exists_succAbove_eq (Ne.symm hva)
  obtain ⟨b₀, hb₀⟩ := Fin.exists_succAbove_eq (Ne.symm hvb)
  have hab₀ : a₀ ≠ b₀ := fun h => hab (by rw [← ha₀, h, hb₀])
  have hqa₀ : q₀ ≠ a₀ := fun h => hQa (by rw [← hq₀, h, ha₀])
  have hqb₀ : q₀ ≠ b₀ := fun h => hQb (by rw [← hq₀, h, hb₀])
  obtain ⟨v', hv', hdv', a', b', ha', hb', hda', hdb', hother'⟩ :=
    r2_tail_delete_closed o e he (by omega) (by decide) hlam hn hleg v
      hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb) q₀ hqa₀ hqb₀
  have hva' : v' ≠ a' := fun h => hva (by rw [← hv', h, ha', ha₀])
  have hvb' : v' ≠ b' := fun h => hvb (by rw [← hv', h, hb', hb₀])
  have hab' : a' ≠ b' := fun h => hab₀
    (Fin.succAbove_right_injective (by rw [← ha', h, hb']))
  rw [← hq₀]
  refine ⟨⟨v', a', b', hva', hvb', hab', hdv', hda', hdb', hother'⟩, ?_⟩
  intro x hdx hxQ
  have hxv : x ≠ v := fun h => by subst h; rw [hdx] at hsat; omega
  have hxa : x ≠ a := fun h => by subst h; rw [hdx] at hda; omega
  have hxb : x ≠ b := fun h => by subst h; rw [hdx] at hdb; omega
  obtain ⟨x₀, hx₀⟩ := Fin.exists_succAbove_eq hxv
  have hxa₀ : x₀ ≠ a₀ := fun h => hxa (by rw [← hx₀, h, ha₀])
  have hxb₀ : x₀ ≠ b₀ := fun h => hxb (by rw [← hx₀, h, hb₀])
  have hxq₀ : x₀ ≠ q₀ := fun h => hxQ (by rw [← hx₀, h])
  obtain ⟨x', -, hdx3', -, -⟩ :=
    defect_three_survivor_gain_zero o e he (by omega) (by decide)
      hlam hn hleg v hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb)
      hqa₀ hqb₀ hxa₀ hxb₀ hxq₀ (hx₀.symm ▸ hdx)
  exact ⟨x', hdx3'⟩

/-- **Descend to seven centres keeping a defect-`3` row.**  From a
`≥ 7`-centre `R2` configuration containing a defect-`3` row, iterated
tail deletion (never deleting the defect-`3` witness) produces a
genuine seven-centre subconfiguration `c' = c ∘ ι` still containing a
defect-`3` row. -/
theorem r2_n4_descend7 :
    ∀ {t : ℕ} (ht : 7 ≤ t) {lam : ℝ} (hlam : 0 < lam)
      (hn : Nat.floor (Real.pi / lam) = 4) {c : Fin t → Plane₂}
      (hleg : Section4Legality c lam) (he : e ≠ 0),
      R2N4Profile o e lam c →
      (∃ x : Fin t, rowDefect 4 lam (directionRow o e c x) = 3) →
      ∃ c' : Fin 7 → Plane₂, ∃ ι : Fin 7 ↪ Fin t, c' = c ∘ ⇑ι ∧
        Section4Legality c' lam ∧ R2N4Profile o e lam c' ∧
        ∃ x : Fin 7, rowDefect 4 lam (directionRow o e c' x) = 3 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht lam hlam hn c hleg he hR2 h3
    rcases Nat.eq_or_lt_of_le ht with rfl | hgt
    · exact ⟨c, Function.Embedding.refl _, rfl, hleg, hR2, h3⟩
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      obtain ⟨v, a, b, hva, hvb, hab, hsat, hda, hdb, htail⟩ := hR2
      obtain ⟨x, hdx⟩ := h3
      obtain ⟨Q, hQv, hQa, hQb, hQx, -⟩ :=
        exists_ne_five (by omega : 5 < s + 1) v a b x x
      obtain ⟨hR2', hkeep⟩ :=
        r2_n4_delete_step (by omega) hlam hn he hleg hva hvb hab
          hsat hda hdb htail hQv hQa hQb
      obtain ⟨x', hdx'⟩ := hkeep x hdx (Ne.symm hQx)
      obtain ⟨c7, ι7, hcomp7, hleg7, hR27, x7, hdx7⟩ :=
        IH s (by omega) (by omega) hlam hn (hleg.erase Q) he hR2'
          ⟨x', hdx'⟩
      exact ⟨c7,
        ⟨Q.succAbove ∘ ⇑ι7,
          Fin.succAbove_right_injective.comp ι7.injective⟩,
        by rw [hcomp7]; rfl, hleg7, hR27, x7, hdx7⟩

/-- **Descend to eight centres.**  Iterated tail deletion of arbitrary
non-anchor non-low rows reduces a `≥ 8`-centre `R2` configuration to a
genuine eight-centre subconfiguration `c' = c ∘ ι`. -/
theorem r2_n4_descend8 :
    ∀ {t : ℕ} (ht : 8 ≤ t) {lam : ℝ} (hlam : 0 < lam)
      (hn : Nat.floor (Real.pi / lam) = 4) {c : Fin t → Plane₂}
      (hleg : Section4Legality c lam) (he : e ≠ 0),
      R2N4Profile o e lam c →
      ∃ c' : Fin 8 → Plane₂, ∃ ι : Fin 8 ↪ Fin t, c' = c ∘ ⇑ι ∧
        Section4Legality c' lam ∧ R2N4Profile o e lam c' := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht lam hlam hn c hleg he hR2
    rcases Nat.eq_or_lt_of_le ht with rfl | hgt
    · exact ⟨c, Function.Embedding.refl _, rfl, hleg, hR2⟩
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      obtain ⟨v, a, b, hva, hvb, hab, hsat, hda, hdb, htail⟩ := hR2
      obtain ⟨Q, hQv, hQa, hQb, -⟩ :=
        exists_ne_five (by omega : 5 < s + 1) v a b v a
      obtain ⟨hR2', -⟩ :=
        r2_n4_delete_step (by omega) hlam hn he hleg hva hvb hab
          hsat hda hdb htail hQv hQa hQb
      obtain ⟨c8, ι8, hcomp8, hleg8, hR28⟩ :=
        IH s (by omega) (by omega) hlam hn (hleg.erase Q) he hR2'
      exact ⟨c8,
        ⟨Q.succAbove ∘ ⇑ι8,
          Fin.succAbove_right_injective.comp ι8.injective⟩,
        by rw [hcomp8]; rfl, hleg8, hR28⟩

/-- **Reduction to the two critical profiles.**  An over-capacity
(`potential > 2^4 + 2^2`) `R2` configuration at `n = 4` with `t ≥ 6`
centres contains, as a literal subconfiguration `c ∘ ι`, either a
seven-centre `(1,2,2,3,4,4,4)` profile or an eight-centre
`(1,2,2,4,4,4,4,4)` profile.

With `F = 16 + 2p + q` and `p ≤ 1` (`r2_n4_tail_defect3_le_one`),
`F > 20` forces either `p = 1, q ≥ 3` — descent to seven centres keeps
the unique defect-`3` row and the other tail rows re-classify to `4`
by the scarcity bound — or `p = 0, q ≥ 5` — descent to eight centres
then re-classifies: if a defect-`3` row appeared, deleting any other
tail row lands on the seven-centre profile; otherwise all five tail
rows are defect `4`. -/
theorem r2_n4_overcap_reduces {t : ℕ} (ht : 6 ≤ t) {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin t → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    (hR2 : R2N4Profile o e lam c)
    (hover : 2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c)) :
    (∃ c' : Fin 7 → Plane₂, ∃ ι : Fin 7 ↪ Fin t, c' = c ∘ ⇑ι ∧
        Section4Legality c' lam ∧
        ∃ v a b u : Fin 7, v ≠ a ∧ v ≠ b ∧ v ≠ u ∧ a ≠ b ∧ a ≠ u ∧
          b ≠ u ∧
          rowDefect 4 lam (directionRow o e c' v) = 1 ∧
          rowDefect 4 lam (directionRow o e c' a) = 2 ∧
          rowDefect 4 lam (directionRow o e c' b) = 2 ∧
          rowDefect 4 lam (directionRow o e c' u) = 3 ∧
          ∀ w : Fin 7, w ≠ v → w ≠ a → w ≠ b → w ≠ u →
            rowDefect 4 lam (directionRow o e c' w) = 4) ∨
    (∃ c' : Fin 8 → Plane₂, ∃ ι : Fin 8 ↪ Fin t, c' = c ∘ ⇑ι ∧
        Section4Legality c' lam ∧
        ∃ v a b : Fin 8, v ≠ a ∧ v ≠ b ∧ a ≠ b ∧
          rowDefect 4 lam (directionRow o e c' v) = 1 ∧
          rowDefect 4 lam (directionRow o e c' a) = 2 ∧
          rowDefect 4 lam (directionRow o e c' b) = 2 ∧
          ∀ w : Fin 8, w ≠ v → w ≠ a → w ≠ b →
            rowDefect 4 lam (directionRow o e c' w) = 4) := by
  classical
  obtain ⟨v, a, b, hva, hvb, hab, hsat, hda, hdb, htail⟩ := hR2
  have hcell : ∀ i : Fin t, rowCells lam (directionRow o e c i) ≤ 4 :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i
      (by omega) hn
  have hdle : ∀ i : Fin t, rowDefect 4 lam (directionRow o e c i) ≤ 4 :=
    fun i => rowDefect_le lam hlam 4 _ (hcell i)
  have hsc : ∀ i : Fin t, exponentAt lam (directionRows o e c) i =
      4 - rowDefect 4 lam (directionRow o e c i) :=
    fun i => rowScore_eq_sub_defect lam hlam 4 _ (hcell i)
  have hcount := r2_n4_tail_defect3_le_one ht hlam hn hleg he v hsat
    (a := a) (b := b) hva.symm hvb.symm hab hda hdb htail
  -- A row whose defect is `≠ 3` and `≥ 3` has defect `4`, hence
  -- contributes exactly `2^(4-4) = 1` to the potential.
  have hterm1 : ∀ i : Fin t,
      3 ≤ rowDefect 4 lam (directionRow o e c i) →
      rowDefect 4 lam (directionRow o e c i) ≠ 3 →
      2 ^ exponentAt lam (directionRows o e c) i = 1 := by
    intro i h3i h4i
    have hd4 : rowDefect 4 lam (directionRow o e c i) = 4 := by
      have := hdle i; omega
    rw [hsc i, hd4]; norm_num
  by_cases h3 : ∃ x : Fin t, rowDefect 4 lam (directionRow o e c x) = 3
  · -- `p = 1`: the weight budget `16 + 2 + (t-4)·1 > 20` forces `t ≥ 7`.
    obtain ⟨x, hdx⟩ := h3
    have hxv : x ≠ v := fun h => by subst h; rw [hdx] at hsat; omega
    have hxa : x ≠ a := fun h => by subst h; rw [hdx] at hda; omega
    have hxb : x ≠ b := fun h => by subst h; rw [hdx] at hdb; omega
    have ht7 : 7 ≤ t := by
      have hsub : ({v, a, b, x} : Finset (Fin t)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hsplit := Finset.sum_sdiff hsub
        (f := fun i => 2 ^ exponentAt lam (directionRows o e c) i)
      have hS : ∑ i ∈ ({v, a, b, x} : Finset (Fin t)),
          2 ^ exponentAt lam (directionRows o e c) i = 18 := by
        have hvmem : v ∉ ({a, b, x} : Finset (Fin t)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hva, hvb, hxv.symm⟩
        have hamem : a ∉ ({b, x} : Finset (Fin t)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hab, hxa.symm⟩
        have hbmem : b ∉ ({x} : Finset (Fin t)) := by
          simp only [Finset.mem_singleton]
          exact hxb.symm
        rw [Finset.sum_insert hvmem, Finset.sum_insert hamem,
          Finset.sum_insert hbmem, Finset.sum_singleton, hsc v, hsat,
          hsc a, hda, hsc b, hdb, hsc x, hdx]; norm_num
      have hrest : ∑ i ∈ Finset.univ \ ({v, a, b, x} : Finset (Fin t)),
          2 ^ exponentAt lam (directionRows o e c) i = t - 4 := by
        have h1 : ∀ i ∈ Finset.univ \ ({v, a, b, x} : Finset (Fin t)),
            2 ^ exponentAt lam (directionRows o e c) i = 1 := by
          intro i hi
          have hi' : i ∉ ({v, a, b, x} : Finset (Fin t)) :=
            (Finset.mem_sdiff.mp hi).2
          simp only [Finset.mem_insert, Finset.mem_singleton,
            not_or] at hi'
          obtain ⟨hiv, hia, hib, hix⟩ := hi'
          exact hterm1 i (htail i hiv hia hib)
            (fun hd3 =>
              hcount x i hxv hxa hxb hiv hia hib (Ne.symm hix)
                ⟨hdx, hd3⟩)
        rw [Finset.sum_congr rfl h1]
        simp only [Finset.sum_const, smul_eq_mul, mul_one]
        have hcard4 : ({v, a, b, x} : Finset (Fin t)).card = 4 := by
          have hvmem : v ∉ ({a, b, x} : Finset (Fin t)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hva, hvb, hxv.symm⟩
          have hamem : a ∉ ({b, x} : Finset (Fin t)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hab, hxa.symm⟩
          have hbmem : b ∉ ({x} : Finset (Fin t)) := by
            simp only [Finset.mem_singleton]
            exact hxb.symm
          rw [Finset.card_insert_of_notMem hvmem,
            Finset.card_insert_of_notMem hamem,
            Finset.card_insert_of_notMem hbmem, Finset.card_singleton]
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
          Finset.inter_univ, hcard4]
      have hpot : potential lam (directionRows o e c) = 18 + (t - 4) := by
        rw [potential_eq_exponent_sum, ← hsplit, hS, hrest]; omega
      rw [hpot] at hover
      omega
    obtain ⟨c7, ι7, hcomp7, hleg7, hR27, x7, hdx7⟩ :=
      r2_n4_descend7 ht7 hlam hn hleg he ⟨v, a, b, hva, hvb, hab, hsat,
        hda, hdb, htail⟩ ⟨x, hdx⟩
    obtain ⟨v7, a7, b7, hva7, hvb7, hab7, hsat7, hda7, hdb7, htail7⟩ :=
      hR27
    have hcell7 : ∀ i : Fin 7,
        rowCells lam (directionRow o e c7 i) ≤ 4 :=
      fun i => rowCells_directionRow_le_of_floor_eq o e c7 hlam i
        (by omega) hn
    have hdle7 : ∀ i : Fin 7,
        rowDefect 4 lam (directionRow o e c7 i) ≤ 4 :=
      fun i => rowDefect_le lam hlam 4 _ (hcell7 i)
    have hcount7 := r2_n4_tail_defect3_le_one (by omega : 6 ≤ 7) hlam hn
      hleg7 he v7 hsat7 (a := a7) (b := b7) hva7.symm hvb7.symm hab7
      hda7 hdb7 htail7
    have hx7v : x7 ≠ v7 := fun h => by
      subst h; rw [hdx7] at hsat7; omega
    have hx7a : x7 ≠ a7 := fun h => by
      subst h; rw [hdx7] at hda7; omega
    have hx7b : x7 ≠ b7 := fun h => by
      subst h; rw [hdx7] at hdb7; omega
    refine Or.inl ⟨c7, ι7, hcomp7, hleg7, v7, a7, b7, x7, hva7, hvb7,
      hx7v.symm, hab7, hx7a.symm, hx7b.symm, hsat7, hda7, hdb7, hdx7,
      ?_⟩
    intro w hwv hwa hwb hwx
    have hw3 : 3 ≤ rowDefect 4 lam (directionRow o e c7 w) :=
      htail7 w hwv hwa hwb
    have hwn3 : rowDefect 4 lam (directionRow o e c7 w) ≠ 3 :=
      fun hd3 => hcount7 x7 w hx7v hx7a hx7b hwv hwa hwb hwx.symm
        ⟨hdx7, hd3⟩
    have hwle := hdle7 w
    omega
  · -- `p = 0`: every tail row has defect `4`, so
    -- `16 + (t-3)·1 > 20` forces `t ≥ 8`.
    push Not at h3
    have ht8 : 8 ≤ t := by
      have hsub : ({v, a, b} : Finset (Fin t)) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hsplit := Finset.sum_sdiff hsub
        (f := fun i => 2 ^ exponentAt lam (directionRows o e c) i)
      have hS : ∑ i ∈ ({v, a, b} : Finset (Fin t)),
          2 ^ exponentAt lam (directionRows o e c) i = 16 := by
        have hvmem : v ∉ ({a, b} : Finset (Fin t)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hva, hvb⟩
        have hamem : a ∉ ({b} : Finset (Fin t)) := by
          simp only [Finset.mem_singleton]
          exact hab
        rw [Finset.sum_insert hvmem, Finset.sum_insert hamem,
          Finset.sum_singleton, hsc v, hsat, hsc a, hda, hsc b, hdb]
        norm_num
      have hrest : ∑ i ∈ Finset.univ \ ({v, a, b} : Finset (Fin t)),
          2 ^ exponentAt lam (directionRows o e c) i = t - 3 := by
        have h1 : ∀ i ∈ Finset.univ \ ({v, a, b} : Finset (Fin t)),
            2 ^ exponentAt lam (directionRows o e c) i = 1 := by
          intro i hi
          have hi' : i ∉ ({v, a, b} : Finset (Fin t)) :=
            (Finset.mem_sdiff.mp hi).2
          simp only [Finset.mem_insert, Finset.mem_singleton,
            not_or] at hi'
          obtain ⟨hiv, hia, hib⟩ := hi'
          exact hterm1 i (htail i hiv hia hib) (h3 i)
        rw [Finset.sum_congr rfl h1]
        simp only [Finset.sum_const, smul_eq_mul, mul_one]
        have hcard3 : ({v, a, b} : Finset (Fin t)).card = 3 := by
          have hvmem : v ∉ ({a, b} : Finset (Fin t)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hva, hvb⟩
          have hamem : a ∉ ({b} : Finset (Fin t)) := by
            simp only [Finset.mem_singleton]
            exact hab
          rw [Finset.card_insert_of_notMem hvmem,
            Finset.card_insert_of_notMem hamem, Finset.card_singleton]
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin,
          Finset.inter_univ, hcard3]
      have hpot : potential lam (directionRows o e c) = 16 + (t - 3) := by
        rw [potential_eq_exponent_sum, ← hsplit, hS, hrest]; omega
      rw [hpot] at hover
      omega
    obtain ⟨c8, ι8, hcomp8, hleg8, hR28⟩ :=
      r2_n4_descend8 ht8 hlam hn hleg he ⟨v, a, b, hva, hvb, hab, hsat,
        hda, hdb, htail⟩
    obtain ⟨v8, a8, b8, hva8, hvb8, hab8, hsat8, hda8, hdb8, htail8⟩ :=
      hR28
    have hcell8 : ∀ i : Fin 8,
        rowCells lam (directionRow o e c8 i) ≤ 4 :=
      fun i => rowCells_directionRow_le_of_floor_eq o e c8 hlam i
        (by omega) hn
    have hdle8 : ∀ i : Fin 8,
        rowDefect 4 lam (directionRow o e c8 i) ≤ 4 :=
      fun i => rowDefect_le lam hlam 4 _ (hcell8 i)
    have hcount8 := r2_n4_tail_defect3_le_one (by omega : 6 ≤ 8) hlam hn
      hleg8 he v8 hsat8 (a := a8) (b := b8) hva8.symm hvb8.symm hab8
      hda8 hdb8 htail8
    by_cases h38 : ∃ u : Fin 8,
        rowDefect 4 lam (directionRow o e c8 u) = 3
    · -- A defect-`3` row appeared during descent: delete any other
      -- tail row and land on the seven-centre profile.
      obtain ⟨u, hdu⟩ := h38
      have huv : u ≠ v8 := fun h => by subst h; rw [hdu] at hsat8; omega
      have hua : u ≠ a8 := fun h => by subst h; rw [hdu] at hda8; omega
      have hub : u ≠ b8 := fun h => by subst h; rw [hdu] at hdb8; omega
      obtain ⟨Q, hQv, hQa, hQb, hQu, -⟩ :=
        exists_ne_five (by omega : 5 < 8) v8 a8 b8 u u
      obtain ⟨hR27', hkeep⟩ :=
        r2_n4_delete_step (by omega : 6 ≤ 7) hlam hn he
          (c := c8) hleg8 hva8 hvb8 hab8 hsat8 hda8 hdb8 htail8
          hQv hQa hQb
      obtain ⟨x7', hdx7'⟩ := hkeep u hdu (Ne.symm hQu)
      set c7 := c8 ∘ Q.succAbove with hc7def
      have hleg7 : Section4Legality c7 lam := hleg8.erase Q
      obtain ⟨v7, a7, b7, hva7, hvb7, hab7, hsat7, hda7, hdb7, htail7⟩ :=
        hR27'
      have hcell7 : ∀ i : Fin 7,
          rowCells lam (directionRow o e c7 i) ≤ 4 :=
        fun i => rowCells_directionRow_le_of_floor_eq o e c7 hlam i
          (by omega) hn
      have hdle7 : ∀ i : Fin 7,
          rowDefect 4 lam (directionRow o e c7 i) ≤ 4 :=
        fun i => rowDefect_le lam hlam 4 _ (hcell7 i)
      have hcount7 := r2_n4_tail_defect3_le_one (by omega : 6 ≤ 7)
        hlam hn hleg7 he v7 hsat7 (a := a7) (b := b7) hva7.symm hvb7.symm
        hab7 hda7 hdb7 htail7
      have hx7v : x7' ≠ v7 := fun h => by
        subst h; rw [hdx7'] at hsat7; omega
      have hx7a : x7' ≠ a7 := fun h => by
        subst h; rw [hdx7'] at hda7; omega
      have hx7b : x7' ≠ b7 := fun h => by
        subst h; rw [hdx7'] at hdb7; omega
      refine Or.inl ⟨c7,
        ⟨⇑ι8 ∘ Q.succAbove, ι8.injective.comp
          Fin.succAbove_right_injective⟩,
        ?_, hleg7, v7, a7, b7, x7', hva7, hvb7, hx7v.symm, hab7,
        hx7a.symm, hx7b.symm, hsat7, hda7, hdb7, hdx7', ?_⟩
      · rw [hc7def, hcomp8]; rfl
      · intro w hwv hwa hwb hwx
        have hw3 : 3 ≤ rowDefect 4 lam (directionRow o e c7 w) :=
          htail7 w hwv hwa hwb
        have hwn3 : rowDefect 4 lam (directionRow o e c7 w) ≠ 3 :=
          fun hd3 => hcount7 x7' w hx7v hx7a hx7b hwv hwa hwb hwx.symm
            ⟨hdx7', hd3⟩
        have hwle := hdle7 w
        omega
    · -- No defect-`3` row: all five tail rows have defect `4`.
      push Not at h38
      refine Or.inr ⟨c8, ι8, hcomp8, hleg8, v8, a8, b8, hva8, hvb8,
        hab8, hsat8, hda8, hdb8, ?_⟩
      intro w hwv hwa hwb
      have hw3 : 3 ≤ rowDefect 4 lam (directionRow o e c8 w) :=
        htail8 w hwv hwa hwb
      have hwn3 : rowDefect 4 lam (directionRow o e c8 w) ≠ 3 := h38 w
      have hwle := hdle8 w
      omega

/-- **Zero gain on every unit deletion in `S7`.**  In a seven-centre
`(1,2,2,3,4,4,4)` profile at `n = 4`, deleting any defect-`4` row `Q`
(the three tail rows other than the defect-`3` row `u`) leaves every
survivor's actual `rowGain` equal to `0`.

The reduced configuration is again `R2` (`r2_tail_delete_closed`), so
`six_centre_n4_overcap` bounds its potential by `20`.  The deleted row
carried weight `1`, and per-row `score' ≥ score` pushes the reduced
potential up to at least the old survivor weight `21 − 1 = 20`.  Hence
`F(C ∖ {Q}) = 20` and every survivor term is unchanged,
`score' = score`, i.e. `rowGain = 0`.  Note this applies only to
deleting a defect-`4` row — deleting `u` loses weight `2` and gets no
such conclusion. -/
theorem seven_centre_n4_unit_delete_gains_zero {lam : ℝ}
    (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 7 → Plane₂} (hleg : Section4Legality c lam) (he : e ≠ 0)
    {v a b u : Fin 7} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hvu : v ≠ u) (hau : a ≠ u) (hbu : b ≠ u)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2)
    (hdu : rowDefect 4 lam (directionRow o e c u) = 3)
    (htail4 : ∀ w : Fin 7, w ≠ v → w ≠ a → w ≠ b → w ≠ u →
      rowDefect 4 lam (directionRow o e c w) = 4)
    {Q : Fin 7} (hQv : Q ≠ v) (hQa : Q ≠ a) (hQb : Q ≠ b)
    (hQu : Q ≠ u) :
    ∀ x' : Fin 6,
      rowGain lam (directionRow o e c (Q.succAbove x'))
        (deleteIndex o e c Q (Q.succAbove x')) = 0 := by
  classical
  obtain ⟨q₀, hq₀⟩ := Fin.exists_succAbove_eq hQv
  obtain ⟨a₀, ha₀⟩ := Fin.exists_succAbove_eq (Ne.symm hva)
  obtain ⟨b₀, hb₀⟩ := Fin.exists_succAbove_eq (Ne.symm hvb)
  have hab₀ : a₀ ≠ b₀ := fun h => hab (by rw [← ha₀, h, hb₀])
  have hqa₀ : q₀ ≠ a₀ := fun h => hQa (by rw [← hq₀, h, ha₀])
  have hqb₀ : q₀ ≠ b₀ := fun h => hQb (by rw [← hq₀, h, hb₀])
  obtain ⟨v', hv', hdv', a', b', ha', hb', hda', hdb', hother'⟩ :=
    r2_tail_delete_closed o e he (by omega) (by decide) hlam hn hleg v
      hsat hab₀ (ha₀.symm ▸ hda) (hb₀.symm ▸ hdb) q₀ hqa₀ hqb₀
  have hva' : v' ≠ a' := fun h => hva (by rw [← hv', h, ha', ha₀])
  have hvb' : v' ≠ b' := fun h => hvb (by rw [← hv', h, hb', hb₀])
  have hab' : a' ≠ b' := fun h => hab₀
    (Fin.succAbove_right_injective (by rw [← ha', h, hb']))
  have hup : ∀ x' : Fin 6,
      rowScore lam (directionRow o e c (Q.succAbove x')) ≤
        rowScore lam (directionRow o e (c ∘ Q.succAbove) x') :=
    fun x' => rowScore_le_of_delete hlam o e c (by omega) Q x'
  have hdel : ∀ x' : Fin 6,
      rowScore lam (directionRow o e (c ∘ Q.succAbove) x') =
        rowScore lam (directionRow o e c (Q.succAbove x')) +
          rowGain lam (directionRow o e c (Q.succAbove x'))
            (deleteIndex o e c Q (Q.succAbove x')) := by
    intro x'
    rw [eraseIdx_directionRow o e Q x']
    exact rowScore_eraseIdx' hlam (directionRow_sorted o e c _)
      (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
      (deleteIndex_lt o e c (Fin.succAbove_ne Q x'))
      (by rw [directionRow_length]; omega)
  -- The pre-deletion survivor weight is exactly `20`.
  have hcell : ∀ i : Fin 7, rowCells lam (directionRow o e c i) ≤ 4 :=
    fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i
      (by omega) hn
  have hsc : ∀ i : Fin 7, exponentAt lam (directionRows o e c) i =
      4 - rowDefect 4 lam (directionRow o e c i) :=
    fun i => rowScore_eq_sub_defect lam hlam 4 _ (hcell i)
  have hdQ : rowDefect 4 lam (directionRow o e c Q) = 4 :=
    htail4 Q hQv hQa hQb hQu
  have htQ : 2 ^ exponentAt lam (directionRows o e c) Q = 1 := by
    rw [hsc Q, hdQ]; norm_num
  have holdE : ∑ i ∈ Finset.univ.erase Q,
      2 ^ exponentAt lam (directionRows o e c) i = 20 := by
    have hsub' : ({v, a, b, u} : Finset (Fin 7)) ⊆ Finset.univ.erase Q := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_erase]
      rcases hw with rfl | rfl | rfl | rfl
      · exact ⟨hQv.symm, Finset.mem_univ _⟩
      · exact ⟨hQa.symm, Finset.mem_univ _⟩
      · exact ⟨hQb.symm, Finset.mem_univ _⟩
      · exact ⟨hQu.symm, Finset.mem_univ _⟩
    have hsplit := Finset.sum_sdiff hsub'
      (f := fun i => 2 ^ exponentAt lam (directionRows o e c) i)
    have hS : ∑ i ∈ ({v, a, b, u} : Finset (Fin 7)),
        2 ^ exponentAt lam (directionRows o e c) i = 18 := by
      have hvmem : v ∉ ({a, b, u} : Finset (Fin 7)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hva, hvb, hvu⟩
      have hamem : a ∉ ({b, u} : Finset (Fin 7)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab, hau⟩
      have hbmem : b ∉ ({u} : Finset (Fin 7)) := by
        simp only [Finset.mem_singleton]
        exact hbu
      rw [Finset.sum_insert hvmem, Finset.sum_insert hamem,
        Finset.sum_insert hbmem, Finset.sum_singleton, hsc v, hsat,
        hsc a, hda, hsc b, hdb, hsc u, hdu]; norm_num
    have hrest : ∑ i ∈ Finset.univ.erase Q \
        ({v, a, b, u} : Finset (Fin 7)),
        2 ^ exponentAt lam (directionRows o e c) i = 2 := by
      have h1 : ∀ i ∈ Finset.univ.erase Q \
          ({v, a, b, u} : Finset (Fin 7)),
          2 ^ exponentAt lam (directionRows o e c) i = 1 := by
        intro i hi
        have hi' : i ∉ ({v, a, b, u} : Finset (Fin 7)) :=
          (Finset.mem_sdiff.mp hi).2
        have hiQ : i ≠ Q := (Finset.mem_erase.mp
          (Finset.mem_sdiff.mp hi).1).1
        simp only [Finset.mem_insert, Finset.mem_singleton,
          not_or] at hi'
        obtain ⟨hiv, hia, hib, hiu⟩ := hi'
        rw [hsc i, htail4 i hiv hia hib hiu]; norm_num
      rw [Finset.sum_congr rfl h1]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      have hcard4 : ({v, a, b, u} : Finset (Fin 7)).card = 4 := by
        have hvmem : v ∉ ({a, b, u} : Finset (Fin 7)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hva, hvb, hvu⟩
        have hamem : a ∉ ({b, u} : Finset (Fin 7)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hab, hau⟩
        have hbmem : b ∉ ({u} : Finset (Fin 7)) := by
          simp only [Finset.mem_singleton]
          exact hbu
        rw [Finset.card_insert_of_notMem hvmem,
          Finset.card_insert_of_notMem hamem,
          Finset.card_insert_of_notMem hbmem, Finset.card_singleton]
      rw [Finset.card_sdiff, Finset.card_erase_of_mem
        (Finset.mem_univ Q), Finset.card_univ, Fintype.card_fin,
        Finset.inter_eq_left.mpr hsub', hcard4]
    rw [← hsplit, hS, hrest]
  have hold : ∑ x' : Fin 6,
      2 ^ exponentAt lam (directionRows o e c) (Q.succAbove x') = 20 := by
    have hfull : ∑ i : Fin 7,
        2 ^ exponentAt lam (directionRows o e c) i =
        2 ^ exponentAt lam (directionRows o e c) Q +
          ∑ x' : Fin 6,
            2 ^ exponentAt lam (directionRows o e c)
              (Q.succAbove x') :=
      Fin.sum_univ_succAbove _ Q
    have herase : 2 ^ exponentAt lam (directionRows o e c) Q +
        ∑ i ∈ Finset.univ.erase Q,
          2 ^ exponentAt lam (directionRows o e c) i =
        ∑ i : Fin 7, 2 ^ exponentAt lam (directionRows o e c) i := by
      simpa using Finset.add_sum_erase Finset.univ
        (fun i : Fin 7 => 2 ^ exponentAt lam (directionRows o e c) i)
        (Finset.mem_univ Q)
    omega
  -- The reduced potential is squeezed to `20`.
  have hred : potential lam (directionRows o e (c ∘ Q.succAbove)) = 20 := by
    apply le_antisymm
    · by_contra hcap'
      push Not at hcap'
      have hcap'' : 2 ^ 4 + 2 ^ 2 <
          potential lam
            (directionRows o e (c ∘ (v.succAbove q₀).succAbove)) := by
        rw [hq₀]; exact hcap'
      exact six_centre_n4_overcap o e he hlam hn
        (hleg.erase (v.succAbove q₀)) hva' hvb' hab' hdv' hda' hdb'
        hother' hcap''
    · rw [potential_eq_exponent_sum]
      calc 20 = ∑ x' : Fin 6,
            2 ^ exponentAt lam (directionRows o e c)
              (Q.succAbove x') := hold.symm
        _ ≤ ∑ x' : Fin 6,
            2 ^ rowScore lam
              (directionRow o e (c ∘ Q.succAbove) x') :=
          Finset.sum_le_sum fun x' _ =>
            Nat.pow_le_pow_right (by omega) (hup x')
  -- Per-term squeeze: each survivor's score is unchanged, so `gain = 0`.
  intro x'
  have hterm_eq : ∀ x' : Fin 6,
      2 ^ rowScore lam (directionRow o e c (Q.succAbove x')) =
        2 ^ rowScore lam (directionRow o e (c ∘ Q.succAbove) x') := by
    have hsum : (∑ x' : Fin 6,
        2 ^ rowScore lam (directionRow o e c (Q.succAbove x'))) =
        ∑ x' : Fin 6,
          2 ^ rowScore lam
            (directionRow o e (c ∘ Q.succAbove) x') := by
      calc (∑ x' : Fin 6,
            2 ^ rowScore lam (directionRow o e c (Q.succAbove x')))
          = 20 := hold
        _ = potential lam (directionRows o e (c ∘ Q.succAbove)) :=
          hred.symm
        _ = ∑ x' : Fin 6,
            2 ^ rowScore lam
              (directionRow o e (c ∘ Q.succAbove) x') := by
          rw [potential_eq_exponent_sum]
          exact Finset.sum_congr rfl fun x' _ => rfl
    exact fun x' => (Finset.sum_eq_sum_iff_of_le
      (fun i _ => Nat.pow_le_pow_right (by omega) (hup i))).mp hsum x'
      (Finset.mem_univ x')
  have hscore_eq :
      rowScore lam (directionRow o e (c ∘ Q.succAbove) x') =
        rowScore lam (directionRow o e c (Q.succAbove x')) :=
    (Nat.pow_right_injective (by omega : 2 ≤ 2)) (hterm_eq x').symm
  rw [hdel x'] at hscore_eq
  omega

end Defect4Reduction

#print axioms r2_n4_tail_defect3_le_one
#print axioms r2_n4_overcap_reduces
#print axioms seven_centre_n4_unit_delete_gains_zero

end Jsp404
