import Jsp000404.FivePointCapacity

/-!
# `R1` profile bundle and tail deletion at `n = 4`

`R1N4Profile` and the deletion lemma `r1_tail_delete`, split from
`R1N4Capacity` so the reduction layer does not import the R2
certificate assembly (`R2N4Assembly`, ~4 GiB olean closure): the R2
over-capacity exclusion enters through the hypothesis
`R2N4OvercapExclusion`, discharged later by `r2_n4_overcap_impossible`
in the terminal assembly.
-/

namespace Jsp404

open scoped EuclideanSpace

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- **The `R1` profile at `n = 4`.**  Saturated anchor `v`, unique
defect-`2` row `a`, every other row of defect `≥ 3`. -/
def R1N4Profile (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂)
    {t : ℕ} (lam : ℝ) (c : Fin t → Plane₂) : Prop :=
  ∃ v a : Fin t, v ≠ a ∧
    rowDefect 4 lam (directionRow o e c v) = 1 ∧
    rowDefect 4 lam (directionRow o e c a) = 2 ∧
    ∀ w : Fin t, w ≠ v → w ≠ a →
      3 ≤ rowDefect 4 lam (directionRow o e c w)

/-- The R2 over-capacity exclusion used by the R1 reduction,
stated as a hypothesis so this module stays independent of the R2
certificate chain.  The statement is the in-lined body of
`R2N4Profile` together with `potential > 20`, matching
`r2_n4_overcap_impossible`. -/
def R2N4OvercapExclusion (o : Orientation ℝ Plane₂ (Fin 2))
    (e : Plane₂) : Prop :=
  ∀ {t : ℕ} (_ht : 6 ≤ t) {lam : ℝ} (_hlam : 0 < lam)
    (_hn : Nat.floor (Real.pi / lam) = 4) {c : Fin t → Plane₂}
    (_hleg : Section4Legality c lam) (_he : e ≠ 0),
    (∃ v a b : Fin t, v ≠ a ∧ v ≠ b ∧ a ≠ b ∧
      rowDefect 4 lam (directionRow o e c v) = 1 ∧
      rowDefect 4 lam (directionRow o e c a) = 2 ∧
      rowDefect 4 lam (directionRow o e c b) = 2 ∧
      ∀ w : Fin t, w ≠ v → w ≠ a → w ≠ b →
        3 ≤ rowDefect 4 lam (directionRow o e c w)) →
    2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c) → False

/-- Pick a centre distinct from `v` and `a` (needs `t ≥ 3`). -/
theorem r1_exists_tail {t : ℕ} (ht : 3 ≤ t) (v a : Fin t) :
    ∃ Q : Fin t, Q ≠ v ∧ Q ≠ a := by
  have hcard : (Finset.univ \ ({v, a} : Finset (Fin t))).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin]
    have h2 : ({v, a} : Finset (Fin t)).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  obtain ⟨Q, hQ⟩ := hcard
  have hQ' := (Finset.mem_sdiff.mp hQ).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hQ'
  exact ⟨Q, hQ'.1, hQ'.2⟩


/-- **Tail deletion of an over-capacity `R1` configuration stays
`R1`.**  Deleting tail centre `Q` (`≠ v, a`) of a `≥ 7`-centre `R1`
configuration with `potential > 20` produces a reduced `R1`
configuration, with the exact potential ledger
`F' + w_Q = F + Σ 2^{sc}(2^{g} − 1)`.

Every deviation of the reduced profile is fatal: defect-`1` survivors
contradict `potential_le_high_of_two_saturated` (their own charge
`≥ 4` keeps the reduced potential above `20`), a promoted defect-`2`
tail either creates a third defect-`2` row
(`defect_two_rows_le_two`) or an over-capacity `R2` sub-configuration
(`hr2 : R2N4OvercapExclusion`), and the anchor's defect `1` cannot
improve. -/
theorem r1_tail_delete {s : ℕ} (hs : 6 ≤ s)
    (hr2 : R2N4OvercapExclusion o e)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    (he : e ≠ 0) {c : Fin (s + 1) → Plane₂}
    (hleg : Section4Legality c lam)
    {v a Q : Fin (s + 1)} (hva : v ≠ a) (hQv : Q ≠ v) (hQa : Q ≠ a)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (htail : ∀ w : Fin (s + 1), w ≠ v → w ≠ a →
      3 ≤ rowDefect 4 lam (directionRow o e c w))
    (hover : 2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c)) :
    R1N4Profile o e lam (c ∘ Q.succAbove) ∧
      potential lam (directionRows o e (c ∘ Q.succAbove)) +
          2 ^ exponentAt lam (directionRows o e c) Q =
        potential lam (directionRows o e c) +
          ∑ x' : Fin s, 2 ^ exponentAt lam (directionRows o e c)
              (Q.succAbove x') *
            (2 ^ rowGain lam (directionRow o e c (Q.succAbove x'))
                (deleteIndex o e c Q (Q.succAbove x')) - 1) := by
  classical
  have hleg' : Section4Legality (c ∘ Q.succAbove) lam := hleg.erase Q
  have h20 : (2 : ℕ) ^ 4 + 2 ^ 2 = 20 := by norm_num
  rw [h20] at hover
  -- per-survivor score bridge: `score' = score + rowGain`
  have hdel : ∀ x' : Fin s,
      rowScore lam (directionRow o e (c ∘ Q.succAbove) x') =
        rowScore lam (directionRow o e c (Q.succAbove x')) +
          rowGain lam (directionRow o e c (Q.succAbove x'))
            (deleteIndex o e c Q (Q.succAbove x')) := by
    intro x'
    rw [eraseIdx_directionRow o e Q x']
    have hx : Q.succAbove x' ≠ Q := Fin.succAbove_ne Q x'
    exact rowScore_eraseIdx' hlam (directionRow_sorted o e c _)
      (fun b hb => Set.mem_Ico.mp (directionRow_mem_Ico o e c hb))
      (deleteIndex_lt o e c hx) (by rw [directionRow_length]; omega)
  have hup : ∀ x' : Fin s,
      rowScore lam (directionRow o e c (Q.succAbove x')) ≤
        rowScore lam (directionRow o e (c ∘ Q.succAbove) x') :=
    fun x' => by rw [hdel x']; omega
  have cO : ∀ x : Fin (s + 1), rowCells lam (directionRow o e c x) ≤ 4 :=
    fun x => rowCells_directionRow_le_of_floor_eq o e c hlam x
      (by omega) hn
  have cN : ∀ x' : Fin s,
      rowCells lam (directionRow o e (c ∘ Q.succAbove) x') ≤ 4 :=
    fun x' => rowCells_directionRow_le_of_floor_eq o e
      (c ∘ Q.succAbove) hlam x' (by omega) hn
  have sO := fun x => rowScore_eq_sub_defect lam hlam 4 _ (cO x)
  have sN := fun x' => rowScore_eq_sub_defect lam hlam 4 _ (cN x')
  have gN := fun x' : Fin s =>
    one_le_rowDefect lam hlam 4 _ (by omega : 1 ≤ 4) (cN x')
  have dO := fun x => rowDefect_le lam hlam 4 _ (cO x)
  have dN := fun x' : Fin s => rowDefect_le lam hlam 4 _ (cN x')
  -- defects only drop under deletion
  have hdN : ∀ x' : Fin s,
      rowDefect 4 lam (directionRow o e (c ∘ Q.succAbove) x') ≤
        rowDefect 4 lam (directionRow o e c (Q.succAbove x')) := by
    intro x'
    have h1 := sN x'
    have h2 := sO (Q.succAbove x')
    have h3 := hup x'
    have h4 := dN x'
    omega
  -- the deleted row has weight `≤ 2`
  have hwQ : 2 ^ exponentAt lam (directionRows o e c) Q ≤ 2 := by
    have hdQ : 3 ≤ rowDefect 4 lam (directionRow o e c Q) :=
      htail Q hQv hQa
    have h1 := sO Q
    have h2 := dO Q
    have h3 : rowScore lam (directionRow o e c Q) ≤ 1 := by omega
    exact Nat.pow_le_pow_right (by omega) h3
  -- the potential ledger `F' + w_Q = F + G`
  set g : Fin (s + 1) → ℕ := fun x =>
    if x = Q then 0 else
      rowGain lam (directionRow o e c x) (deleteIndex o e c Q x)
    with hgdef
  set T : Fin (s + 1) → ℕ := fun x =>
    2 ^ exponentAt lam (directionRows o e c) x * (2 ^ g x - 1)
    with hTdef
  have hF' : potential lam (directionRows o e (c ∘ Q.succAbove)) +
      2 ^ exponentAt lam (directionRows o e c) Q =
        potential lam (directionRows o e c) +
          ∑ x' : Fin s, T (Q.succAbove x') := by
    have hsc' : ∀ x' : Fin s,
        exponentAt lam (directionRows o e (c ∘ Q.succAbove)) x' =
          rowScore lam (directionRow o e (c ∘ Q.succAbove) x') :=
      fun _ => rfl
    have hexp : potential lam (directionRows o e (c ∘ Q.succAbove)) =
        ∑ x' : Fin s, 2 ^ (exponentAt lam (directionRows o e c)
            (Q.succAbove x') + g (Q.succAbove x')) := by
      rw [potential_eq_exponent_sum]
      apply Finset.sum_congr rfl
      intro x' _
      have hx : Q.succAbove x' ≠ Q := Fin.succAbove_ne Q x'
      have hgx : g (Q.succAbove x') =
          rowGain lam (directionRow o e c (Q.succAbove x'))
            (deleteIndex o e c Q (Q.succAbove x')) := by
        rw [hgdef]
        exact if_neg hx
      rw [hsc' x', hdel x', hgx]
      rfl
    have hsplit : ∀ x : Fin (s + 1),
        2 ^ (exponentAt lam (directionRows o e c) x + g x) =
          2 ^ exponentAt lam (directionRows o e c) x + T x := by
      intro x
      have h1 : 1 ≤ 2 ^ g x := Nat.one_le_two_pow
      have hAB : 2 ^ exponentAt lam (directionRows o e c) x ≤
          2 ^ exponentAt lam (directionRows o e c) x * 2 ^ g x := by
        conv_lhs =>
          rw [← mul_one (2 ^ exponentAt lam (directionRows o e c) x)]
        exact Nat.mul_le_mul_left _ h1
      simp only [hTdef]
      rw [pow_add, Nat.mul_sub, mul_one]
      exact (Nat.add_sub_cancel' hAB).symm
    have hTQ : T Q = 0 := by
      simp [hTdef, hgdef]
    have hgQ : g Q = 0 := by
      rw [hgdef]
      exact if_pos rfl
    have hsum : ∑ x : Fin (s + 1),
        2 ^ (exponentAt lam (directionRows o e c) x + g x) =
          2 ^ (exponentAt lam (directionRows o e c) Q + g Q) +
            ∑ x' : Fin s, 2 ^ (exponentAt lam (directionRows o e c)
                (Q.succAbove x') + g (Q.succAbove x')) :=
      Fin.sum_univ_succAbove _ Q
    rw [Finset.sum_congr rfl (fun x _ => hsplit x),
      Finset.sum_add_distrib] at hsum
    have hsumT : ∑ x : Fin (s + 1), T x =
        ∑ x' : Fin s, T (Q.succAbove x') := by
      have h1 := Fin.sum_univ_succAbove T Q
      rw [hTQ, zero_add] at h1
      exact h1
    rw [hgQ, add_zero] at hsum
    rw [hsumT] at hsum
    rw [hexp, potential_eq_exponent_sum]
    omega
  -- survivors of the reduced configuration
  obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq (Ne.symm hQv)
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (Ne.symm hQa)
  have hva' : v' ≠ a' := fun h => hva (by rw [← hv', h, ha'])
  set G := ∑ x' : Fin s, T (Q.succAbove x') with hGdef
  -- any specific survivor's charge bounds `G` from below
  have hGge : ∀ x' : Fin s, T (Q.succAbove x') ≤ G := by
    intro x'
    rw [hGdef]
    exact Finset.single_le_sum
      (f := fun y => T (Q.succAbove y)) (fun y _ => Nat.zero_le _)
      (Finset.mem_univ x')
  have hgT : ∀ x' : Fin s, T (Q.succAbove x') =
      2 ^ exponentAt lam (directionRows o e c) (Q.succAbove x') *
        (2 ^ rowGain lam (directionRow o e c (Q.succAbove x'))
            (deleteIndex o e c Q (Q.succAbove x')) - 1) := by
    intro x'
    have hx : Q.succAbove x' ≠ Q := Fin.succAbove_ne Q x'
    simp only [hTdef, hgdef, if_neg hx]
  -- anchor stays saturated: defect cannot drop below `1`.
  have hdv' : rowDefect 4 lam
      (directionRow o e (c ∘ Q.succAbove) v') = 1 := by
    have h1 := hdN v'
    rw [hv'] at h1
    have h2 := gN v'
    omega
  -- kill a defect-`1` survivor: the two-saturated cap bounds the
  -- reduced potential by `20`, yet the promoted row alone charges
  -- `≥ 4`, forcing `F' ≥ F − 2 + 4 > 20`.
  have kill1 : ∀ x' : Fin s, x' ≠ v' →
      rowDefect 4 lam (directionRow o e (c ∘ Q.succAbove) x') ≠ 1 := by
    intro x' hxv' hd1
    have hcap := potential_le_high_of_two_saturated o e he
      (by omega : 3 ≤ s) (by omega : 2 ≤ 4) hlam hn hleg' hxv'
      hd1 hdv'
    have hcap20 : potential lam
        (directionRows o e (c ∘ Q.succAbove)) ≤ 20 :=
      hcap.trans (by norm_num)
    -- charge of `x'` is ≥ 4
    have hdO : 2 ≤ rowDefect 4 lam
        (directionRow o e c (Q.succAbove x')) := by
      rcases eq_or_ne (Q.succAbove x') a with rfl | hxa
      · omega
      · have h := htail _ (fun h =>
            hxv' (Fin.succAbove_right_injective (h.trans hv'.symm))) hxa
        omega
    have hsc_x : rowScore lam
        (directionRow o e c (Q.succAbove x')) ≤ 2 := by
      have h1 := sO (Q.succAbove x')
      have h2 := dO (Q.succAbove x')
      omega
    -- the promoted row's charge: `score + gain = 3` gives
    -- `2^{sc}(2^g − 1) = 2^3 − 2^{sc} ≥ 8 − 4 = 4`.
    have hsg : rowScore lam (directionRow o e c (Q.succAbove x')) +
        rowGain lam (directionRow o e c (Q.succAbove x'))
          (deleteIndex o e c Q (Q.succAbove x')) = 3 := by
      have h1 := hdel x'
      have h2 := sN x'
      rw [hd1] at h2
      omega
    have hterm : 4 ≤ 2 ^ exponentAt lam (directionRows o e c)
        (Q.succAbove x') *
        (2 ^ rowGain lam (directionRow o e c (Q.succAbove x'))
            (deleteIndex o e c Q (Q.succAbove x')) - 1) := by
      have hexp' : (2 : ℕ) ^ exponentAt lam (directionRows o e c)
          (Q.succAbove x') *
          (2 ^ rowGain lam (directionRow o e c (Q.succAbove x'))
              (deleteIndex o e c Q (Q.succAbove x')) - 1) =
          2 ^ (rowScore lam (directionRow o e c (Q.succAbove x')) +
            rowGain lam (directionRow o e c (Q.succAbove x'))
              (deleteIndex o e c Q (Q.succAbove x'))) -
            2 ^ rowScore lam
              (directionRow o e c (Q.succAbove x')) := by
        simp only [exponentAt, directionRows]
        rw [pow_add, Nat.mul_sub, mul_one]
      have hle4 : (2 : ℕ) ^ rowScore lam
          (directionRow o e c (Q.succAbove x')) ≤ 4 :=
        Nat.pow_le_pow_right (by omega) hsc_x
      rw [hexp', hsg]
      norm_num
      omega
    have hG4 : 4 ≤ G :=
      (hgT x' ▸ hterm).trans (hGge x')
    -- F' + w_Q = F + G with w_Q ≤ 2, F ≥ 21, G ≥ 4 → F' ≥ 23
    have hF'pot : 20 <
        potential lam (directionRows o e (c ∘ Q.succAbove)) := by
      have hGge' := hGge x'
      rw [hgT x'] at hGge'
      have := hF'
      omega
    exact absurd hcap20 (by omega)
  -- a' keeps defect `2` (it cannot reach defect `1`)
  have hda' : rowDefect 4 lam
      (directionRow o e (c ∘ Q.succAbove) a') = 2 := by
    have h1 := hdN a'
    rw [ha'] at h1
    have h2 := gN a'
    have h3 := kill1 a' hva'.symm
    omega
  -- kill a defect-`2` tail survivor: a third defect-`2` row or an
  -- over-capacity `R2` reduced configuration, both impossible.
  have kill2 : ∀ x' : Fin s, x' ≠ v' → x' ≠ a' →
      rowDefect 4 lam (directionRow o e (c ∘ Q.succAbove) x') ≠ 2 := by
    intro x' hxv' hxa' hd2
    -- the promoted tail's charge is ≥ 2
    have hdO : 3 ≤ rowDefect 4 lam
        (directionRow o e c (Q.succAbove x')) :=
      htail _ (fun h =>
        hxv' (Fin.succAbove_right_injective (h.trans hv'.symm)))
        (fun h => hxa'
          (Fin.succAbove_right_injective (h.trans ha'.symm)))
    have hsc_x : rowScore lam
        (directionRow o e c (Q.succAbove x')) ≤ 1 := by
      have h1 := sO (Q.succAbove x')
      have h2 := dO (Q.succAbove x')
      omega
    -- the promoted row's charge: `score + gain = 2` gives
    -- `2^{sc}(2^g − 1) = 2^2 − 2^{sc} ≥ 4 − 2 = 2`.
    have hsg : rowScore lam (directionRow o e c (Q.succAbove x')) +
        rowGain lam (directionRow o e c (Q.succAbove x'))
          (deleteIndex o e c Q (Q.succAbove x')) = 2 := by
      have h1 := hdel x'
      have h2 := sN x'
      rw [hd2] at h2
      omega
    have hterm : 2 ≤ 2 ^ exponentAt lam (directionRows o e c)
        (Q.succAbove x') *
        (2 ^ rowGain lam (directionRow o e c (Q.succAbove x'))
            (deleteIndex o e c Q (Q.succAbove x')) - 1) := by
      have hexp' : (2 : ℕ) ^ exponentAt lam (directionRows o e c)
          (Q.succAbove x') *
          (2 ^ rowGain lam (directionRow o e c (Q.succAbove x'))
              (deleteIndex o e c Q (Q.succAbove x')) - 1) =
          2 ^ (rowScore lam (directionRow o e c (Q.succAbove x')) +
            rowGain lam (directionRow o e c (Q.succAbove x'))
              (deleteIndex o e c Q (Q.succAbove x'))) -
            2 ^ rowScore lam
              (directionRow o e c (Q.succAbove x')) := by
        simp only [exponentAt, directionRows]
        rw [pow_add, Nat.mul_sub, mul_one]
      have hle2 : (2 : ℕ) ^ rowScore lam
          (directionRow o e c (Q.succAbove x')) ≤ 2 :=
        Nat.pow_le_pow_right (by omega) hsc_x
      rw [hexp', hsg]
      norm_num
      omega
    have hF'pot : 20 <
        potential lam (directionRows o e (c ∘ Q.succAbove)) := by
      have hGge' := hGge x'
      rw [hgT x'] at hGge'
      have := hF'
      omega
    -- either a third defect-`2` row exists (count bound) or the
    -- reduced configuration is `R2` (over-capacity)
    by_cases h3rd : ∃ y' : Fin s, y' ≠ v' ∧ y' ≠ a' ∧ y' ≠ x' ∧
        rowDefect 4 lam (directionRow o e (c ∘ Q.succAbove) y') = 2
    · obtain ⟨y', hyv', hya', hyx', hdy'⟩ := h3rd
      have hle2 := defect_two_rows_le_two o e he
        (by omega : 5 ≤ s) (by omega : 3 ≤ 4) hlam hn hleg' v' hdv'
      have hcard : 3 ≤ (Finset.univ.filter (fun i : Fin s =>
          rowDefect 4 lam (directionRow o e (c ∘ Q.succAbove) i)
            = 2)).card := by
        have hsub : ({a', x', y'} : Finset (Fin s)) ⊆
            Finset.univ.filter (fun i : Fin s =>
              rowDefect 4 lam (directionRow o e (c ∘ Q.succAbove) i)
                = 2) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ z, ?_⟩
          rcases hz with rfl | rfl | rfl
          · exact hda'
          · exact hd2
          · exact hdy'
        have h3 : ({a', x', y'} : Finset (Fin s)).card = 3 := by
          have h1 : a' ∉ ({x', y'} : Finset (Fin s)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton,
              not_or]
            exact ⟨hxa'.symm, hya'.symm⟩
          have h2 : x' ∉ ({y'} : Finset (Fin s)) := by
            simp only [Finset.mem_singleton]
            exact hyx'.symm
          rw [Finset.card_insert_of_notMem h1,
            Finset.card_insert_of_notMem h2, Finset.card_singleton]
        have hcc := Finset.card_le_card hsub
        rw [h3] at hcc
        exact hcc
      omega
    · push Not at h3rd
      -- the reduced configuration is `R2` at `s ≥ 6` centres
      have htail' : ∀ w' : Fin s, w' ≠ v' → w' ≠ a' → w' ≠ x' →
          3 ≤ rowDefect 4 lam
            (directionRow o e (c ∘ Q.succAbove) w') := by
        intro w' hwv' hwa' hwx'
        have h1 := gN w'
        have h2 := kill1 w' hwv'
        have h3 := h3rd w' hwv' hwa' hwx'
        have h4 := hdN w'
        omega
      exact hr2 (by omega : 6 ≤ s) hlam hn
        hleg' he ⟨v', a', x', hva', hxv'.symm, hxa'.symm, hdv', hda',
          hd2, htail'⟩ hF'pot
  refine ⟨⟨v', a', hva', hdv', hda', ?_⟩, ?_⟩
  · intro w' hwv' hwa'
    have h1 := gN w'
    have h2 := kill1 w' hwv'
    have h3 := kill2 w' hwv' hwa'
    have h4 := hdN w'
    omega
  · exact hF'.trans (by
      congr 1
      rw [hGdef]
      exact Finset.sum_congr rfl fun x' _ => hgT x')
end Jsp404
