import Jsp000404.R1N4Delete

/-!
# Arbitrary-size `R1` capacity at `n = 4`, stage 1: descent

An `R1` profile at `n = 4` is a legal configuration with a saturated
anchor `v`, exactly one defect-`2` row `a`, and every remaining row of
defect `≥ 3`.  Its potential is

  `F = 8 + 4 + (2k + l)`  with `k + l = t - 2`,

so `F = 10 + t + k` where `k` is the number of defect-`3` tail rows.
At `t = 6` the profile cannot exceed the cap `20` (`F ≤ 20`), and
`defect_two_rows_le_two` rules out `R ≥ 3` low rows, so `R1` is the
last single-low-row regime after `R2`.

Internal helper `r1_n4_overcap_reduces_of_r2_exclusion` carries
`hr2 : R2N4OvercapExclusion o e` as an explicit hypothesis so this
module does not import the R2 certificate assembly.  The original
no-callback API `r1_n4_overcap_reduces` is preserved as the wrapper
in `R1N4Reduction.lean`, which supplies `hr2` from the proved
`r2_n4_overcap_impossible`.
-/

namespace Jsp404

open scoped EuclideanSpace

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}

/-- **Reduction to the six boundary profiles.**  An over-capacity
`R1` configuration at `n = 4` with `t ≥ 6` centres contains — as a
literal subconfiguration `c ∘ ι` — a configuration at `T` centres
whose potential is pinned to the boundary: `(T, F)` is one of
`(7, 22)` or `(T, 21)` for `7 ≤ T ≤ 11`.

Since `F = 10 + t + k` with `k ≤ t − 2` the number of defect-`3`
tails, `t = 6` forces `F ≤ 20`, so over-capacity implies `t ≥ 7`.
Deleting a defect-`4` tail (when one exists, weight `1`) or otherwise
a defect-`3` tail (weight `2`) keeps the configuration `R1`
(`r1_tail_delete`) with `F' = F − w + G`, `G ≥ 0`.  While
`F' > 20` the induction hypothesis supplies a boundary
subconfiguration of the reduced configuration, hence of the original.
When `F' ≤ 20` the deleted weight forces `F ≤ 22`, and the
`F = 10 + t + k` identity pins the size:

* `F = 21` (defect-`4` deletion): `k = 11 − t`, `7 ≤ t ≤ 11`;
* `F = 22` (all-defect-`3` deletion): `k = 12 − t` with `k = t − 2`,
  forcing `t = 7`. -/
theorem r1_n4_overcap_reduces_of_r2_exclusion
    (hr2 : R2N4OvercapExclusion o e) :
    ∀ {t : ℕ} (_ht : 6 ≤ t) {lam : ℝ} (_hlam : 0 < lam)
      (_hn : Nat.floor (Real.pi / lam) = 4) {c : Fin t → Plane₂}
      (_hleg : Section4Legality c lam) (_he : e ≠ 0),
      R1N4Profile o e lam c →
      2 ^ 4 + 2 ^ 2 < potential lam (directionRows o e c) →
      ∃ (T : ℕ) (c' : Fin T → Plane₂) (ι : Fin T ↪ Fin t),
        c' = c ∘ ⇑ι ∧ Section4Legality c' lam ∧
        R1N4Profile o e lam c' ∧
        ((T = 7 ∧ potential lam (directionRows o e c') = 22) ∨
         (T = 7 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 8 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 9 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 10 ∧ potential lam (directionRows o e c') = 21) ∨
         (T = 11 ∧ potential lam (directionRows o e c') = 21)) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
    intro ht lam hlam hn c hleg he hR1 hover
    classical
    obtain ⟨v, a, hva, hsat, hda, htail⟩ := hR1
    have hcell : ∀ i : Fin t, rowCells lam (directionRow o e c i) ≤ 4 :=
      fun i => rowCells_directionRow_le_of_floor_eq o e c hlam i
        (by omega) hn
    have hdle : ∀ i : Fin t,
        rowDefect 4 lam (directionRow o e c i) ≤ 4 :=
      fun i => rowDefect_le lam hlam 4 _ (hcell i)
    have hsc : ∀ i : Fin t, exponentAt lam (directionRows o e c) i =
        4 - rowDefect 4 lam (directionRow o e c i) :=
      fun i => rowScore_eq_sub_defect lam hlam 4 _ (hcell i)
    -- tail decomposition: `F = 12 + Σ_tails`, `Σ_tails = t − 2 + k`
    have h20 : (2 : ℕ) ^ 4 + 2 ^ 2 = 20 := by norm_num
    set Tails : Finset (Fin t) := Finset.univ \ {v, a} with hTdef
    have hTmem : ∀ w : Fin t, w ∈ Tails ↔ w ≠ v ∧ w ≠ a := by
      intro w
      rw [hTdef]
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, not_or, true_and]
    have hTcard : Tails.card = t - 2 := by
      have h2 : ({v, a} : Finset (Fin t)).card = 2 := by
        rw [Finset.card_insert_of_notMem (show v ∉ ({a} : Finset (Fin t))
          by simp only [Finset.mem_singleton]; exact hva),
          Finset.card_singleton]
      rw [hTdef, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, Fintype.card_fin, h2]
    set K : ℕ := (Tails.filter (fun w =>
      rowDefect 4 lam (directionRow o e c w) = 3)).card with hKdef
    have hKle : K ≤ t - 2 := by
      rw [hKdef, ← hTcard]
      exact Finset.card_filter_le _ _
    have hsumT : ∑ w ∈ Tails, 2 ^ exponentAt lam (directionRows o e c) w
        = t - 2 + K := by
      have hsplit := Finset.sum_filter_add_sum_filter_not Tails
        (fun w => rowDefect 4 lam (directionRow o e c w) = 3)
        (fun w => 2 ^ exponentAt lam (directionRows o e c) w)
      have hA : ∑ w ∈ Tails.filter (fun w =>
            rowDefect 4 lam (directionRow o e c w) = 3),
          2 ^ exponentAt lam (directionRows o e c) w = 2 * K := by
        rw [Finset.sum_congr rfl (fun w hw => by
          rw [hsc w, (Finset.mem_filter.mp hw).2])]
        rw [Finset.sum_const, smul_eq_mul]
        rw [← hKdef]
        exact Nat.mul_comm _ _
      have hB : ∑ w ∈ Tails.filter (fun w =>
            ¬ rowDefect 4 lam (directionRow o e c w) = 3),
          2 ^ exponentAt lam (directionRows o e c) w =
            Tails.card - K := by
        have hcong : ∑ w ∈ Tails.filter (fun w =>
              ¬ rowDefect 4 lam (directionRow o e c w) = 3),
            2 ^ exponentAt lam (directionRows o e c) w =
            ∑ w ∈ Tails.filter (fun w =>
              ¬ rowDefect 4 lam (directionRow o e c w) = 3), 1 := by
          apply Finset.sum_congr rfl
          intro w hw
          have hd := Finset.mem_filter.mp hw
          obtain ⟨hwv, hwa⟩ := (hTmem w).mp hd.1
          have hd3 := htail w hwv hwa
          have hd4 := hdle w
          have hd4' : rowDefect 4 lam (directionRow o e c w) = 4 := by
            omega
          rw [hsc w, hd4']
          norm_num
        have hcard : (Tails.filter (fun w =>
              ¬ rowDefect 4 lam (directionRow o e c w) = 3)).card =
            Tails.card - K := by
          have hcover : Tails.filter (fun w =>
                ¬ rowDefect 4 lam (directionRow o e c w) = 3) =
              Tails \ Tails.filter (fun w =>
                rowDefect 4 lam (directionRow o e c w) = 3) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            tauto
          rw [hKdef, hcover, Finset.card_sdiff,
            Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
        rw [hcong, Finset.sum_const, smul_eq_mul, mul_one, hcard]
      rw [← hsplit, hA, hB, hTcard]
      omega
    have hFeq : potential lam (directionRows o e c) = 10 + t + K := by
      have hsplit := Finset.sum_sdiff (Finset.subset_univ
        ({v, a} : Finset (Fin t)))
        (f := fun i => 2 ^ exponentAt lam (directionRows o e c) i)
      rw [← hTdef] at hsplit
      have hS : ∑ i ∈ ({v, a} : Finset (Fin t)),
          2 ^ exponentAt lam (directionRows o e c) i = 12 := by
        have hvmem : v ∉ ({a} : Finset (Fin t)) := by
          simp only [Finset.mem_singleton]
          exact hva
        rw [Finset.sum_insert hvmem, Finset.sum_singleton,
          hsc v, hsat, hsc a, hda]
        norm_num
      have htot : ∑ i : Fin t, 2 ^ exponentAt lam (directionRows o e c) i
          = 12 + (t - 2 + K) := by
        rw [← hsplit, hS, hsumT]
        omega
      rw [potential_eq_exponent_sum, htot]
      omega
    -- `t = 6` is under the cap; otherwise `t = s + 1` with `s ≥ 6`.
    rcases Nat.eq_or_lt_of_le ht with h6 | hgt
    · exfalso
      subst h6
      have hFge : 20 < potential lam (directionRows o e c) := hover
      have hFle : potential lam (directionRows o e c) ≤ 20 := by omega
      omega
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hs6 : 6 ≤ s := by omega
      -- deletion branch: prefer a defect-`4` tail (weight `1`),
      -- else all tails have defect `3` (weight `2`)
      by_cases h4 : ∃ Q : Fin (s + 1), Q ≠ v ∧ Q ≠ a ∧
          rowDefect 4 lam (directionRow o e c Q) = 4
      · obtain ⟨Q, hQv, hQa, hdQ⟩ := h4
        obtain ⟨hR1', hled⟩ := r1_tail_delete hs6 hr2 hlam hn he hleg hva
          hQv hQa hsat hda htail hover
        by_cases hF' : 20 <
            potential lam (directionRows o e (c ∘ Q.succAbove))
        · -- descend: the reduced over-cap `R1` contains a boundary.
          obtain ⟨T, c', ι, hcomp, hlegT, hR1T, hTF⟩ :=
            IH s (by omega) hs6 hlam hn (hleg.erase Q) he hR1' hF'
          exact ⟨T, c', ⟨Q.succAbove ∘ ⇑ι,
              Fin.succAbove_right_injective.comp ι.injective⟩,
            hcomp.trans (Function.comp_assoc _ _ _),
            hlegT, hR1T, hTF⟩
        · -- boundary: `F' ≤ 20`, `w_Q = 1` forces `F = 21`.
          push Not at hF'
          have hFge : 20 < potential lam (directionRows o e c) := hover
          have hwQ : 2 ^ exponentAt lam (directionRows o e c) Q = 1 := by
            rw [hsc Q, hdQ]
            norm_num
          have hF21 : potential lam (directionRows o e c) = 21 := by
            omega
          have hs10 : s ≤ 10 := by omega
          refine ⟨s + 1, c, Function.Embedding.refl _, rfl, hleg,
            ⟨v, a, hva, hsat, hda, htail⟩, ?_⟩
          have hscases : s = 6 ∨ s = 7 ∨ s = 8 ∨ s = 9 ∨ s = 10 := by
            omega
          rcases hscases with rfl | rfl | rfl | rfl | rfl
          · exact Or.inr (Or.inl ⟨rfl, hF21⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨rfl, hF21⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hF21⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl ⟨rfl, hF21⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr ⟨rfl, hF21⟩))))
      · push Not at h4
        obtain ⟨Q, hQv, hQa⟩ := r1_exists_tail (by omega : 3 ≤ s + 1) v a
        have hdQ : rowDefect 4 lam (directionRow o e c Q) = 3 := by
          have h1 := htail Q hQv hQa
          have h2 := h4 Q hQv hQa
          have h3 := hdle Q
          omega
        obtain ⟨hR1', hled⟩ := r1_tail_delete hs6 hr2 hlam hn he hleg hva
          hQv hQa hsat hda htail hover
        by_cases hF' : 20 <
            potential lam (directionRows o e (c ∘ Q.succAbove))
        · obtain ⟨T, c', ι, hcomp, hlegT, hR1T, hTF⟩ :=
            IH s (by omega) hs6 hlam hn (hleg.erase Q) he hR1' hF'
          exact ⟨T, c', ⟨Q.succAbove ∘ ⇑ι,
              Fin.succAbove_right_injective.comp ι.injective⟩,
            hcomp.trans (Function.comp_assoc _ _ _),
            hlegT, hR1T, hTF⟩
        · -- boundary: `F' ≤ 20`, `w_Q = 2`, all tails defect-`3` —
          -- `F = 8 + 2t` forces `F = 22` and `t = 7`.
          push Not at hF'
          have hFge : 20 < potential lam (directionRows o e c) := hover
          have hwQ : 2 ^ exponentAt lam (directionRows o e c) Q = 2 := by
            rw [hsc Q, hdQ]
            norm_num
          have hKeq : K = s + 1 - 2 := by
            have hall : Tails.filter (fun w =>
                rowDefect 4 lam (directionRow o e c w) = 3) = Tails := by
              rw [Finset.filter_eq_self]
              intro w hw
              obtain ⟨hwv, hwa⟩ := (hTmem w).mp hw
              have h1 := htail w hwv hwa
              have h2 := h4 w hwv hwa
              have h3 := hdle w
              omega
            rw [hKdef, hall, hTcard]
          have hF22 : potential lam (directionRows o e c) = 22 := by
            omega
          have ht7 : s + 1 = 7 := by omega
          refine ⟨s + 1, c, Function.Embedding.refl _, rfl, hleg,
            ⟨v, a, hva, hsat, hda, htail⟩, ?_⟩
          exact Or.inl ⟨ht7, hF22⟩

end Jsp404
