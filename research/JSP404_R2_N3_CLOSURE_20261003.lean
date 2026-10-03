import Jsp000404.N3Extraction

/-!
# Local candidate: arbitrary-size n = 3 R2 closure

This proof was initially checked against frozen scalar/extraction copies:
`R2SixCentreN3.lean` SHA-256 7568c8d21192025bc42b29b6433da6a9ecc332a029649bcfeff42e6b846e09f2;
`N3Extraction.lean` SHA-256 654ede99876d4eb530b7faec07b098acc4f00bb0a6f79d6619a1ac38977a2f76.
The remote AIR pin 8365f3cb5ec3738ecb8787c14a2514e6e7e4bb46 does not contain
these modules. Upstream published their strong terminal at 1391721; the review
checkout now imports that public source. This file remains a scoped R2 closure,
not a global Sendov proof.

The induction is only on the actual number of centers. It retains the
saturated anchor and two defect-two rows, deletes another center by the
proved R2 hereditary lemma, and excludes six centers geometrically.
No capacity induction hypothesis, minimum-excess hypothesis, or assumed
zero-gain/face certificate is used.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404.AirCandidate

/-- At strip index three, a legal configuration with a saturated anchor
and two distinct defect-two rows contains at most five actual centers. -/
theorem n3_r2_centres_le_five
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3) :
    ∀ {s : ℕ} {c : Fin s → Plane₂}, Section4Legality c lam →
      ∀ {v A B : Fin s}, v ≠ A → v ≠ B → A ≠ B →
        rowDefect 3 lam (directionRow o e c v) = 1 →
        rowDefect 3 lam (directionRow o e c A) = 2 →
        rowDefect 3 lam (directionRow o e c B) = 2 → s ≤ 5 := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s IH =>
    intro c hleg v A B hvA hvB hAB hsat hA hB
    by_cases hs5 : s ≤ 5
    · exact hs5
    by_cases hs6 : s = 6
    · subst s
      exact False.elim
        (six_centre_n3_terminal o e he hlam hn hleg hvA hvB hAB hsat hA hB)
    have hs7 : 7 ≤ s := by omega
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hvA.symm
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hvB.symm
    have hab : a ≠ b := by
      intro h
      apply hAB
      calc
        A = v.succAbove a := ha.symm
        _ = v.succAbove b := congrArg v.succAbove h
        _ = B := hb
    have hda : rowDefect 3 lam
        (directionRow o e c (v.succAbove a)) = 2 := by rwa [ha]
    have hdb : rowDefect 3 lam
        (directionRow o e c (v.succAbove b)) = 2 := by rwa [hb]
    obtain ⟨q, hqa, hqb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
    obtain ⟨v', hv', hsat', a', b', ha', hb', hA', hB', _⟩ :=
      r2_tail_delete_closed o e he (by omega) (le_refl 3) hlam hn hleg
        v hsat hab hda hdb q hqa hqb
    have hvA' : v' ≠ a' := by
      intro h
      apply hvA
      calc
        v = (v.succAbove q).succAbove v' := hv'.symm
        _ = (v.succAbove q).succAbove a' := by rw [h]
        _ = v.succAbove a := ha'
        _ = A := ha
    have hvB' : v' ≠ b' := by
      intro h
      apply hvB
      calc
        v = (v.succAbove q).succAbove v' := hv'.symm
        _ = (v.succAbove q).succAbove b' := by rw [h]
        _ = v.succAbove b := hb'
        _ = B := hb
    have hAB' : a' ≠ b' := by
      intro h
      apply hAB
      calc
        A = v.succAbove a := ha.symm
        _ = (v.succAbove q).succAbove a' := ha'.symm
        _ = (v.succAbove q).succAbove b' := by rw [h]
        _ = v.succAbove b := hb'
        _ = B := hb
    have hsmall : t ≤ 5 := IH t (by omega)
      (Section4Legality.erase hleg (v.succAbove q))
      hvA' hvB' hAB' hsat' hA' hB'
    omega

/-- The full high capacity ten holds for the arbitrary-size n = 3 R2
subdomain: the geometric cardinality bound reduces it to the existing
unconditional at-most-five-center capacity theorem. -/
theorem n3_r2_potential_le_ten {s : ℕ}
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    (hs3 : 3 ≤ s) {lam : ℝ} (hlam : 0 < lam)
    (hn : Nat.floor (Real.pi / lam) = 3)
    {c : Fin s → Plane₂} (hleg : Section4Legality c lam)
    {v A B : Fin s} (hvA : v ≠ A) (hvB : v ≠ B) (hAB : A ≠ B)
    (hsat : rowDefect 3 lam (directionRow o e c v) = 1)
    (hA : rowDefect 3 lam (directionRow o e c A) = 2)
    (hB : rowDefect 3 lam (directionRow o e c B) = 2) :
    potential lam (directionRows o e c) ≤ 10 := by
  have hs5 := n3_r2_centres_le_five o e he hlam hn hleg
    hvA hvB hAB hsat hA hB
  simpa using potential_le_high_cap_of_le_five o e he hs3 hs5
    (le_refl 3) hlam hn hleg

#print axioms n3_r2_centres_le_five
#print axioms n3_r2_potential_le_ten

end Jsp404.AirCandidate
