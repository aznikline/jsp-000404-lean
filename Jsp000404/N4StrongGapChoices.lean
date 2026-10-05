import Jsp000404.SmallScoreGapBounds

namespace Jsp404.N4StrongGapChoices

open StrongGapBudget SmallScoreGapBounds

theorem two_large_of_sublist (gs : List ℝ) (a b : ℝ)
    (hsub : [a, b].Sublist gs) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2 ≤ countAtLeast 2 gs := by
  have h := (hsub.filter (fun g => decide ((2 : ℝ) ≤ g))).length_le
  simpa [countAtLeast, ha, hb] using h

theorem no_two_large (gs : List ℝ) (a b : ℝ) (hsub : [a, b].Sublist gs)
    (hcount : countAtLeast 2 gs ≤ 1) : a < 2 ∨ b < 2 := by
  by_cases ha : 2 ≤ a
  · right
    by_contra hh
    have hb : 2 ≤ b := by linarith
    have h := two_large_of_sublist gs a b hsub ha hb
    omega
  · left
    linarith

theorem budget_exists_large {n c : ℕ} (gs : List ℝ) (h : Budget n c gs) :
    ∃ g ∈ gs, 2 ≤ g := by
  rcases h with ⟨selected, hsub, hpos, _, _, hlarge, _⟩
  cases selected with
  | nil => simp at hpos
  | cons a rest => exact ⟨a, hsub.subset (by simp), hlarge a (by simp)⟩

theorem budget_two_case (gs : List ℝ) (h : Budget 4 2 gs) :
    (∃ g ∈ gs, 3 ≤ g) ∨ 2 ≤ countAtLeast 2 gs := by
  rcases h with ⟨selected, hsub, hpos, hlen, _, hlarge, hsum⟩
  cases selected with
  | nil => simp at hpos
  | cons a rest =>
    cases rest with
    | nil =>
      left
      have ha : 3 ≤ a := by norm_num at hsum; exact hsum
      exact ⟨a, hsub.subset (by simp), ha⟩
    | cons b rest =>
      have hnil : rest = [] := by
        have hz : rest.length = 0 := by simp only [List.length_cons] at hlen; omega
        exact List.eq_nil_of_length_eq_zero hz
      subst rest
      right
      exact two_large_of_sublist gs a b hsub (hlarge a (by simp)) (hlarge b (by simp))


def ChoicesTwo (a b c d e : ℝ) : Prop :=
  3 ≤ a ∨ 3 ≤ b ∨ 3 ≤ c ∨ 3 ≤ d ∨ 3 ≤ e ∨ (2 ≤ a ∧ 2 ≤ b) ∨ (2 ≤ a ∧ 2 ≤ c) ∨ (2 ≤ a ∧ 2 ≤ d) ∨ (2 ≤ a ∧ 2 ≤ e) ∨ (2 ≤ b ∧ 2 ≤ c) ∨ (2 ≤ b ∧ 2 ≤ d) ∨ (2 ≤ b ∧ 2 ≤ e) ∨ (2 ≤ c ∧ 2 ≤ d) ∨ (2 ≤ c ∧ 2 ≤ e) ∨ (2 ≤ d ∧ 2 ≤ e)

theorem choices_two (a b c d e : ℝ) (h : Budget 4 2 [a,b,c,d,e]) :
    ChoicesTwo a b c d e := by
  rcases budget_two_case [a,b,c,d,e] h with hlarge | hcount
  · rcases hlarge with ⟨g, hg, hge⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hge
    · exact Or.inr (Or.inl hge)
    · exact Or.inr (Or.inr (Or.inl hge))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hge)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hge))))
  ·
    by_cases h0 : (2 : ℝ) ≤ a
    ·
      by_cases h1 : (2 : ℝ) ≤ b
      ·
        by_cases h2 : (2 : ℝ) ≤ c
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))))
      ·
        by_cases h2 : (2 : ℝ) ≤ c
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h2⟩))))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h2⟩))))))
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h2⟩))))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h2⟩))))))
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h3⟩)))))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h3⟩)))))))
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h4⟩))))))))
            ·
              simp [countAtLeast, h0, h1, h2, h3, h4] at hcount
    ·
      by_cases h1 : (2 : ℝ) ≤ b
      ·
        by_cases h2 : (2 : ℝ) ≤ c
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))))
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h3⟩))))))))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h3⟩))))))))))
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h4⟩)))))))))))
            ·
              simp [countAtLeast, h0, h1, h2, h3, h4] at hcount
      ·
        by_cases h2 : (2 : ℝ) ≤ c
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))))))))))))
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))))))))))))
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h4⟩)))))))))))))
            ·
              simp [countAtLeast, h0, h1, h2, h3, h4] at hcount
        ·
          by_cases h3 : (2 : ℝ) ≤ d
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨h3, h4⟩))))))))))))))
            ·
              simp [countAtLeast, h0, h1, h2, h3, h4] at hcount
          ·
            by_cases h4 : (2 : ℝ) ≤ e
            ·
              simp [countAtLeast, h0, h1, h2, h3, h4] at hcount
            ·
              simp [countAtLeast, h0, h1, h2, h3, h4] at hcount

def ChoicesThree (a b c d e : ℝ) : Prop :=
  2 ≤ a ∨ 2 ≤ b ∨ 2 ≤ c ∨ 2 ≤ d ∨ 2 ≤ e

theorem choices_three (a b c d e : ℝ) (h : Budget 4 3 [a,b,c,d,e]) :
    ChoicesThree a b c d e := by
  obtain ⟨g, hg, hge⟩ := budget_exists_large [a,b,c,d,e] h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hge
  · exact Or.inr (Or.inl hge)
  · exact Or.inr (Or.inr (Or.inl hge))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hge)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hge))))

#print axioms choices_two
#print axioms choices_three
end Jsp404.N4StrongGapChoices
