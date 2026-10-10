import Jsp000404.S8Extraction

/-!
# S8 θ-region dispatch

Connects `defect_two_pair_theta_cluster` (s = 7, n = 4) to the
three terminal theorems of `S8Extraction`.  The three θ-regions
locate the two defect-`2` rows at ranks `{0,1}`, `{5,6}` or `{0,6}`
— each closed directly by one of `s8cert_{AA,BT,AB}`; the five
remaining defect-`4` rows are inert.

The θ-rank identification lemmas are the `Fin 7` ports of the
`n4σ_*` machinery; `eight_centre_n4_terminal` is the terminal
exclusion for the critical eight-centre profile
`(1,2,2,4,4,4,4,4)`.
-/

namespace Jsp404

open Classical
open scoped EuclideanSpace

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 8 → Plane₂} {v : Fin 8} {theta : Fin 7 → ℝ}
  (C : SatChart o e 4 lam c v theta)

/-- A `Fin 7` copy of `n3_pigeon`. -/
private theorem n8_pigeon {lo hi a b c : Fin 7}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a = lo ∨ a = hi) (hb : b = lo ∨ b = hi)
    (hc : c = lo ∨ c = hi) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> simp_all

/-- All-above region: the two defect-`2` rows occupy ranks `0`, `1`. -/
theorem n8σ_zero_one_of_all_above {lo hi : Fin 7}
    (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 7, z ≠ lo → z ≠ hi → theta hi < theta z) :
    n8σ C 0 = lo ∧ n8σ C 1 = hi := by
  have hge : ∀ z : Fin 7, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hθ.trans (hcl z h1 h2)).le
  have hT0 : n8T C 0 = theta lo := by
    apply n8T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n8σ_spec C 0]; exact hge _
  have hσ0 : n8σ C 0 = lo := (n8σ_eq_iff C lo 0).mpr hT0
  have hT1 : n8T C 1 = theta hi := by
    apply n8T_eq_of_bounds C hi 1
    · intro s hs
      have hs0 : s = 0 := Fin.ext (Nat.lt_one_iff.mp hs)
      rw [hs0, hT0]; exact hθ
    · rw [← n8σ_spec C 1]
      rcases eq_or_ne (n8σ C 1) lo with h1 | h1
      · exact absurd (n8σ_injective C (h1.trans hσ0.symm)) (by decide)
      · rcases eq_or_ne (n8σ C 1) hi with rfl | h2
        · exact le_refl _
        · exact (hcl _ h1 h2).le
  exact ⟨hσ0, (n8σ_eq_iff C hi 1).mpr hT1⟩

/-- All-below region: the two defect-`2` rows occupy ranks `5`, `6`. -/
theorem n8σ_five_six_of_all_below {lo hi : Fin 7}
    (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 7, z ≠ lo → z ≠ hi → theta z < theta lo) :
    n8σ C 5 = lo ∧ n8σ C 6 = hi := by
  have hle : ∀ z : Fin 7, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact ((hcl z h2 h1).trans hθ).le
  have hT6 : n8T C 6 = theta hi := by
    apply n8T_eq_of_bounds C hi 6
    · intro s hs
      rw [← n8σ_spec C s]
      rcases eq_or_ne (n8σ C s) hi with h1 | h1
      · exfalso
        have hmax : n8T C 6 ≤ theta hi := by
          rw [← n8σ_spec C 6]; exact hle _
        have hlt : n8T C s < n8T C 6 := n8T_strictMono C hs
        rw [← n8σ_spec C s, h1] at hlt
        linarith
      · rcases eq_or_ne (n8σ C s) lo with rfl | h2
        · exact hθ
        · exact (hcl _ h2 h1).trans hθ
    · obtain ⟨r', hr'⟩ := (n8σ_bijective C).surjective hi
      have hle6 : r' ≤ (6 : Fin 7) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n8T_strictMono C).monotone hle6
      rw [← n8σ_spec C r', hr'] at hm
      exact hm
  have hσ6 : n8σ C 6 = hi := (n8σ_eq_iff C hi 6).mpr hT6
  have hT5 : n8T C 5 = theta lo := by
    apply n8T_eq_of_bounds C lo 5
    · intro s hs
      rw [← n8σ_spec C s]
      by_contra hnn
      replace hnn := not_lt.mp hnn
      have h1 : n8σ C s = lo ∨ n8σ C s = hi := by
        rcases eq_or_ne (n8σ C s) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n8σ C s) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hnn)
      have h5 : n8σ C 5 = lo ∨ n8σ C 5 = hi := by
        have hge5 : theta lo ≤ n8T C 5 := by
          have hlt := n8T_strictMono C hs
          rw [← n8σ_spec C s] at hlt
          linarith
        rw [← n8σ_spec C 5] at hge5
        rcases eq_or_ne (n8σ C 5) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n8σ C 5) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge5)
      have h6 : n8σ C 6 = lo ∨ n8σ C 6 = hi := by
        have hge6 : theta lo ≤ n8T C 6 := by
          have hlt := n8T_strictMono C
            (hs.trans (by decide : (5 : Fin 7) < 6))
          rw [← n8σ_spec C s] at hlt
          linarith
        rw [← n8σ_spec C 6] at hge6
        rcases eq_or_ne (n8σ C 6) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n8σ C 6) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge6)
      exact n8_pigeon
        (fun h => (ne_of_lt hs) (n8σ_injective C h))
        (fun h => (ne_of_lt (hs.trans (by decide : (5 : Fin 7) < 6)))
          (n8σ_injective C h))
        (fun h => absurd (n8σ_injective C h) (by decide))
        h1 h5 h6
    · rw [← n8σ_spec C 5]
      rcases eq_or_ne (n8σ C 5) hi with h5hi | h5hi
      · exact absurd (n8σ_injective C (h5hi.trans hσ6.symm)) (by decide)
      · rcases eq_or_ne (n8σ C 5) lo with rfl | h5lo
        · exact le_refl _
        · exfalso
          obtain ⟨r_l, hr_l⟩ := (n8σ_bijective C).surjective lo
          have hrl5 : r_l ≠ 5 := fun h => h5lo (h ▸ hr_l)
          have hrl6 : r_l ≠ 6 := fun h =>
            hθ.ne (by rw [← hr_l, ← hσ6, h])
          have hrl4 : r_l.val ≤ 4 := by
            have hlt7 := r_l.isLt
            have h5v : r_l.val ≠ 5 := fun hv => hrl5 (Fin.ext hv)
            have h6v : r_l.val ≠ 6 := fun hv => hrl6 (Fin.ext hv)
            omega
          have hlt : n8T C r_l < n8T C 5 := by
            apply n8T_strictMono C
            rw [Fin.lt_def]
            omega
          rw [← n8σ_spec C r_l, hr_l] at hlt
          have hcl5 : n8T C 5 < theta lo := by
            have h := hcl _ h5lo h5hi
            rwa [n8σ_spec C 5] at h
          linarith
  exact ⟨(n8σ_eq_iff C lo 5).mpr hT5, hσ6⟩

/-- Between region: the two defect-`2` rows occupy ranks `0`, `6`. -/
theorem n8σ_zero_six_of_between {lo hi : Fin 7}
    (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 7, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi) :
    n8σ C 0 = lo ∧ n8σ C 6 = hi := by
  have hge : ∀ z : Fin 7, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hcl z h1 h2).1.le
  have hle : ∀ z : Fin 7, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact (hcl z h2 h1).2.le
  have hT0 : n8T C 0 = theta lo := by
    apply n8T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n8σ_spec C 0]; exact hge _
  have hT6 : n8T C 6 = theta hi := by
    apply n8T_eq_of_bounds C hi 6
    · intro s hs
      rw [← n8σ_spec C s]
      rcases eq_or_ne (n8σ C s) hi with h1 | h1
      · exfalso
        have hmax : theta (n8σ C 6) ≤ theta hi := hle _
        have hlt : n8T C s < n8T C 6 := n8T_strictMono C hs
        rw [← n8σ_spec C s, ← n8σ_spec C 6, h1] at hlt
        linarith
      · rcases eq_or_ne (n8σ C s) lo with h2 | h2
        · rw [h2]; exact hθ
        · exact (hcl _ h2 h1).2
    · obtain ⟨r', hr'⟩ := (n8σ_bijective C).surjective hi
      have hle6 : r' ≤ (6 : Fin 7) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n8T_strictMono C).monotone hle6
      rw [← n8σ_spec C r', hr'] at hm
      exact hm
  exact ⟨(n8σ_eq_iff C lo 0).mpr hT0, (n8σ_eq_iff C hi 6).mpr hT6⟩

/-- **Eight-centre `n = 4` terminal exclusion.**  An eight-centre
configuration at `n = 4` with a saturated anchor and two defect-`2`
rows `a, b` is impossible: the θ-cluster regions enumerate exactly
the three rank classes `{0,1}`, `{0,6}`, `{5,6}` excluded by the
`s8cert_*` certificates; the five defect-`4` rows are inert. -/
theorem eight_centre_n4_terminal
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 8 → Plane₂} (hleg : Section4Legality c lam)
    {v a b : Fin 8}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2) :
    False := by
  classical
  obtain ⟨e', he', theta, C, lo, hi, hswap, hθlt, hclass⟩ :=
    defect_two_pair_theta_cluster o e he (by omega : 4 ≤ 7)
      (by omega : 3 ≤ 4) hlam hn hleg hva hvb hab hsat hda hdb
  have href : ∀ x : Fin 8,
      rowDefect 4 lam (directionRow o e' c x) =
        rowDefect 4 lam (directionRow o e c x) :=
    fun x => rowDefect_directionRow_reference_eq o e' e he' he c
      hleg.inj x hlam (by omega) hn
  have hdlo : rowDefect 4 lam (directionRow o e' c (v.succAbove lo))
      = 2 := by
    rcases hswap with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1, href] <;> assumption
  have hdhi : rowDefect 4 lam (directionRow o e' c (v.succAbove hi))
      = 2 := by
    rcases hswap with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2, href] <;> assumption
  rcases hclass with hbelow | hbetween | habove
  · obtain ⟨hσ5, hσ6⟩ := n8σ_five_six_of_all_below C hθlt hbelow
    exact eight_centre_n4_AB C hσ5 hσ6 hdlo hdhi
  · obtain ⟨hσ0, hσ6⟩ := n8σ_zero_six_of_between C hθlt hbetween
    exact eight_centre_n4_BT C hσ0 hσ6 hdlo hdhi
  · obtain ⟨hσ0, hσ1⟩ := n8σ_zero_one_of_all_above C hθlt habove
    exact eight_centre_n4_AA C hσ0 hσ1 hdlo hdhi

end Jsp404
