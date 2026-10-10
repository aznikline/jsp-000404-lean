import Jsp000404.S7Extraction

/-!
# S7 θ-region dispatch

Connects `defect_two_pair_theta_cluster` (s = 6, n = 4) to the
twelve terminal theorems of `S7Extraction`.  The three θ-regions
locate the two defect-`2` rows at ranks `{0,1}`, `{4,5}` or `{0,5}`;
the defect-`3` row then occupies one of the four remaining ranks,
each closed by a generated `s7cert_*` certificate.

The θ-rank identification lemmas `n7σ_zero_one_of_all_above`,
`n7σ_four_five_of_all_below`, `n7σ_zero_five_of_between` are direct
`Fin 6` ports of the `n4σ_*` machinery in `N4Extraction`.

`seven_centre_n4_terminal` is the terminal exclusion for the
critical seven-centre profile `(1,2,2,3,4,4,4)`: a saturated anchor,
two defect-`2` rows, one defect-`3` row.  The remaining defect-`4`
rows are inert — the certificates only need the three rows.
-/

namespace Jsp404

open Classical
open scoped EuclideanSpace

variable {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂} {lam : ℝ}
  {c : Fin 7 → Plane₂} {v : Fin 7} {theta : Fin 6 → ℝ}
  (C : SatChart o e 4 lam c v theta)

/-- A `Fin 6` copy of `n3_pigeon`: three pairwise distinct elements
cannot all live in a two-element set. -/
private theorem n7_pigeon {lo hi a b c : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a = lo ∨ a = hi) (hb : b = lo ∨ b = hi)
    (hc : c = lo ∨ c = hi) : False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> simp_all

/-- All-above region: the two defect-`2` rows occupy ranks `0`, `1`. -/
theorem n7σ_zero_one_of_all_above {lo hi : Fin 6}
    (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 6, z ≠ lo → z ≠ hi → theta hi < theta z) :
    n7σ C 0 = lo ∧ n7σ C 1 = hi := by
  have hge : ∀ z : Fin 6, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hθ.trans (hcl z h1 h2)).le
  have hT0 : n7T C 0 = theta lo := by
    apply n7T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n7σ_spec C 0]; exact hge _
  have hσ0 : n7σ C 0 = lo := (n7σ_eq_iff C lo 0).mpr hT0
  have hT1 : n7T C 1 = theta hi := by
    apply n7T_eq_of_bounds C hi 1
    · intro s hs
      have hs0 : s = 0 := Fin.ext (Nat.lt_one_iff.mp hs)
      rw [hs0, hT0]; exact hθ
    · rw [← n7σ_spec C 1]
      rcases eq_or_ne (n7σ C 1) lo with h1 | h1
      · exact absurd (n7σ_injective C (h1.trans hσ0.symm)) (by decide)
      · rcases eq_or_ne (n7σ C 1) hi with rfl | h2
        · exact le_refl _
        · exact (hcl _ h1 h2).le
  exact ⟨hσ0, (n7σ_eq_iff C hi 1).mpr hT1⟩

/-- All-below region: the two defect-`2` rows occupy ranks `4`, `5`. -/
theorem n7σ_four_five_of_all_below {lo hi : Fin 6}
    (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 6, z ≠ lo → z ≠ hi → theta z < theta lo) :
    n7σ C 4 = lo ∧ n7σ C 5 = hi := by
  have hle : ∀ z : Fin 6, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact ((hcl z h2 h1).trans hθ).le
  have hT5 : n7T C 5 = theta hi := by
    apply n7T_eq_of_bounds C hi 5
    · intro s hs
      rw [← n7σ_spec C s]
      rcases eq_or_ne (n7σ C s) hi with h1 | h1
      · exfalso
        have hmax : n7T C 5 ≤ theta hi := by
          rw [← n7σ_spec C 5]; exact hle _
        have hlt : n7T C s < n7T C 5 := n7T_strictMono C hs
        rw [← n7σ_spec C s, h1] at hlt
        linarith
      · rcases eq_or_ne (n7σ C s) lo with rfl | h2
        · exact hθ
        · exact (hcl _ h2 h1).trans hθ
    · obtain ⟨r', hr'⟩ := (n7σ_bijective C).surjective hi
      have hle5 : r' ≤ (5 : Fin 6) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n7T_strictMono C).monotone hle5
      rw [← n7σ_spec C r', hr'] at hm
      exact hm
  have hσ5 : n7σ C 5 = hi := (n7σ_eq_iff C hi 5).mpr hT5
  have hT4 : n7T C 4 = theta lo := by
    apply n7T_eq_of_bounds C lo 4
    · intro s hs
      rw [← n7σ_spec C s]
      by_contra hnn
      replace hnn := not_lt.mp hnn
      have h1 : n7σ C s = lo ∨ n7σ C s = hi := by
        rcases eq_or_ne (n7σ C s) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n7σ C s) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hnn)
      have h4 : n7σ C 4 = lo ∨ n7σ C 4 = hi := by
        have hge4 : theta lo ≤ n7T C 4 := by
          have hlt := n7T_strictMono C hs
          rw [← n7σ_spec C s] at hlt
          linarith
        rw [← n7σ_spec C 4] at hge4
        rcases eq_or_ne (n7σ C 4) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n7σ C 4) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge4)
      have h5 : n7σ C 5 = lo ∨ n7σ C 5 = hi := by
        have hge5 : theta lo ≤ n7T C 5 := by
          have hlt := n7T_strictMono C
            (hs.trans (by decide : (4 : Fin 6) < 5))
          rw [← n7σ_spec C s] at hlt
          linarith
        rw [← n7σ_spec C 5] at hge5
        rcases eq_or_ne (n7σ C 5) lo with h | h
        · exact Or.inl h
        · rcases eq_or_ne (n7σ C 5) hi with h' | h'
          · exact Or.inr h'
          · exact absurd (hcl _ h h') (not_lt.mpr hge5)
      exact n7_pigeon
        (fun h => (ne_of_lt hs) (n7σ_injective C h))
        (fun h => (ne_of_lt (hs.trans (by decide : (4 : Fin 6) < 5)))
          (n7σ_injective C h))
        (fun h => absurd (n7σ_injective C h) (by decide))
        h1 h4 h5
    · rw [← n7σ_spec C 4]
      rcases eq_or_ne (n7σ C 4) hi with h4hi | h4hi
      · exact absurd (n7σ_injective C (h4hi.trans hσ5.symm)) (by decide)
      · rcases eq_or_ne (n7σ C 4) lo with rfl | h4lo
        · exact le_refl _
        · exfalso
          obtain ⟨r_l, hr_l⟩ := (n7σ_bijective C).surjective lo
          have hrl4 : r_l ≠ 4 := fun h => h4lo (h ▸ hr_l)
          have hrl5 : r_l ≠ 5 := fun h =>
            hθ.ne (by rw [← hr_l, ← hσ5, h])
          have hrl3 : r_l.val ≤ 3 := by
            have hlt6 := r_l.isLt
            have h4v : r_l.val ≠ 4 := fun hv => hrl4 (Fin.ext hv)
            have h5v : r_l.val ≠ 5 := fun hv => hrl5 (Fin.ext hv)
            omega
          have hlt : n7T C r_l < n7T C 4 := by
            apply n7T_strictMono C
            rw [Fin.lt_def]
            omega
          rw [← n7σ_spec C r_l, hr_l] at hlt
          have hcl4 : n7T C 4 < theta lo := by
            have h := hcl _ h4lo h4hi
            rwa [n7σ_spec C 4] at h
          linarith
  exact ⟨(n7σ_eq_iff C lo 4).mpr hT4, hσ5⟩

/-- Between region: the two defect-`2` rows occupy ranks `0`, `5`. -/
theorem n7σ_zero_five_of_between {lo hi : Fin 6}
    (hθ : theta lo < theta hi)
    (hcl : ∀ z : Fin 6, z ≠ lo → z ≠ hi →
      theta lo < theta z ∧ theta z < theta hi) :
    n7σ C 0 = lo ∧ n7σ C 5 = hi := by
  have hge : ∀ z : Fin 6, theta lo ≤ theta z := by
    intro z
    rcases eq_or_ne z lo with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z hi with rfl | h2
      · exact hθ.le
      · exact (hcl z h1 h2).1.le
  have hle : ∀ z : Fin 6, theta z ≤ theta hi := by
    intro z
    rcases eq_or_ne z hi with rfl | h1
    · exact le_refl _
    · rcases eq_or_ne z lo with rfl | h2
      · exact hθ.le
      · exact (hcl z h2 h1).2.le
  have hT0 : n7T C 0 = theta lo := by
    apply n7T_eq_of_bounds C lo 0
    · intro s hs; exact absurd hs (Nat.not_lt_zero s.val)
    · rw [← n7σ_spec C 0]; exact hge _
  have hT5 : n7T C 5 = theta hi := by
    apply n7T_eq_of_bounds C hi 5
    · intro s hs
      rw [← n7σ_spec C s]
      rcases eq_or_ne (n7σ C s) hi with h1 | h1
      · exfalso
        have hmax : theta (n7σ C 5) ≤ theta hi := hle _
        have hlt : n7T C s < n7T C 5 := n7T_strictMono C hs
        rw [← n7σ_spec C s, ← n7σ_spec C 5, h1] at hlt
        linarith
      · rcases eq_or_ne (n7σ C s) lo with h2 | h2
        · rw [h2]; exact hθ
        · exact (hcl _ h2 h1).2
    · obtain ⟨r', hr'⟩ := (n7σ_bijective C).surjective hi
      have hle5 : r' ≤ (5 : Fin 6) := by
        rw [Fin.le_iff_val_le_val]
        exact Nat.le_of_lt_succ r'.isLt
      have hm := (n7T_strictMono C).monotone hle5
      rw [← n7σ_spec C r', hr'] at hm
      exact hm
  exact ⟨(n7σ_eq_iff C lo 0).mpr hT0, (n7σ_eq_iff C hi 5).mpr hT5⟩

/-- **Seven-centre `n = 4` terminal exclusion.**  A seven-centre
configuration at `n = 4` with a saturated anchor, two defect-`2`
rows `a, b` and a defect-`3` row `u` is impossible: the θ-cluster
regions and the defect-`3` rank enumerate exactly the twelve
position classes excluded by the `s7cert_*` certificates. -/
theorem seven_centre_n4_terminal
    (o : Orientation ℝ Plane₂ (Fin 2)) (e : Plane₂) (he : e ≠ 0)
    {lam : ℝ} (hlam : 0 < lam) (hn : Nat.floor (Real.pi / lam) = 4)
    {c : Fin 7 → Plane₂} (hleg : Section4Legality c lam)
    {v a b u : Fin 7}
    (hva : v ≠ a) (hvb : v ≠ b) (hvu : v ≠ u)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hsat : rowDefect 4 lam (directionRow o e c v) = 1)
    (hda : rowDefect 4 lam (directionRow o e c a) = 2)
    (hdb : rowDefect 4 lam (directionRow o e c b) = 2)
    (hdu : rowDefect 4 lam (directionRow o e c u) = 3) :
    False := by
  classical
  obtain ⟨e', he', theta, C, lo, hi, hswap, hθlt, hclass⟩ :=
    defect_two_pair_theta_cluster o e he (by omega : 4 ≤ 6)
      (by omega : 3 ≤ 4) hlam hn hleg hva hvb hab hsat hda hdb
  have href : ∀ x : Fin 7,
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
  -- `u`'s non-anchor index and its θ-rank.
  obtain ⟨uu, huu⟩ := Fin.exists_succAbove_eq (Ne.symm hvu)
  have hdu' : rowDefect 4 lam (directionRow o e' c (v.succAbove uu))
      = 3 := by
    rw [huu, href]; exact hdu
  obtain ⟨r, hr⟩ := (n7σ_bijective C).surjective uu
  -- `u` is not `lo` or `hi` (different defects).
  have hulo : uu ≠ lo := by
    intro hcon
    rw [hcon] at hdu'; rw [hdu'] at hdlo; omega
  have huhi : uu ≠ hi := by
    intro hcon
    rw [hcon] at hdu'; rw [hdu'] at hdhi; omega
  have hr_ne {r' : Fin 6} {w : Fin 6}
      (hσw : n7σ C r' = w) (huw : uu ≠ w) : r ≠ r' :=
    fun h => huw (by rw [← hσw, ← hr, h])
  rcases hclass with hbelow | hbetween | habove
  · -- pair at ranks `4`, `5`; `r ∈ {0,1,2,3}`.
    obtain ⟨hσ4, hσ5⟩ := n7σ_four_five_of_all_below C hθlt hbelow
    have h4 := hr_ne hσ4 hulo
    have h5 := hr_ne hσ5 huhi
    fin_cases r
    · exact seven_centre_n4_AB0 C hσ4 hσ5 hr hdlo hdhi hdu'
    · exact seven_centre_n4_AB1 C hσ4 hσ5 hr hdlo hdhi hdu'
    · exact seven_centre_n4_AB2 C hσ4 hσ5 hr hdlo hdhi hdu'
    · exact seven_centre_n4_AB3 C hσ4 hσ5 hr hdlo hdhi hdu'
    · exact absurd rfl h4
    · exact absurd rfl h5
  · -- pair at ranks `0`, `5`; `r ∈ {1,2,3,4}`.
    obtain ⟨hσ0, hσ5⟩ := n7σ_zero_five_of_between C hθlt hbetween
    have h0 := hr_ne hσ0 hulo
    have h5 := hr_ne hσ5 huhi
    fin_cases r
    · exact absurd rfl h0
    · exact seven_centre_n4_BT1 C hσ0 hσ5 hr hdlo hdhi hdu'
    · exact seven_centre_n4_BT2 C hσ0 hσ5 hr hdlo hdhi hdu'
    · exact seven_centre_n4_BT3 C hσ0 hσ5 hr hdlo hdhi hdu'
    · exact seven_centre_n4_BT4 C hσ0 hσ5 hr hdlo hdhi hdu'
    · exact absurd rfl h5
  · -- pair at ranks `0`, `1`; `r ∈ {2,3,4,5}`.
    obtain ⟨hσ0, hσ1⟩ := n7σ_zero_one_of_all_above C hθlt habove
    have h0 := hr_ne hσ0 hulo
    have h1 := hr_ne hσ1 huhi
    fin_cases r
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact seven_centre_n4_AA2 C hσ0 hσ1 hr hdlo hdhi hdu'
    · exact seven_centre_n4_AA3 C hσ0 hσ1 hr hdlo hdhi hdu'
    · exact seven_centre_n4_AA4 C hσ0 hσ1 hr hdlo hdhi hdu'
    · exact seven_centre_n4_AA5 C hσ0 hσ1 hr hdlo hdhi hdu'

end Jsp404
