import Jsp000404.DeletionRigidityRows

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section TwoIn

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- **Two-in receiver, F side.**  If `h` receives short chords from
`a, b` whose rows sit above (`theta h < theta ·`), both chords land in
the F window.  Either the third direction `z` leaves the defect at `2`,
or `z` lies strictly above both received directions and the defect is
`2 + μ` with `μ ≤ 2` the merge gain of the split last gap. -/
theorem two_in_F_row {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta h < theta b)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) = 2 ∨
      (dirRep o e (c ∘ v.succAbove) h b < dirRep o e (c ∘ v.succAbove) h t ∧
        rowDefect n lam (directionRow o e c (v.succAbove h)) =
          2 + mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
            (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) ∧
        mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
            (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) ≤ 2) := by
  classical
  set xa := dirRep o e (c ∘ v.succAbove) h a with hxa
  set xb := dirRep o e (c ∘ v.succAbove) h b with hxb
  set z := dirRep o e (c ∘ v.succAbove) h t with hz
  have hn3 := C.hn3
  have hθ0 := (C.htheta h).1.1
  have P : StarParams n lam (theta h) :=
    ⟨C.hn3, C.hlam, (C.htheta h).1.1, (C.htheta h).1.2, C.hβ⟩
  have hFa : StarF n lam (theta h) xa := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwa with
      hF | hL
    · exact hF.1
    · exact absurd hL.2 (not_lt.mpr haθ.le)
  have hFb : StarF n lam (theta h) xb := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwb with
      hF | hL
    · exact hF.1
    · exact absurd hL.2 (not_lt.mpr hbθ.le)
  have hsort2 : [xa, xb].Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simpa using hord.le, List.pairwise_singleton _ _⟩
  have hwin2 : ∀ w ∈ [xa, xb],
      StarF n lam (theta h) w ∨ StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hFa
    · exact Or.inl hFb
  have hside2 : ∀ w ∈ [xa, xb], StarF n lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hFa
    · exact hFb
  have hk2 : linearGapScore lam (theta h) (theta h + Real.pi) [xa, xb] = n - 2 :=
    star_linear_score_one_sided P hsort2 (by simp) hwin2 (Or.inl hside2)
  have hsd := score_add_defect C (by decide) h
  have hθz : theta h < z := by
    have h1 := phi_ge_lam C htt
    have h2 := (C.htheta h).1.2
    have h3 := C.hβ
    linarith
  have hzπ : z < Real.pi := (phi_mem C h t).2
  have hgap0 : xa - theta h < 2 * lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.1
    linarith [hFa.2]
  have hgap1 : xb - xa < 2 * lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.1
    linarith [hFa.1, hFb.2]
  rcases lt_trichotomy z xa with hz1 | hz1 | hz1
  · left
    have hrow := row4_eq C htt hta htb hz1 hord
    rw [hrow] at hsd
    simp only [← hxa, ← hxb, ← hz] at hsd
    have hμ : mergeGain lam (z - theta h) (xa - z) = 0 :=
      mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hθz.le) (sub_nonneg.mpr hz1.le) (by linarith)
    have hsp := linScore_split_low (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hθz.le hz1.le
    omega
  · exact absurd hz1 hzta
  · rcases lt_trichotomy z xb with hz2 | hz2 | hz2
    · left
      have hrow := row4_eq C hta htt htb hz1 hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xa) (xb - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz1.le) (sub_nonneg.mpr hz2.le) (by linarith)
      have hsp := linScore_split_mid (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hz1.le hz2.le
      omega
    · exact absurd hz2 hztb
    · right
      have hrow := row4_eq C hta htb htt hord hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ2 := mergeGain_le_two C.hlam (sub_nonneg.mpr hz2.le)
        (by linarith : (0 : ℝ) ≤ theta h + Real.pi - z)
      have hsp := linScore_split_high (θ := theta h) (x := xa) (y := xb) (R := theta h + Real.pi) C.hlam hz2.le
        (by linarith : z ≤ theta h + Real.pi)
      refine ⟨hz2, by omega, ?_⟩
      omega

/-- F-side consumer: defect `≥ 3` forces `z` above both received
directions, positive merge gain, and defect `≤ 4`. -/
theorem two_in_F_above {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta h < theta b)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h))) :
    dirRep o e (c ∘ v.succAbove) h b < dirRep o e (c ∘ v.succAbove) h t ∧
      1 ≤ mergeGain lam
        (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
        (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) ∧
      rowDefect n lam (directionRow o e c (v.succAbove h)) =
        2 + mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h b)
          (theta h + Real.pi - dirRep o e (c ∘ v.succAbove) h t) := by
  rcases two_in_F_row C hta htb htt hwa hwb haθ hbθ hord hzta hztb with
    h | ⟨h1, h2, _⟩
  · omega
  · exact ⟨h1, by omega, h2⟩

/-- **Two-in receiver, L side** (mirror of `two_in_F_row`). -/
theorem two_in_L_row {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta a < theta h) (hbθ : theta b < theta h)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) = 2 ∨
      (dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h a ∧
        rowDefect n lam (directionRow o e c (v.succAbove h)) =
          2 + mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - theta h)
            (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t) ∧
        mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - theta h)
            (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t)
          ≤ 2) := by
  classical
  set xa := dirRep o e (c ∘ v.succAbove) h a with hxa
  set xb := dirRep o e (c ∘ v.succAbove) h b with hxb
  set z := dirRep o e (c ∘ v.succAbove) h t with hz
  have hn3 := C.hn3
  have hθ0 := (C.htheta h).1.1
  have P : StarParams n lam (theta h) :=
    ⟨C.hn3, C.hlam, (C.htheta h).1.1, (C.htheta h).1.2, C.hβ⟩
  have hLa : StarL lam (theta h) xa := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwa with
      hF | hL
    · exact absurd hF.2 (not_lt.mpr haθ.le)
    · exact hL.1
  have hLb : StarL lam (theta h) xb := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwb with
      hF | hL
    · exact absurd hF.2 (not_lt.mpr hbθ.le)
    · exact hL.1
  have hsort2 : [xa, xb].Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simpa using hord.le, List.pairwise_singleton _ _⟩
  have hwin2 : ∀ w ∈ [xa, xb],
      StarF n lam (theta h) w ∨ StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inr hLa
    · exact Or.inr hLb
  have hside2 : ∀ w ∈ [xa, xb], StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hLa
    · exact hLb
  have hk2 : linearGapScore lam (theta h) (theta h + Real.pi) [xa, xb] = n - 2 :=
    star_linear_score_one_sided P hsort2 (by simp) hwin2 (Or.inr hside2)
  have hsd := score_add_defect C (by decide) h
  have hθz : theta h < z := by
    have h1 := phi_ge_lam C htt
    have h2 := (C.htheta h).1.2
    have h3 := C.hβ
    linarith
  have hzπ : z < Real.pi := (phi_mem C h t).2
  have hθlt : theta h < lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.2
    linarith
  have hgap1 : xb - xa < 2 * lam := by
    linarith [hLa.1, hLb.2]
  have hgap2 : theta h + Real.pi - xb < 2 * lam := by
    linarith [hLb.1]
  rcases lt_trichotomy z xa with hz1 | hz1 | hz1
  · right
    have hrow := row4_eq C htt hta htb hz1 hord
    rw [hrow] at hsd
    simp only [← hxa, ← hxb, ← hz] at hsd
    have hμ2 := mergeGain_le_two C.hlam (sub_nonneg.mpr hθz.le)
      (sub_nonneg.mpr hz1.le)
    have hsp := linScore_split_low (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hθz.le hz1.le
    refine ⟨hz1, by omega, ?_⟩
    omega
  · exact absurd hz1 hzta
  · rcases lt_trichotomy z xb with hz2 | hz2 | hz2
    · left
      have hrow := row4_eq C hta htt htb hz1 hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xa) (xb - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz1.le) (sub_nonneg.mpr hz2.le) (by linarith)
      have hsp := linScore_split_mid (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hz1.le hz2.le
      omega
    · exact absurd hz2 hztb
    · left
      have hrow := row4_eq C hta htb htt hord hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xb) (theta h + Real.pi - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz2.le)
          (by linarith : (0 : ℝ) ≤ theta h + Real.pi - z)
          (by linarith)
      have hsp := linScore_split_high (θ := theta h) (x := xa) (y := xb) (R := theta h + Real.pi) C.hlam hz2.le
        (by linarith : z ≤ theta h + Real.pi)
      omega

/-- L-side consumer: defect `≥ 3` forces `z` below both received
directions, positive merge gain, and defect `≤ 4`. -/
theorem two_in_L_below {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta a < theta h) (hbθ : theta b < theta h)
    (hord : dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h b)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h))) :
    dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h a ∧
      1 ≤ mergeGain lam
        (dirRep o e (c ∘ v.succAbove) h t - theta h)
        (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t) ∧
      rowDefect n lam (directionRow o e c (v.succAbove h)) =
        2 + mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - theta h)
          (dirRep o e (c ∘ v.succAbove) h a - dirRep o e (c ∘ v.succAbove) h t) := by
  rcases two_in_L_row C hta htb htt hwa hwb haθ hbθ hord hzta hztb with
    h | ⟨h1, h2, _⟩
  · omega
  · exact ⟨h1, by omega, h2⟩

/-- **Two-in receiver, mixed.**  One F chord `a` and one L chord `b`.
Either the defect is exactly `3`, or `z` lies strictly between the two
received directions and the defect is `3 + μ` with `μ ≤ 2` the merge
gain of the split middle gap. -/
theorem two_in_mixed_row {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b) (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    rowDefect n lam (directionRow o e c (v.succAbove h)) = 3 ∨
      (dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h t ∧
        dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h b ∧
        rowDefect n lam (directionRow o e c (v.succAbove h)) =
          3 + mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
            (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) ∧
        mergeGain lam
            (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
            (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t)
          ≤ 2) := by
  classical
  set xa := dirRep o e (c ∘ v.succAbove) h a with hxa
  set xb := dirRep o e (c ∘ v.succAbove) h b with hxb
  set z := dirRep o e (c ∘ v.succAbove) h t with hz
  have hn3 := C.hn3
  have hθ0 := (C.htheta h).1.1
  have P : StarParams n lam (theta h) :=
    ⟨C.hn3, C.hlam, (C.htheta h).1.1, (C.htheta h).1.2, C.hβ⟩
  have hFa : StarF n lam (theta h) xa := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwa with
      hF | hL
    · exact hF.1
    · exact absurd hL.2 (not_lt.mpr haθ.le)
  have hLb : StarL lam (theta h) xb := by
    rcases star_chord_window C.he C.hn3 C.hlam C.hn C.hleg C.htheta hwb with
      hF | hL
    · exact absurd hF.2 (not_lt.mpr hbθ.le)
    · exact hL.1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hord : xa < xb := by
    have h1 : 2 * lam ≤ n * lam := by nlinarith [C.hlam]
    linarith [hFa.2, hLb.1]
  have hsort2 : [xa, xb].Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simpa using hord.le, List.pairwise_singleton _ _⟩
  have hwin2 : ∀ w ∈ [xa, xb],
      StarF n lam (theta h) w ∨ StarL lam (theta h) w := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hFa
    · exact Or.inr hLb
  have hk2 : linearGapScore lam (theta h) (theta h + Real.pi) [xa, xb] = n - 3 :=
    star_linear_score_mixed P hsort2 hwin2
      ⟨xa, by simp, hFa⟩ ⟨xb, by simp, hLb⟩
  have hsd := score_add_defect C (by decide) h
  have hθz : theta h < z := by
    have h1 := phi_ge_lam C htt
    have h2 := (C.htheta h).1.2
    have h3 := C.hβ
    linarith
  have hzπ : z < Real.pi := (phi_mem C h t).2
  have hθlt : theta h < lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.2
    linarith
  have hgap0 : xa - theta h < 2 * lam := by
    have h1 := C.hβ
    have h2 := (C.htheta h).1.1
    linarith [hFa.2]
  have hgap2 : theta h + Real.pi - xb < 2 * lam := by
    linarith [hLb.1]
  rcases lt_trichotomy z xa with hz1 | hz1 | hz1
  · left
    have hrow := row4_eq C htt hta htb hz1 hord
    rw [hrow] at hsd
    simp only [← hxa, ← hxb, ← hz] at hsd
    have hμ : mergeGain lam (z - theta h) (xa - z) = 0 :=
      mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hθz.le) (sub_nonneg.mpr hz1.le) (by linarith)
    have hsp := linScore_split_low (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hθz.le hz1.le
    omega
  · exact absurd hz1 hzta
  · rcases lt_trichotomy z xb with hz2 | hz2 | hz2
    · right
      have hrow := row4_eq C hta htt htb hz1 hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ2 := mergeGain_le_two C.hlam (sub_nonneg.mpr hz1.le)
        (sub_nonneg.mpr hz2.le)
      have hsp := linScore_split_mid (θ := theta h) (y := xb) (R := theta h + Real.pi) C.hlam hz1.le hz2.le
      exact ⟨hz1, hz2, by omega, hμ2⟩
    · exact absurd hz2 hztb
    · left
      have hrow := row4_eq C hta htb htt hord hz2
      rw [hrow] at hsd
      simp only [← hxa, ← hxb, ← hz] at hsd
      have hμ : mergeGain lam (z - xb) (theta h + Real.pi - z) = 0 :=
        mergeGain_eq_zero_of_lt C.hlam (sub_nonneg.mpr hz2.le)
          (by linarith : (0 : ℝ) ≤ theta h + Real.pi - z)
          (by linarith)
      have hsp := linScore_split_high (θ := theta h) (x := xa) (y := xb) (R := theta h + Real.pi) C.hlam hz2.le
        (by linarith : z ≤ theta h + Real.pi)
      omega

/-- A mixed two-in receiver always has defect `≥ 3`. -/
theorem two_in_mixed_ge_three {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b)
    (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b) :
    3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h)) := by
  rcases two_in_mixed_row C hta htb htt hwa hwb haθ hbθ hzta hztb with
    h | ⟨_, _, h2, _⟩
  · omega
  · omega

/-- Mixed consumer: defect `> 3` forces `z` strictly between the received
directions and defect `= 3 + μ`, `μ ∈ {1, 2}`. -/
theorem two_in_mixed_between {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b)
    (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : 3 < rowDefect n lam (directionRow o e c (v.succAbove h))) :
    dirRep o e (c ∘ v.succAbove) h a < dirRep o e (c ∘ v.succAbove) h t ∧
      dirRep o e (c ∘ v.succAbove) h t < dirRep o e (c ∘ v.succAbove) h b ∧
      rowDefect n lam (directionRow o e c (v.succAbove h)) =
        3 + mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
          (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) ∧
      1 ≤ mergeGain lam
          (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
          (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) := by
  rcases two_in_mixed_row C hta htb htt hwa hwb haθ hbθ hzta hztb with
    h | ⟨h1, h2, h3, _⟩
  · omega
  · exact ⟨h1, h2, h3, by omega⟩

/-- The extremal mixed case `c_h = 5`: the insertion gain is `2`, so both
split pieces are `≥ λ` with a floor carry, and `n ≥ 5`. -/
theorem two_in_mixed_five {h a b t : Fin 4} (hta : h ≠ a) (htb : h ≠ b)
    (htt : h ≠ t)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta a h)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta b h)
    (haθ : theta h < theta a) (hbθ : theta b < theta h)
    (hzta : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h a)
    (hztb : dirRep o e (c ∘ v.succAbove) h t ≠ dirRep o e (c ∘ v.succAbove) h b)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove h)) = 5) :
    lam ≤ dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a ∧
      lam ≤ dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t ∧
      ⌊(dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h a) /
          lam⌋₊ =
        ⌊(dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a) /
            lam⌋₊ +
          ⌊(dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) /
            lam⌋₊ + 1 ∧
      5 ≤ n := by
  obtain ⟨h1, h2, h3, hμ1⟩ := two_in_mixed_between C hta htb htt hwa hwb
    haθ hbθ hzta hztb (by omega)
  have hμ : mergeGain lam
      (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a)
      (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) = 2 := by
    omega
  obtain ⟨hx, hy, hcar⟩ := mergeGain_eq_two C.hlam
    (sub_nonneg.mpr h1.le) (sub_nonneg.mpr h2.le) hμ
  rw [show (dirRep o e (c ∘ v.succAbove) h t - dirRep o e (c ∘ v.succAbove) h a) +
      (dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h t) =
      dirRep o e (c ∘ v.succAbove) h b - dirRep o e (c ∘ v.succAbove) h a
      by ring] at hcar
  have hsd := score_add_defect C (by decide) h
  exact ⟨hx, hy, hcar, by omega⟩

end TwoIn

end Jsp404
