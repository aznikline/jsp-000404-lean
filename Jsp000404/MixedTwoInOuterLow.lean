import Jsp000404.MixedTwoInHelpers

/-!
# Mixed two-in: outer-low exclusion

Equivalent file split of `Jsp000404.MixedTwoInCentral` (original bytes in the
lane verification snapshot); declarations, statements and proofs are verbatim.
Split only so each unit elaborates within the 180 s guard.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section TwoInCentral

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

set_option maxHeartbeats 1600000 in
/-- **Mixed two-in: the third direction cannot lie below `u` (outer-low).**

Under the same five-point hypotheses as `mixed_two_in_central` —
`P → H` short-first, `R → H` short-last, `Q` defect-2 — the remaining
direction `z = φ(H,Q)` cannot sit below `u = φ(H,P)` either.

* `Up (Q,H)`: the cap on the path `Q→H→P` gives `u − z ≥ λ`, and the
  excluded all-in chord gives `z − θ_Q ≥ λ`; hence `u ≥ 2λ`, but the
  short-first chord gives `u < θ_P + λ < 2λ`.
* `Up (H,Q)`, `Up (Q,R)`: `Up (H,R)` contradicts `Up (R,H)`.
* `Up (H,Q)`, `Up (R,Q)`, `Up (P,Q)`: `t < z < u` against the corridor
  lower bound `θ_P + λ ≤ t`.
* `Up (H,Q)`, `Up (R,Q)`, `Up (Q,P)` with `t < x < y`: the `Q`-row
  `[z,t,y]` has adjacent big gaps `t − z, y − t`.
* `Up (H,Q)`, `Up (R,Q)`, `Up (Q,P)` with `y < x < t` (the `A1` branch):
  defect `2` on the `Q`-row `[z,y,t]` forces `t − y ≥ (n−1)λ` (the other
  gaps are `< 2λ` or excluded by adjacency); defect `2` on the
  `R`-row `[y,x,w]` forces either `w − x ≥ (n−1)λ` — which pushes
  `w > θ_H + nλ` past its corridor bound — or `y − θ_R ≥ 2λ`, which
  pushes `t ≥ θ_R + (n+1)λ > θ_P + π − λ`. -/
theorem mixed_two_in_outer_low {H P Q R : Fin 4}
    (hHP : H ≠ P) (hHQ : H ≠ Q) (hHR : H ≠ R)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hA : rowDefect n lam (directionRow o e c v) = 1)
    (hH : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove H)))
    (hP : rowDefect n lam (directionRow o e c (v.succAbove P)) = 2)
    (hQ : rowDefect n lam (directionRow o e c (v.succAbove Q)) = 2)
    (hR : rowDefect n lam (directionRow o e c (v.succAbove R)) = 2)
    (hfs : dirRep o e (c ∘ v.succAbove) P H - theta P < lam)
    (hls : theta R + Real.pi - dirRep o e (c ∘ v.succAbove) R H < lam)
    (hθP : theta H < theta P) (hθR : theta R < theta H)
    (hu : theta H + lam ≤ dirRep o e (c ∘ v.succAbove) H P)
    (hu' : dirRep o e (c ∘ v.succAbove) H P < theta P + lam)
    (hw : Real.pi - lam < dirRep o e (c ∘ v.succAbove) H R)
    (hzu : dirRep o e (c ∘ v.succAbove) H Q <
      dirRep o e (c ∘ v.succAbove) H P) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H P with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H R with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H Q with hz_def
  set x := dirRep o e (c ∘ v.succAbove) R P with hx_def
  set y := dirRep o e (c ∘ v.succAbove) R Q with hy_def
  set t := dirRep o e (c ∘ v.succAbove) P Q with ht_def
  have hupHP : Up o e c v H P := up_of_short_first C hHP.symm hfs
  have hupRH : Up o e c v R H := up_of_short_last C hHR.symm hls
  have hβP : theta P ≤ Real.pi - n * lam := (C.htheta P).1.2
  have hθQ0 : 0 ≤ theta Q := (C.htheta Q).1.1
  have hθR0 : 0 ≤ theta R := (C.htheta R).1.1
  have hβ : Real.pi - n * lam < lam := C.hβ
  have hπ : Real.pi < (n + 1) * lam := C.hπ
  have hn3 := C.hn3
  have huw : u < w := by
    have hn3r := C.hn3'
    nlinarith [hu', hw, hβP, C.hlam]
  -- `Up (R,P)` with `u < x < w`.
  obtain ⟨hupRP, hxbet⟩ := up_trans C hHR.symm hHP hPR.symm hupRH hupHP
  rw [phi_comm C hHR.symm] at hxbet
  simp only [← hx_def, ← hu_def, ← hw_def] at hxbet
  have huxw : u < x ∧ x < w := by
    rcases hxbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact ⟨h1, h2⟩
  -- `Q` cannot also send a short chord to `H`.
  have hnotSW : ¬ ShortWitness (lam := lam) (c := c) o e v theta Q H := by
    intro hswQ
    have hlow : ∀ j : Fin 4, j ≠ H →
        rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 := by
      intro j hj
      rcases fin4_cover C hHP hHQ hHR hPQ hPR hQR j with rfl | rfl | rfl | rfl
      · exact absurd rfl hj
      · exact hP
      · exact hQ
      · exact hR
    have hall : ∀ j : Fin 4, j ≠ H →
        ShortWitness (lam := lam) (c := c) o e v theta j H := by
      intro j hj
      rcases fin4_cover C hHP hHQ hHR hPQ hPR hQR j with rfl | rfl | rfl | rfl
      · exact absurd rfl hj
      · exact ⟨hHP.symm, Or.inl hfs⟩
      · exact hswQ
      · exact ⟨hHR.symm, Or.inr hls⟩
    exact five_point_high_receiver_not_full_in C H hH hlow hall
  obtain ⟨hz1, hz2⟩ := not_short_witness_bounds C hHQ.symm hnotSW
  rw [phi_comm C hHQ.symm] at hz1 hz2
  simp only [← hz_def] at hz1 hz2
  rcases up_or_up C hHQ with hupHQ | hupQH
  swap
  · -- `Up (Q,H)`: cap `Q→H→P` plus non-shortness of `Q→H` already kill it.
    have hcap := up_cap C hHQ.symm hHP hPQ.symm hupQH hupHP
    rw [phi_comm C hHQ.symm] at hcap
    simp only [← hu_def, ← hz_def] at hcap
    rw [abs_of_pos (by linarith : (0 : ℝ) < u - z)] at hcap
    -- `u ≥ z + λ ≥ θ_Q + 2λ ≥ 2λ` but `u < θ_P + λ < 2λ`.
    linarith
  · rcases up_or_up C hQR with hupQR | hupRQ
    · -- `Up (H,Q) ∘ Up (Q,R)` gives `Up (H,R)`, against `Up (R,H)`.
      obtain ⟨hupHR, -⟩ := up_trans C hHQ hQR hHR hupHQ hupQR
      exact up_not_both C hHR.symm hupRH hupHR
    · -- `Up (R,Q)`: `y` sits strictly between `z` and `w`.
      obtain ⟨hupRQ', hbet2⟩ := up_trans C hHR.symm hHQ hQR.symm hupRH hupHQ
      rw [phi_comm C hHR.symm] at hbet2
      simp only [← hy_def, ← hz_def, ← hw_def] at hbet2
      have hzyw : z < y ∧ y < w := by
        rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · exact ⟨h1, h2⟩
      rcases up_or_up C hPQ with hupPQ | hupQP
      · -- `Up (P,Q)`: `t < z < u` against the corridor `θ_P + λ ≤ t`.
        obtain ⟨-, hbet1⟩ := up_trans C hHP hPQ hHQ hupHP hupPQ
        simp only [← hz_def, ← hu_def, ← ht_def] at hbet1
        have htz : t < z := by
          rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · exact h1
        have hcorr : theta P + lam ≤ t := by
          have h := (up_corridor C hPQ hupPQ).1
          simp only [← ht_def] at h
          exact h
        linarith
      · -- `Up (Q,P)`: `z < u < t` and `x` lies between `y` and `t`.
        obtain ⟨-, hbet1⟩ := up_trans C hHQ hPQ.symm hHP hupHQ hupQP
        rw [phi_comm C hPQ.symm] at hbet1
        simp only [← hz_def, ← hu_def, ← ht_def] at hbet1
        have hzut : z < u ∧ u < t := by
          rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1, h2⟩
          · linarith
        obtain ⟨hupRP', hbet3⟩ := up_trans C hQR.symm hPQ.symm hPR.symm hupRQ hupQP
        rw [phi_comm C hPQ.symm] at hbet3
        simp only [← hx_def, ← hy_def, ← ht_def] at hbet3
        -- Caps from the actual `Up` paths.
        have hcap_ty : lam ≤ |t - y| := by
          have h := up_cap C hQR.symm hPQ.symm hPR.symm hupRQ hupQP
          rw [phi_comm C hPQ.symm] at h
          simp only [← ht_def, ← hy_def] at h
          exact h
        have hcap_tz : lam ≤ t - z := by
          have h := up_cap C hHQ hPQ.symm hHP hupHQ hupQP
          rw [phi_comm C hPQ.symm] at h
          simp only [← ht_def, ← hz_def] at h
          rw [abs_of_pos (by linarith : (0 : ℝ) < t - z)] at h
          exact h
        have hcy : theta R + lam ≤ y := by
          have h := (up_corridor C hQR.symm hupRQ).1
          simp only [← hy_def] at h
          exact h
        have hct : t ≤ Real.pi - lam + theta P := by
          have h := (up_corridor C hPQ.symm hupQP).2
          rw [phi_comm C hPQ.symm] at h
          simp only [← ht_def] at h
          exact h
        have hcw : w ≤ Real.pi - lam + theta H := by
          have h := (up_corridor C hHR.symm hupRH).2
          rw [phi_comm C hHR.symm] at h
          simp only [← hw_def] at h
          exact h
        rcases hbet3 with ⟨hyx, hxt⟩ | ⟨htx, hxy⟩
        swap
        · -- A2 (`t < x < y`): row `Q = [z,t,y]` has adjacent big gaps `{1,2}`.
          have hcap_yt : lam ≤ y - t := by
            rw [abs_of_neg (by linarith : (0 : ℝ) > t - y)] at hcap_ty
            linarith
          have h1q : dirRep o e (c ∘ v.succAbove) Q H <
              dirRep o e (c ∘ v.succAbove) Q P := by
            rw [phi_comm C hHQ.symm, phi_comm C hPQ.symm]
            simp only [← hz_def, ← ht_def]
            linarith
          have h2q : dirRep o e (c ∘ v.succAbove) Q P <
              dirRep o e (c ∘ v.succAbove) Q R := by
            rw [phi_comm C hPQ.symm, phi_comm C hQR]
            simp only [← hy_def, ← ht_def]
            linarith
          have hnab := five_point_no_adjacent_big C hHQ.symm hPQ.symm hQR
            hPQ hHP.symm hQR.symm hPR.symm hPQ hPR h1q h2q hA hQ hP hR hP
          rw [phi_comm C hHQ.symm, phi_comm C hPQ.symm, phi_comm C hQR] at hnab
          simp only [← hz_def, ← hy_def, ← ht_def] at hnab
          exact hnab.2.1 ⟨hcap_tz, hcap_yt⟩
        · -- A1 (`y < x < t`): the defect-2 score forcing.
          have hcap_ty' : lam ≤ t - y := by
            rw [abs_of_pos (by linarith : (0 : ℝ) < t - y)] at hcap_ty
            exact hcap_ty
          -- Row `Q = [z,y,t]`: `g₁ < λ`, `g₃ < λ` by adjacency, `g₀ < 2λ`
          -- since `z < θ_P + λ < 2λ`.  Hence the whole score sits on `t − y`.
          have h1q : dirRep o e (c ∘ v.succAbove) Q H <
              dirRep o e (c ∘ v.succAbove) Q R := by
            rw [phi_comm C hHQ.symm, phi_comm C hQR]
            simp only [← hz_def, ← hy_def]
            exact hzyw.1
          have h2q : dirRep o e (c ∘ v.succAbove) Q R <
              dirRep o e (c ∘ v.succAbove) Q P := by
            rw [phi_comm C hQR, phi_comm C hPQ.symm]
            simp only [← hy_def, ← ht_def]
            linarith
          have hnabQ := five_point_no_adjacent_big C hHQ.symm hQR hPQ.symm
            hPQ hHP.symm hPQ hPR hQR.symm hPR.symm h1q h2q hA hQ hP hP hR
          rw [phi_comm C hHQ.symm, phi_comm C hQR, phi_comm C hPQ.symm] at hnabQ
          simp only [← hz_def, ← hy_def, ← ht_def] at hnabQ
          have hg1q : y - z < lam := by
            by_contra hc; push_neg at hc; exact hnabQ.1 ⟨hz1, hc⟩
          have hg3q : theta Q + Real.pi - t < lam := by
            by_contra hc; push_neg at hc; exact hnabQ.2.2 ⟨hcap_ty', hc⟩
          have hrowQ := row4_eq C hHQ.symm hQR hPQ.symm h1q h2q
          rw [phi_comm C hHQ.symm, phi_comm C hQR, phi_comm C hPQ.symm] at hrowQ
          simp only [← hz_def, ← hy_def, ← ht_def] at hrowQ
          have hsdQ := score_add_defect C (by decide : (2 : ℕ) ≤ 4) Q
          rw [hrowQ, hQ] at hsdQ
          have hg0q : gapScore lam (z - theta Q) = 0 :=
            gapScore_zero_of_lt_two C.hlam (by linarith)
          have hg1qs : gapScore lam (y - z) = 0 := gapScore_zero_of_lt' C hg1q
          have hg3qs : gapScore lam (theta Q + Real.pi - t) = 0 :=
            gapScore_zero_of_lt' C hg3q
          have hscQ : gapScore lam (t - y) = n - 2 := by
            rw [linScore4 C (theta Q) z y t] at hsdQ
            omega
          have hty : (↑(n - 1) : ℝ) * lam ≤ t - y :=
            big_gap_lower C (by linarith) hscQ
          -- Row `R = [y,x,w]`: `g₁ < λ` by adjacency, `g₃ < λ` short-last.
          have h1r : dirRep o e (c ∘ v.succAbove) R Q <
              dirRep o e (c ∘ v.succAbove) R P := by
            simp only [← hx_def, ← hy_def]
            exact hyx
          have h2r : dirRep o e (c ∘ v.succAbove) R P <
              dirRep o e (c ∘ v.succAbove) R H := by
            rw [phi_comm C hHR.symm]
            simp only [← hx_def, ← hw_def]
            exact huxw.2
          have hnabR := five_point_no_adjacent_big C hQR.symm hPR.symm hHR.symm
            hPR hPQ hQR hPQ.symm hPR hHP.symm h1r h2r hA hR hP hQ hP
          rw [phi_comm C hHR.symm] at hnabR
          simp only [← hx_def, ← hy_def, ← hw_def] at hnabR
          have hg1r : x - y < lam := by
            by_contra hc; push_neg at hc
            exact hnabR.1 ⟨by linarith, hc⟩
          have hls' : theta R + Real.pi - w < lam := by
            have h := hls
            rw [phi_comm C hHR.symm] at h
            simp only [← hw_def] at h
            exact h
          have hrowR := row4_eq C hQR.symm hPR.symm hHR.symm h1r h2r
          rw [phi_comm C hHR.symm] at hrowR
          simp only [← hx_def, ← hy_def, ← hw_def] at hrowR
          have hsdR := score_add_defect C (by decide : (2 : ℕ) ≤ 4) R
          rw [hrowR, hR] at hsdR
          rw [linScore4 C (theta R) y x w] at hsdR
          have hg1rs : gapScore lam (x - y) = 0 := gapScore_zero_of_lt' C hg1r
          have hg3rs : gapScore lam (theta R + Real.pi - w) = 0 :=
            gapScore_zero_of_lt' C hls'
          have hscR : gapScore lam (y - theta R) + gapScore lam (w - x) =
              n - 2 := by omega
          have e0 : gapScore lam (y - theta R) = ⌊(y - theta R) / lam⌋₊ - 1 := rfl
          have e2 : gapScore lam (w - x) = ⌊(w - x) / lam⌋₊ - 1 := rfl
          rw [e0, e2] at hscR
          rcases lt_or_ge ⌊(w - x) / lam⌋₊ (n - 1) with hq2 | hq2
          · -- `⌊(w−x)/λ⌋ ≤ n−2`, so `⌊(y−θ_R)/λ⌋ ≥ 2` and `t` overflows.
            have hq0 : 2 ≤ ⌊(y - theta R) / lam⌋₊ := by omega
            have hyθR : (2 : ℝ) * lam ≤ y - theta R := by
              have h := floor_mul_le_gap C.hlam (by linarith : (0 : ℝ) ≤ y - theta R)
              have hq' : (2 : ℝ) ≤ (⌊(y - theta R) / lam⌋₊ : ℝ) := by
                exact_mod_cast hq0
              nlinarith
            -- `t ≥ y + (n−1)λ ≥ θ_R + (n+1)λ` but `t ≤ θ_P + π − λ`,
            -- hence `θ_P − θ_R ≥ (n+2)λ − π > π − nλ ≥ θ_P − θ_R`.
            have hn1 : ((n : ℝ) - 1) * lam ≤ t - y := by
              have : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
                have hn1' : (1 : ℕ) ≤ n := by omega
                rw [Nat.cast_sub hn1']; push_cast; ring
              rwa [this] at hty
            nlinarith [hct]
          · -- `⌊(w−x)/λ⌋ ≥ n−1`: `w > θ_H + nλ`, beyond its corridor bound.
            have hwx : ((n : ℝ) - 1) * lam ≤ w - x := by
              have h := floor_mul_le_gap C.hlam (by linarith : (0 : ℝ) ≤ w - x)
              have hq' : ((n : ℝ) - 1) ≤ (⌊(w - x) / lam⌋₊ : ℝ) := by
                have hn1' : (1 : ℕ) ≤ n := by omega
                have := Nat.cast_le (α := ℝ).mpr hq2
                rw [Nat.cast_sub hn1'] at this
                push_cast at this
                linarith
              nlinarith
            -- `w ≥ x + (n−1)λ > u + (n−1)λ ≥ θ_H + nλ`, but `w ≤ θ_H + π − λ`
            -- and `π < (n+1)λ`.
            nlinarith [hcw, hπ]

end TwoInCentral

end Jsp404
