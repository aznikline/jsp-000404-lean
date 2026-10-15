import Jsp000404.MixedTwoInHelpers

/-!
# Mixed two-in: outer-high exclusion

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
/-- **Mixed two-in: the third direction cannot lie above `w` (outer-high).**

Under the same five-point hypotheses — `P → H` short-first,
`R → H` short-last, `Q` defect-2 — the third direction `z = φ(H,Q)`
cannot sit above `w = φ(H,R)` either.

* `Up (H,Q)`: the cap on the path `R→H→Q` gives `z − w ≥ λ`, hence
  `z ≥ w + λ > π`, contradicting `z < π`.
* `Up (Q,H)`, `Up (Q,R)`: `z` sits between `y` and `w`, so `w < z < y`.
  The `R`-row `[x,w,y]` then has big first gap `x − θ_R ≥ λ` (corridor
  `R→P`), forced `w − x < λ` and `θ_R + π − y < λ`, hence its defect-2
  score reads `q₀ + q₂ = n` and `y − θ_R ≥ nλ`; but the corridor
  `Q→R` gives `y − θ_R ≤ π − λ < nλ`.
* `Up (Q,H)`, `Up (R,Q)`, `Up (P,Q)`: `t < u < z` and `y < w < z`; the
  caps `|z − t|, |z − y|, |t − y| ≥ λ` give the `Q`-row adjacent big
  gaps at positions `{1,2}` in either ordering of `t,y`.
* `Up (Q,H)`, `Up (R,Q)`, `Up (Q,P)` with `t < y`: the `Q`-row
  `[t,y,z]` has adjacent big gaps `t − θ_Q` (corridor) and `y − t`
  (cap) at `{0,1}`.
* `Up (Q,H)`, `Up (R,Q)`, `Up (Q,P)` with `y < t` (the mirror-`A1`
  branch): `x` lands strictly between `y` and `t`.  In the `Q`-row —
  either `[y,t,z]` or `[y,z,t]` — the first gap is `< λ` by adjacency
  and the last is `< 2λ` automatically (`z,t > w > π − λ`), so the
  defect-2 score concentrates: `t − y > (n−1)λ`.  In the `P`-row
  `[u,x,t]`, the corridor forces `θ_P + π − t ≥ λ`, adjacency forces
  `t − x < λ`, so `⌊(θ_P+π−t)/λ⌋ = 1` gives `x − u ≥ (n−1)λ`, pushing
  `x > θ_H + nλ` past `x < w ≤ θ_H + π − λ`; and `⌊·⌋ ≥ 2` gives
  `t ≤ θ_P + π − 2λ`, pushing `y < θ_P + β − λ` against `y ≥ θ_R + λ`. -/
theorem mixed_two_in_outer_high {H P Q R : Fin 4}
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
    (hwz : dirRep o e (c ∘ v.succAbove) H R <
      dirRep o e (c ∘ v.succAbove) H Q) : False := by
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
  have hzw : w < z := hwz
  obtain ⟨hupRP, hxbet⟩ := up_trans C hHR.symm hHP hPR.symm hupRH hupHP
  rw [phi_comm C hHR.symm] at hxbet
  simp only [← hx_def, ← hu_def, ← hw_def] at hxbet
  have huxw : u < x ∧ x < w := by
    rcases hxbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact ⟨h1, h2⟩
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
  · -- `Up (H,Q)`: cap `R→H→Q` gives `z − w ≥ λ`, so `z > π`.
    have hcap := up_cap C hHR.symm hHQ hQR.symm hupRH hupHQ
    rw [phi_comm C hHR.symm] at hcap
    simp only [← hw_def, ← hz_def] at hcap
    rw [abs_of_pos (by linarith : (0 : ℝ) < z - w)] at hcap
    have hzlt : z < Real.pi := (phi_mem C H Q).2
    linarith
  · -- `Up (Q,H)`:
    rcases up_or_up C hQR with hupQR | hupRQ
    · -- `Up (Q,R)`: `z` sits between `y` and `w`, hence `w < z < y`; the
      -- `R`-row `[x,w,y]` gives `y − θ_R ≥ nλ`, against `y ≤ θ_R + π − λ`.
      obtain ⟨-, hbet⟩ := up_trans C hQR hHR.symm hHQ.symm hupQR hupRH
      rw [phi_comm C hQR, phi_comm C hHR.symm, phi_comm C hHQ.symm] at hbet
      simp only [← hy_def, ← hz_def, ← hw_def] at hbet
      have hzy : z < y := by
        rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · exact h2
      have h1r : dirRep o e (c ∘ v.succAbove) R P <
          dirRep o e (c ∘ v.succAbove) R H := by
        rw [phi_comm C hHR.symm]
        simp only [← hx_def, ← hw_def]
        exact huxw.2
      have h2r : dirRep o e (c ∘ v.succAbove) R H <
          dirRep o e (c ∘ v.succAbove) R Q := by
        rw [phi_comm C hHR.symm]
        simp only [← hw_def, ← hy_def]
        linarith
      have hnabR := five_point_no_adjacent_big C hPR.symm hHR.symm hQR.symm
        hQR hPQ.symm hQR hHQ.symm hPR hPQ h1r h2r hA hR hQ hQ hP
      rw [phi_comm C hHR.symm] at hnabR
      simp only [← hx_def, ← hy_def, ← hw_def] at hnabR
      have hcx : theta R + lam ≤ x := by
        have h := (up_corridor C hPR.symm hupRP).1
        simp only [← hx_def] at h
        exact h
      have hcap_yw : lam ≤ y - w := by
        have h := up_cap C hQR hHR.symm hHQ.symm hupQR hupRH
        rw [phi_comm C hHR.symm, phi_comm C hQR] at h
        simp only [← hy_def, ← hw_def] at h
        rw [abs_of_neg (by linarith : (0 : ℝ) > w - y)] at h
        linarith
      have hg1r : w - x < lam := by
        by_contra hc; push_neg at hc
        exact hnabR.1 ⟨by linarith, hc⟩
      have hg3r : theta R + Real.pi - y < lam := by
        have h := hls
        rw [phi_comm C hHR.symm] at h
        simp only [← hw_def] at h
        linarith
      have hrowR := row4_eq C hPR.symm hHR.symm hQR.symm h1r h2r
      rw [phi_comm C hHR.symm] at hrowR
      simp only [← hx_def, ← hy_def, ← hw_def] at hrowR
      have hsdR := score_add_defect C (by decide : (2 : ℕ) ≤ 4) R
      rw [hrowR, hR] at hsdR
      rw [linScore4 C (theta R) x w y] at hsdR
      have hg1rs : gapScore lam (w - x) = 0 := gapScore_zero_of_lt' C hg1r
      have hg3rs : gapScore lam (theta R + Real.pi - y) = 0 :=
        gapScore_zero_of_lt' C hg3r
      have hscR : gapScore lam (x - theta R) + gapScore lam (y - w) =
          n - 2 := by omega
      have e0 : gapScore lam (x - theta R) = ⌊(x - theta R) / lam⌋₊ - 1 := rfl
      have e2 : gapScore lam (y - w) = ⌊(y - w) / lam⌋₊ - 1 := rfl
      rw [e0, e2] at hscR
      have hq0 : (1 : ℕ) ≤ ⌊(x - theta R) / lam⌋₊ :=
        Nat.le_floor (by rw [le_div_iff₀ C.hlam, Nat.cast_one, one_mul]; linarith)
      have hq2 : (1 : ℕ) ≤ ⌊(y - w) / lam⌋₊ :=
        Nat.le_floor (by rw [le_div_iff₀ C.hlam, Nat.cast_one, one_mul]; linarith)
      have hsum : ⌊(x - theta R) / lam⌋₊ + ⌊(y - w) / lam⌋₊ = n := by omega
      have hybig : (↑n : ℝ) * lam ≤ y - theta R := by
        have h0 := floor_mul_le_gap C.hlam (by linarith : (0 : ℝ) ≤ x - theta R)
        have h2 := floor_mul_le_gap C.hlam (by linarith : (0 : ℝ) ≤ y - w)
        have hs : ((⌊(x - theta R) / lam⌋₊ : ℝ) + ⌊(y - w) / lam⌋₊) * lam =
            (n : ℝ) * lam := by
          rw [← Nat.cast_add, hsum]
        nlinarith
      have hcor : y ≤ Real.pi - lam + theta R := by
        have h := (up_corridor C hQR hupQR).2
        rw [phi_comm C hQR] at h
        simp only [← hy_def] at h
        exact h
      nlinarith [hπ]
    · -- `Up (R,Q)`: `w` sits between `y` and `z`, hence `y < w < z`.
      obtain ⟨-, hbet⟩ := up_trans C hQR.symm hHQ.symm hHR.symm hupRQ hupQH
      rw [phi_comm C hHR.symm, phi_comm C hHQ.symm] at hbet
      simp only [← hy_def, ← hz_def, ← hw_def] at hbet
      have hywz : y < w ∧ w < z := by
        rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exfalso; linarith
      rcases up_or_up C hPQ with hupPQ | hupQP
      · -- `Up (P,Q)`: `t < u`; the `Q`-row ends in `z`, whose last two
        -- gaps are both `≥ λ` — `{2,3}` adjacency, either ordering of `t,y`.
        obtain ⟨-, hbet1⟩ := up_trans C hPQ hHQ.symm hHP.symm hupPQ hupQH
        rw [phi_comm C hHP.symm, phi_comm C hHQ.symm] at hbet1
        simp only [← hz_def, ← hu_def, ← ht_def] at hbet1
        have htz : t < u := by
          rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h1
          · linarith
        have hcap_zy : lam ≤ z - y := by
          have h := up_cap C hQR.symm hHQ.symm hHR.symm hupRQ hupQH
          rw [phi_comm C hHQ.symm] at h
          simp only [← hy_def, ← hz_def] at h
          rw [abs_of_pos (by linarith : (0 : ℝ) < z - y)] at h
          exact h
        have hcap_zt : lam ≤ z - t := by
          have h := up_cap C hPQ hHQ.symm hHP.symm hupPQ hupQH
          rw [phi_comm C hHQ.symm] at h
          simp only [← ht_def, ← hz_def] at h
          rw [abs_of_pos (by linarith : (0 : ℝ) < z - t)] at h
          exact h
        have hytne : y ≠ t := by
          have h := legal_dirRep_ne C C.hleg_sub C.he hQR hPQ.symm hPR.symm
          rw [phi_comm C hQR, phi_comm C hPQ.symm] at h
          simp only [← hy_def, ← ht_def] at h
          exact h
        rcases lt_or_gt_of_ne hytne with hlt | hgt
        · -- `y < t`: `Q = [y,t,z]` — `{2,3}` are `z − t` and `θ_Q + π − z`.
          have h1q : dirRep o e (c ∘ v.succAbove) Q R <
              dirRep o e (c ∘ v.succAbove) Q P := by
            rw [phi_comm C hQR, phi_comm C hPQ.symm]
            simp only [← hy_def, ← ht_def]
            exact hlt
          have h2q : dirRep o e (c ∘ v.succAbove) Q P <
              dirRep o e (c ∘ v.succAbove) Q H := by
            rw [phi_comm C hPQ.symm, phi_comm C hHQ.symm]
            simp only [← ht_def, ← hz_def]
            linarith
          have hnab := five_point_no_adjacent_big C hQR hPQ.symm hHQ.symm
            hPQ hPR hQR.symm hPR.symm hPQ hHP.symm h1q h2q hA hQ hP hR hP
          rw [phi_comm C hQR, phi_comm C hPQ.symm, phi_comm C hHQ.symm] at hnab
          simp only [← hy_def, ← ht_def, ← hz_def] at hnab
          exact hnab.2.2 ⟨hcap_zt, hz2⟩
        · -- `t < y`: `Q = [t,y,z]` — `{2,3}` are `z − y` and `θ_Q + π − z`.
          have h1q : dirRep o e (c ∘ v.succAbove) Q P <
              dirRep o e (c ∘ v.succAbove) Q R := by
            rw [phi_comm C hPQ.symm, phi_comm C hQR]
            simp only [← ht_def, ← hy_def]
            exact hgt
          have h2q : dirRep o e (c ∘ v.succAbove) Q R <
              dirRep o e (c ∘ v.succAbove) Q H := by
            rw [phi_comm C hQR, phi_comm C hHQ.symm]
            simp only [← hy_def, ← hz_def]
            linarith
          have hnab := five_point_no_adjacent_big C hPQ.symm hQR hHQ.symm
            hQR.symm hPR.symm hPQ hPR hPQ hHP.symm h1q h2q hA hQ hR hP hP
          rw [phi_comm C hPQ.symm, phi_comm C hQR, phi_comm C hHQ.symm] at hnab
          simp only [← ht_def, ← hy_def, ← hz_def] at hnab
          exact hnab.2.2 ⟨hcap_zy, hz2⟩
      · -- `Up (Q,P)`: `x` lies between `y` and `t`.
        obtain ⟨-, hbet3⟩ := up_trans C hQR.symm hPQ.symm hPR.symm hupRQ hupQP
        rw [phi_comm C hPQ.symm] at hbet3
        simp only [← hx_def, ← hy_def, ← ht_def] at hbet3
        have hcap_zy : lam ≤ z - y := by
          have h := up_cap C hQR.symm hHQ.symm hHR.symm hupRQ hupQH
          rw [phi_comm C hHQ.symm] at h
          simp only [← hy_def, ← hz_def] at h
          rw [abs_of_pos (by linarith : (0 : ℝ) < z - y)] at h
          exact h
        have hcap_ty : lam ≤ |t - y| := by
          have h := up_cap C hQR.symm hPQ.symm hPR.symm hupRQ hupQP
          rw [phi_comm C hPQ.symm] at h
          simp only [← ht_def, ← hy_def] at h
          exact h
        have hctu : theta Q + lam ≤ t := by
          have h := (up_corridor C hPQ.symm hupQP).1
          rw [phi_comm C hPQ.symm] at h
          simp only [← ht_def] at h
          exact h
        have hct : t ≤ Real.pi - lam + theta P := by
          have h := (up_corridor C hPQ.symm hupQP).2
          rw [phi_comm C hPQ.symm] at h
          simp only [← ht_def] at h
          exact h
        have hcy : theta R + lam ≤ y := by
          have h := (up_corridor C hQR.symm hupRQ).1
          simp only [← hy_def] at h
          exact h
        have hcu : w ≤ Real.pi - lam + theta H := by
          have h := (up_corridor C hHR.symm hupRH).2
          rw [phi_comm C hHR.symm] at h
          simp only [← hw_def] at h
          exact h
        rcases hbet3 with ⟨hyx, hxt⟩ | ⟨htx, hxy⟩
        swap
        · -- `t < x < y` (so `t < y < z`): `Q = [t,y,z]` dies at `{0,1}` —
          -- corridor `Q→P` gives `t − θ_Q ≥ λ`, the cap gives `y − t ≥ λ`.
          have hcap_yt : lam ≤ y - t := by
            rw [abs_of_neg (by linarith : (0 : ℝ) > t - y)] at hcap_ty
            linarith
          have h1q : dirRep o e (c ∘ v.succAbove) Q P <
              dirRep o e (c ∘ v.succAbove) Q R := by
            rw [phi_comm C hPQ.symm, phi_comm C hQR]
            simp only [← ht_def, ← hy_def]
            linarith
          have h2q : dirRep o e (c ∘ v.succAbove) Q R <
              dirRep o e (c ∘ v.succAbove) Q H := by
            rw [phi_comm C hQR, phi_comm C hHQ.symm]
            simp only [← hy_def, ← hz_def]
            linarith
          have hnab := five_point_no_adjacent_big C hPQ.symm hQR hHQ.symm
            hQR.symm hPR.symm hPQ hPR hPQ hHP.symm h1q h2q hA hQ hR hP hP
          rw [phi_comm C hPQ.symm, phi_comm C hQR, phi_comm C hHQ.symm] at hnab
          simp only [← ht_def, ← hy_def, ← hz_def] at hnab
          exact hnab.1 ⟨by linarith, hcap_yt⟩
        · -- `y < x < t` (so `y < t`): the score-forcing leaf.
          have hcap_ty' : lam ≤ t - y := by
            rw [abs_of_pos (by linarith : (0 : ℝ) < t - y)] at hcap_ty
            exact hcap_ty
          -- Concentrate the `Q`-row score: whichever of `z,t` is larger,
          -- the gap after `y` carries `n − 2`, so `(n−1)λ ≤ t − y`.
          have htQ : ((n : ℝ) - 1) * lam ≤ t - y := by
            have hztne : z ≠ t := by
              have h := legal_dirRep_ne C C.hleg_sub C.he hHQ.symm hPQ.symm
                hHP
              rw [phi_comm C hHQ.symm, phi_comm C hPQ.symm] at h
              simp only [← hz_def, ← ht_def] at h
              exact h
            rcases lt_or_gt_of_ne hztne with hzt | htz
            · -- `z < t`: `Q = [y,z,t]` — the score is all on `z − y`.
              have h1q : dirRep o e (c ∘ v.succAbove) Q R <
                  dirRep o e (c ∘ v.succAbove) Q H := by
                rw [phi_comm C hQR, phi_comm C hHQ.symm]
                simp only [← hy_def, ← hz_def]
                linarith
              have h2q : dirRep o e (c ∘ v.succAbove) Q H <
                  dirRep o e (c ∘ v.succAbove) Q P := by
                rw [phi_comm C hHQ.symm, phi_comm C hPQ.symm]
                simp only [← hz_def, ← ht_def]
                exact hzt
              have hnab := five_point_no_adjacent_big C hQR hHQ.symm hPQ.symm
                hPQ hPR hPQ hHP.symm hQR.symm hPR.symm h1q h2q hA hQ hP hP hR
              rw [phi_comm C hQR, phi_comm C hHQ.symm,
                phi_comm C hPQ.symm] at hnab
              simp only [← hy_def, ← hz_def, ← ht_def] at hnab
              have hg0q : y - theta Q < lam := by
                by_contra hc; push_neg at hc
                exact hnab.1 ⟨hc, hcap_zy⟩
              have hg2q : t - z < lam := by
                by_contra hc; push_neg at hc
                exact hnab.2.1 ⟨hcap_zy, hc⟩
              have hg3q : theta Q + Real.pi - t < 2 * lam := by
                have hβQ := (C.htheta Q).1.2
                have htpi : Real.pi - lam < t := by linarith
                linarith
              have hrowQ := row4_eq C hQR hHQ.symm hPQ.symm h1q h2q
              rw [phi_comm C hQR, phi_comm C hHQ.symm,
                phi_comm C hPQ.symm] at hrowQ
              simp only [← hy_def, ← hz_def, ← ht_def] at hrowQ
              have hsdQ := score_add_defect C (by decide : (2 : ℕ) ≤ 4) Q
              rw [hrowQ, hQ] at hsdQ
              rw [linScore4 C (theta Q) y z t] at hsdQ
              have hg0qs : gapScore lam (y - theta Q) = 0 :=
                gapScore_zero_of_lt' C hg0q
              have hg2qs : gapScore lam (t - z) = 0 :=
                gapScore_zero_of_lt' C hg2q
              have hg3qs : gapScore lam (theta Q + Real.pi - t) = 0 :=
                gapScore_zero_of_lt_two C.hlam hg3q
              have hscQ : gapScore lam (z - y) = n - 2 := by omega
              have h := big_gap_lower C (by linarith) hscQ
              have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
                rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
              rw [hnm1] at h
              linarith
            · -- `t < z`: `Q = [y,t,z]` — the score is all on `t − y`.
              have h1q : dirRep o e (c ∘ v.succAbove) Q R <
                  dirRep o e (c ∘ v.succAbove) Q P := by
                rw [phi_comm C hQR, phi_comm C hPQ.symm]
                simp only [← hy_def, ← ht_def]
                linarith
              have h2q : dirRep o e (c ∘ v.succAbove) Q P <
                  dirRep o e (c ∘ v.succAbove) Q H := by
                rw [phi_comm C hPQ.symm, phi_comm C hHQ.symm]
                simp only [← ht_def, ← hz_def]
                exact htz
              have hnab := five_point_no_adjacent_big C hQR hPQ.symm hHQ.symm
                hPQ hPR hQR.symm hPR.symm hPQ hHP.symm h1q h2q hA hQ hP hR hP
              rw [phi_comm C hQR, phi_comm C hPQ.symm,
                phi_comm C hHQ.symm] at hnab
              simp only [← hy_def, ← ht_def, ← hz_def] at hnab
              have hg0q : y - theta Q < lam := by
                by_contra hc; push_neg at hc
                exact hnab.1 ⟨hc, hcap_ty'⟩
              have hg2q : z - t < lam := by
                by_contra hc; push_neg at hc
                exact hnab.2.1 ⟨hcap_ty', hc⟩
              have hg3q : theta Q + Real.pi - z < 2 * lam := by
                have hβQ := (C.htheta Q).1.2
                linarith
              have hrowQ := row4_eq C hQR hPQ.symm hHQ.symm h1q h2q
              rw [phi_comm C hQR, phi_comm C hPQ.symm,
                phi_comm C hHQ.symm] at hrowQ
              simp only [← hy_def, ← ht_def, ← hz_def] at hrowQ
              have hsdQ := score_add_defect C (by decide : (2 : ℕ) ≤ 4) Q
              rw [hrowQ, hQ] at hsdQ
              rw [linScore4 C (theta Q) y t z] at hsdQ
              have hg0qs : gapScore lam (y - theta Q) = 0 :=
                gapScore_zero_of_lt' C hg0q
              have hg2qs : gapScore lam (z - t) = 0 :=
                gapScore_zero_of_lt' C hg2q
              have hg3qs : gapScore lam (theta Q + Real.pi - z) = 0 :=
                gapScore_zero_of_lt_two C.hlam hg3q
              have hscQ : gapScore lam (t - y) = n - 2 := by omega
              have h := big_gap_lower C (by linarith) hscQ
              have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
                rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
              rwa [hnm1] at h
          -- Row `P = [u,x,t]`: `θ_P + π − t ≥ λ` (corridor), `t − x < λ`
          -- (adjacency); the two scoring gaps split on `⌊(θ_P+π−t)/λ⌋`.
          have h1p : dirRep o e (c ∘ v.succAbove) P H <
              dirRep o e (c ∘ v.succAbove) P R := by
            rw [phi_comm C hHP.symm, phi_comm C hPR]
            simp only [← hu_def, ← hx_def]
            exact huxw.1
          have h2p : dirRep o e (c ∘ v.succAbove) P R <
              dirRep o e (c ∘ v.succAbove) P Q := by
            rw [phi_comm C hPR]
            simp only [← hx_def, ← ht_def]
            exact hxt
          have hnabP := five_point_no_adjacent_big C hHP.symm hPR hPQ
            hPR.symm hHR.symm hPQ.symm hQR hPR.symm hQR.symm h1p h2p
            hA hP hR hQ hR
          rw [phi_comm C hHP.symm, phi_comm C hPR] at hnabP
          simp only [← hu_def, ← hx_def, ← ht_def] at hnabP
          have hg3p : lam ≤ theta P + Real.pi - t := by linarith
          have hg2p : t - x < lam := by
            by_contra hc; push_neg at hc
            exact hnabP.2.2 ⟨hc, hg3p⟩
          have hrowP := row4_eq C hHP.symm hPR hPQ h1p h2p
          rw [phi_comm C hHP.symm, phi_comm C hPR] at hrowP
          simp only [← hu_def, ← hx_def, ← ht_def] at hrowP
          have hsdP := score_add_defect C (by decide : (2 : ℕ) ≤ 4) P
          rw [hrowP, hP] at hsdP
          rw [linScore4 C (theta P) u x t] at hsdP
          have hg0ps : gapScore lam (u - theta P) = 0 := by
            apply gapScore_zero_of_lt' C
            have h := hfs
            rw [phi_comm C hHP.symm] at h
            simp only [← hu_def] at h
            exact h
          have hg2ps : gapScore lam (t - x) = 0 := gapScore_zero_of_lt' C hg2p
          have hscP : gapScore lam (x - u) +
              gapScore lam (theta P + Real.pi - t) = n - 2 := by omega
          have e1 : gapScore lam (x - u) = ⌊(x - u) / lam⌋₊ - 1 := rfl
          have e3 : gapScore lam (theta P + Real.pi - t) =
              ⌊(theta P + Real.pi - t) / lam⌋₊ - 1 := rfl
          rw [e1, e3] at hscP
          rcases lt_or_ge ⌊(theta P + Real.pi - t) / lam⌋₊ 2 with hq3 | hq3
          · -- `⌊·⌋ = 1`, so `⌊(x−u)/λ⌋ = n − 1` and `x > θ_H + nλ ≥ w`.
            have hq3eq : ⌊(theta P + Real.pi - t) / lam⌋₊ = 1 := by
              have hq3lb : (1 : ℕ) ≤ ⌊(theta P + Real.pi - t) / lam⌋₊ :=
                Nat.le_floor (by
                  rw [le_div_iff₀ C.hlam, Nat.cast_one, one_mul]; linarith)
              omega
            have hq1 : ⌊(x - u) / lam⌋₊ = n - 1 := by omega
            have hxbig : ((n : ℝ) - 1) * lam ≤ x - u := by
              have h := floor_mul_le_gap C.hlam (by linarith : (0 : ℝ) ≤ x - u)
              rw [hq1] at h
              have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
                rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
              rwa [hnm1] at h
            -- `x ≥ u + (n−1)λ ≥ θ_H + nλ > θ_H + π − λ ≥ w > x`.
            nlinarith [hu, huxw.2, hcu, hπ]
          · -- `⌊·⌋ ≥ 2`, so `t ≤ θ_P + π − 2λ` and `y < θ_P + β − λ`.
            have hq3' : (2 : ℝ) ≤ (⌊(theta P + Real.pi - t) / lam⌋₊ : ℝ) := by
              exact_mod_cast hq3
            have hg3big : (2 : ℝ) * lam ≤ theta P + Real.pi - t := by
              have h := floor_mul_le_gap C.hlam
                (by linarith : (0 : ℝ) ≤ theta P + Real.pi - t)
              nlinarith
            -- `y ≤ t − (n−1)λ ≤ θ_P + π − 2λ − (n−1)λ = θ_P + β − λ`, but
            -- `y ≥ θ_R + λ`, forcing `θ_P ≥ θ_R + (n+2)λ − π > π − nλ`.
            nlinarith [hcy, htQ, hg3big, hβP, hθR0, hπ]

end TwoInCentral

end Jsp404
