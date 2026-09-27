import Jsp000404.DeletionRigidity

/-!
# Mixed two-in receivers: the central insertion is impossible

In a five-point `R = 3` configuration (saturated anchor `A`, defect `≥ 3`
row `H`, defect-`2` rows `P, Q, R`), let `P → H` be a short-first chord and
`R → H` a short-last chord.  Write

    u = φ_HP,  w = φ_HR,  z = φ_HQ,
    x = φ_RP,  y = φ_RQ,  t = φ_PQ.

The main theorem `mixed_two_in_central` proves `u < z < w → ⊥`: the third
incoming direction cannot split the gap between the two received
directions.  Combined with `two_in_mixed_between` this pins a mixed two-in
receiver to defect `3` (and with legality, `z` outside `(u, w)`).

Proof outline (six leaves, mirroring the packet):
* `five_point_high_receiver_not_full_in` gives `¬ ShortWitness Q H`, so
  both `H`-direction end gaps of the `Q`-row are `≥ λ`.
* `Up(H,P)`, `Up(R,H)` give `Up(R,P)` with `u < x < w` (`up_trans`).
* The three unknown `Up`-orientations on `HQ, PQ, RQ` collapse to four
  consistent triples; zero merge gains (`five_point_no_adjacent_big`) or
  the cross-row argument (a forced `≥ (n−1)λ` gap in one row, the
  `≤ π − nλ` end-span of `linearGapScore_span_le_of_big_ends` in the next,
  adjacent big gaps in the third) yield the contradiction.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section TwoInCentral

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- Four pairwise-distinct elements of `Fin 4` cover it. -/
theorem fin4_cover {a b d e : Fin 4} (hab : a ≠ b) (had : a ≠ d)
    (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    ∀ j : Fin 4, j = a ∨ j = b ∨ j = d ∨ j = e := by
  intro j
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have had' : a.val ≠ d.val := fun h => had (Fin.ext h)
  have hae' : a.val ≠ e.val := fun h => hae (Fin.ext h)
  have hbd' : b.val ≠ d.val := fun h => hbd (Fin.ext h)
  have hbe' : b.val ≠ e.val := fun h => hbe (Fin.ext h)
  have hde' : d.val ≠ e.val := fun h => hde (Fin.ext h)
  have hav := a.2; have hbv := b.2; have hdv := d.2; have hev := e.2
  have hv := j.2
  have : j.val = a.val ∨ j.val = b.val ∨ j.val = d.val ∨ j.val = e.val := by
    omega
  rcases this with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- A non-short-witness leaves both end gaps `≥ λ`. -/
theorem not_short_witness_bounds {i j : Fin 4} (hij : i ≠ j)
    (h : ¬ ShortWitness (lam := lam) (c := c) o e v theta i j) :
    lam ≤ dirRep o e (c ∘ v.succAbove) i j - theta i ∧
      lam ≤ theta i + Real.pi - dirRep o e (c ∘ v.succAbove) i j := by
  constructor
  · by_contra hc
    push_neg at hc
    exact h ⟨hij, Or.inl hc⟩
  · by_contra hc
    push_neg at hc
    exact h ⟨hij, Or.inr hc⟩

/-- A gap `< λ` contributes `0` to the score. -/
theorem gapScore_zero_of_lt' {g : ℝ} (hg : g < lam) : gapScore lam g = 0 := by
  unfold gapScore
  have : ⌊g / lam⌋₊ = 0 := by
    rw [Nat.floor_eq_zero, div_lt_one C.hlam]
    exact hg
  omega

/-- If the score of a `n − 2` row concentrates on one gap `g`, its floor
is `n − 1`, hence `(n − 1)λ ≤ g`. -/
theorem big_gap_lower {g : ℝ} (hg0 : 0 ≤ g)
    (hs : gapScore lam g = n - 2) :
    (↑(n - 1) : ℝ) * lam ≤ g := by
  have hn3 := C.hn3
  have hfl : ⌊g / lam⌋₊ = n - 1 := by
    unfold gapScore at hs; omega
  have h := floor_mul_le_gap C.hlam hg0
  rw [hfl] at h
  exact h

/-- Expand `linearGapScore` on an explicit three-element row. -/
theorem linScore4 (θ A B D : ℝ) :
    linearGapScore lam θ (θ + Real.pi) [A, B, D] =
      gapScore lam (A - θ) + gapScore lam (B - A) + gapScore lam (D - B) +
        gapScore lam (θ + Real.pi - D) := by
  simp only [linearGapScore]
  ring_nf

/-- `⌊π / λ⌋ = n` gives `π < (n+1)λ`. -/
theorem pi_lt_succ_mul (hn : ⌊Real.pi / lam⌋₊ = n) :
    Real.pi < (↑n + 1) * lam := by
  have h := Nat.lt_floor_add_one (Real.pi / lam)
  rw [hn] at h
  rw [div_lt_iff₀ C.hlam] at h
  push_cast at h
  linarith

set_option maxHeartbeats 1600000 in
/-- **Mixed two-in: the third direction cannot be central.**

Setup: `H` receives a short-first chord from `P` and a short-last chord
from `R`; `Q` is the third defect-`2` source.  With `u = φ_HP`,
`w = φ_HR`, `z = φ_HQ`, the assumption `u < z < w` is impossible. -/
theorem mixed_two_in_central {H P Q R : Fin 4}
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
    (huz : dirRep o e (c ∘ v.succAbove) H P < dirRep o e (c ∘ v.succAbove) H Q)
    (hzw : dirRep o e (c ∘ v.succAbove) H Q < dirRep o e (c ∘ v.succAbove) H R) :
    False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H P with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H R with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H Q with hz_def
  set x := dirRep o e (c ∘ v.succAbove) R P with hx_def
  set y := dirRep o e (c ∘ v.succAbove) R Q with hy_def
  set t := dirRep o e (c ∘ v.succAbove) P Q with ht_def
  -- Actual orientations of the two received chords.
  have hupHP : Up o e c v H P := up_of_short_first C hHP.symm hfs
  have hupRH : Up o e c v R H := up_of_short_last C hHR.symm hls
  -- `u < w` from the F/L windows.
  have huw : u < w := by
    have hβP := (C.htheta P).1.2
    have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast C.hn3
    have hl := C.hlam
    nlinarith [hu', hw]
  -- `Up(R,P)` and `u < x < w`.
  obtain ⟨hupRP, hxbet⟩ := up_trans C hHR.symm hHP hPR.symm hupRH hupHP
  rw [phi_comm C hHR.symm] at hxbet
  have huxw : u < x ∧ x < w := by
    rcases hxbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso; linarith
    · exact ⟨h1, h2⟩
  -- `Q` cannot also send a short chord to `H` (the all-in case is excluded).
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
  -- Orientation case split on the three chords through `Q`.
  rcases up_or_up C hHQ with hupHQ | hupQH
  · rcases up_or_up C hQR with hupQR | hupRQ
    · -- `Up(H,Q) ∧ Up(Q,R)` gives `Up(H,R)`, against `Up(R,H)`.
      obtain ⟨hupHR, -⟩ := up_trans C hHQ hQR hHR hupHQ hupQR
      exact up_not_both C hHR.symm hupRH hupHR
    · rcases up_or_up C hPQ with hupPQ | hupQP
      · -- LEAF 2: `Up(H,Q)`, `Up(P,Q)`, `Up(R,Q)`.
        obtain ⟨-, hbet1⟩ := up_trans C hHP hPQ hHQ hupHP hupPQ
        -- (u < z ∧ z < t) ∨ (t < z ∧ z < u); `u < z` forces `u < z < t`.
        obtain ⟨-, hbet2⟩ := up_trans C hHR.symm hHQ hQR.symm hupRH hupHQ
        rw [phi_comm C hHR.symm] at hbet2
        -- (w < y ∧ y < z) ∨ (z < y ∧ y < w); `z < w` forces `z < y < w`.
        obtain ⟨-, hbet3⟩ := up_trans C hPR.symm hPQ hQR.symm hupRP hupPQ
        -- (x < y ∧ y < t) ∨ (t < y ∧ y < x)
        have hzt : z < t := by
          rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h2
          · linarith
        have hzyw : z < y ∧ y < w := by
          rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · exact ⟨h1, h2⟩
        have hcapu : lam ≤ t - u := by
          have h := up_cap C hHP hPQ hHQ hupHP hupPQ
          rw [abs_of_pos (by linarith : (0 : ℝ) < t - u)] at h
          exact h
        have hcaptx := up_cap C hPR.symm hPQ hQR.symm hupRP hupPQ
        simp only [← ht_def, ← hx_def] at hcaptx
        obtain ⟨-, hcorr2⟩ := up_corridor C hPQ hupPQ
        simp only [← ht_def] at hcorr2
        have hne_tx : t ≠ x := by
          intro he
          rw [he, sub_self, abs_zero] at hcaptx
          linarith [C.hlam]
        rcases lt_or_gt_of_ne hne_tx with htx | htx
        · -- `t < x`: row `P` has adjacent big gaps at positions 1,2.
          have h1p : dirRep o e (c ∘ v.succAbove) P H <
              dirRep o e (c ∘ v.succAbove) P Q := by
            rw [phi_comm C hHP.symm]
            simp only [← hu_def, ← ht_def]
            linarith
          have h2p : dirRep o e (c ∘ v.succAbove) P Q <
              dirRep o e (c ∘ v.succAbove) P R := by
            rw [phi_comm C hPR]
            simp only [← hx_def, ← ht_def]
            exact htx
          have hnab := five_point_no_adjacent_big C hHP.symm hPQ hPR
            hPR.symm hHR.symm hPR.symm hQR.symm hPQ.symm hQR h1p h2p hA hP hR hR hQ
          rw [phi_comm C hHP.symm, phi_comm C hPR] at hnab
          simp only [← hu_def, ← hx_def, ← ht_def] at hnab
          have hxm : lam ≤ x - t := by
            rw [abs_of_neg (by linarith : t - x < 0)] at hcaptx
            linarith
          exact hnab.2.1 ⟨hcapu, hxm⟩
        · -- `x < t`: the `P → Q → R` cross-row chain.
          have h1p : dirRep o e (c ∘ v.succAbove) P H <
              dirRep o e (c ∘ v.succAbove) P R := by
            rw [phi_comm C hHP.symm, phi_comm C hPR]
            simp only [← hu_def, ← hx_def]
            exact huxw.1
          have h2p : dirRep o e (c ∘ v.succAbove) P R <
              dirRep o e (c ∘ v.succAbove) P Q := by
            rw [phi_comm C hPR]
            simp only [← hx_def, ← ht_def]
            exact htx
          have hnab := five_point_no_adjacent_big C hHP.symm hPR hPQ
            hPR.symm hHR.symm hPQ.symm hQR hPR.symm hQR.symm h1p h2p hA hP hR hQ hR
          rw [phi_comm C hHP.symm, phi_comm C hPR] at hnab
          simp only [← hu_def, ← hx_def, ← ht_def] at hnab
          have htx_ge : lam ≤ t - x := by
            rw [abs_of_pos (by linarith : (0 : ℝ) < t - x)] at hcaptx
            exact hcaptx
          have hg1 : x - u < lam := by
            by_contra hc; push_neg at hc; exact hnab.2.1 ⟨hc, htx_ge⟩
          have hg3 : theta P + Real.pi - t < lam := by
            by_contra hc; push_neg at hc; exact hnab.2.2 ⟨htx_ge, hc⟩
          -- row `P`: only the gap `t − x` contributes to the score.
          have hrowP := row4_eq C hHP.symm hPR hPQ h1p h2p
          rw [phi_comm C hHP.symm, phi_comm C hPR] at hrowP
          simp only [← hu_def, ← hx_def, ← ht_def] at hrowP
          have hsd := score_add_defect C (by decide : (2 : ℕ) ≤ 4) P
          rw [hrowP, hP] at hsd
          have hlin : gapScore lam (t - x) = n - 2 := by
            have e := linScore4 C (theta P) u x t
            rw [e] at hsd
            have g0 : gapScore lam (u - theta P) = 0 := by
              apply gapScore_zero_of_lt' C
              rw [hu_def, ← phi_comm C hHP.symm]
              exact hfs
            have g1 : gapScore lam (x - u) = 0 := gapScore_zero_of_lt' C hg1
            have g3 : gapScore lam (theta P + Real.pi - t) = 0 :=
              gapScore_zero_of_lt' C hg3
            omega
          have hPbig := big_gap_lower C (by linarith : (0 : ℝ) ≤ t - x) hlin
          -- row `Q`: both end gaps `≥ λ` → span `t − z ≤ π − nλ`.
          have hyt : y < t := by
            rcases hbet3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact h2
            · linarith
          have hxy' : x < y := by
            rcases hbet3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact h1
            · linarith
          have h1q : dirRep o e (c ∘ v.succAbove) Q H <
              dirRep o e (c ∘ v.succAbove) Q R := by
            rw [phi_comm C hHQ.symm, phi_comm C hQR]
            simp only [← hz_def, ← hy_def]
            exact hzyw.1
          have h2q : dirRep o e (c ∘ v.succAbove) Q R <
              dirRep o e (c ∘ v.succAbove) Q P := by
            rw [phi_comm C hQR, phi_comm C hPQ.symm]
            simp only [← hy_def, ← ht_def]
            exact hyt
          have hrowQ := row4_eq C hHQ.symm hQR hPQ.symm h1q h2q
          rw [phi_comm C hHQ.symm, phi_comm C hQR, phi_comm C hPQ.symm] at hrowQ
          simp only [← hz_def, ← hy_def, ← ht_def] at hrowQ
          have hsdQ := score_add_defect C (by decide : (2 : ℕ) ≤ 4) Q
          rw [hrowQ, hQ] at hsdQ
          have hsortQ : [z, y, t].Pairwise (· ≤ ·) := by
            apply List.Pairwise.cons
            · intro b hb
              fin_cases hb <;> linarith
            · apply List.Pairwise.cons
              · intro b hb
                fin_cases hb
                exact hyt.le
              · simp
          have hmemQ : ∀ a ∈ [z, y, t],
              theta Q ≤ a ∧ a ≤ theta Q + Real.pi := by
            intro a ha
            fin_cases ha <;> constructor <;> linarith
          have hnfQ : ⌊(theta Q + Real.pi - theta Q) / lam⌋₊ = n := by
            rw [show theta Q + Real.pi - theta Q = Real.pi by ring]
            exact C.hn
          have hne' : [z, y, t] ≠ [] := by simp
          have hgl : [z, y, t].getLast hne' = t := rfl
          have hhd : [z, y, t].head hne' = z := rfl
          have hspan := linearGapScore_span_le_of_big_ends lam (theta Q)
            (theta Q + Real.pi) C.hlam hne' hsortQ hmemQ
            (by rw [hhd]; exact hz1) (by rw [hgl]; linarith [hcorr2]) hnfQ hsdQ
          rw [hgl, hhd] at hspan
          -- row `R`: `x − θ_R ≥ λ` and `y − x > λ` adjacent at positions 0,1.
          have h1r : dirRep o e (c ∘ v.succAbove) R P <
              dirRep o e (c ∘ v.succAbove) R Q := by
            simp only [← hx_def, ← hy_def]
            exact hxy'
          have h2r : dirRep o e (c ∘ v.succAbove) R Q <
              dirRep o e (c ∘ v.succAbove) R H := by
            rw [phi_comm C hHR.symm]
            simp only [← hy_def, ← hw_def]
            exact hzyw.2
          have hnab2 := five_point_no_adjacent_big C hPR.symm hQR.symm hHR.symm
            hQR hPQ.symm hPR hPQ hPR hHP.symm h1r h2r hA hR hQ hP hP
          simp only [← hx_def, ← hy_def] at hnab2
          have hxθ : lam ≤ x - theta R := by linarith [huxw.1, hu, hθR]
          have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast C.hn3
          have hπ := pi_lt_succ_mul C C.hn
          have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
          rw [hnm1] at hPbig
          have hM : (3 : ℝ) * lam ≤ (n : ℝ) * lam :=
            mul_le_mul_of_nonneg_right hn3r C.hlam.le
          push_cast at hM hπ
          have hspan' : t - z ≤ Real.pi - ↑n * lam := by linarith [hspan]
          have hyx : lam ≤ y - x := by
            have e : y - x = (t - x) - (t - z) + (y - z) := by ring
            rw [e]
            nlinarith [hPbig, hspan', hzyw.1]
          exact hnab2.1 ⟨hxθ, hyx⟩
      · -- LEAF 1: `Up(H,Q)`, `Up(Q,P)`, `Up(R,Q)` — row `Q` first two gaps big.
        obtain ⟨-, hbet1⟩ := up_trans C hHQ hPQ.symm hHP hupHQ hupQP
        rw [phi_comm C hPQ.symm] at hbet1
        -- (z < u ∧ u < t) ∨ (t < u ∧ u < z); `u < z` forces `t < u < z`.
        obtain ⟨-, hbet2⟩ := up_trans C hHR.symm hHQ hQR.symm hupRH hupHQ
        rw [phi_comm C hHR.symm] at hbet2
        -- (w < y ∧ y < z) ∨ (z < y ∧ y < w); `z < w` forces `z < y < w`.
        have htz : t < z := by
          rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · linarith
        have hzy : z < y := by
          rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · exact h1
        have hcap : lam ≤ z - t := by
          have h := up_cap C hHQ hPQ.symm hHP hupHQ hupQP
          rw [phi_comm C hPQ.symm] at h
          rw [abs_of_neg (by linarith : t - z < 0)] at h
          linarith
        have hcorr := (up_corridor C hPQ.symm hupQP).1
        rw [phi_comm C hPQ.symm] at hcorr
        simp only [← ht_def] at hcorr
        -- row `Q` sorted `[t, z, y]`.
        have h1q : dirRep o e (c ∘ v.succAbove) Q P <
            dirRep o e (c ∘ v.succAbove) Q H := by
          rw [phi_comm C hPQ.symm, phi_comm C hHQ.symm]
          simp only [← ht_def, ← hz_def]
          exact htz
        have h2q : dirRep o e (c ∘ v.succAbove) Q H <
            dirRep o e (c ∘ v.succAbove) Q R := by
          rw [phi_comm C hHQ.symm, phi_comm C hQR]
          simp only [← hz_def, ← hy_def]
          exact hzy
        have hnab := five_point_no_adjacent_big C hPQ.symm hHQ.symm hQR
          hQR.symm hPR.symm hQR.symm hHR.symm hPQ hPR h1q h2q hA hQ hR hR hP
        rw [phi_comm C hPQ.symm, phi_comm C hHQ.symm] at hnab
        simp only [← ht_def, ← hz_def] at hnab
        exact hnab.1 ⟨by linarith, hcap⟩
  · -- `Up(Q,H)` forces `Up(Q,P)` by transitivity through `P`.
    have hupQP : Up o e c v Q P :=
      (up_trans C hHQ.symm hHP hPQ.symm hupQH hupHP).1
    rcases up_or_up C hPQ with hupPQ | -
    · exact up_not_both C hPQ.symm hupQP hupPQ
    · rcases up_or_up C hQR with hupQR | hupRQ
      · -- LEAF 4: `Up(Q,H)`, `Up(Q,P)`, `Up(Q,R)`.
        obtain ⟨-, hbet1⟩ := up_trans C hQR hHR.symm hHQ.symm hupQR hupRH
        rw [phi_comm C hQR, phi_comm C hHQ.symm, phi_comm C hHR.symm] at hbet1
        -- (y < z ∧ z < w) ∨ (w < z ∧ z < y); `z < w` forces `y < z < w`.
        have hyz : y < z := by
          rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h1
          · linarith
        obtain ⟨-, hbet2⟩ := up_trans C hHQ.symm hHP hPQ.symm hupQH hupHP
        rw [phi_comm C hHQ.symm, phi_comm C hPQ.symm] at hbet2
        -- (z < t ∧ t < u) ∨ (u < t ∧ t < z); `u < z` forces `u < t < z`.
        have hut : u < t := by
          rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · exact h1
        have htz : t < z := by
          rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · exact h2
        obtain ⟨-, hbet3⟩ := up_trans C hQR hPR.symm hPQ.symm hupQR hupRP
        rw [phi_comm C hQR, phi_comm C hPQ.symm] at hbet3
        -- (y < t ∧ t < x) ∨ (x < t ∧ t < y)
        have hcap := up_cap C hQR hPR.symm hPQ.symm hupQR hupRP
        rw [phi_comm C hQR] at hcap
        simp only [← hx_def, ← hy_def] at hcap
        obtain ⟨hcorrQ1, -⟩ := up_corridor C hQR hupQR
        rw [phi_comm C hQR] at hcorrQ1
        simp only [← hy_def] at hcorrQ1
        obtain ⟨-, hcorrP2⟩ := up_corridor C hPR.symm hupRP
        simp only [← hx_def] at hcorrP2
        have hne_xy : x ≠ y := by
          intro he
          rw [he, sub_self, abs_zero] at hcap
          linarith [C.hlam]
        rcases lt_or_gt_of_ne hne_xy with hxy | hxy
        · -- `x < y`: row `R` has adjacent big gaps at positions 0,1.
          have h1r : dirRep o e (c ∘ v.succAbove) R P <
              dirRep o e (c ∘ v.succAbove) R Q := by
            simp only [← hx_def, ← hy_def]
            exact hxy
          have h2r : dirRep o e (c ∘ v.succAbove) R Q <
              dirRep o e (c ∘ v.succAbove) R H := by
            rw [phi_comm C hHR.symm]
            simp only [← hy_def, ← hw_def]
            linarith
          have hnab := five_point_no_adjacent_big C hPR.symm hQR.symm hHR.symm
            hQR hPQ.symm hPR hPQ hPR hHP.symm h1r h2r hA hR hQ hP hP
          simp only [← hx_def, ← hy_def] at hnab
          have hyx' : lam ≤ y - x := by
            rw [abs_of_neg (by linarith : x - y < 0)] at hcap; linarith
          have hxθ : lam ≤ x - theta R := by linarith [huxw.1, hu, hθR]
          exact hnab.1 ⟨hxθ, hyx'⟩
        · -- `y < x`: the `R → Q → P` mirror cross-row chain.
          have hytx : y < t ∧ t < x := by
            rcases hbet3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h1, h2⟩
            · linarith
          -- row `R` sorted `[y, x, w]`: only `x − y` contributes.
          have h1r : dirRep o e (c ∘ v.succAbove) R Q <
              dirRep o e (c ∘ v.succAbove) R P := by
            simp only [← hy_def, ← hx_def]
            exact hxy
          have h2r : dirRep o e (c ∘ v.succAbove) R P <
              dirRep o e (c ∘ v.succAbove) R H := by
            rw [phi_comm C hHR.symm]
            simp only [← hx_def, ← hw_def]
            exact huxw.2
          have hnab := five_point_no_adjacent_big C hQR.symm hPR.symm hHR.symm
            hPR hPQ hQR hPQ.symm hPR hHP.symm h1r h2r hA hR hP hQ hP
          rw [phi_comm C hHR.symm] at hnab
          simp only [← hy_def, ← hx_def, ← hw_def] at hnab
          have hxy_ge : lam ≤ x - y := by
            rw [abs_of_pos (by linarith : (0 : ℝ) < x - y)] at hcap; exact hcap
          have hg0 : y - theta R < lam := by
            by_contra hc; push_neg at hc; exact hnab.1 ⟨hc, hxy_ge⟩
          have hg2 : w - x < lam := by
            by_contra hc; push_neg at hc; exact hnab.2.1 ⟨hxy_ge, hc⟩
          have hg3 : theta R + Real.pi - w < lam := by
            rw [hw_def, ← phi_comm C hHR.symm]
            exact hls
          have hrowR := row4_eq C hQR.symm hPR.symm hHR.symm h1r h2r
          rw [phi_comm C hHR.symm] at hrowR
          simp only [← hy_def, ← hx_def, ← hw_def] at hrowR
          have hsd := score_add_defect C (by decide : (2 : ℕ) ≤ 4) R
          rw [hrowR, hR] at hsd
          have hlin : gapScore lam (x - y) = n - 2 := by
            have e := linScore4 C (theta R) y x w
            rw [e] at hsd
            have g0 : gapScore lam (y - theta R) = 0 :=
              gapScore_zero_of_lt' C hg0
            have g2 : gapScore lam (w - x) = 0 := gapScore_zero_of_lt' C hg2
            have g3 : gapScore lam (theta R + Real.pi - w) = 0 :=
              gapScore_zero_of_lt' C hg3
            omega
          have hRbig := big_gap_lower C (by linarith : (0 : ℝ) ≤ x - y) hlin
          -- row `Q` sorted `[y, t, z]`: both ends big → `z − y ≤ π − nλ`.
          have h1q : dirRep o e (c ∘ v.succAbove) Q R <
              dirRep o e (c ∘ v.succAbove) Q P := by
            rw [phi_comm C hQR, phi_comm C hPQ.symm]
            simp only [← hy_def, ← ht_def]
            exact hytx.1
          have h2q : dirRep o e (c ∘ v.succAbove) Q P <
              dirRep o e (c ∘ v.succAbove) Q H := by
            rw [phi_comm C hPQ.symm, phi_comm C hHQ.symm]
            simp only [← ht_def, ← hz_def]
            exact htz
          have hrowQ := row4_eq C hQR hPQ.symm hHQ.symm h1q h2q
          rw [phi_comm C hQR, phi_comm C hPQ.symm, phi_comm C hHQ.symm] at hrowQ
          simp only [← hy_def, ← ht_def, ← hz_def] at hrowQ
          have hsdQ := score_add_defect C (by decide : (2 : ℕ) ≤ 4) Q
          rw [hrowQ, hQ] at hsdQ
          have hsortQ : [y, t, z].Pairwise (· ≤ ·) := by
            apply List.Pairwise.cons
            · intro b hb
              fin_cases hb <;> linarith
            · apply List.Pairwise.cons
              · intro b hb
                fin_cases hb
                exact htz.le
              · simp
          have hmemQ : ∀ a ∈ [y, t, z],
              theta Q ≤ a ∧ a ≤ theta Q + Real.pi := by
            intro a ha
            fin_cases ha <;> constructor <;> linarith
          have hnfQ : ⌊(theta Q + Real.pi - theta Q) / lam⌋₊ = n := by
            rw [show theta Q + Real.pi - theta Q = Real.pi by ring]
            exact C.hn
          have hne2 : [y, t, z] ≠ [] := by simp
          have hgl2 : [y, t, z].getLast hne2 = z := rfl
          have hhd2 : [y, t, z].head hne2 = y := rfl
          have hspan := linearGapScore_span_le_of_big_ends lam (theta Q)
            (theta Q + Real.pi) C.hlam hne2 hsortQ hmemQ
            (by rw [hhd2]; linarith [hcorrQ1]) (by rw [hgl2]; exact hz2) hnfQ hsdQ
          rw [hgl2, hhd2] at hspan
          have hspan' : z - y ≤ Real.pi - ↑n * lam := by linarith [hspan]
          -- row `P` sorted `[u, t, x]`: `(x−t)`, `(θ_P+π−x)` both `≥ λ`.
          have h1p : dirRep o e (c ∘ v.succAbove) P H <
              dirRep o e (c ∘ v.succAbove) P Q := by
            rw [phi_comm C hHP.symm]
            simp only [← hu_def, ← ht_def]
            linarith
          have h2p : dirRep o e (c ∘ v.succAbove) P Q <
              dirRep o e (c ∘ v.succAbove) P R := by
            rw [phi_comm C hPR]
            simp only [← ht_def, ← hx_def]
            exact hytx.2
          have hnab2 := five_point_no_adjacent_big C hHP.symm hPQ hPR
            hPR.symm hHR.symm hPR.symm hQR.symm hPQ.symm hQR h1p h2p hA hP hR hR hQ
          rw [phi_comm C hHP.symm, phi_comm C hPR] at hnab2
          simp only [← hu_def, ← ht_def, ← hx_def] at hnab2
          have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast C.hn3
          have hπ := pi_lt_succ_mul C C.hn
          have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
          rw [hnm1] at hRbig
          have hM : (3 : ℝ) * lam ≤ (n : ℝ) * lam :=
            mul_le_mul_of_nonneg_right hn3r C.hlam.le
          push_cast at hM hπ
          have hty : t - y < Real.pi - ↑n * lam := by
            linarith [htz, hspan']
          have hxt : lam ≤ x - t := by
            have e : x - t = (x - y) - (t - y) := by ring
            rw [e]
            nlinarith [hRbig, hty]
          have hxend : lam ≤ theta P + Real.pi - x := by linarith [hcorrP2]
          exact hnab2.2.2 ⟨hxt, hxend⟩
      · -- LEAF 3: `Up(Q,H)`, `Up(Q,P)`, `Up(R,Q)` — row `Q` last two gaps big.
        obtain ⟨-, hbet1⟩ := up_trans C hHQ.symm hHP hPQ.symm hupQH hupHP
        rw [phi_comm C hHQ.symm, phi_comm C hPQ.symm] at hbet1
        -- (z < t ∧ t < u) ∨ (u < t ∧ t < z); `u < z` forces `u < t < z`.
        have htz : t < z := by
          rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · linarith
        obtain ⟨-, hbet2⟩ := up_trans C hQR.symm hHQ.symm hHR.symm hupRQ hupQH
        rw [phi_comm C hHQ.symm, phi_comm C hHR.symm] at hbet2
        -- (y < w ∧ w < z) ∨ (z < w ∧ w < y); `z < w` forces `z < w < y`.
        have hzy : z < y := by
          rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · linarith
        have hcap : lam ≤ y - z := by
          have h := up_cap C hQR.symm hHQ.symm hHR.symm hupRQ hupQH
          rw [phi_comm C hHQ.symm] at h
          rw [abs_of_neg (by linarith : z - y < 0)] at h
          linarith
        obtain ⟨-, hcorr2⟩ := up_corridor C hQR.symm hupRQ
        simp only [← hy_def] at hcorr2
        -- `y ≤ π − λ + θ_Q`.
        -- row `Q` sorted `[t, z, y]` (same order as leaf 1).
        have h1q : dirRep o e (c ∘ v.succAbove) Q P <
            dirRep o e (c ∘ v.succAbove) Q H := by
          rw [phi_comm C hPQ.symm, phi_comm C hHQ.symm]
          simp only [← ht_def, ← hz_def]
          exact htz
        have h2q : dirRep o e (c ∘ v.succAbove) Q H <
            dirRep o e (c ∘ v.succAbove) Q R := by
          rw [phi_comm C hHQ.symm, phi_comm C hQR]
          simp only [← hz_def, ← hy_def]
          exact hzy
        have hnab := five_point_no_adjacent_big C hPQ.symm hHQ.symm hQR
          hQR.symm hPR.symm hQR.symm hHR.symm hPQ hPR h1q h2q hA hQ hR hR hP
        rw [phi_comm C hPQ.symm, phi_comm C hHQ.symm, phi_comm C hQR] at hnab
        simp only [← ht_def, ← hz_def, ← hy_def] at hnab
        exact hnab.2.2 ⟨hcap, by linarith⟩

/-- Legality restricted to the non-anchor subfamily `c ∘ v.succAbove`:
the fields carry over pointwise through the injective reindexing. -/
theorem SatChart.hleg_sub : Section4Legality (c ∘ v.succAbove) lam where
  lam_pos := C.hlam
  inj := fun _ _ h => Fin.succAbove_right_injective (C.hleg.inj h)
  triAngle := fun i j k hij hjk hik =>
    C.hleg.triAngle _ _ _
      (fun hh => hij (Fin.succAbove_right_injective hh))
      (fun hh => hjk (Fin.succAbove_right_injective hh))
      (fun hh => hik (Fin.succAbove_right_injective hh))

/-- **Direction distinctness.** In a legal configuration the outgoing
projective directions from one vertex to two distinct vertices differ:
equal `dirRep` values force the `oangle` between the two chord vectors to
`0` or `π`, so the three points are collinear — excluded by
`legal_triple_not_collinear`. -/
theorem legal_dirRep_ne {s : ℕ} {c' : Fin s → Plane₂} {lam : ℝ}
    (hleg : Section4Legality c' lam) (he : e ≠ 0)
    {i j k : Fin s} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    dirRep o e c' i j ≠ dirRep o e c' i k := by
  intro hdir
  have hX0 : c' j - c' i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hij).symm
  have hY0 : c' k - c' i ≠ 0 := sub_ne_zero.mpr (hleg.inj.ne hik).symm
  have hdir' : linRep (o.oangle e (c' j - c' i)) =
      linRep (o.oangle e (c' k - c' i)) := hdir
  have hcl1 := linRep_class (o.oangle e (c' j - c' i))
  have hcl2 := linRep_class (o.oangle e (c' k - c' i))
  have hXY : o.oangle (c' j - c' i) (c' k - c' i) =
      o.oangle e (c' k - c' i) - o.oangle e (c' j - c' i) := by
    have h := o.oangle_add hX0 he hY0
    rw [o.oangle_rev e (c' j - c' i)] at h
    rw [← h]
    abel
  have hπ : o.oangle (c' j - c' i) (c' k - c' i) = 0 ∨
      o.oangle (c' j - c' i) (c' k - c' i) = (Real.pi : ℝ) := by
    rcases hcl1 with h1 | h1 <;> rcases hcl2 with h2 | h2
    · left
      rw [hXY, ← h1, ← h2, hdir', sub_self]
    · right
      rw [hXY, ← h1, eq_sub_of_add_eq h2.symm, hdir', sub_right_comm,
        sub_self, zero_sub, Real.Angle.neg_coe_pi]
    · right
      rw [hXY, ← h2, eq_sub_of_add_eq h1.symm, hdir', sub_sub_self]
    · left
      rw [hXY, eq_sub_of_add_eq h2.symm, eq_sub_of_add_eq h1.symm, hdir',
        sub_self]
  rcases (o.oangle_eq_zero_or_eq_pi_iff_right_eq_smul).mp hπ with hzero | ⟨r, hr⟩
  · exact hX0 hzero
  · have hk_mem : c' k ∈ affineSpan ℝ ({c' i, c' j} : Set Plane₂) := by
      have hk_eq : c' k = AffineMap.lineMap (c' i) (c' j) r := by
        rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hr]
        abel
      rw [hk_eq]
      exact AffineMap.lineMap_mem_affineSpan_pair r (c' i) (c' j)
    have hcol : Collinear ℝ ({c' i, c' j, c' k} : Set Plane₂) := by
      have h0 := collinear_insert_of_mem_affineSpan_pair hk_mem
      rwa [Set.insert_comm (c' k) (c' i), Set.pair_comm (c' k) (c' j)] at h0
    exact legal_triple_not_collinear hleg hij hik hjk hcol

/-- **Consumer**: a mixed two-in receiver has defect exactly `3`, and the third
direction lies strictly outside the two received directions.

Combines `two_in_mixed_ge_three` (`c_H ≥ 3`), `two_in_mixed_between`
(`c_H > 3` forces `u < z < w`), `mixed_two_in_central` (that position is
impossible), and legality (which gives the direction distinctness
`z ≠ u`, `z ≠ w` via `legal_dirRep_ne`). -/
theorem two_in_mixed_central_exclusion {H P Q R : Fin 4}
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
    (hw : Real.pi - lam < dirRep o e (c ∘ v.succAbove) H R) :
    rowDefect n lam (directionRow o e c (v.succAbove H)) = 3 ∧
      (dirRep o e (c ∘ v.succAbove) H Q < dirRep o e (c ∘ v.succAbove) H P ∨
        dirRep o e (c ∘ v.succAbove) H R < dirRep o e (c ∘ v.succAbove) H Q) := by
  have hswP : ShortWitness (lam := lam) (c := c) o e v theta P H :=
    ⟨hHP.symm, Or.inl hfs⟩
  have hswR : ShortWitness (lam := lam) (c := c) o e v theta R H :=
    ⟨hHR.symm, Or.inr hls⟩
  have hzu : dirRep o e (c ∘ v.succAbove) H Q ≠
      dirRep o e (c ∘ v.succAbove) H P :=
    legal_dirRep_ne C C.hleg_sub C.he hHQ hHP hPQ.symm
  have hzw : dirRep o e (c ∘ v.succAbove) H Q ≠
      dirRep o e (c ∘ v.succAbove) H R :=
    legal_dirRep_ne C C.hleg_sub C.he hHQ hHR hQR
  constructor
  · -- `c_H = 3`: `> 3` would force `z` between the received directions.
    by_contra hne
    have hge := two_in_mixed_ge_three C hHP hHR hHQ hswP hswR hθP hθR hzu hzw
    have hgt : 3 < rowDefect n lam (directionRow o e c (v.succAbove H)) :=
      Nat.lt_of_le_of_ne hge (Ne.symm hne)
    rcases two_in_mixed_between C hHP hHR hHQ hswP hswR hθP hθR hzu hzw hgt with
      ⟨huz, hzw', -, -⟩
    exact mixed_two_in_central C hHP hHQ hHR hPQ hPR hQR hA hH hP hQ hR hfs hls
      hθP hθR hu hu' hw huz hzw'
  · -- `z` is strictly outside `[u, w]`.
    by_contra h
    push_neg at h
    have huz : dirRep o e (c ∘ v.succAbove) H P < dirRep o e (c ∘ v.succAbove) H Q :=
      lt_of_le_of_ne' h.1 hzu
    have hzw' : dirRep o e (c ∘ v.succAbove) H Q < dirRep o e (c ∘ v.succAbove) H R :=
      lt_of_le_of_ne' h.2 hzw.symm
    exact mixed_two_in_central C hHP hHQ hHR hPQ hPR hQR hA hH hP hQ hR hfs hls
      hθP hθR hu hu' hw huz hzw'

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

/-- **Mixed two-in receivers are impossible at a high-defect row.**

Combining `two_in_mixed_central_exclusion` (`c_H = 3` and the third
direction lands strictly outside `u, w`) with `mixed_two_in_outer_low`
and `mixed_two_in_outer_high`, which exclude both outer positions. -/
theorem mixed_two_in_excluded {H P Q R : Fin 4}
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
    (hw : Real.pi - lam < dirRep o e (c ∘ v.succAbove) H R) : False := by
  obtain ⟨-, hout⟩ := two_in_mixed_central_exclusion C hHP hHQ hHR hPQ hPR hQR
    hA hH hP hQ hR hfs hls hθP hθR hu hu' hw
  rcases hout with hzu | hzw
  · exact mixed_two_in_outer_low C hHP hHQ hHR hPQ hPR hQR hA hH hP hQ hR hfs
      hls hθP hθR hu hu' hw hzu
  · exact mixed_two_in_outer_high C hHP hHQ hHR hPQ hPR hQR hA hH hP hQ hR hfs
      hls hθP hθR hu hu' hw hzw

end TwoInCentral

end Jsp404
