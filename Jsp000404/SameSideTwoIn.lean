import Jsp000404.MixedTwoInCentral

/-!
# Same-side two-in receivers (F/F)

Five-point R=3 `SatChart`: anchor defect `1`, receiver `H` defect `≥ 3`,
low rows `A B T` defect `2`.  Both `A → H` and `B → H` are *short-first*
witnesses whose receiver-side chords land in `H`'s F window
(`θ_H < θ_A`, `θ_H < θ_B`; the F/L side follows from
`star_chord_window`).

Both senders are forced short-first, hence `Up H A` and `Up H B`
(`up_of_short_first`).  `two_in_F_above` places the third direction
`z = φ_HT` above both received directions and expresses the defect as
`2 + μ`, `1 ≤ μ ≤ 2`.

The four remaining chords `{H,T}, {A,B}, {A,T}, {B,T}` each carry one of
two `Up` orientations (`up_or_up`); `up_trans`/`up_not_both` kill all
non-transitive triples, leaving the eight total orders compatible with
`Up H A`, `Up H B`.  Direction-layer corridor/cap/betweenness
constraints kill four more, and defect-`2` score equations kill three,
leaving the single residual order

    `Up T H ∧ Up A B ∧ Up T A ∧ Up T B`     — the "T-source" leaf,

proved in `same_side_two_in_F_forces`.  The residual leaf itself is the
open frontier (see `SAME_SIDE_ANALYSIS.md`); direction+score arithmetic
is satisfiable, so it needs distance-closure (sine-rule product) or a
five-point-specific argument — *not* assumed here.
-/

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section SameSideTwoIn

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}

variable (C : SatChart o e n lam c v theta)
include C

/-- Both F-side senders are short-first, so `Up H A` and `Up H B`. -/
theorem ff_sender_ups {H A : Fin 4} (hHA : H ≠ A)
    (hfs : dirRep o e (c ∘ v.succAbove) A H - theta A < lam) :
    Up o e c v H A :=
  up_of_short_first C hHA.symm hfs

/-- The third row cannot also send a short chord into `H`
(`five_point_high_receiver_not_full_in`). -/
theorem ff_notSW {H A B T : Fin 4}
    (hHP : H ≠ A) (hHQ : H ≠ B) (hHR : H ≠ T)
    (hPQ : A ≠ B) (hPR : A ≠ T) (hQR : B ≠ T)
    (hH : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove H)))
    (hPA : rowDefect n lam (directionRow o e c (v.succAbove A)) = 2)
    (hPB : rowDefect n lam (directionRow o e c (v.succAbove B)) = 2)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hfsA : dirRep o e (c ∘ v.succAbove) A H - theta A < lam)
    (hfsB : dirRep o e (c ∘ v.succAbove) B H - theta B < lam) :
    ¬ ShortWitness (lam := lam) (c := c) o e v theta T H := by
  intro hswQ
  have hlow : ∀ j : Fin 4, j ≠ H →
      rowDefect n lam (directionRow o e c (v.succAbove j)) = 2 := by
    intro j hj
    rcases fin4_cover C hHP hHQ hHR hPQ hPR hQR j with rfl | rfl | rfl | rfl
    · exact absurd rfl hj
    · exact hPA
    · exact hPB
    · exact hPT
  have hall : ∀ j : Fin 4, j ≠ H →
      ShortWitness (lam := lam) (c := c) o e v theta j H := by
    intro j hj
    rcases fin4_cover C hHP hHQ hHR hPQ hPR hQR j with rfl | rfl | rfl | rfl
    · exact absurd rfl hj
    · exact ⟨hHP.symm, Or.inl hfsA⟩
    · exact ⟨hHQ.symm, Or.inl hfsB⟩
    · exact hswQ
  exact five_point_high_receiver_not_full_in C H hH hlow hall

/-- `⌊g/λ⌋₊ · λ ≤ g` for `g ≥ 0`. -/
theorem ff_floor_mul_le {g : ℝ} (hg : 0 ≤ g) :
    (⌊g / lam⌋₊ : ℝ) * lam ≤ g :=
  floor_mul_le_gap C.hlam hg

/-- **Budget overflow.**  In a five-point row `[θ, A, B, D]` whose four
anchored gap floors sum to `≥ n + 1`, the gaps (which sum to `π`)
would force `(n+1)λ ≤ π`, contradicting `π < (n+1)λ`.

Combined with `row4_defect`, a defect-`2` row therefore admits at most
*two* gaps with floor `≥ 1`: three `≥ λ` anchored gaps force
`Σ⌊g/λ⌋ ≥ (n−2) + 3 = n+1`. -/
theorem ff_floor_sum_overflow {R a b d : Fin 4} {A B D : ℝ}
    (hha : R ≠ a) (hhb : R ≠ b) (hhd : R ≠ d)
    (h1 : dirRep o e (c ∘ v.succAbove) R a <
      dirRep o e (c ∘ v.succAbove) R b)
    (h2 : dirRep o e (c ∘ v.succAbove) R b <
      dirRep o e (c ∘ v.succAbove) R d)
    (hdef : rowDefect n lam (directionRow o e c (v.succAbove R)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) R a = A)
    (hB : dirRep o e (c ∘ v.succAbove) R b = B)
    (hD : dirRep o e (c ∘ v.succAbove) R d = D)
    (hsum : n + 1 ≤ ⌊(A - theta R) / lam⌋₊ + ⌊(B - A) / lam⌋₊ +
      ⌊(D - B) / lam⌋₊ + ⌊(theta R + Real.pi - D) / lam⌋₊) :
    False := by
  have hpi := pi_lt_succ_mul C C.hn
  have hθ0 := (C.htheta R).1.1
  have hθβ := (C.htheta R).1.2
  have hA0 : 0 ≤ A := by rw [← hA]; exact (phi_mem C R a).1
  have hB0 : 0 ≤ B := by rw [← hB]; exact (phi_mem C R b).1
  have hDπ : D < Real.pi := by rw [← hD]; exact (phi_mem C R d).2
  have hAlam : lam ≤ A := by rw [← hA]; exact phi_ge_lam C hha
  have hβ := C.hβ
  have hg0 : 0 ≤ A - theta R := by linarith
  have h12 : A < B ∧ B < D := ⟨by rwa [hA, hB] at h1, by rwa [hB, hD] at h2⟩
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta R + Real.pi - D := by linarith
  have f0 := ff_floor_mul_le C hg0
  have f1 := ff_floor_mul_le C hg1
  have f2 := ff_floor_mul_le C hg2
  have f3 := ff_floor_mul_le C hg3
  have hsum' : (n + 1 : ℝ) * lam ≤
      (⌊(A - theta R) / lam⌋₊ + ⌊(B - A) / lam⌋₊ +
        ⌊(D - B) / lam⌋₊ + ⌊(theta R + Real.pi - D) / lam⌋₊ : ℕ) * lam := by
    have h' : (n + 1 : ℝ) ≤
        (⌊(A - theta R) / lam⌋₊ + ⌊(B - A) / lam⌋₊ +
          ⌊(D - B) / lam⌋₊ + ⌊(theta R + Real.pi - D) / lam⌋₊ : ℕ) := by
      exact_mod_cast hsum
    exact mul_le_mul_of_nonneg_right h' C.hlam.le
  push_cast at hsum'
  nlinarith

/-- `Up B A` is impossible: `up_trans` on `H → B → A` forces
`φ_BA < φ_HA < φ_HB`, but the corridor on `B → A` plus the sender
short-first bound `φ_BH − θ_B < λ` force `φ_BA > φ_HB`. -/
theorem ff_not_upBA {H A B : Fin 4} (hHA : H ≠ A) (hHB : H ≠ B)
    (hAB : A ≠ B)
    (hfsB : dirRep o e (c ∘ v.succAbove) B H - theta B < lam)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hupBA : Up o e c v B A) : False := by
  have hupHB : Up o e c v H B := up_of_short_first C hHB.symm hfsB
  obtain ⟨-, hbet⟩ := up_trans C hHB hAB.symm hHA hupHB hupBA
  rw [phi_comm C hAB.symm] at hbet
  -- hbet : (φ_HB < φ_HA < φ_AB) ∨ (φ_AB < φ_HA < φ_HB); u < w kills 1st.
  have hplt : dirRep o e (c ∘ v.succAbove) A B <
      dirRep o e (c ∘ v.succAbove) H A := by
    rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact h1
  obtain ⟨hcor, -⟩ := up_corridor C hAB.symm hupBA
  rw [phi_comm C hAB.symm] at hcor
  have hfsB' : dirRep o e (c ∘ v.succAbove) H B - theta B < lam := by
    rwa [← phi_comm C hHB.symm]
  linarith

/-- **Leaf O6**: `Up H T ∧ Up T A ∧ Up T B ∧ Up A B`.
Row `T` has three `≥ λ` anchored gaps regardless of the `x/y` order:
its defect-`2` budget overflows. -/
theorem ff_leaf_O6 {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzw : dirRep o e (c ∘ v.succAbove) H B <
      dirRep o e (c ∘ v.succAbove) H T)
    (hupHT : Up o e c v H T) (hupTA : Up o e c v T A)
    (hupTB : Up o e c v T B) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  -- Corridors: g0, g3 of row T.
  obtain ⟨hcTA1, -⟩ := up_corridor C hAT.symm hupTA
  rw [phi_comm C hAT.symm] at hcTA1
  obtain ⟨hcTB1, -⟩ := up_corridor C hBT.symm hupTB
  rw [phi_comm C hBT.symm] at hcTB1
  obtain ⟨-, hcHT2⟩ := up_corridor C hHT hupHT
  rw [phi_comm C hHT] at hcHT2
  -- Caps: |z - x|, |z - y| ≥ λ.
  have hcapx : lam ≤ |dirRep o e (c ∘ v.succAbove) T A -
      dirRep o e (c ∘ v.succAbove) H T| :=
    up_cap C hHT hAT.symm hHA hupHT hupTA
  rw [phi_comm C hAT.symm] at hcapx
  simp only [← hx_def, ← hz_def] at hcapx
  have hcapy : lam ≤ |dirRep o e (c ∘ v.succAbove) T B -
      dirRep o e (c ∘ v.succAbove) H T| :=
    up_cap C hHT hBT.symm hHB hupHT hupTB
  rw [phi_comm C hBT.symm] at hcapy
  simp only [← hy_def, ← hz_def] at hcapy
  -- Betweenness on H: `x < u < z` and `y < w < z`.
  obtain ⟨-, hbetA⟩ := up_trans C hHT hAT.symm hHA hupHT hupTA
  rw [phi_comm C hAT.symm] at hbetA
  simp only [← hx_def] at hbetA
  have huxz : x < u ∧ u < z := by
    rcases hbetA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith [hzw, hord]
    · exact ⟨h1, h2⟩
  obtain ⟨-, hbetB⟩ := up_trans C hHT hBT.symm hHB hupHT hupTB
  rw [phi_comm C hBT.symm] at hbetB
  simp only [← hy_def] at hbetB
  have hywz : y < w ∧ w < z := by
    rcases hbetB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith [hzw]
    · exact ⟨h1, h2⟩
  -- The `x ≠ y` direction distinctness.
  have hdxy' := legal_dirRep_ne C C.hleg C.he
    (show v.succAbove T ≠ v.succAbove A from
      fun h => hAT (Fin.succAbove_right_injective h).symm)
    (show v.succAbove T ≠ v.succAbove B from
      fun h => hBT (Fin.succAbove_right_injective h).symm)
    (show v.succAbove A ≠ v.succAbove B from
      fun h => hAB (Fin.succAbove_right_injective h))
  have hdxy : dirRep o e (c ∘ v.succAbove) T A ≠
      dirRep o e (c ∘ v.succAbove) T B := hdxy'
  -- Both `x < y` and `y < x` give three `≥ λ` gaps on row `T`.
  rcases lt_trichotomy x y with hlt | heq | hgt
  · -- row `T` = [x, y, z]: big gaps g0, g2, g3.
    have h1T : dirRep o e (c ∘ v.succAbove) T A <
        dirRep o e (c ∘ v.succAbove) T B := by
      rw [phi_comm C hAT.symm, phi_comm C hBT.symm]; exact hlt
    have h2T : dirRep o e (c ∘ v.succAbove) T B <
        dirRep o e (c ∘ v.succAbove) T H := by
      rw [phi_comm C hBT.symm, ← phi_comm C hHT]; linarith [hywz.2]
    have hrowT := row4_defect C rfl (hAT.symm) (hBT.symm) (hHT.symm) h1T h2T
    rw [hPT] at hrowT
    rw [phi_comm C hAT.symm, phi_comm C hBT.symm, ← phi_comm C hHT] at hrowT
    simp only [← hx_def, ← hy_def, ← hz_def] at hrowT
    -- floors ≥ 1 on gaps 0, 2, 3.
    have hf0 : 1 ≤ ⌊(x - theta T) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
    have hf2 : 1 ≤ ⌊(z - y) / lam⌋₊ := (one_le_floor_iff_ge lam _ C.hlam).mpr
      (by rw [abs_of_neg (by linarith : y - z < 0)] at hcapy; linarith)
    have hzcap : z ≤ Real.pi - lam + theta T := by
      rw [hz_def, phi_comm C hHT]; exact hcHT2
    have hf3 : 1 ≤ ⌊(theta T + Real.pi - z) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
    -- `2 + Σ (fᵢ − 1) = n` with three fᵢ ≥ 1 forces `Σ fᵢ ≥ n + 1`.
    have hsum : n + 1 ≤ ⌊(x - theta T) / lam⌋₊ + ⌊(y - x) / lam⌋₊ +
        ⌊(z - y) / lam⌋₊ + ⌊(theta T + Real.pi - z) / lam⌋₊ := by omega
    exact ff_floor_sum_overflow C hAT.symm hBT.symm hHT.symm h1T h2T hPT
      (phi_comm C hAT.symm) (phi_comm C hBT.symm) (phi_comm C hHT.symm) hsum
  · rw [phi_comm C hAT.symm, phi_comm C hBT.symm] at hdxy
    simp only [← hx_def, ← hy_def] at hdxy
    exact absurd heq hdxy
  · -- row `T` = [y, x, z]: big gaps g0, g2, g3.
    have h1T : dirRep o e (c ∘ v.succAbove) T B <
        dirRep o e (c ∘ v.succAbove) T A := by
      rw [phi_comm C hBT.symm, phi_comm C hAT.symm]; exact hgt
    have h2T : dirRep o e (c ∘ v.succAbove) T A <
        dirRep o e (c ∘ v.succAbove) T H := by
      rw [phi_comm C hAT.symm, ← phi_comm C hHT]; linarith [huxz.2]
    have hrowT := row4_defect C rfl (hBT.symm) (hAT.symm) (hHT.symm) h1T h2T
    rw [hPT] at hrowT
    rw [phi_comm C hBT.symm, phi_comm C hAT.symm, ← phi_comm C hHT] at hrowT
    simp only [← hx_def, ← hy_def, ← hz_def] at hrowT
    have hf0 : 1 ≤ ⌊(y - theta T) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
    have hf2 : 1 ≤ ⌊(z - x) / lam⌋₊ := (one_le_floor_iff_ge lam _ C.hlam).mpr
      (by rw [abs_of_neg (by linarith : x - z < 0)] at hcapx; linarith)
    have hzcap : z ≤ Real.pi - lam + theta T := by
      rw [hz_def, phi_comm C hHT]; exact hcHT2
    have hf3 : 1 ≤ ⌊(theta T + Real.pi - z) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
    have hsum : n + 1 ≤ ⌊(y - theta T) / lam⌋₊ + ⌊(x - y) / lam⌋₊ +
        ⌊(z - x) / lam⌋₊ + ⌊(theta T + Real.pi - z) / lam⌋₊ := by omega
    exact ff_floor_sum_overflow C hBT.symm hAT.symm hHT.symm h1T h2T hPT
      (phi_comm C hBT.symm) (phi_comm C hAT.symm) (phi_comm C hHT.symm) hsum

end SameSideTwoIn

end Jsp404
