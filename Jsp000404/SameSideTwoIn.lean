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

/-- A directed 3-cycle of `Up` is impossible: two applications of
`up_trans` force `φ_ik` strictly between `φ_ij, φ_jk` and `φ_ji`
strictly between `φ_jk, φ_ki`; since `φ_ij = φ_ji` and `φ_ki = φ_ik`
all four disjunct combinations contradict each other. -/
theorem up_not_cycle3 {i j k : Fin 4} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k)
    (h1 : Up o e c v i j) (h2 : Up o e c v j k)
    (h3 : Up o e c v k i) : False := by
  obtain ⟨-, hb1⟩ := up_trans C hij hjk hik h1 h2
  obtain ⟨-, hb2⟩ := up_trans C hjk hik.symm hij.symm h2 h3
  rw [← phi_comm C hij, ← phi_comm C hik] at hb2
  rcases hb1 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    rcases hb2 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> linarith

/-- **Leaf O7**: `Up H T ∧ Up A T ∧ Up T B ∧ Up H A`.
Row `T` sorted order is `φ_TB < φ_TH < φ_TA`: the corridor on
`T → B` gives `g0 ≥ λ`, the `H → T → B` cap gives `g1 ≥ λ`, and the
corridor on `A → T` gives `g3 ≥ λ`.  The defect-`2` budget overflows. -/
theorem ff_leaf_O7 {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzw : dirRep o e (c ∘ v.succAbove) H B <
      dirRep o e (c ∘ v.succAbove) H T)
    (hupHA : Up o e c v H A) (hupHT : Up o e c v H T)
    (hupAT : Up o e c v A T) (hupTB : Up o e c v T B) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  -- `y < w < z` from betweenness on `H → T → B`.
  obtain ⟨-, hbetB⟩ := up_trans C hHT hBT.symm hHB hupHT hupTB
  rw [phi_comm C hBT.symm] at hbetB
  simp only [← hy_def] at hbetB
  have hywz : y < w ∧ w < z := by
    rcases hbetB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith [hzw]
    · exact ⟨h1, h2⟩
  -- `u < z < x` from betweenness on `H → A → T`.
  obtain ⟨-, hbetA⟩ := up_trans C hHA hAT hHT hupHA hupAT
  simp only [← hx_def] at hbetA
  have huzx : z < x := by
    rcases hbetA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith [h1, hzw, hord]
    · linarith [h2, hzw, hord]
  -- Row `T` sorted: `y < z < x`.
  have h1T : dirRep o e (c ∘ v.succAbove) T B <
      dirRep o e (c ∘ v.succAbove) T H := by
    rw [phi_comm C hBT.symm, ← phi_comm C hHT]; linarith [hywz.1, hzw]
  have h2T : dirRep o e (c ∘ v.succAbove) T H <
      dirRep o e (c ∘ v.succAbove) T A := by
    rw [← phi_comm C hHT, phi_comm C hAT.symm]; linarith [huzx, hzw]
  have hrowT := row4_defect C rfl (hBT.symm) (hHT.symm) (hAT.symm) h1T h2T
  rw [hPT] at hrowT
  rw [phi_comm C hBT.symm, ← phi_comm C hHT, phi_comm C hAT.symm] at hrowT
  simp only [← hx_def, ← hy_def, ← hz_def] at hrowT
  -- Big gaps: `g0 = y − θ_T` (corridor `T → B`), `g1 = z − y` (cap),
  -- `g3 = θ_T + π − x` (corridor `A → T`).
  obtain ⟨hcTB1, -⟩ := up_corridor C hBT.symm hupTB
  rw [phi_comm C hBT.symm] at hcTB1
  obtain ⟨-, hcAT2⟩ := up_corridor C hAT hupAT
  have hcap : lam ≤ |dirRep o e (c ∘ v.succAbove) T B -
      dirRep o e (c ∘ v.succAbove) H T| :=
    up_cap C hHT hBT.symm hHB hupHT hupTB
  rw [phi_comm C hBT.symm] at hcap
  simp only [← hy_def, ← hz_def] at hcap
  rw [abs_of_neg (by linarith [hywz.1, hzw] : y - z < 0)] at hcap
  have hf0 : 1 ≤ ⌊(y - theta T) / lam⌋₊ :=
    (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
  have hf1 : 1 ≤ ⌊(z - y) / lam⌋₊ :=
    (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
  have hf3 : 1 ≤ ⌊(theta T + Real.pi - x) / lam⌋₊ :=
    (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
  have hsum : n + 1 ≤ ⌊(y - theta T) / lam⌋₊ + ⌊(z - y) / lam⌋₊ +
      ⌊(x - z) / lam⌋₊ + ⌊(theta T + Real.pi - x) / lam⌋₊ := by omega
  exact ff_floor_sum_overflow C hBT.symm hHT.symm hAT.symm h1T h2T hPT
    (phi_comm C hBT.symm) (phi_comm C hHT.symm) (phi_comm C hAT.symm) hsum

/-- **Leaf O8**: `Up` on every chord (`H → A → B → T` total order).
Betweenness forces `w < p := φ_AB` and `z < y := φ_BT`, so row `B`
splits into two sorted arrangements:

* `y < p`: row `B = [w, y, p]` has three `≥ λ` anchored gaps (caps on
  `H → B → T`, `A → B → T`, corridor upper bound on `A → B`) — direct
  budget overflow.
* `p < y`: row `B = [w, p, y]` with `g2 = y − p ≥ λ` (cap) and
  `g0 < λ` (short-first).  A case split on which of `g1, g3` reach `λ`
  kills every sub-case by a short chain through the defect-`2` score
  equation — all for arbitrary `n`, using only `π < (n+1)λ` and
  `θ ≤ β = π − nλ`. -/
theorem ff_leaf_O8 {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPB : rowDefect n lam (directionRow o e c (v.succAbove B)) = 2)
    (hfsB : dirRep o e (c ∘ v.succAbove) B H - theta B < lam)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzw : dirRep o e (c ∘ v.succAbove) H B <
      dirRep o e (c ∘ v.succAbove) H T)
    (hupHA : Up o e c v H A) (hupHB : Up o e c v H B)
    (hupHT : Up o e c v H T) (hupAB : Up o e c v A B)
    (hupAT : Up o e c v A T) (hupBT : Up o e c v B T) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set p := dirRep o e (c ∘ v.succAbove) A B with hp_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  -- Betweenness: `w` sits strictly between `u` and `p` (`H → A → B`),
  -- `z` sits strictly between `w` and `y` (`H → B → T`), and `x` sits
  -- strictly between `p` and `y` (`A → B → T`).
  obtain ⟨-, hbet1⟩ := up_trans C hHA hAB hHB hupHA hupAB
  simp only [← hu_def, ← hw_def, ← hp_def] at hbet1
  have hwp : w < p := by
    rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · linarith [hord]
  obtain ⟨-, hbet4⟩ := up_trans C hHB hBT hHT hupHB hupBT
  simp only [← hw_def, ← hz_def, ← hy_def] at hbet4
  have hzy : z < y := by
    rcases hbet4 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · linarith [hzw]
  obtain ⟨-, hbet3⟩ := up_trans C hAB hBT hAT hupAB hupBT
  simp only [← hp_def, ← hx_def, ← hy_def] at hbet3
  -- Caps and corridors.
  have hcap1 : lam ≤ p - u := by
    have hc := up_cap C hHA hAB hHB hupHA hupAB
    simp only [← hu_def, ← hp_def] at hc
    rw [abs_of_pos (by linarith [hwp, hord] : (0 : ℝ) < p - u)] at hc
    exact hc
  have hcapw : lam ≤ y - w := by
    have hc := up_cap C hHB hBT hHT hupHB hupBT
    simp only [← hw_def, ← hy_def] at hc
    rw [abs_of_pos (by linarith [hzy, hzw] : (0 : ℝ) < y - w)] at hc
    exact hc
  have hcap2 : lam ≤ |y - p| := by
    have hc := up_cap C hAB hBT hAT hupAB hupBT
    simpa only [← hp_def, ← hy_def] using hc
  obtain ⟨hcHA1, -⟩ := up_corridor C hHA hupHA
  obtain ⟨hcHB1, -⟩ := up_corridor C hHB hupHB
  obtain ⟨-, hcAB2⟩ := up_corridor C hAB hupAB
  simp only [← hu_def] at hcHA1
  simp only [← hw_def] at hcHB1
  simp only [← hp_def] at hcAB2
  -- Global facts.
  have hpi := pi_lt_succ_mul C C.hn
  have hθH0 := (C.htheta H).1.1
  have hθB0 := (C.htheta B).1.1
  have hθBβ := (C.htheta B).1.2
  have hβ := C.hβ
  have hyπ : y < Real.pi := by
    have h := (phi_mem C B T).2
    rwa [← hy_def] at h
  have hfsBw : w - theta B < lam := by
    have h := hfsB
    rw [phi_comm C hHB.symm] at h
    rwa [← hw_def] at h
  have hf0 : ⌊(w - theta B) / lam⌋₊ = 0 := by
    have hlt : ¬ 1 ≤ ⌊(w - theta B) / lam⌋₊ := by
      rw [one_le_floor_iff_ge lam _ C.hlam]; linarith [hfsBw]
    omega
  -- The `p = y` degenerate case dies to betweenness; otherwise row `B`
  -- is sorted `[w, y, p]` (`y < p`) or `[w, p, y]` (`p < y`).
  rcases lt_trichotomy y p with hyp | hyp | hyp
  · -- **Case `y < p`**: row `B = [w, y, p]`, three `≥ λ` gaps.
    have h1B : dirRep o e (c ∘ v.succAbove) B H <
        dirRep o e (c ∘ v.succAbove) B T := by
      rw [phi_comm C hHB.symm]
      linarith [hzy, hzw]
    have h2B : dirRep o e (c ∘ v.succAbove) B T <
        dirRep o e (c ∘ v.succAbove) B A := by
      rw [phi_comm C hAB.symm]
      exact hyp
    have hrowB := row4_defect C rfl hHB.symm hBT hAB.symm h1B h2B
    rw [hPB] at hrowB
    rw [phi_comm C hHB.symm, phi_comm C hAB.symm] at hrowB
    simp only [← hw_def, ← hp_def, ← hy_def] at hrowB
    have hcap2' : lam ≤ p - y := by
      rw [abs_of_neg (by linarith : y - p < 0)] at hcap2
      linarith
    have hf1 : 1 ≤ ⌊(y - w) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr hcapw
    have hf2 : 1 ≤ ⌊(p - y) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr hcap2'
    have hf3 : 1 ≤ ⌊(theta B + Real.pi - p) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith [hcAB2])
    have hsum : n + 1 ≤ ⌊(w - theta B) / lam⌋₊ + ⌊(y - w) / lam⌋₊ +
        ⌊(p - y) / lam⌋₊ + ⌊(theta B + Real.pi - p) / lam⌋₊ := by omega
    exact ff_floor_sum_overflow C hHB.symm hBT hAB.symm h1B h2B hPB
      (phi_comm C hHB.symm) rfl (phi_comm C hAB.symm) hsum
  · -- **`p = y`**: `x` is strictly between `p` and `y`.
    rcases hbet3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · -- **Case `p < y`**: row `B = [w, p, y]`, score case split.
    have h1B : dirRep o e (c ∘ v.succAbove) B H <
        dirRep o e (c ∘ v.succAbove) B A := by
      rw [phi_comm C hHB.symm, phi_comm C hAB.symm]
      exact hwp
    have h2B : dirRep o e (c ∘ v.succAbove) B A <
        dirRep o e (c ∘ v.succAbove) B T := by
      rw [phi_comm C hAB.symm]
      exact hyp
    have hrowB := row4_defect C rfl hHB.symm hAB.symm hBT h1B h2B
    rw [hPB] at hrowB
    rw [phi_comm C hHB.symm, phi_comm C hAB.symm] at hrowB
    simp only [← hw_def, ← hp_def, ← hy_def] at hrowB
    have hcap2' : lam ≤ y - p := by
      rw [abs_of_pos (by linarith : (0 : ℝ) < y - p)] at hcap2
      exact hcap2
    have hf2 : 1 ≤ ⌊(y - p) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ C.hlam).mpr hcap2'
    have h2m := ff_floor_mul_le C (show (0 : ℝ) ≤ y - p by linarith)
    by_cases hg1 : lam ≤ p - w
    · by_cases hg3 : lam ≤ theta B + Real.pi - y
      · -- `g1, g2, g3` all `≥ λ`: three big gaps, budget overflows.
        have hf1 : 1 ≤ ⌊(p - w) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hg1
        have hf3 : 1 ≤ ⌊(theta B + Real.pi - y) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hg3
        have hsum : n + 1 ≤ ⌊(w - theta B) / lam⌋₊ + ⌊(p - w) / lam⌋₊ +
            ⌊(y - p) / lam⌋₊ + ⌊(theta B + Real.pi - y) / lam⌋₊ := by omega
        exact ff_floor_sum_overflow C hHB.symm hAB.symm hBT h1B h2B hPB
          (phi_comm C hHB.symm) (phi_comm C hAB.symm) rfl hsum
      · -- `g1, g2 ≥ λ`, `g3 < λ`: score forces `f1 + f2 = n`, but then
        -- `y ≥ w + nλ ≥ θ_H + (n+1)λ > π`.
        have hf1 : 1 ≤ ⌊(p - w) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hg1
        have hf3 : ⌊(theta B + Real.pi - y) / lam⌋₊ = 0 := by
          have hlt : ¬ 1 ≤ ⌊(theta B + Real.pi - y) / lam⌋₊ := by
            rw [one_le_floor_iff_ge lam _ C.hlam]; exact hg3
          omega
        have hK : ⌊(p - w) / lam⌋₊ + ⌊(y - p) / lam⌋₊ = n := by omega
        have hK' : (⌊(p - w) / lam⌋₊ : ℝ) + (⌊(y - p) / lam⌋₊ : ℝ) = n := by
          exact_mod_cast hK
        have h1m := ff_floor_mul_le C (show (0 : ℝ) ≤ p - w by linarith)
        have hle : (n : ℝ) * lam ≤ y - w := by
          have h' := add_le_add h1m h2m
          rw [← add_mul, hK'] at h'
          linarith
        linarith [hcHB1]
    · by_cases hg3 : lam ≤ theta B + Real.pi - y
      · -- `g2, g3 ≥ λ`, `g1 < λ`: score forces `f2 + f3 = n`, but then
        -- `p ≤ θ_B + β` while `p ≥ θ_H + 2λ` and `β < λ`.
        have hf1 : ⌊(p - w) / lam⌋₊ = 0 := by
          have hlt : ¬ 1 ≤ ⌊(p - w) / lam⌋₊ := by
            rw [one_le_floor_iff_ge lam _ C.hlam]; exact hg1
          omega
        have hf3 : 1 ≤ ⌊(theta B + Real.pi - y) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hg3
        have hK : ⌊(y - p) / lam⌋₊ + ⌊(theta B + Real.pi - y) / lam⌋₊ = n := by
          omega
        have hK' : (⌊(y - p) / lam⌋₊ : ℝ) +
            (⌊(theta B + Real.pi - y) / lam⌋₊ : ℝ) = n := by
          exact_mod_cast hK
        have h3m := ff_floor_mul_le C
          (show (0 : ℝ) ≤ theta B + Real.pi - y by linarith)
        have hle : (n : ℝ) * lam ≤ theta B + Real.pi - p := by
          have h' := add_le_add h2m h3m
          rw [← add_mul, hK'] at h'
          linarith
        linarith [hcap1, hcHA1, hθBβ]
      · -- Only `g2 ≥ λ`: score forces `f2 = n − 1`, but then
        -- `y ≥ p + (n−1)λ ≥ θ_H + (n+1)λ > π`.
        have hf1 : ⌊(p - w) / lam⌋₊ = 0 := by
          have hlt : ¬ 1 ≤ ⌊(p - w) / lam⌋₊ := by
            rw [one_le_floor_iff_ge lam _ C.hlam]; exact hg1
          omega
        have hf3 : ⌊(theta B + Real.pi - y) / lam⌋₊ = 0 := by
          have hlt : ¬ 1 ≤ ⌊(theta B + Real.pi - y) / lam⌋₊ := by
            rw [one_le_floor_iff_ge lam _ C.hlam]; exact hg3
          omega
        have hK : ⌊(y - p) / lam⌋₊ + 1 = n := by omega
        have hK' : (⌊(y - p) / lam⌋₊ : ℝ) + 1 = n := by exact_mod_cast hK
        have hle : (n : ℝ) * lam - lam ≤ y - p := by
          have h' : (⌊(y - p) / lam⌋₊ : ℝ) * lam + 1 * lam = (n : ℝ) * lam := by
            rw [← add_mul, hK']
          linarith [h2m]
        linarith [hcap1, hcHA1, hθH0, hyπ, hpi]

/-- **F/F orientation reduction.**  With `Up H A`, `Up H B` fixed (the
senders are short-first) and `φ_HA < φ_HB < φ_HT`, each of the four
remaining chords `{H,T}, {A,B}, {A,T}, {B,T}` is oriented one of two
ways (`up_or_up`).  Fifteen of the sixteen combinations are closed:

* every combination containing `Up B A` dies to `ff_not_upBA`;
* two cycle combinations die to `up_not_cycle3` / transitivity;
* O8 (all-Up), O7 (`H ≺ A ≺ T ≺ B`) and O6 (`H ≺ T ≺ A ≺ B`) die to
  `ff_leaf_O8`, `ff_leaf_O7`, `ff_leaf_O6`.

The unique residual is the **T-source leaf**: `Up T H`, `Up T A`,
`Up T B` (with `Up A B`), returned here as the remaining obligation —
it is the real mathematical frontier (see `SAME_SIDE_ANALYSIS.md`). -/
theorem ff_reduces_to_Tsource {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPB : rowDefect n lam (directionRow o e c (v.succAbove B)) = 2)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hfsB : dirRep o e (c ∘ v.succAbove) B H - theta B < lam)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzw : dirRep o e (c ∘ v.succAbove) H B <
      dirRep o e (c ∘ v.succAbove) H T)
    (hupHA : Up o e c v H A) (hupHB : Up o e c v H B) :
    Up o e c v T H ∧ Up o e c v T A ∧ Up o e c v T B ∧ Up o e c v A B := by
  rcases up_or_up C hHT with hupHT | hupTH
  · rcases up_or_up C hAB with hupAB | hupBA
    · rcases up_or_up C hAT with hupAT | hupTA
      · rcases up_or_up C hBT with hupBT | hupTB
        · -- `H ≺ A ≺ B ≺ T`: all-Up leaf O8.
          exact (ff_leaf_O8 C hHA hHB hHT hAB hAT hBT hPB hfsB hord hzw
            hupHA hupHB hupHT hupAB hupAT hupBT).elim
        · -- `H ≺ A ≺ T ≺ B`: leaf O7.
          exact (ff_leaf_O7 C hHA hHB hHT hAB hAT hBT hPT hord hzw
            hupHA hupHT hupAT hupTB).elim
      · rcases up_or_up C hBT with hupBT | hupTB
        · -- Cycle `B ≺ T ≺ A ≺ B`.
          exact (up_not_cycle3 C hBT hAT.symm hAB.symm hupBT hupTA hupAB).elim
        · -- `H ≺ T ≺ A ≺ B`: leaf O6.
          exact (ff_leaf_O6 C hHA hHB hHT hAB hAT hBT hPT hord hzw
            hupHT hupTA hupTB).elim
    · rcases up_or_up C hAT with hupAT | hupTA <;>
        rcases up_or_up C hBT with hupBT | hupTB <;>
        exact (ff_not_upBA C hHA hHB hAB hfsB hord hupBA).elim
  · rcases up_or_up C hAB with hupAB | hupBA
    · rcases up_or_up C hAT with hupAT | hupTA
      · rcases up_or_up C hBT with hupBT | hupTB
        · -- `B ≺ T ≺ H` forces `Up B H`, contradicting `Up H B`.
          obtain ⟨hBH, -⟩ := up_trans C hBT hHT.symm hHB.symm hupBT hupTH
          exact (up_not_both C hHB hupHB hBH).elim
        · -- `T ≺ H ≺ A` forces `Up T A`, contradicting `Up A T`.
          obtain ⟨hTA, -⟩ := up_trans C hHT.symm hHA hAT.symm hupTH hupHA
          exact (up_not_both C hAT hupAT hTA).elim
      · rcases up_or_up C hBT with hupBT | hupTB
        · -- `B ≺ T ≺ A` forces `Up B A` (short-first kill).
          obtain ⟨hBA, -⟩ := up_trans C hBT hAT.symm hAB.symm hupBT hupTA
          exact (ff_not_upBA C hHA hHB hAB hfsB hord hBA).elim
        · -- Residual: the T-source leaf.
          exact ⟨hupTH, hupTA, hupTB, hupAB⟩
    · rcases up_or_up C hAT with hupAT | hupTA <;>
        rcases up_or_up C hBT with hupBT | hupTB <;>
        exact (ff_not_upBA C hHA hHB hAB hfsB hord hupBA).elim

/-! ### Metric closure infrastructure (sine-rule)

The T-source residual is not killed by direction+score arithmetic; it
needs the distance consistency of the four points: every chord `(i,j)`
satisfies `r_i·sin(φ − θ_i) = r_j·sin(φ − θ_j)` (both equal the doubled
oriented area `areaForm w_i w_j` divided by the chord length).  Cycling
through a triangle forces the sine product around the triangle to be `1`,
and in the T-source order the two sides differ by a strict Schur
transfer. -/

/-- Fixed-sum Schur step for `sin`: moving `δ` from the larger to the
smaller of two angles strictly increases their sine product. -/
theorem sin_mul_sin_lt_of_transfer {x y δ : ℝ} (hδ : 0 < δ)
    (hδxy : δ < y - x) (hxy : y - x ≤ Real.pi) :
    Real.sin x * Real.sin y < Real.sin (x + δ) * Real.sin (y - δ) := by
  have hneg : x - y < 0 := by linarith
  have hnew : |x - y + 2 * δ| < |x - y| := by
    rw [abs_of_neg hneg, abs_lt]
    constructor <;> linarith
  have hcos : Real.cos (x - y) < Real.cos (x - y + 2 * δ) := by
    rw [← Real.cos_abs (x - y), ← Real.cos_abs (x - y + 2 * δ)]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by rw [abs_of_neg hneg]; linarith) hnew
  have prod : ∀ a b : ℝ, 2 * (Real.sin a * Real.sin b) =
      Real.cos (a - b) - Real.cos (a + b) := by
    intro a b; rw [Real.cos_sub, Real.cos_add]; ring
  have e1 := prod (x + δ) (y - δ)
  have e2 := prod x y
  rw [show x + δ - (y - δ) = x - y + 2 * δ by ring,
      show x + δ + (y - δ) = x + y by ring] at e1
  linarith

/-- Signed area via `areaForm`: `ω x y = ‖x‖·‖y‖·sin(oangle x y)`. -/
theorem areaForm_eq_sin_oangle_mul (x y : Plane₂) :
    o.areaForm x y = Real.Angle.sin (o.oangle x y) * (‖x‖ * ‖y‖) := by
  have him : (o.kahler x y).im = o.areaForm x y := by
    rw [Orientation.kahler_apply_apply]; simp
  have hsin : Real.Angle.sin (o.oangle x y) =
      (o.kahler x y).im / (‖x‖ * ‖y‖) := by
    show Real.Angle.sin (Complex.arg (o.kahler x y) : Real.Angle) = _
    rw [Real.Angle.sin_coe, Complex.sin_arg, o.norm_kahler]
  rw [hsin, him]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  exact (div_mul_cancel₀ _ (mul_ne_zero (norm_ne_zero_iff.mpr hx)
    (norm_ne_zero_iff.mpr hy))).symm

/-- Chord viewing identity: the two endpoints see the chord `(i,j)`
under the same perpendicular distance, giving the sine ratio
`r_i·sin(φ_ij − θ_i) = r_j·sin(φ_ij − θ_j)` for `φ = dirRep i j`. -/
theorem chord_view_sin {i j : Fin 4} (hij : i ≠ j) :
    ‖c (v.succAbove i) - c v‖ * Real.sin (dirRep o e (c ∘ v.succAbove) i j
        - theta i)
      = ‖c (v.succAbove j) - c v‖ *
        Real.sin (dirRep o e (c ∘ v.succAbove) i j - theta j) := by
  classical
  set wi := c (v.succAbove i) - c v with hwi
  set wj := c (v.succAbove j) - c v with hwj
  set wij := c (v.succAbove j) - c (v.succAbove i) with hwij
  set φ := dirRep o e (c ∘ v.succAbove) i j with hφ
  have hsub : wij = wj - wi := by simp only [hwij, hwi, hwj]; abel
  have hwi0 : wi ≠ 0 := sub_ne_zero.mpr (C.pt_ne_anchor i)
  have hwj0 : wj ≠ 0 := sub_ne_zero.mpr (C.pt_ne_anchor j)
  have hwij0 : wij ≠ 0 := sub_ne_zero.mpr (C.pt_ne hij).symm
  -- oangle relations
  have ho_i : o.oangle e wi = (theta i : Real.Angle) := (C.htheta i).2
  have ho_j : o.oangle e wj = (theta j : Real.Angle) := (C.htheta j).2
  have hoi : o.oangle wi wij = o.oangle e wij - (theta i : Real.Angle) := by
    have h := o.oangle_add C.he hwi0 hwij0
    -- h : oangle e wi + oangle wi wij = oangle e wij
    rw [ho_i] at h
    have : o.oangle wi wij = o.oangle e wij - (theta i : Real.Angle) := by
      rw [← h]; abel
    exact this
  have hoj : o.oangle wj wij = o.oangle e wij - (theta j : Real.Angle) := by
    have h := o.oangle_add C.he hwj0 hwij0
    rw [ho_j] at h
    have : o.oangle wj wij = o.oangle e wij - (theta j : Real.Angle) := by
      rw [← h]; abel
    exact this
  -- areaForm of both views equals ω wi wj
  have hFi : o.areaForm wi wij = o.areaForm wi wj := by
    rw [hsub, map_sub, o.areaForm_apply_self, sub_zero]
  have hFj : o.areaForm wj wij = o.areaForm wi wj := by
    rw [hsub, map_sub, o.areaForm_apply_self, zero_sub,
      o.areaForm_swap, neg_neg]
  -- Expand both sides via the sine-oangle formula
  have key : ‖wi‖ * Real.Angle.sin (o.oangle wi wij)
      = ‖wj‖ * Real.Angle.sin (o.oangle wj wij) := by
    have e1 := areaForm_eq_sin_oangle_mul C wi wij
    have e2 := areaForm_eq_sin_oangle_mul C wj wij
    rw [hFi] at e1; rw [hFj] at e2
    rw [e1] at e2
    rw [← mul_assoc, ← mul_assoc] at e2
    have k := mul_right_cancel₀ (norm_ne_zero_iff.mpr hwij0) e2
    rw [mul_comm ‖wi‖, mul_comm ‖wj‖]
    exact k
  -- Convert `oangle` views to `linRep`/`theta` form; the two sides pick
  -- up the same sign under the `linRep_class` alternative.
  have hφeq : linRep (o.oangle e wij) = φ := rfl
  rcases linRep_class (o.oangle e wij) with hcl | hcl <;>
    rw [hφeq] at hcl
  · -- `φ = oangle e wij` directly
    have si : Real.Angle.sin (o.oangle wi wij) = Real.sin (φ - theta i) := by
      rw [hoi, ← hcl, ← Real.Angle.coe_sub, Real.Angle.sin_coe]
    have sj : Real.Angle.sin (o.oangle wj wij) = Real.sin (φ - theta j) := by
      rw [hoj, ← hcl, ← Real.Angle.coe_sub, Real.Angle.sin_coe]
    rwa [si, sj] at key
  · -- `φ = oangle e wij + π`: both sines flip sign, cancels
    have hojw : o.oangle e wij = (φ : Real.Angle) - Real.pi := by
      rw [hcl]; abel
    have si : Real.Angle.sin (o.oangle wi wij) =
        -Real.sin (φ - theta i) := by
      rw [hoi, hojw, ← Real.Angle.coe_sub, ← Real.Angle.coe_sub,
        Real.Angle.sin_coe,
        show (φ - Real.pi) - theta i = (φ - theta i) - Real.pi by ring,
        Real.sin_sub_pi]
    have sj : Real.Angle.sin (o.oangle wj wij) =
        -Real.sin (φ - theta j) := by
      rw [hoj, hojw, ← Real.Angle.coe_sub, ← Real.Angle.coe_sub,
        Real.Angle.sin_coe,
        show (φ - Real.pi) - theta j = (φ - theta j) - Real.pi by ring,
        Real.sin_sub_pi]
    rw [si, sj] at key
    linarith [key]

/-- Triangle sine closure: multiplying the three chord identities of
`(i,j,k)` and cancelling `r_i r_j r_k > 0` gives the sine product
identity around the triangle. -/
theorem triangle_view_sin {i j k : Fin 4} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    Real.sin (dirRep o e (c ∘ v.succAbove) i j - theta i)
        * Real.sin (dirRep o e (c ∘ v.succAbove) j k - theta j)
        * Real.sin (dirRep o e (c ∘ v.succAbove) k i - theta k)
      = Real.sin (dirRep o e (c ∘ v.succAbove) i j - theta j)
        * Real.sin (dirRep o e (c ∘ v.succAbove) j k - theta k)
        * Real.sin (dirRep o e (c ∘ v.succAbove) k i - theta i) := by
  have e1 := chord_view_sin C hij
  have e2 := chord_view_sin C hjk
  have e3 := chord_view_sin C hik.symm
  set ri := ‖c (v.succAbove i) - c v‖ with hri_d
  set rj := ‖c (v.succAbove j) - c v‖ with hrj_d
  set rk := ‖c (v.succAbove k) - c v‖ with hrk_d
  have hri : 0 < ri := norm_pos_iff.mpr (sub_ne_zero.mpr (C.pt_ne_anchor i))
  have hrj : 0 < rj := norm_pos_iff.mpr (sub_ne_zero.mpr (C.pt_ne_anchor j))
  have hrk : 0 < rk := norm_pos_iff.mpr (sub_ne_zero.mpr (C.pt_ne_anchor k))
  have hprod : 0 < ri * rj * rk := mul_pos (mul_pos hri hrj) hrk
  have this : (ri * Real.sin (dirRep o e (c ∘ v.succAbove) i j - theta i))
        * (rj * Real.sin (dirRep o e (c ∘ v.succAbove) j k - theta j))
        * (rk * Real.sin (dirRep o e (c ∘ v.succAbove) k i - theta k))
      = (rj * Real.sin (dirRep o e (c ∘ v.succAbove) i j - theta j))
        * (rk * Real.sin (dirRep o e (c ∘ v.succAbove) j k - theta k))
        * (ri * Real.sin (dirRep o e (c ∘ v.succAbove) k i - theta i)) := by
    rw [e1, e2, e3]
  have this' : ri * rj * rk *
        (Real.sin (dirRep o e (c ∘ v.succAbove) i j - theta i)
        * Real.sin (dirRep o e (c ∘ v.succAbove) j k - theta j)
        * Real.sin (dirRep o e (c ∘ v.succAbove) k i - theta k))
      = ri * rj * rk *
        (Real.sin (dirRep o e (c ∘ v.succAbove) i j - theta j)
        * Real.sin (dirRep o e (c ∘ v.succAbove) j k - theta k)
        * Real.sin (dirRep o e (c ∘ v.succAbove) k i - theta i)) := by
    linear_combination this
  exact mul_left_cancel₀ (ne_of_gt hprod) this'

/-- Non-strict Robin Hood transfer (the `δ = 0` boundary gives equality). -/
theorem sin_mul_sin_le_of_transfer {x y δ : ℝ} (hδ : 0 ≤ δ)
    (hδxy : δ ≤ y - x) (hxy : y - x ≤ Real.pi) :
    Real.sin x * Real.sin y ≤ Real.sin (x + δ) * Real.sin (y - δ) := by
  have hnonpos : x - y ≤ 0 := by linarith
  have hnew : |x - y + 2 * δ| ≤ |x - y| := by
    rw [abs_of_nonpos hnonpos, abs_le]
    constructor <;> linarith
  have hcos : Real.cos (x - y) ≤ Real.cos (x - y + 2 * δ) := by
    rw [← Real.cos_abs (x - y), ← Real.cos_abs (x - y + 2 * δ)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by rw [abs_of_nonpos hnonpos]; linarith) hnew
  have prod : ∀ a b : ℝ, 2 * (Real.sin a * Real.sin b) =
      Real.cos (a - b) - Real.cos (a + b) := by
    intro a b; rw [Real.cos_sub, Real.cos_add]; ring
  have e1 := prod (x + δ) (y - δ)
  have e2 := prod x y
  rw [show x + δ - (y - δ) = x - y + 2 * δ by ring,
      show x + δ + (y - δ) = x + y by ring] at e1
  linarith

/-- `(⌊g/λ⌋₊ − 1)·λ ≤ g − λ` for `λ ≤ g`. -/
theorem ff_floor_sub_one_mul_le {g : ℝ} (hg : lam ≤ g) :
    ((⌊g / lam⌋₊ - 1 : ℕ) : ℝ) * lam ≤ g - lam := by
  have h1 : (1 : ℕ) ≤ ⌊g / lam⌋₊ := (one_le_floor_iff_ge lam g C.hlam).mpr hg
  have hle : (⌊g / lam⌋₊ : ℝ) * lam ≤ g :=
    ff_floor_mul_le C (le_trans C.hlam.le hg)
  have hcast : ((⌊g / lam⌋₊ - 1 : ℕ) : ℝ) = (⌊g / lam⌋₊ : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hcast]
  linarith

/-- `g < λ` forces `⌊g/λ⌋₊ = 0`, so the truncated contribution vanishes. -/
theorem ff_floor_zero {g : ℝ} (hg : g < lam) : ⌊g / lam⌋₊ = 0 :=
  Nat.floor_eq_zero.mpr (by rw [div_lt_one C.hlam]; linarith)

/-- `g < 2λ` forces `⌊g/λ⌋₊ ≤ 1`, so the truncated contribution vanishes. -/
theorem ff_floor_le_one {g : ℝ} (hg : g < 2 * lam) : ⌊g / lam⌋₊ ≤ 1 := by
  have h : ⌊g / lam⌋₊ < 2 := fl_lt C.hlam (by norm_num) hg
  omega

/-- `g < (⌊g/λ⌋₊ + 1)·λ` (the upper half of `Nat.floor`). -/
theorem ff_floor_lt_succ_mul {g : ℝ} :
    g < ((⌊g / lam⌋₊ : ℝ) + 1) * lam := by
  have h : g / lam < (⌊g / lam⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (g / lam)
  rwa [div_lt_iff₀ C.hlam] at h

set_option maxHeartbeats 1600000 in
/-- **The T-source leaf.**  Under `Up T H`, `Up T A`, `Up T B`, `Up A B` the
defect equations and the triangle sine-closure cannot both hold: if
`θ_T ≤ θ_H` the row-`T`/row-`A` defect equations are unsatisfiable; if
`θ_H < θ_T` the sine closure of triangle `(H, A, T)` fails by two Robin Hood
transfers. -/
theorem ff_leaf_Tsource {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPA : rowDefect n lam (directionRow o e c (v.succAbove A)) = 2)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hfsA : dirRep o e (c ∘ v.succAbove) A H - theta A < lam)
    (hfsB : dirRep o e (c ∘ v.succAbove) B H - theta B < lam)
    (hord : dirRep o e (c ∘ v.succAbove) H A < dirRep o e (c ∘ v.succAbove) H B)
    (hzw : dirRep o e (c ∘ v.succAbove) H B < dirRep o e (c ∘ v.succAbove) H T)
    (hupHA : Up o e c v H A) (hupHB : Up o e c v H B)
    (hupTH : Up o e c v T H) (hupTA : Up o e c v T A)
    (hupTB : Up o e c v T B) (hupAB : Up o e c v A B) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  set p := dirRep o e (c ∘ v.succAbove) A B with hp_def
  have hlam := C.hlam
  have hβ := C.hβ
  have hπ := C.hπ
  have hnl := C.hnl
  obtain ⟨tH0, tHβ⟩ := (C.htheta H).1
  obtain ⟨tA0, tAβ⟩ := (C.htheta A).1
  obtain ⟨tB0, tBβ⟩ := (C.htheta B).1
  obtain ⟨tT0, tTβ⟩ := (C.htheta T).1
  have hn3 : 3 ≤ n := C.hn3
  have ncast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_two]
  -- Corridors for the six chords.
  obtain ⟨hcu1, hcu2⟩ := up_corridor C hHA hupHA
  obtain ⟨hcw1, hcw2⟩ := up_corridor C hHB hupHB
  obtain ⟨hcz1, hcz2⟩ := up_corridor C hHT.symm hupTH
  obtain ⟨hcx1, hcx2⟩ := up_corridor C hAT.symm hupTA
  obtain ⟨hcy1, hcy2⟩ := up_corridor C hBT.symm hupTB
  obtain ⟨hcp1, hcp2⟩ := up_corridor C hAB hupAB
  rw [phi_comm C hHT.symm] at hcz1 hcz2
  rw [phi_comm C hAT.symm] at hcx1 hcx2
  rw [phi_comm C hBT.symm] at hcy1 hcy2
  simp only [← hu_def, ← hw_def, ← hz_def, ← hx_def, ← hy_def, ← hp_def]
    at hcu1 hcu2 hcw1 hcw2 hcz1 hcz2 hcx1 hcx2 hcy1 hcy2 hcp1 hcp2
  -- Caps.
  have hc1 : lam ≤ |u - z| := by
    have hh := up_cap C hHT.symm hHA hAT.symm hupTH hupHA
    rw [phi_comm C hHT.symm] at hh
    simpa only [← hu_def, ← hz_def] using hh
  have hc2 : lam ≤ |w - z| := by
    have hh := up_cap C hHT.symm hHB hBT.symm hupTH hupHB
    rw [phi_comm C hHT.symm] at hh
    simpa only [← hw_def, ← hz_def] using hh
  have hc3 : lam ≤ |p - x| := by
    have hh := up_cap C hAT.symm hAB hBT.symm hupTA hupAB
    rw [phi_comm C hAT.symm] at hh
    simpa only [← hp_def, ← hx_def] using hh
  have hc4 : lam ≤ |p - u| := by
    have hh := up_cap C hHA hAB hHB hupHA hupAB
    simpa only [← hp_def, ← hu_def] using hh
  -- Betweenness.
  obtain ⟨-, hbtha⟩ := up_trans C hHT.symm hHA hAT.symm hupTH hupHA
  rw [phi_comm C hHT.symm, phi_comm C hAT.symm] at hbtha
  simp only [← hu_def, ← hx_def, ← hz_def] at hbtha
  obtain ⟨-, hbthb⟩ := up_trans C hHT.symm hHB hBT.symm hupTH hupHB
  rw [phi_comm C hBT.symm, phi_comm C hHT.symm] at hbthb
  simp only [← hw_def, ← hy_def, ← hz_def] at hbthb
  obtain ⟨-, hbtab⟩ := up_trans C hAT.symm hAB hBT.symm hupTA hupAB
  rw [phi_comm C hBT.symm, phi_comm C hAT.symm] at hbtab
  simp only [← hx_def, ← hy_def, ← hp_def] at hbtab
  obtain ⟨-, hbhab⟩ := up_trans C hHA hAB hHB hupHA hupAB
  simp only [← hu_def, ← hw_def, ← hp_def] at hbhab
  -- Derived strict orders.
  have hux : u < x := by
    rcases hbtha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact h1
  have hxz : x < z := by
    rcases hbtha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact h2
  have hwy : w < y := by
    rcases hbthb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact h1
  have hyz : y < z := by
    rcases hbthb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · exact h2
  have hwp : w < p := by
    rcases hbhab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · linarith
  -- `z ≥ w + λ` hence `z > θ_H + 2λ`.
  have hz2 : theta H + 2 * lam < z := by
    have hzw' : lam ≤ z - w := by
      have := abs_of_neg (by linarith : w - z < 0)
      rw [this] at hc2; linarith
    linarith
  -- `θ_B > θ_H`.
  have hθB : theta H < theta B := by
    have hsfB' : dirRep o e (c ∘ v.succAbove) H B - theta B < lam := by
      have hh := hfsB; rwa [phi_comm C hHB.symm] at hh
    simp only [← hw_def] at hsfB'; linarith
  -- Short-first on row A : `u - θ_A < λ`.
  have hsfA' : u - theta A < lam := by
    have hh : dirRep o e (c ∘ v.succAbove) H A - theta A < lam := by
      have := hfsA; rwa [phi_comm C hHA.symm] at this
    simpa only [← hu_def] using hh
  -- `θ_A ≤ θ_H` is impossible in all branches.
  have hθA : theta H < theta A := by
    rcases le_or_gt (theta A) (theta H) with h | h
    · linarith
    · exact h
  rcases lt_or_ge (theta H) (theta T) with htgt | httle
  · -- **θ_H < θ_T : sine-transfer kill.** --------------------------------------
    -- Positivity of the sine factors used below.
    have hs_uH : 0 < Real.sin (u - theta H) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
        have h := (phi_mem C H A).2; simp only [← hu_def] at h; linarith)
    have hs_zH : 0 < Real.sin (z - theta H) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs_xT : 0 < Real.sin (x - theta T) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
        have h := (phi_mem C A T).2; simp only [← hx_def] at h; linarith)
    have hs_xA : 0 < Real.sin (x - theta A) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
        have h := (phi_mem C A T).2; simp only [← hx_def] at h; linarith)
    -- Triangle closure on (H, A, T).
    have hE := triangle_view_sin C hHA hAT hHT
    rw [phi_comm C hHT.symm] at hE
    simp only [← hu_def, ← hx_def, ← hz_def] at hE
    rcases le_or_gt (theta A) (theta T) with hATle | hATgt
    · -- `θ_H < θ_A ≤ θ_T` : transfers `(θ_A−θ_H)` then `(θ_T−θ_A)`.
      have t1 := sin_mul_sin_lt_of_transfer C (x := u - theta A) (y := z - theta H)
        (δ := theta A - theta H)
        (show 0 < theta A - theta H by linarith)
        (show theta A - theta H < (z - theta H) - (u - theta A) by linarith)
        (show (z - theta H) - (u - theta A) ≤ Real.pi by linarith)
      rw [show u - theta A + (theta A - theta H) = u - theta H by ring,
          show z - theta H - (theta A - theta H) = z - theta A by ring] at t1
      have q1 : Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
          < Real.sin (u - theta H) * Real.sin (x - theta T) * Real.sin (z - theta A) := by
        rw [show Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
            = Real.sin (x - theta T) * (Real.sin (u - theta A) * Real.sin (z - theta H)) by ring,
          show Real.sin (u - theta H) * Real.sin (x - theta T) * Real.sin (z - theta A)
            = Real.sin (x - theta T) * (Real.sin (u - theta H) * Real.sin (z - theta A)) by ring]
        exact mul_lt_mul_of_pos_left t1 hs_xT
      have t2 := sin_mul_sin_le_of_transfer C (x := x - theta T) (y := z - theta A)
        (δ := theta T - theta A)
        (show 0 ≤ theta T - theta A by linarith)
        (show theta T - theta A ≤ (z - theta A) - (x - theta T) by linarith)
        (show (z - theta A) - (x - theta T) ≤ Real.pi by linarith)
      rw [show x - theta T + (theta T - theta A) = x - theta A by ring,
          show z - theta A - (theta T - theta A) = z - theta T by ring] at t2
      have q2 : Real.sin (u - theta H) * Real.sin (x - theta T) * Real.sin (z - theta A)
          ≤ Real.sin (u - theta H) * Real.sin (x - theta A) * Real.sin (z - theta T) := by
        rw [show Real.sin (u - theta H) * Real.sin (x - theta T) * Real.sin (z - theta A)
            = Real.sin (u - theta H) * (Real.sin (x - theta T) * Real.sin (z - theta A)) by ring,
          show Real.sin (u - theta H) * Real.sin (x - theta A) * Real.sin (z - theta T)
            = Real.sin (u - theta H) * (Real.sin (x - theta A) * Real.sin (z - theta T)) by ring]
        exact mul_le_mul_of_nonneg_left t2 hs_uH.le
      linarith
    · -- `θ_T < θ_A` : transfers `(θ_A−θ_T)` then `(θ_T−θ_H)`.
      have t1 := sin_mul_sin_lt_of_transfer C (x := u - theta A) (y := x - theta T)
        (δ := theta A - theta T)
        (show 0 < theta A - theta T by linarith)
        (show theta A - theta T < (x - theta T) - (u - theta A) by linarith)
        (show (x - theta T) - (u - theta A) ≤ Real.pi by linarith)
      rw [show u - theta A + (theta A - theta T) = u - theta T by ring,
          show x - theta T - (theta A - theta T) = x - theta A by ring] at t1
      have q1 : Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
          < Real.sin (u - theta T) * Real.sin (x - theta A) * Real.sin (z - theta H) := by
        rw [show Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
            = Real.sin (z - theta H) * (Real.sin (u - theta A) * Real.sin (x - theta T)) by ring,
          show Real.sin (u - theta T) * Real.sin (x - theta A) * Real.sin (z - theta H)
            = Real.sin (z - theta H) * (Real.sin (u - theta T) * Real.sin (x - theta A)) by ring]
        exact mul_lt_mul_of_pos_left t1 hs_zH
      have t2 := sin_mul_sin_lt_of_transfer C (x := u - theta T) (y := z - theta H)
        (δ := theta T - theta H)
        (show 0 < theta T - theta H by linarith)
        (show theta T - theta H < (z - theta H) - (u - theta T) by linarith)
        (show (z - theta H) - (u - theta T) ≤ Real.pi by linarith)
      rw [show u - theta T + (theta T - theta H) = u - theta H by ring,
          show z - theta H - (theta T - theta H) = z - theta T by ring] at t2
      have q2 : Real.sin (u - theta T) * Real.sin (x - theta A) * Real.sin (z - theta H)
          < Real.sin (u - theta H) * Real.sin (x - theta A) * Real.sin (z - theta T) := by
        rw [show Real.sin (u - theta T) * Real.sin (x - theta A) * Real.sin (z - theta H)
            = Real.sin (x - theta A) * (Real.sin (u - theta T) * Real.sin (z - theta H)) by ring,
          show Real.sin (u - theta H) * Real.sin (x - theta A) * Real.sin (z - theta T)
            = Real.sin (x - theta A) * (Real.sin (u - theta H) * Real.sin (z - theta T)) by ring]
        exact mul_lt_mul_of_pos_left t2 hs_xA
      linarith
  · -- **θ_T ≤ θ_H : defect/floor kill.** --------------------------------------
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · -- `x < y` : either `x − θ_T ≥ 2λ` (row A dies) or `x − θ_T < 2λ` (row T dies).
      have hpx : x < p := by
        rcases hbtab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · linarith
      rcases lt_or_ge (x - theta T) (2 * lam) with hg0 | hg0
      · -- row T, ordering (x, y, z); `g₀ = x − θ_T < 2λ`.
        have h1T : dirRep o e (c ∘ v.succAbove) T A < dirRep o e (c ∘ v.succAbove) T B := by
          rw [phi_comm C hAT.symm, phi_comm C hBT.symm]; exact hxy
        have h2T : dirRep o e (c ∘ v.succAbove) T B < dirRep o e (c ∘ v.succAbove) T H := by
          rw [phi_comm C hBT.symm, ← phi_comm C hHT]; exact hyz
        have hrowT := row4_defect C rfl hAT.symm hBT.symm hHT.symm h1T h2T
        rw [hPT] at hrowT
        rw [phi_comm C hAT.symm, phi_comm C hBT.symm, ← phi_comm C hHT] at hrowT
        simp only [← hx_def, ← hy_def, ← hz_def] at hrowT
        have hk0 : ⌊(x - theta T) / lam⌋₊ ≤ 1 := ff_floor_le_one C hg0
        rcases le_or_gt lam (y - x) with hb1 | hs1 <;>
          rcases le_or_gt lam (z - y) with hb2 | hs2 <;>
            rcases le_or_gt lam (theta T + Real.pi - z) with hb3 | hs3
        · -- S = {1,2,3} : `π + θ_T − x ≥ (n+1)λ`, but `x > u ≥ θ_H+λ ≥ θ_T+λ`.
          have hsum : (⌊(y - x)/lam⌋₊ - 1) + (⌊(z - y)/lam⌋₊ - 1) + (⌊(theta T + Real.pi - z)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e2 := ff_floor_sub_one_mul_le C hb2
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(y - x)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(z - y)/lam⌋₊ - 1 :ℕ):ℝ) + ((⌊(theta T + Real.pi - z)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1,2} : `z − x ≥ nλ`, but `z − x < π − 2λ < nλ`.
          have hs3' : ⌊(theta T + Real.pi - z)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : (⌊(y - x)/lam⌋₊ - 1) + (⌊(z - y)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e2 := ff_floor_sub_one_mul_le C hb2
          have hre : ((⌊(y - x)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(z - y)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1,3} : `(y−x) + (θ_T+π−z) ≥ nλ`, but the sum `< π + θ_T − x < π − λ + θ_T ≤ ...`.
          have hs2' : ⌊(z - y)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : (⌊(y - x)/lam⌋₊ - 1) + (⌊(theta T + Real.pi - z)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(y - x)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(theta T + Real.pi - z)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1} : `y − x ≥ (n−1)λ`, but `y − x ≤ π − 2λ`.
          have hs2' : ⌊(z - y)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hs3' : ⌊(theta T + Real.pi - z)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : ⌊(y - x)/lam⌋₊ - 1 = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have hre : ((⌊(y - x)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith
        · -- S = {2,3} : `(z−y)+(θ_T+π−z) = θ_T+π−y ≥ nλ`, but `y > x ≥ θ_T+λ`.
          have hs1' : ⌊(y - x)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hsum : (⌊(z - y)/lam⌋₊ - 1) + (⌊(theta T + Real.pi - z)/lam⌋₊ - 1) = n - 2 := by omega
          have e2 := ff_floor_sub_one_mul_le C hb2
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(z - y)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(theta T + Real.pi - z)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {2} : `z − y ≥ (n−1)λ`, but `z − y < π − 2λ`.
          have hs1' : ⌊(y - x)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs3' : ⌊(theta T + Real.pi - z)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : ⌊(z - y)/lam⌋₊ - 1 = n - 2 := by omega
          have e2 := ff_floor_sub_one_mul_le C hb2
          have hre : ((⌊(z - y)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith
        · -- S = {3} : `θ_T + π − z ≥ (n−1)λ`, but `z > θ_H + 2λ ≥ θ_T + 2λ`.
          have hs1' : ⌊(y - x)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(z - y)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : ⌊(theta T + Real.pi - z)/lam⌋₊ - 1 = n - 2 := by omega
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(theta T + Real.pi - z)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith
        · -- S = ∅ : `n = 2`.
          have hs1' : ⌊(y - x)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(z - y)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hs3' : ⌊(theta T + Real.pi - z)/lam⌋₊ = 0 := ff_floor_zero C hs3
          omega
      · -- `x − θ_T ≥ 2λ` : row A, ordering (u, x, p).
        have h1A : dirRep o e (c ∘ v.succAbove) A H < dirRep o e (c ∘ v.succAbove) A T := by
          rw [phi_comm C hHA.symm]; exact hux
        have h2A : dirRep o e (c ∘ v.succAbove) A T < dirRep o e (c ∘ v.succAbove) A B := hpx
        have hrowA := row4_defect C rfl hHA.symm hAT hAB h1A h2A
        rw [hPA] at hrowA
        rw [phi_comm C hHA.symm] at hrowA
        simp only [← hu_def, ← hx_def, ← hp_def] at hrowA
        have hk0 : ⌊(u - theta A)/lam⌋₊ = 0 := ff_floor_zero C hsfA'
        have hpx' : lam ≤ p - x := by
          have := abs_of_pos (by linarith : 0 < p - x); rwa [this] at hc3
        rcases le_or_gt lam (x - u) with hb1 | hs1 <;>
          rcases le_or_gt lam (p - x) with hb2 | hs2 <;>
            rcases le_or_gt lam (theta A + Real.pi - p) with hb3 | hs3
        · -- S = {1,2,3} : `θ_A + π − u ≥ (n+1)λ`, but `u > θ_H + λ` and `θ_A ≤ β`.
          have hsum : (⌊(x - u)/lam⌋₊ - 1) + (⌊(p - x)/lam⌋₊ - 1) + (⌊(theta A + Real.pi - p)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e2 := ff_floor_sub_one_mul_le C hb2
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(x - u)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(p - x)/lam⌋₊ - 1 :ℕ):ℝ) + ((⌊(theta A + Real.pi - p)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1,2} : `p − u ≥ nλ`, but `p − u ≤ π − 2λ + β`.
          have hs3' : ⌊(theta A + Real.pi - p)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : (⌊(x - u)/lam⌋₊ - 1) + (⌊(p - x)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e2 := ff_floor_sub_one_mul_le C hb2
          have hre : ((⌊(x - u)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(p - x)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1,3} : `(x−u)+(θ_A+π−p) ≥ nλ`; `p − x ≥ λ` gives `≤ θ_A+π−u−λ`.
          have hs2' : ⌊(p - x)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : (⌊(x - u)/lam⌋₊ - 1) + (⌊(theta A + Real.pi - p)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(x - u)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(theta A + Real.pi - p)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1} : `x − u ≥ (n−1)λ`, but `x < z ≤ π − λ + θ_H` and `u ≥ θ_H + λ`.
          have hs2' : ⌊(p - x)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hs3' : ⌊(theta A + Real.pi - p)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : ⌊(x - u)/lam⌋₊ - 1 = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have hre : ((⌊(x - u)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith
        · -- S = {2,3} : `θ_A + π − x ≥ nλ`, but `x ≥ θ_T + 2λ ≥ 2λ`, `θ_A ≤ β`.
          have hs1' : ⌊(x - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hsum : (⌊(p - x)/lam⌋₊ - 1) + (⌊(theta A + Real.pi - p)/lam⌋₊ - 1) = n - 2 := by omega
          have e2 := ff_floor_sub_one_mul_le C hb2
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(p - x)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(theta A + Real.pi - p)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {2} : `p − x ≥ (n−1)λ`, but `p ≤ π−λ+θ_B ≤ π−λ+β`, `x ≥ θ_T+2λ`.
          have hs1' : ⌊(x - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs3' : ⌊(theta A + Real.pi - p)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : ⌊(p - x)/lam⌋₊ - 1 = n - 2 := by omega
          have e2 := ff_floor_sub_one_mul_le C hb2
          have hre : ((⌊(p - x)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith
        · -- S = {3} : `θ_A + π − p ≥ (n−1)λ`, but `p ≥ x + λ ≥ θ_T + 3λ`.
          have hs1' : ⌊(x - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(p - x)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : ⌊(theta A + Real.pi - p)/lam⌋₊ - 1 = n - 2 := by omega
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(theta A + Real.pi - p)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith
        · -- S = ∅ : `n = 2`.
          have hs1' : ⌊(x - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(p - x)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hs3' : ⌊(theta A + Real.pi - p)/lam⌋₊ = 0 := ff_floor_zero C hs3
          omega
    · -- `x = y` is impossible (`y` strictly between `x` and `p`).
      rcases hbtab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [hxy]
    · -- `y < x` : either `y − θ_T < 2λ` (direction kill) or `≥ 2λ` (row A dies).
      have hpy : p < y := by
        rcases hbtab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · exact h1
      have hpx : p < x := by linarith
      rcases lt_or_ge (y - theta T) (2 * lam) with hsmall | hbig
      · -- `p < y < θ_T + 2λ ≤ θ_H + 2λ ≤ u + λ`, but `p > u` forces `p ≥ u + λ`.
        have hpu : lam ≤ p - u := by
          have h' : |p - u| = p - u := abs_of_pos (by linarith : 0 < p - u)
          rwa [h'] at hc4
        linarith
      · -- `x − θ_T > 2λ` : row A, ordering (u, p, x).
        have hxt : 2 * lam < x - theta T := by linarith
        have hup' : u < p := by linarith
        have h1A : dirRep o e (c ∘ v.succAbove) A H < dirRep o e (c ∘ v.succAbove) A B := by
          rw [phi_comm C hHA.symm]; exact hup'
        have h2A : dirRep o e (c ∘ v.succAbove) A B < dirRep o e (c ∘ v.succAbove) A T := hpx
        have hrowA := row4_defect C rfl hHA.symm hAB hAT h1A h2A
        rw [hPA] at hrowA
        rw [phi_comm C hHA.symm] at hrowA
        simp only [← hu_def, ← hx_def, ← hp_def] at hrowA
        have hk0 : ⌊(u - theta A)/lam⌋₊ = 0 := ff_floor_zero C hsfA'
        have hxp' : lam ≤ x - p := by
          have h' : |p - x| = x - p := by
            rw [abs_of_neg (by linarith : p - x < 0)]; ring
          rw [h'] at hc3; linarith
        rcases le_or_gt lam (p - u) with hb1 | hs1 <;>
          rcases le_or_gt lam (x - p) with hb2 | hs2 <;>
            rcases le_or_gt lam (theta A + Real.pi - x) with hb3 | hs3
        · -- S = {1,2,3} : `θ_A + π − u ≥ (n+1)λ`.
          have hsum : (⌊(p - u)/lam⌋₊ - 1) + (⌊(x - p)/lam⌋₊ - 1) + (⌊(theta A + Real.pi - x)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e2 := ff_floor_sub_one_mul_le C hb2
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(p - u)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(x - p)/lam⌋₊ - 1 :ℕ):ℝ) + ((⌊(theta A + Real.pi - x)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1,2} : `x − u ≥ nλ`, but `x ≤ π−λ+θ_A`, `u ≥ θ_H+λ`, `θ_A−θ_H ≤ β`.
          have hs3' : ⌊(theta A + Real.pi - x)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : (⌊(p - u)/lam⌋₊ - 1) + (⌊(x - p)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e2 := ff_floor_sub_one_mul_le C hb2
          have hre : ((⌊(p - u)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(x - p)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1,3} : `(p−u)+(θ_A+π−x) ≥ nλ`; `x − p ≥ λ` gives `≤ θ_A+π−u−λ`.
          have hs2' : ⌊(x - p)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : (⌊(p - u)/lam⌋₊ - 1) + (⌊(theta A + Real.pi - x)/lam⌋₊ - 1) = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(p - u)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(theta A + Real.pi - x)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith
        · -- S = {1} : `p − u ≥ (n−1)λ`, but `p < x < z ≤ π − λ + θ_H`.
          have hs2' : ⌊(x - p)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hs3' : ⌊(theta A + Real.pi - x)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : ⌊(p - u)/lam⌋₊ - 1 = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have hre : ((⌊(p - u)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith
        · -- S = {2,3} : `θ_A + π − p ≥ nλ`, but `p ≥ θ_A + λ`.
          have hs1' : ⌊(p - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hsum : (⌊(x - p)/lam⌋₊ - 1) + (⌊(theta A + Real.pi - x)/lam⌋₊ - 1) = n - 2 := by omega
          have e2 := ff_floor_sub_one_mul_le C hb2
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(x - p)/lam⌋₊ - 1 : ℕ):ℝ) + ((⌊(theta A + Real.pi - x)/lam⌋₊ - 1 :ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith only [hm, e2, e3, hcp1, hπ]
        · -- S = {2} : `x − p ≥ (n−1)λ`, but `x < z ≤ π−λ+θ_H`, `p > u ≥ θ_H+λ`.
          have hs1' : ⌊(p - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs3' : ⌊(theta A + Real.pi - x)/lam⌋₊ = 0 := ff_floor_zero C hs3
          have hsum : ⌊(x - p)/lam⌋₊ - 1 = n - 2 := by omega
          have e2 := ff_floor_sub_one_mul_le C hb2
          have hre : ((⌊(x - p)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith only [hm, e2, hcx2, hcp1, hπ]
        · -- S = {3} : `θ_A + π − x ≥ (n−1)λ`, but `x ≥ p + λ ≥ θ_A + 2λ`.
          have hs1' : ⌊(p - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(x - p)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : ⌊(theta A + Real.pi - x)/lam⌋₊ - 1 = n - 2 := by omega
          have e3 := ff_floor_sub_one_mul_le C hb3
          have hre : ((⌊(theta A + Real.pi - x)/lam⌋₊ - 1 : ℕ):ℝ) = (n:ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith only [hm, e3, hxp', hcp1, hπ]
        · -- S = ∅ : `n = 2`.
          have hs1' : ⌊(p - u)/lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(x - p)/lam⌋₊ = 0 := ff_floor_zero C hs2
          have hs3' : ⌊(theta A + Real.pi - x)/lam⌋₊ = 0 := ff_floor_zero C hs3
          omega

/-- **Same-side two-in exclusion (F/F).**  A defect `≥ 3` row cannot
receive two F-side short witnesses: the senders are forced `Up`, the
sixteen `Up`-orientations reduce to the T-source leaf
(`ff_reduces_to_Tsource`), and the leaf dies to
`ff_leaf_Tsource`. -/
theorem same_side_two_in_F {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta A H)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta B H)
    (haθ : theta H < theta A) (hbθ : theta H < theta B)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzta : dirRep o e (c ∘ v.succAbove) H T ≠
      dirRep o e (c ∘ v.succAbove) H A)
    (hztb : dirRep o e (c ∘ v.succAbove) H T ≠
      dirRep o e (c ∘ v.succAbove) H B)
    (hH : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove H)))
    (hPA : rowDefect n lam (directionRow o e c (v.succAbove A)) = 2)
    (hPB : rowDefect n lam (directionRow o e c (v.succAbove B)) = 2)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2) :
    False := by
  have hn2 : 2 ≤ n := by have := C.hn3; omega
  -- F-side witnesses are short-first: the short-last alternative would
  -- force `θ_A < θ_H` (top sliver), contradicting `haθ`.
  have hfsA : dirRep o e (c ∘ v.succAbove) A H - theta A < lam := by
    rcases hwa.2 with hf | hl
    · exact hf
    · exfalso
      have hlt := saturated_row_top_sliver_forces_high o e C.he hn2 C.hlam
        C.hn C.hleg v C.htheta A H hwa.1 le_rfl (by linarith)
      linarith
  have hfsB : dirRep o e (c ∘ v.succAbove) B H - theta B < lam := by
    rcases hwb.2 with hf | hl
    · exact hf
    · exfalso
      have hlt := saturated_row_top_sliver_forces_high o e C.he hn2 C.hlam
        C.hn C.hleg v C.htheta B H hwb.1 le_rfl (by linarith)
      linarith
  have hupHA := ff_sender_ups C hHA hfsA
  have hupHB := ff_sender_ups C hHB hfsB
  obtain ⟨hzw, -, -⟩ :=
    two_in_F_above C hHA hHB hHT hwa hwb haθ hbθ hord hzta hztb hH
  obtain ⟨hupTH, hupTA, hupTB, hupAB⟩ :=
    ff_reduces_to_Tsource C hHA hHB hHT hAB hAT hBT hPB hPT hfsB hord hzw
      hupHA hupHB
  exact ff_leaf_Tsource C hHA hHB hHT hAB hAT hBT hPA hPT hfsA hfsB hord hzw
    hupHA hupHB hupTH hupTA hupTB hupAB

/-! ### L/L mirror: two senders below the receiver

For L/L the senders `A, B` lie below `H` (`θ_A, θ_B < θ_H`) and are
short-last (`θ_S + π − φ_SH < λ`), forcing `Up A H` and `Up B H`, and
`two_in_L_below` places the third direction `z = φ_HT` *below* both
received directions: `z < u < w`.  Of the sixteen orientations, eight
contain `Up B A` and die to `ll_not_upBA`, four fail transitivity
(`up_trans` forces a chord whose opposite `Up` is already present),
and three die to single-row defect equations (`ll_leaf_1/2/3`).  The
residual is the **A-source leaf**
`Up A B ∧ Up A H ∧ Up A T ∧ Up B H ∧ Up B T ∧ Up H T`,
closed by `ll_leaf_Asource` in `same_side_two_in_L`. -/

/-- `Up B A` is impossible: `up_trans` on `B → A → H` forces
`φ_AB` strictly between `φ_HA` and `φ_HB`, and either disjunct
contradicts `φ_HA < φ_HB` or the `B → A` corridor plus the sender
short-last bound `θ_A + π − φ_HA < λ`. -/
theorem ll_not_upBA {H A B : Fin 4} (hHA : H ≠ A) (hHB : H ≠ B)
    (hAB : A ≠ B)
    (hlsA : theta A + Real.pi - dirRep o e (c ∘ v.succAbove) A H < lam)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hupBA : Up o e c v B A) : False := by
  have hupAH : Up o e c v A H := up_of_short_last C hHA.symm hlsA
  obtain ⟨-, hbet⟩ := up_trans C hAB.symm hHA.symm hHB.symm hupBA hupAH
  rw [phi_comm C hAB.symm, phi_comm C hHB.symm, phi_comm C hHA.symm] at hbet
  -- hbet : (φ_AB < φ_HB < φ_HA) ∨ (φ_HA < φ_HB < φ_AB).
  obtain ⟨hcor1, hcor2⟩ := up_corridor C hAB.symm hupBA
  rw [phi_comm C hAB.symm] at hcor2
  have hlsA' : theta A + Real.pi - dirRep o e (c ∘ v.succAbove) H A < lam := by
    rwa [← phi_comm C hHA.symm]
  rcases hbet with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · linarith

/-- **L/L leaf 2**: `Up T H ∧ Up A T ∧ Up T B ∧ Up A B`.
Betweenness on `A → T → H` and `T → B → H` orders row `T` as
`φ_TB < φ_TH < φ_TA`; the corridors on `T → B` and `A → T` plus the
`A → T → H` cap give three `≥ λ` gaps, overflowing the defect-`2`
budget. -/
theorem ll_leaf_2 {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzu : dirRep o e (c ∘ v.succAbove) H T <
      dirRep o e (c ∘ v.succAbove) H A)
    (hupBH : Up o e c v B H) (hupTH : Up o e c v T H)
    (hupAT : Up o e c v A T) (hupTB : Up o e c v T B) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  -- Corridors: `g0 = y − θ_T ≥ λ` (from `Up T B`), `g3 = θ_T + π − x ≥ λ`
  -- (from `Up A T`).
  obtain ⟨hcTB1, -⟩ := up_corridor C hBT.symm hupTB
  rw [phi_comm C hBT.symm] at hcTB1
  obtain ⟨-, hcAT2⟩ := up_corridor C hAT hupAT
  -- Cap `|z − x| ≥ λ` from `A → T → H`.
  have hcap : lam ≤ |dirRep o e (c ∘ v.succAbove) T H -
      dirRep o e (c ∘ v.succAbove) A T| :=
    up_cap C hAT hHT.symm hHA.symm hupAT hupTH
  rw [phi_comm C hHT.symm] at hcap
  simp only [← hx_def, ← hz_def] at hcap
  -- `z < u < x` from betweenness on `A → T → H` (using `z < u`).
  obtain ⟨-, hbetA⟩ := up_trans C hAT hHT.symm hHA.symm hupAT hupTH
  rw [phi_comm C hHT.symm, phi_comm C hHA.symm] at hbetA
  simp only [← hx_def, ← hu_def, ← hz_def] at hbetA
  have hzx : z < x := by
    rcases hbetA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  -- `y < z` from betweenness on `T → B → H` (using `z < u < w`).
  obtain ⟨-, hbetB⟩ := up_trans C hBT.symm hHB.symm hHT.symm hupTB hupBH
  rw [phi_comm C hBT.symm, phi_comm C hHT.symm, phi_comm C hHB.symm] at hbetB
  simp only [← hy_def, ← hz_def, ← hw_def] at hbetB
  have hyz : y < z := by
    rcases hbetB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · linarith [hzu, hord]
  -- Row `T` sorted: `y < z < x`.
  have h1T : dirRep o e (c ∘ v.succAbove) T B <
      dirRep o e (c ∘ v.succAbove) T H := by
    rw [phi_comm C hBT.symm, phi_comm C hHT.symm]; exact hyz
  have h2T : dirRep o e (c ∘ v.succAbove) T H <
      dirRep o e (c ∘ v.succAbove) T A := by
    rw [phi_comm C hHT.symm, phi_comm C hAT.symm]; exact hzx
  have hrowT := row4_defect C rfl hBT.symm hHT.symm hAT.symm h1T h2T
  rw [hPT] at hrowT
  rw [phi_comm C hBT.symm, phi_comm C hHT.symm, phi_comm C hAT.symm] at hrowT
  simp only [← hx_def, ← hy_def, ← hz_def] at hrowT
  -- Floors `≥ 1` on gaps `0, 2, 3`.
  have hf0 : 1 ≤ ⌊(y - theta T) / lam⌋₊ :=
    (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
  have hf2 : 1 ≤ ⌊(x - z) / lam⌋₊ := (one_le_floor_iff_ge lam _ C.hlam).mpr
    (by rw [abs_of_neg (by linarith : z - x < 0)] at hcap; linarith)
  have hf3 : 1 ≤ ⌊(theta T + Real.pi - x) / lam⌋₊ :=
    (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
  have hsum : n + 1 ≤ ⌊(y - theta T) / lam⌋₊ + ⌊(z - y) / lam⌋₊ +
      ⌊(x - z) / lam⌋₊ + ⌊(theta T + Real.pi - x) / lam⌋₊ := by omega
  exact ff_floor_sum_overflow C hBT.symm hHT.symm hAT.symm h1T h2T hPT
    (phi_comm C hBT.symm) (phi_comm C hHT.symm) (phi_comm C hAT.symm) hsum

/-- **L/L leaf 3**: `Up T H ∧ Up A T ∧ Up B T ∧ Up A B`.
Row `T` sorted order is `φ_TH < φ_TA < φ_TB`: the corridor on `T → H`
gives `g0 ≥ λ`, the `A → T → H` cap gives `g1 ≥ λ`, and the corridor on
`B → T` gives `g3 ≥ λ`.  The defect-`2` budget overflows. -/
theorem ll_leaf_3 {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzu : dirRep o e (c ∘ v.succAbove) H T <
      dirRep o e (c ∘ v.succAbove) H A)
    (hupBH : Up o e c v B H) (hupTH : Up o e c v T H)
    (hupAT : Up o e c v A T) (hupBT : Up o e c v B T)
    (hupAB : Up o e c v A B) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  set p := dirRep o e (c ∘ v.succAbove) A B with hp_def
  -- Corridors: `g0 = z − θ_T ≥ λ` (from `Up T H`), `g3 = θ_T + π − y ≥ λ`
  -- (from `Up B T`).
  obtain ⟨hcTH1, -⟩ := up_corridor C hHT.symm hupTH
  rw [phi_comm C hHT.symm] at hcTH1
  obtain ⟨-, hcBT2⟩ := up_corridor C hBT hupBT
  -- Cap `|z − x| ≥ λ` from `A → T → H`.
  have hcap : lam ≤ |dirRep o e (c ∘ v.succAbove) T H -
      dirRep o e (c ∘ v.succAbove) A T| :=
    up_cap C hAT hHT.symm hHA.symm hupAT hupTH
  rw [phi_comm C hHT.symm] at hcap
  simp only [← hx_def, ← hz_def] at hcap
  -- `z < u < x` from betweenness on `A → T → H` (using `z < u`).
  obtain ⟨-, hbetA⟩ := up_trans C hAT hHT.symm hHA.symm hupAT hupTH
  rw [phi_comm C hHT.symm, phi_comm C hHA.symm] at hbetA
  simp only [← hx_def, ← hu_def, ← hz_def] at hbetA
  have hzx : z < x := by
    rcases hbetA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  -- `p < u` from betweenness on `A → B → H` (using `u < w`).
  obtain ⟨-, hbetH⟩ := up_trans C hAB hHB.symm hHA.symm hupAB hupBH
  rw [phi_comm C hHB.symm, phi_comm C hHA.symm] at hbetH
  simp only [← hu_def, ← hw_def, ← hp_def] at hbetH
  have hpu : p < u := by
    rcases hbetH with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · linarith [hord]
  -- `x < y` from betweenness on `A → B → T` (using `p < u < x`).
  obtain ⟨-, hbetT⟩ := up_trans C hAB hBT hAT hupAB hupBT
  simp only [← hx_def, ← hy_def, ← hp_def] at hbetT
  have hxy : x < y := by
    rcases hbetT with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · have : u < x := by
        rcases hbetA with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · exact h2
      linarith
  -- Row `T` sorted: `z < x < y`.
  have h1T : dirRep o e (c ∘ v.succAbove) T H <
      dirRep o e (c ∘ v.succAbove) T A := by
    rw [phi_comm C hHT.symm, phi_comm C hAT.symm]; exact hzx
  have h2T : dirRep o e (c ∘ v.succAbove) T A <
      dirRep o e (c ∘ v.succAbove) T B := by
    rw [phi_comm C hAT.symm, phi_comm C hBT.symm]; exact hxy
  have hrowT := row4_defect C rfl hHT.symm hAT.symm hBT.symm h1T h2T
  rw [hPT] at hrowT
  rw [phi_comm C hHT.symm, phi_comm C hAT.symm, phi_comm C hBT.symm] at hrowT
  simp only [← hx_def, ← hy_def, ← hz_def] at hrowT
  -- Floors `≥ 1` on gaps `0, 1, 3`.
  have hf0 : 1 ≤ ⌊(z - theta T) / lam⌋₊ :=
    (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
  have hf1 : 1 ≤ ⌊(x - z) / lam⌋₊ := (one_le_floor_iff_ge lam _ C.hlam).mpr
    (by rw [abs_of_neg (by linarith : z - x < 0)] at hcap; linarith)
  have hf3 : 1 ≤ ⌊(theta T + Real.pi - y) / lam⌋₊ :=
    (one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith)
  have hsum : n + 1 ≤ ⌊(z - theta T) / lam⌋₊ + ⌊(x - z) / lam⌋₊ +
      ⌊(y - x) / lam⌋₊ + ⌊(theta T + Real.pi - y) / lam⌋₊ := by omega
  exact ff_floor_sum_overflow C hHT.symm hAT.symm hBT.symm h1T h2T hPT
    (phi_comm C hHT.symm) (phi_comm C hAT.symm) (phi_comm C hBT.symm) hsum

set_option maxHeartbeats 800000 in
/-- **L/L leaf 1**: `Up T H ∧ Up T A ∧ Up T B ∧ Up A B`.
The senders force `x < z < u` and `p < u`, so row `A` orders as
`{p, x} < u` with `g3 = θ_A + π − u < λ` (short-last).  The defect-`2`
budget then exhausts over the two orderings: each assignment of big
(`≥ λ`) gaps contradicts the corridor/betweenness bounds. -/
theorem ll_leaf_1 {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPA : rowDefect n lam (directionRow o e c (v.succAbove A)) = 2)
    (hlsA : theta A + Real.pi - dirRep o e (c ∘ v.succAbove) A H < lam)
    (hlsB : theta B + Real.pi - dirRep o e (c ∘ v.succAbove) B H < lam)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzu : dirRep o e (c ∘ v.succAbove) H T <
      dirRep o e (c ∘ v.succAbove) H A)
    (hupAH : Up o e c v A H) (hupBH : Up o e c v B H)
    (hupTH : Up o e c v T H) (hupTA : Up o e c v T A)
    (hupTB : Up o e c v T B) (hupAB : Up o e c v A B) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  set p := dirRep o e (c ∘ v.succAbove) A B with hp_def
  have hlam := C.hlam
  have hβ := C.hβ
  have hπ := C.hπ
  have hnl := C.hnl
  obtain ⟨tH0, tHβ⟩ := (C.htheta H).1
  obtain ⟨tA0, tAβ⟩ := (C.htheta A).1
  obtain ⟨tB0, tBβ⟩ := (C.htheta B).1
  obtain ⟨tT0, tTβ⟩ := (C.htheta T).1
  have hn3 : 3 ≤ n := C.hn3
  have ncast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_two]
  -- Corridors for the six chords (senders, the `T`-fan, `A → B`).
  obtain ⟨hcu1, hcu2⟩ := up_corridor C hHA.symm hupAH
  obtain ⟨hcw1, hcw2⟩ := up_corridor C hHB.symm hupBH
  obtain ⟨hcz1, hcz2⟩ := up_corridor C hHT.symm hupTH
  obtain ⟨hcx1, hcx2⟩ := up_corridor C hAT.symm hupTA
  obtain ⟨hcy1, hcy2⟩ := up_corridor C hBT.symm hupTB
  obtain ⟨hcp1, hcp2⟩ := up_corridor C hAB hupAB
  rw [phi_comm C hHA.symm] at hcu1 hcu2
  rw [phi_comm C hHB.symm] at hcw1 hcw2
  rw [phi_comm C hHT.symm] at hcz1 hcz2
  rw [phi_comm C hAT.symm] at hcx1 hcx2
  rw [phi_comm C hBT.symm] at hcy1 hcy2
  simp only [← hu_def, ← hw_def, ← hz_def, ← hx_def, ← hy_def, ← hp_def]
    at hcu1 hcu2 hcw1 hcw2 hcz1 hcz2 hcx1 hcx2 hcy1 hcy2 hcp1 hcp2
  -- Short-last facts in `u`, `w` form.
  have hlsA' : theta A + Real.pi - u < lam := by
    have := hlsA; rwa [phi_comm C hHA.symm] at this
  have hlsB' : theta B + Real.pi - w < lam := by
    have := hlsB; rwa [phi_comm C hHB.symm] at this
  -- `x < z < u` from betweenness on `T → A → H` (using `z < u`).
  obtain ⟨-, hbetA⟩ := up_trans C hAT.symm hHA.symm hHT.symm hupTA hupAH
  rw [phi_comm C hAT.symm, phi_comm C hHT.symm, phi_comm C hHA.symm] at hbetA
  simp only [← hx_def, ← hu_def, ← hz_def] at hbetA
  have hxz : x < z := by
    rcases hbetA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · linarith
  have hxu : x < u := by
    rcases hbetA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  -- `p < u` from betweenness on `A → B → H` (using `u < w`).
  obtain ⟨-, hbetH⟩ := up_trans C hAB hHB.symm hHA.symm hupAB hupBH
  rw [phi_comm C hHB.symm, phi_comm C hHA.symm] at hbetH
  simp only [← hu_def, ← hw_def, ← hp_def] at hbetH
  have hpu : p < u := by
    rcases hbetH with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · linarith
  have hpw : p < w := by linarith
  -- Caps on the `T`-fan and `A`-fan triangles.
  have hcapTX := up_cap C hAT.symm hAB hBT.symm hupTA hupAB
  rw [phi_comm C hAT.symm] at hcapTX
  have hcapAB := up_cap C hAB hHB.symm hHA.symm hupAB hupBH
  rw [phi_comm C hHB.symm] at hcapAB
  simp only [← hw_def, ← hp_def, ← hx_def] at hcapTX hcapAB
  -- `0 ≤ φ < π` bounds for the six direction representatives.
  have hu0 := (phi_mem C H A).1
  have huπ := (phi_mem C H A).2
  have hw0 := (phi_mem C H B).1
  have hwπ := (phi_mem C H B).2
  have hz0 := (phi_mem C H T).1
  have hzπ := (phi_mem C H T).2
  have hx0 := (phi_mem C A T).1
  have hxπ := (phi_mem C A T).2
  have hy0 := (phi_mem C B T).1
  have hyπ := (phi_mem C B T).2
  have hp0 := (phi_mem C A B).1
  have hpπ := (phi_mem C A B).2
  simp only [← hu_def, ← hw_def, ← hz_def, ← hx_def, ← hy_def, ← hp_def]
    at hu0 huπ hw0 hwπ hz0 hzπ hx0 hxπ hy0 hyπ hp0 hpπ
  -- `p ≠ x` (`dirRep A B ≠ dirRep A T`).
  have hdpx' := legal_dirRep_ne C C.hleg C.he
    (show v.succAbove A ≠ v.succAbove B from
      fun h => hAB (Fin.succAbove_right_injective h))
    (show v.succAbove A ≠ v.succAbove T from
      fun h => hAT (Fin.succAbove_right_injective h))
    (show v.succAbove B ≠ v.succAbove T from
      fun h => hBT (Fin.succAbove_right_injective h))
  have hdpx : p ≠ x := hdpx'
  -- `g3` of row `A` is small: `θ_A + π − u < λ`.
  have hk3 : ⌊(theta A + Real.pi - u) / lam⌋₊ = 0 := ff_floor_zero C hlsA'
  rcases lt_trichotomy p x with hpx | hpx | hpx
  · -- ordering `p < x < u`.
    have h1A : dirRep o e (c ∘ v.succAbove) A B <
        dirRep o e (c ∘ v.succAbove) A T := hpx
    have h2A : dirRep o e (c ∘ v.succAbove) A T <
        dirRep o e (c ∘ v.succAbove) A H := by
      rw [phi_comm C hHA.symm]; exact hxu
    have hrowA := row4_defect C rfl hAB hAT hHA.symm h1A h2A
    rw [hPA] at hrowA
    rw [phi_comm C hHA.symm] at hrowA
    simp only [← hu_def, ← hx_def, ← hp_def] at hrowA
    have hgapsum : (p - theta A) + (x - p) + (u - x) +
        (theta A + Real.pi - u) = Real.pi := by ring
    rcases le_or_gt lam (p - theta A) with hb0 | hs0 <;>
      rcases le_or_gt lam (x - p) with hb1 | hs1 <;>
        rcases le_or_gt lam (u - x) with hb2 | hs2
    · -- S = {0,1,2} : floor sum ≥ n+1 overflows.
      have hsum : n + 1 ≤ ⌊(p - theta A) / lam⌋₊ + ⌊(x - p) / lam⌋₊ +
          ⌊(u - x) / lam⌋₊ + ⌊(theta A + Real.pi - u) / lam⌋₊ := by
        have e0 : 1 ≤ ⌊(p - theta A) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hb0
        have e1 : 1 ≤ ⌊(x - p) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hb1
        have e2 : 1 ≤ ⌊(u - x) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hb2
        omega
      exact ff_floor_sum_overflow C hAB hAT hHA.symm h1A h2A hPA
        hp_def.symm hx_def.symm ((phi_comm C hHA.symm).trans hu_def.symm) hsum
    · -- S = {0,1} : `x − θ_A ≥ nλ`, but `x < z < u < π` and `θ_A < λ`.
      have hs2' : ⌊(u - x) / lam⌋₊ = 0 := ff_floor_zero C hs2
      have hsum : (⌊(p - theta A) / lam⌋₊ - 1) + (⌊(x - p) / lam⌋₊ - 1) = n - 2 := by omega
      have e0 := ff_floor_sub_one_mul_le C hb0
      have e1 := ff_floor_sub_one_mul_le C hb1
      have hre : ((⌊(p - theta A) / lam⌋₊ - 1 : ℕ) : ℝ) +
          ((⌊(x - p) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
      have hm := congrArg (· * lam) hre
      rw [add_mul] at hm
      linarith
    · -- `x − p < λ` contradicts the `T→A→B` cap `λ ≤ |p − x|`.
      rw [abs_of_neg (sub_neg.mpr hpx)] at hcapTX
      linarith
    · -- `x − p < λ` contradicts the `T→A→B` cap `λ ≤ |p − x|`.
      rw [abs_of_neg (sub_neg.mpr hpx)] at hcapTX
      linarith
    · -- `g0 < λ` contradicts `θ_A + λ ≤ p`.
      linarith
    · linarith
    · linarith
    · linarith
  · -- `p = x` contradicts `dirRep A B ≠ dirRep A T`.
    exact absurd hpx hdpx
  · -- ordering `x < p < u`.
    have h1A : dirRep o e (c ∘ v.succAbove) A T <
        dirRep o e (c ∘ v.succAbove) A B := hpx
    have h2A : dirRep o e (c ∘ v.succAbove) A B <
        dirRep o e (c ∘ v.succAbove) A H := by
      rw [phi_comm C hHA.symm]; exact hpu
    have hrowA := row4_defect C rfl hAT hAB hHA.symm h1A h2A
    rw [hPA] at hrowA
    rw [phi_comm C hHA.symm] at hrowA
    simp only [← hu_def, ← hx_def, ← hp_def] at hrowA
    have hgapsum : (x - theta A) + (p - x) + (u - p) +
        (theta A + Real.pi - u) = Real.pi := by ring
    rcases le_or_gt lam (x - theta A) with hb0 | hs0 <;>
      rcases le_or_gt lam (p - x) with hb1 | hs1 <;>
        rcases le_or_gt lam (u - p) with hb2 | hs2
    · -- S = {0,1,2} : floor sum ≥ n+1 overflows.
      have hsum : n + 1 ≤ ⌊(x - theta A) / lam⌋₊ + ⌊(p - x) / lam⌋₊ +
          ⌊(u - p) / lam⌋₊ + ⌊(theta A + Real.pi - u) / lam⌋₊ := by
        have e0 : 1 ≤ ⌊(x - theta A) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hb0
        have e1 : 1 ≤ ⌊(p - x) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hb1
        have e2 : 1 ≤ ⌊(u - p) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hb2
        omega
      exact ff_floor_sum_overflow C hAT hAB hHA.symm h1A h2A hPA
        hx_def.symm hp_def.symm ((phi_comm C hHA.symm).trans hu_def.symm) hsum
    · -- S = {0,1} : `p − θ_A ≥ nλ`, but `p ≤ w − λ ≤ 2π − (n+2)λ`.
      have hs2' : ⌊(u - p) / lam⌋₊ = 0 := ff_floor_zero C hs2
      have hsum : (⌊(x - theta A) / lam⌋₊ - 1) + (⌊(p - x) / lam⌋₊ - 1) = n - 2 := by omega
      have e0 := ff_floor_sub_one_mul_le C hb0
      have e1 := ff_floor_sub_one_mul_le C hb1
      have hre : ((⌊(x - theta A) / lam⌋₊ - 1 : ℕ) : ℝ) +
          ((⌊(p - x) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
      have hm := congrArg (· * lam) hre
      rw [add_mul] at hm
      rw [abs_of_pos (sub_pos.mpr hpw)] at hcapAB
      linarith only [e0, e1, hm, tA0, hcapAB, hcw2, tHβ, hπ]
    · -- `p − x < λ` contradicts the `T→A→B` cap `λ ≤ |p − x|`.
      rw [abs_of_pos (sub_pos.mpr hpx)] at hcapTX
      linarith
    · -- `p − x < λ` contradicts the `T→A→B` cap `λ ≤ |p − x|`.
      rw [abs_of_pos (sub_pos.mpr hpx)] at hcapTX
      linarith
    · -- `g0 < λ` : the defect budget must come from `g1, g2 < ...`.
      have hs0' : ⌊(x - theta A) / lam⌋₊ = 0 := ff_floor_zero C hs0
      have hsum : (⌊(p - x) / lam⌋₊ - 1) + (⌊(u - p) / lam⌋₊ - 1) = n - 2 := by omega
      have e1 := ff_floor_sub_one_mul_le C hb1
      have e2 := ff_floor_sub_one_mul_le C hb2
      have hre : ((⌊(p - x) / lam⌋₊ - 1 : ℕ) : ℝ) +
          ((⌊(u - p) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
      have hm := congrArg (· * lam) hre
      rw [add_mul] at hm
      linarith
    · -- `g0, g2 < λ` : `p − x ≥ (n−1)λ` and `x ≥ λ` give `p ≥ nλ`, but
      -- `p ≤ w − λ ≤ 2π − (n+2)λ`.
      have hs0' : ⌊(x - theta A) / lam⌋₊ = 0 := ff_floor_zero C hs0
      have hs2' : ⌊(u - p) / lam⌋₊ = 0 := ff_floor_zero C hs2
      have hsum : ⌊(p - x) / lam⌋₊ - 1 = n - 2 := by omega
      have e1 := ff_floor_sub_one_mul_le C hb1
      have hre : ((⌊(p - x) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        rw [← ncast]; exact_mod_cast hsum
      have hm := congrArg (· * lam) hre
      rw [abs_of_pos (sub_pos.mpr hpw)] at hcapAB
      linarith only [e1, hm, hcx1, tT0, hcapAB, hcw2, tHβ, hπ]
    · -- `p − x < λ` contradicts the `T→A→B` cap `λ ≤ |p − x|`.
      rw [abs_of_pos (sub_pos.mpr hpx)] at hcapTX
      linarith
    · -- S = ∅ : `n = 2`.
      have hs0' : ⌊(x - theta A) / lam⌋₊ = 0 := ff_floor_zero C hs0
      have hs1' : ⌊(p - x) / lam⌋₊ = 0 := ff_floor_zero C hs1
      have hs2' : ⌊(u - p) / lam⌋₊ = 0 := ff_floor_zero C hs2
      omega

/-- **L/L orientation reduction.**  Of the sixteen orientations of the
four free chords `(H,T), (A,B), (A,T), (B,T)` under `Up A H`, `Up B H`
and `φ_HT < φ_HA < φ_HB`: every orientation with `Up B A` dies to
`ll_not_upBA`; four orientations fail transitivity (a forced third
`Up` collides with an opposite `Up` already present); three die to the
single-row defect leaves `ll_leaf_1/2/3`.  The only survivor is the
A-source residual `Up H T ∧ Up A T ∧ Up B T ∧ Up A B`. -/
theorem ll_reduces_to_Asource {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPA : rowDefect n lam (directionRow o e c (v.succAbove A)) = 2)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hlsA : theta A + Real.pi - dirRep o e (c ∘ v.succAbove) A H < lam)
    (hlsB : theta B + Real.pi - dirRep o e (c ∘ v.succAbove) B H < lam)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzu : dirRep o e (c ∘ v.succAbove) H T <
      dirRep o e (c ∘ v.succAbove) H A)
    (hupAH : Up o e c v A H) (hupBH : Up o e c v B H) :
    Up o e c v H T ∧ Up o e c v A T ∧ Up o e c v B T ∧ Up o e c v A B := by
  rcases up_or_up C hHT with hupHT | hupTH
  · rcases up_or_up C hAB with hupAB | hupBA
    · rcases up_or_up C hAT with hupAT | hupTA
      · rcases up_or_up C hBT with hupBT | hupTB
        · -- Residual A-source leaf.
          exact ⟨hupHT, hupAT, hupBT, hupAB⟩
        · -- `B → H → T` forces `Up B T`, colliding with `Up T B`.
          obtain ⟨hBT', -⟩ := up_trans C hHB.symm hHT hBT hupBH hupHT
          exact (up_not_both C hBT.symm hupTB hBT').elim
      · rcases up_or_up C hBT with hupBT | hupTB
        · -- `B → T → A` forces `Up B A`, colliding with `Up A B`.
          obtain ⟨hBA, -⟩ := up_trans C hBT hAT.symm hAB.symm hupBT hupTA
          exact (up_not_both C hAB hupAB hBA).elim
        · -- `B → H → T` forces `Up B T`, colliding with `Up T B`.
          obtain ⟨hBT', -⟩ := up_trans C hHB.symm hHT hBT hupBH hupHT
          exact (up_not_both C hBT.symm hupTB hBT').elim
    · rcases up_or_up C hAT with hupAT | hupTA <;>
        rcases up_or_up C hBT with hupBT | hupTB <;>
        exact (ll_not_upBA C hHA hHB hAB hlsA hord hupBA).elim
  · rcases up_or_up C hAB with hupAB | hupBA
    · rcases up_or_up C hAT with hupAT | hupTA
      · rcases up_or_up C hBT with hupBT | hupTB
        · exact (ll_leaf_3 C hHA hHB hHT hAB hAT hBT hPT hord hzu
            hupBH hupTH hupAT hupBT hupAB).elim
        · exact (ll_leaf_2 C hHA hHB hHT hAB hAT hBT hPT hord hzu
            hupBH hupTH hupAT hupTB).elim
      · rcases up_or_up C hBT with hupBT | hupTB
        · -- `B → T → A` forces `Up B A`, colliding with `Up A B`.
          obtain ⟨hBA, -⟩ := up_trans C hBT hAT.symm hAB.symm hupBT hupTA
          exact (up_not_both C hAB hupAB hBA).elim
        · exact (ll_leaf_1 C hHA hHB hHT hAB hAT hBT hPA hlsA hlsB hord hzu
            hupAH hupBH hupTH hupTA hupTB hupAB).elim
    · rcases up_or_up C hAT with hupAT | hupTA <;>
        rcases up_or_up C hBT with hupBT | hupTB <;>
        exact (ll_not_upBA C hHA hHB hAB hlsA hord hupBA).elim

set_option maxHeartbeats 1600000 in
/-- **L/L residual leaf — A-source**: `Up A B ∧ Up A H ∧ Up A T ∧
Up B H ∧ Up B T ∧ Up H T` is impossible.

If `θ_T ≤ θ_H` the triangle `(H, A, T)` sine closure fails by two
Robin Hood transfers on the pair `sin(u − θ_A)·sin(z − θ_H)` versus
`sin(u − θ_H)·sin(z − θ_T)`: the transfers are forced by `z < x < u`,
the corridors, and `θ_A < θ_H`.

If `θ_H < θ_T` the direction layer forces `z, x, y > θ_T` and
`θ_B < p`; the `A → B → T` betweenness then splits into `p < x < y`
(row `B` order `θ_B < p < y < w`, row `T` order `θ_T < z < x < y`)
and `y < x < p` (row `B` order `θ_B < y < p < w`).  The second dies to
row `B` alone (either the floor budget overflows or `w − y ≥ nλ`
collides with `w ≤ π − λ + θ_H`); for the first, `w − y ≥ λ` dies to
row `B` alone, while `w − y < λ` forces `θ_T + π − y < 2λ`, which
collapses row `T`'s last gap floor to `1` and leaves the defect-`2`
equation no witness. -/
theorem ll_leaf_Asource {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hPB : rowDefect n lam (directionRow o e c (v.succAbove B)) = 2)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2)
    (hlsA : theta A + Real.pi - dirRep o e (c ∘ v.succAbove) A H < lam)
    (hlsB : theta B + Real.pi - dirRep o e (c ∘ v.succAbove) B H < lam)
    (haθ : theta A < theta H) (hbθ : theta B < theta H)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzu : dirRep o e (c ∘ v.succAbove) H T <
      dirRep o e (c ∘ v.succAbove) H A)
    (hupAH : Up o e c v A H) (hupBH : Up o e c v B H)
    (hupHT : Up o e c v H T) (hupAB : Up o e c v A B)
    (hupAT : Up o e c v A T) (hupBT : Up o e c v B T) : False := by
  classical
  set u := dirRep o e (c ∘ v.succAbove) H A with hu_def
  set w := dirRep o e (c ∘ v.succAbove) H B with hw_def
  set z := dirRep o e (c ∘ v.succAbove) H T with hz_def
  set x := dirRep o e (c ∘ v.succAbove) A T with hx_def
  set y := dirRep o e (c ∘ v.succAbove) B T with hy_def
  set p := dirRep o e (c ∘ v.succAbove) A B with hp_def
  have hlam := C.hlam
  have hβ := C.hβ
  have hπ := C.hπ
  have hnl := C.hnl
  obtain ⟨tH0, tHβ⟩ := (C.htheta H).1
  obtain ⟨tA0, tAβ⟩ := (C.htheta A).1
  obtain ⟨tB0, tBβ⟩ := (C.htheta B).1
  obtain ⟨tT0, tTβ⟩ := (C.htheta T).1
  have hn3 : 3 ≤ n := C.hn3
  have ncast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_two]
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  -- Corridors.
  obtain ⟨hcu1, hcu2⟩ := up_corridor C hHA.symm hupAH
  rw [phi_comm C hHA.symm] at hcu1 hcu2
  obtain ⟨hcw1, hcw2⟩ := up_corridor C hHB.symm hupBH
  rw [phi_comm C hHB.symm] at hcw1 hcw2
  obtain ⟨hcz1, hcz2⟩ := up_corridor C hHT hupHT
  obtain ⟨hcx1, hcx2⟩ := up_corridor C hAT hupAT
  obtain ⟨hcy1, hcy2⟩ := up_corridor C hBT hupBT
  obtain ⟨hcp1, hcp2⟩ := up_corridor C hAB hupAB
  simp only [← hu_def, ← hw_def, ← hz_def, ← hx_def, ← hy_def, ← hp_def]
    at hcu1 hcu2 hcw1 hcw2 hcz1 hcz2 hcx1 hcx2 hcy1 hcy2 hcp1 hcp2
  -- Short-last in canonical form.
  have hlsA' : theta A + Real.pi - u < lam := by
    rw [hu_def, ← phi_comm C hHA.symm]; exact hlsA
  have hlsB' : theta B + Real.pi - w < lam := by
    rw [hw_def, ← phi_comm C hHB.symm]; exact hlsB
  -- Caps.
  have hc1 : lam ≤ |z - u| := by
    have hh := up_cap C hHA.symm hHT hAT hupAH hupHT
    rw [phi_comm C hHA.symm] at hh
    simpa only [← hu_def, ← hz_def] using hh
  have hc2 : lam ≤ |w - p| := by
    have hh := up_cap C hAB hHB.symm hHA.symm hupAB hupBH
    rw [phi_comm C hHB.symm] at hh
    simpa only [← hw_def, ← hp_def] using hh
  have hc3 : lam ≤ |y - p| := by
    have hh := up_cap C hAB hBT hAT hupAB hupBT
    simpa only [← hy_def, ← hp_def] using hh
  have hc4 : lam ≤ |z - w| := by
    have hh := up_cap C hHB.symm hHT hBT hupBH hupHT
    rw [phi_comm C hHB.symm] at hh
    simpa only [← hz_def, ← hw_def] using hh
  -- Betweenness-derived orders: `z < x < u`, `z < y < w`, `p < u < w`.
  obtain ⟨-, hbet1⟩ := up_trans C hHA.symm hHT hAT hupAH hupHT
  rw [phi_comm C hHA.symm] at hbet1
  simp only [← hu_def, ← hx_def, ← hz_def] at hbet1
  have hzx : z < x := by
    rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hxu : x < u := by
    rcases hbet1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  obtain ⟨-, hbet2⟩ := up_trans C hHB.symm hHT hBT hupBH hupHT
  rw [phi_comm C hHB.symm] at hbet2
  simp only [← hw_def, ← hy_def, ← hz_def] at hbet2
  have hzy : z < y := by
    rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hyw : y < w := by
    rcases hbet2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  obtain ⟨-, hbet3⟩ := up_trans C hAB hHB.symm hHA.symm hupAB hupBH
  rw [phi_comm C hHB.symm, phi_comm C hHA.symm] at hbet3
  simp only [← hu_def, ← hw_def, ← hp_def] at hbet3
  have hpu : p < u := by
    rcases hbet3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hpw : p < w := by linarith
  obtain ⟨-, hbet4⟩ := up_trans C hAB hBT hAT hupAB hupBT
  simp only [← hp_def, ← hx_def, ← hy_def] at hbet4
  -- hbet4 : (p < x ∧ x < y) ∨ (y < x ∧ x < p).
  -- Positions live in `[0, π)`.
  have hwπ : w < Real.pi := by have := (phi_mem C H B).2; rwa [← hw_def] at this
  have huπ : u < Real.pi := by have := (phi_mem C H A).2; rwa [← hu_def] at this
  have hxπ : x < Real.pi := by have := (phi_mem C A T).2; rwa [← hx_def] at this
  have hyπ : y < Real.pi := by have := (phi_mem C B T).2; rwa [← hy_def] at this
  have hzπ : z < Real.pi := by have := (phi_mem C H T).2; rwa [← hz_def] at this
  have hpπ : p < Real.pi := by have := (phi_mem C A B).2; rwa [← hp_def] at this
  -- Derived separations.
  have hzw : z < w := by linarith
  have hwz : lam ≤ w - z := by
    rw [abs_of_neg (by linarith : z - w < 0)] at hc4; linarith
  have huz : lam ≤ u - z := by
    rw [abs_of_neg (by linarith : z - u < 0)] at hc1; linarith
  have hwp' : lam ≤ w - p := by
    rw [abs_of_pos (by linarith : 0 < w - p)] at hc2; linarith
  -- `θ_B < p` already at the direction layer.
  have hpb : theta B < p := by
    by_contra h'
    push_neg at h'
    linarith
  rcases le_or_gt (theta T) (theta H) with httle | htgt
  · -- **θ_T ≤ θ_H — sine closure on the triangle `(H, A, T)`.**
    have hE := triangle_view_sin C hHA hAT hHT
    rw [phi_comm C hHT.symm] at hE
    simp only [← hu_def, ← hx_def, ← hz_def] at hE
    -- hE : sin(u−θh)·sin(x−θa)·sin(z−θt) = sin(u−θa)·sin(x−θt)·sin(z−θh)
    have hs_zH : 0 < Real.sin (z - theta H) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
    have hs_xT : 0 < Real.sin (x - theta T) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
    have hs_xA : 0 < Real.sin (x - theta A) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
    have hs_uH : 0 < Real.sin (u - theta H) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
    have hs_uA : 0 < Real.sin (u - theta A) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
    rcases le_or_gt (theta T) (theta A) with hta | hat
    · -- `θ_T ≤ θ_A`: move `θ_H − θ_A` from `u − θ_A` onto `z − θ_H`,
      -- then `θ_A − θ_T` from `x − θ_T` onto `z − θ_A`.
      have t1 := sin_mul_sin_lt_of_transfer C
        (show (0:ℝ) < theta H - theta A by linarith)
        (show theta H - theta A < (u - theta A) - (z - theta H) by linarith)
        (show (u - theta A) - (z - theta H) ≤ Real.pi by linarith)
        (x := z - theta H) (y := u - theta A)
      rw [show z - theta H + (theta H - theta A) = z - theta A by ring,
        show u - theta A - (theta H - theta A) = u - theta H by ring] at t1
      -- t1 : sin(z−θh)·sin(u−θa) < sin(z−θa)·sin(u−θh)
      have q1 : Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
          < Real.sin (u - theta H) * Real.sin (z - theta A) * Real.sin (x - theta T) := by
        have h0 : Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
            = Real.sin (x - theta T) * (Real.sin (z - theta H) * Real.sin (u - theta A)) := by
          ring
        have h1 : Real.sin (u - theta H) * Real.sin (z - theta A) * Real.sin (x - theta T)
            = Real.sin (x - theta T) * (Real.sin (z - theta A) * Real.sin (u - theta H)) := by
          ring
        rw [h0, h1]
        exact mul_lt_mul_of_pos_left t1 hs_xT
      have t2 := sin_mul_sin_le_of_transfer C
        (show (0:ℝ) ≤ theta A - theta T by linarith)
        (show theta A - theta T ≤ (x - theta T) - (z - theta A) by linarith)
        (show (x - theta T) - (z - theta A) ≤ Real.pi by linarith)
        (x := z - theta A) (y := x - theta T)
      rw [show z - theta A + (theta A - theta T) = z - theta T by ring,
        show x - theta T - (theta A - theta T) = x - theta A by ring] at t2
      -- t2 : sin(z−θa)·sin(x−θt) ≤ sin(z−θt)·sin(x−θa)
      have q2 : Real.sin (u - theta H) * Real.sin (z - theta A) * Real.sin (x - theta T)
          ≤ Real.sin (u - theta H) * Real.sin (x - theta A) * Real.sin (z - theta T) := by
        have h0 : Real.sin (u - theta H) * Real.sin (z - theta A) * Real.sin (x - theta T)
            = Real.sin (u - theta H) * (Real.sin (z - theta A) * Real.sin (x - theta T)) := by
          ring
        have h1 : Real.sin (u - theta H) * Real.sin (x - theta A) * Real.sin (z - theta T)
            = Real.sin (u - theta H) * (Real.sin (z - theta T) * Real.sin (x - theta A)) := by
          ring
        rw [h0, h1]
        exact mul_le_mul_of_nonneg_left t2 hs_uH.le
      linarith
    · -- `θ_A < θ_T ≤ θ_H`: move `θ_T − θ_A` from `u − θ_A` onto
      -- `x − θ_T`, then `θ_H − θ_T` from `u − θ_T` onto `z − θ_H`.
      have t1 := sin_mul_sin_lt_of_transfer C
        (show (0:ℝ) < theta T - theta A by linarith)
        (show theta T - theta A < (u - theta A) - (x - theta T) by linarith)
        (show (u - theta A) - (x - theta T) ≤ Real.pi by linarith)
        (x := x - theta T) (y := u - theta A)
      rw [show x - theta T + (theta T - theta A) = x - theta A by ring,
        show u - theta A - (theta T - theta A) = u - theta T by ring] at t1
      -- t1 : sin(x−θt)·sin(u−θa) < sin(x−θa)·sin(u−θt)
      have q1 : Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
          < Real.sin (x - theta A) * Real.sin (u - theta T) * Real.sin (z - theta H) := by
        have h0 : Real.sin (u - theta A) * Real.sin (x - theta T) * Real.sin (z - theta H)
            = Real.sin (z - theta H) * (Real.sin (x - theta T) * Real.sin (u - theta A)) := by
          ring
        have h1 : Real.sin (x - theta A) * Real.sin (u - theta T) * Real.sin (z - theta H)
            = Real.sin (z - theta H) * (Real.sin (x - theta A) * Real.sin (u - theta T)) := by
          ring
        rw [h0, h1]
        exact mul_lt_mul_of_pos_left t1 hs_zH
      have t2 := sin_mul_sin_le_of_transfer C
        (show (0:ℝ) ≤ theta H - theta T by linarith)
        (show theta H - theta T ≤ (u - theta T) - (z - theta H) by linarith)
        (show (u - theta T) - (z - theta H) ≤ Real.pi by linarith)
        (x := z - theta H) (y := u - theta T)
      rw [show z - theta H + (theta H - theta T) = z - theta T by ring,
        show u - theta T - (theta H - theta T) = u - theta H by ring] at t2
      -- t2 : sin(z−θh)·sin(u−θt) ≤ sin(z−θt)·sin(u−θh)
      have q2 : Real.sin (x - theta A) * Real.sin (u - theta T) * Real.sin (z - theta H)
          ≤ Real.sin (x - theta A) * Real.sin (z - theta T) * Real.sin (u - theta H) := by
        have h0 : Real.sin (x - theta A) * Real.sin (u - theta T) * Real.sin (z - theta H)
            = Real.sin (x - theta A) * (Real.sin (z - theta H) * Real.sin (u - theta T)) := by
          ring
        have h1 : Real.sin (x - theta A) * Real.sin (z - theta T) * Real.sin (u - theta H)
            = Real.sin (x - theta A) * (Real.sin (z - theta T) * Real.sin (u - theta H)) := by
          ring
        rw [h0, h1]
        exact mul_le_mul_of_nonneg_left t2 hs_xA.le
      linarith
  · -- **θ_H < θ_T — floor/defect kills.**
    have hzt : theta T < z := by
      by_contra hz'; push_neg at hz'; linarith
    have hxt : theta T < x := by
      by_contra hx'; push_neg at hx'; linarith
    have hyt : theta T < y := by
      by_contra hy'; push_neg at hy'; linarith
    rcases hbet4 with ⟨hpx, hxy⟩ | ⟨hyx, hxp⟩
    · -- **alpha**: `p < x < y`; row `B` order `θ_B < p < y < w`,
      -- row `T` order `θ_T < z < x < y`.
      have h1B : dirRep o e (c ∘ v.succAbove) B A <
          dirRep o e (c ∘ v.succAbove) B T := by
        rw [phi_comm C hAB.symm]; exact lt_trans hpx hxy
      have h2B : dirRep o e (c ∘ v.succAbove) B T <
          dirRep o e (c ∘ v.succAbove) B H := by
        rw [phi_comm C hHB.symm]; exact hyw
      have hrowB := row4_defect C rfl hAB.symm hBT hHB.symm h1B h2B
      rw [hPB] at hrowB
      rw [phi_comm C hAB.symm, phi_comm C hHB.symm] at hrowB
      simp only [← hw_def, ← hy_def, ← hp_def] at hrowB
      have hkB3 : ⌊(theta B + Real.pi - w) / lam⌋₊ = 0 := ff_floor_zero C hlsB'
      have hfB1 : 1 ≤ ⌊(y - p) / lam⌋₊ := (one_le_floor_iff_ge lam _ C.hlam).mpr
        (show lam ≤ y - p by
          rwa [abs_of_pos (by linarith : 0 < y - p)] at hc3)
      rcases le_or_gt lam (w - y) with hbwy | hswy
      · -- `w − y ≥ λ`: row `B` alone dies.
        have hfB2 : 1 ≤ ⌊(w - y) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hbwy
        rcases le_or_gt lam (p - theta B) with hb0 | hs0
        · -- `{0,1,2}`: the floor budget overflows.
          have hfB0 : 1 ≤ ⌊(p - theta B) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb0
          have hsum : n + 1 ≤ ⌊(p - theta B) / lam⌋₊ + ⌊(y - p) / lam⌋₊ +
              ⌊(w - y) / lam⌋₊ + ⌊(theta B + Real.pi - w) / lam⌋₊ := by omega
          exact ff_floor_sum_overflow C hAB.symm hBT hHB.symm h1B h2B hPB
            ((phi_comm C hAB.symm).trans hp_def.symm) hy_def.symm
            ((phi_comm C hHB.symm).trans hw_def.symm) hsum
        · -- `{1,2}`: `w − p ≥ nλ` against `w < π < (n+1)λ`.
          have hs0' : ⌊(p - theta B) / lam⌋₊ = 0 := ff_floor_zero C hs0
          have hsum : (⌊(y - p) / lam⌋₊ - 1) + (⌊(w - y) / lam⌋₊ - 1) = n - 2 := by
            omega
          have e1 := ff_floor_sub_one_mul_le C (show lam ≤ y - p by
            rwa [abs_of_pos (by linarith : 0 < y - p)] at hc3)
          have e2 := ff_floor_sub_one_mul_le C hbwy
          have hre : ((⌊(y - p) / lam⌋₊ - 1 : ℕ) : ℝ) +
              ((⌊(w - y) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
            rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          rw [add_mul] at hm
          linarith only [e1, e2, hm, hcp1, tA0, hwπ, hπ]
      · -- `w − y < λ`: row `B` forces `θ_T + π − y < 2λ`.
        have hkB2 : ⌊(w - y) / lam⌋₊ = 0 := ff_floor_zero C hswy
        have hg3lt : theta T + Real.pi - y < 2 * lam := by
          rcases le_or_gt lam (p - theta B) with hb0 | hs0
          · -- `{0,1}`: `y − θ_B ≥ nλ`.
            have hsum : (⌊(p - theta B) / lam⌋₊ - 1) + (⌊(y - p) / lam⌋₊ - 1)
                = n - 2 := by omega
            have e0 := ff_floor_sub_one_mul_le C hb0
            have e1 := ff_floor_sub_one_mul_le C (show lam ≤ y - p by
              rwa [abs_of_pos (by linarith : 0 < y - p)] at hc3)
            have hre : ((⌊(p - theta B) / lam⌋₊ - 1 : ℕ) : ℝ) +
                ((⌊(y - p) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
              rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
            have hm := congrArg (· * lam) hre
            rw [add_mul] at hm
            linarith only [e0, e1, hm, tTβ, tB0, hβ]
          · -- `{1}`: `y − p ≥ (n−1)λ`, so `y > θ_A + nλ`.
            have hs0' : ⌊(p - theta B) / lam⌋₊ = 0 := ff_floor_zero C hs0
            have hsum : ⌊(y - p) / lam⌋₊ - 1 = n - 2 := by omega
            have e1 := ff_floor_sub_one_mul_le C (show lam ≤ y - p by
              rwa [abs_of_pos (by linarith : 0 < y - p)] at hc3)
            have hre : ((⌊(y - p) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
              rw [← ncast]; exact_mod_cast hsum
            have hm := congrArg (· * lam) hre
            linarith only [e1, hm, hcp1, tA0, tTβ, hβ]
        -- Row `T`: `θ_T < z < x < y`, last gap floor collapsed to `1`.
        have h1T : dirRep o e (c ∘ v.succAbove) T H <
            dirRep o e (c ∘ v.succAbove) T A := by
          rw [phi_comm C hHT.symm, phi_comm C hAT.symm]; exact hzx
        have h2T : dirRep o e (c ∘ v.succAbove) T A <
            dirRep o e (c ∘ v.succAbove) T B := by
          rw [phi_comm C hAT.symm, phi_comm C hBT.symm]; exact hxy
        have hrowT := row4_defect C rfl hHT.symm hAT.symm hBT.symm h1T h2T
        rw [hPT] at hrowT
        rw [phi_comm C hHT.symm, phi_comm C hAT.symm, phi_comm C hBT.symm] at hrowT
        simp only [← hx_def, ← hy_def, ← hz_def] at hrowT
        have hfT3 : ⌊(theta T + Real.pi - y) / lam⌋₊ = 1 :=
          le_antisymm (ff_floor_le_one C hg3lt)
            ((one_le_floor_iff_ge lam _ C.hlam).mpr (by linarith))
        rcases le_or_gt lam (z - theta T) with hb0 | hs0 <;>
          rcases le_or_gt lam (x - z) with hb1 | hs1 <;>
            rcases le_or_gt lam (y - x) with hb2 | hs2
        · -- `{0,1,2,3}`: overflow.
          have hf0 : 1 ≤ ⌊(z - theta T) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb0
          have hf1 : 1 ≤ ⌊(x - z) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb1
          have hf2 : 1 ≤ ⌊(y - x) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb2
          have hsum : n + 1 ≤ ⌊(z - theta T) / lam⌋₊ + ⌊(x - z) / lam⌋₊ +
              ⌊(y - x) / lam⌋₊ + ⌊(theta T + Real.pi - y) / lam⌋₊ := by omega
          exact ff_floor_sum_overflow C hHT.symm hAT.symm hBT.symm h1T h2T hPT
            ((phi_comm C hHT.symm).trans hz_def.symm)
            ((phi_comm C hAT.symm).trans hx_def.symm)
            ((phi_comm C hBT.symm).trans hy_def.symm) hsum
        · -- `{0,1,3}`: `k0 + k1 + k3 = n + 1` overflows (with `k2 = 0`).
          have hs2' : ⌊(y - x) / lam⌋₊ = 0 := ff_floor_zero C hs2
          have hf0 : 1 ≤ ⌊(z - theta T) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb0
          have hf1 : 1 ≤ ⌊(x - z) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb1
          have hsum : n + 1 ≤ ⌊(z - theta T) / lam⌋₊ + ⌊(x - z) / lam⌋₊ +
              ⌊(y - x) / lam⌋₊ + ⌊(theta T + Real.pi - y) / lam⌋₊ := by omega
          exact ff_floor_sum_overflow C hHT.symm hAT.symm hBT.symm h1T h2T hPT
            ((phi_comm C hHT.symm).trans hz_def.symm)
            ((phi_comm C hAT.symm).trans hx_def.symm)
            ((phi_comm C hBT.symm).trans hy_def.symm) hsum
        · -- `{0,2,3}`: overflow.
          have hs1' : ⌊(x - z) / lam⌋₊ = 0 := ff_floor_zero C hs1
          have hf0 : 1 ≤ ⌊(z - theta T) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb0
          have hf2 : 1 ≤ ⌊(y - x) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb2
          have hsum : n + 1 ≤ ⌊(z - theta T) / lam⌋₊ + ⌊(x - z) / lam⌋₊ +
              ⌊(y - x) / lam⌋₊ + ⌊(theta T + Real.pi - y) / lam⌋₊ := by omega
          exact ff_floor_sum_overflow C hHT.symm hAT.symm hBT.symm h1T h2T hPT
            ((phi_comm C hHT.symm).trans hz_def.symm)
            ((phi_comm C hAT.symm).trans hx_def.symm)
            ((phi_comm C hBT.symm).trans hy_def.symm) hsum
        · -- `{0}` (+`k3 = 1`): `z − θ_T ≥ (n−1)λ` reaches `w`.
          have hs1' : ⌊(x - z) / lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(y - x) / lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : ⌊(z - theta T) / lam⌋₊ - 1 = n - 2 := by omega
          have e0 := ff_floor_sub_one_mul_le C hb0
          have hre : ((⌊(z - theta T) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith only [e0, hm, htgt, hcz1, hwz, hcw2, hπ]
        · -- `{1,2,3}`: overflow.
          have hs0' : ⌊(z - theta T) / lam⌋₊ = 0 := ff_floor_zero C hs0
          have hf1 : 1 ≤ ⌊(x - z) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb1
          have hf2 : 1 ≤ ⌊(y - x) / lam⌋₊ :=
            (one_le_floor_iff_ge lam _ C.hlam).mpr hb2
          have hsum : n + 1 ≤ ⌊(z - theta T) / lam⌋₊ + ⌊(x - z) / lam⌋₊ +
              ⌊(y - x) / lam⌋₊ + ⌊(theta T + Real.pi - y) / lam⌋₊ := by omega
          exact ff_floor_sum_overflow C hHT.symm hAT.symm hBT.symm h1T h2T hPT
            ((phi_comm C hHT.symm).trans hz_def.symm)
            ((phi_comm C hAT.symm).trans hx_def.symm)
            ((phi_comm C hBT.symm).trans hy_def.symm) hsum
        · -- `{1}`: `x − z ≥ (n−1)λ` reaches `u`.
          have hs0' : ⌊(z - theta T) / lam⌋₊ = 0 := ff_floor_zero C hs0
          have hs2' : ⌊(y - x) / lam⌋₊ = 0 := ff_floor_zero C hs2
          have hsum : ⌊(x - z) / lam⌋₊ - 1 = n - 2 := by omega
          have e1 := ff_floor_sub_one_mul_le C hb1
          have hre : ((⌊(x - z) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith only [e1, hm, hcz1, hxu, hcu2, hπ]
        · -- `{2}`: `y − x ≥ (n−1)λ` reaches `w`.
          have hs0' : ⌊(z - theta T) / lam⌋₊ = 0 := ff_floor_zero C hs0
          have hs1' : ⌊(x - z) / lam⌋₊ = 0 := ff_floor_zero C hs1
          have hsum : ⌊(y - x) / lam⌋₊ - 1 = n - 2 := by omega
          have e2 := ff_floor_sub_one_mul_le C hb2
          have hre : ((⌊(y - x) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
            rw [← ncast]; exact_mod_cast hsum
          have hm := congrArg (· * lam) hre
          linarith only [e2, hm, hcz1, hzx, hyw, hcw2, hπ]
        · -- `S = ∅`: `n = 2`.
          have hs0' : ⌊(z - theta T) / lam⌋₊ = 0 := ff_floor_zero C hs0
          have hs1' : ⌊(x - z) / lam⌋₊ = 0 := ff_floor_zero C hs1
          have hs2' : ⌊(y - x) / lam⌋₊ = 0 := ff_floor_zero C hs2
          omega
    · -- **beta**: `y < x < p`; row `B` order `θ_B < y < p < w` — row
      -- `B` alone dies.
      have h1B : dirRep o e (c ∘ v.succAbove) B T <
          dirRep o e (c ∘ v.succAbove) B A := by
        rw [phi_comm C hAB.symm]; exact lt_trans hyx hxp
      have h2B : dirRep o e (c ∘ v.succAbove) B A <
          dirRep o e (c ∘ v.succAbove) B H := by
        rw [phi_comm C hAB.symm, phi_comm C hHB.symm]; exact hpw
      have hrowB := row4_defect C rfl hBT hAB.symm hHB.symm h1B h2B
      rw [hPB] at hrowB
      rw [phi_comm C hAB.symm, phi_comm C hHB.symm] at hrowB
      simp only [← hw_def, ← hy_def, ← hp_def] at hrowB
      have hkB3 : ⌊(theta B + Real.pi - w) / lam⌋₊ = 0 := ff_floor_zero C hlsB'
      have hfB1 : 1 ≤ ⌊(p - y) / lam⌋₊ := (one_le_floor_iff_ge lam _ C.hlam).mpr
        (show lam ≤ p - y by
          rw [abs_of_neg (by linarith : y - p < 0)] at hc3; linarith)
      have hfB2 : 1 ≤ ⌊(w - p) / lam⌋₊ :=
        (one_le_floor_iff_ge lam _ C.hlam).mpr hwp'
      rcases le_or_gt lam (y - theta B) with hb0 | hs0
      · -- `{0,1,2}`: overflow.
        have hfB0 : 1 ≤ ⌊(y - theta B) / lam⌋₊ :=
          (one_le_floor_iff_ge lam _ C.hlam).mpr hb0
        have hsum : n + 1 ≤ ⌊(y - theta B) / lam⌋₊ + ⌊(p - y) / lam⌋₊ +
            ⌊(w - p) / lam⌋₊ + ⌊(theta B + Real.pi - w) / lam⌋₊ := by omega
        exact ff_floor_sum_overflow C hBT hAB.symm hHB.symm h1B h2B hPB
          hy_def.symm
          ((phi_comm C hAB.symm).trans hp_def.symm)
          ((phi_comm C hHB.symm).trans hw_def.symm) hsum
      · -- `{1,2}`: `w − y ≥ nλ` against `y > θ_T > θ_H` and `w ≤ π − λ + θ_H`.
        have hs0' : ⌊(y - theta B) / lam⌋₊ = 0 := ff_floor_zero C hs0
        have hsum : (⌊(p - y) / lam⌋₊ - 1) + (⌊(w - p) / lam⌋₊ - 1) = n - 2 := by
          omega
        have e1 := ff_floor_sub_one_mul_le C (show lam ≤ p - y by
          rw [abs_of_neg (by linarith : y - p < 0)] at hc3; linarith)
        have e2 := ff_floor_sub_one_mul_le C hwp'
        have hre : ((⌊(p - y) / lam⌋₊ - 1 : ℕ) : ℝ) +
            ((⌊(w - p) / lam⌋₊ - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
          rw [← Nat.cast_add, ← ncast]; exact_mod_cast hsum
        have hm := congrArg (· * lam) hre
        rw [add_mul] at hm
        linarith only [e1, e2, hm, hyt, htgt, hcw2, hπ]

/-- **L/L same-side two-in exclusion.**  Two short witnesses into `H`
from below (`θ_A, θ_B < θ_H`, `φ_HA < φ_HB`) are impossible.

Both senders are short-last (a short-first sender would sit above `H`),
which forces `Up A H` and `Up B H`, and `two_in_L_below` places
`φ_HT < φ_HA`.  `ll_reduces_to_Asource` then discharges fifteen of the
sixteen orientations — eight via `ll_not_upBA`, four via transitivity,
three via the single-row defect leaves — and the residual A-source
orientation is killed by `ll_leaf_Asource`. -/
theorem same_side_two_in_L {H A B T : Fin 4}
    (hHA : H ≠ A) (hHB : H ≠ B) (hHT : H ≠ T)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T)
    (hwa : ShortWitness (lam := lam) (c := c) o e v theta A H)
    (hwb : ShortWitness (lam := lam) (c := c) o e v theta B H)
    (haθ : theta A < theta H) (hbθ : theta B < theta H)
    (hord : dirRep o e (c ∘ v.succAbove) H A <
      dirRep o e (c ∘ v.succAbove) H B)
    (hzta : dirRep o e (c ∘ v.succAbove) H T ≠
      dirRep o e (c ∘ v.succAbove) H A)
    (hztb : dirRep o e (c ∘ v.succAbove) H T ≠
      dirRep o e (c ∘ v.succAbove) H B)
    (hH : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove H)))
    (hPA : rowDefect n lam (directionRow o e c (v.succAbove A)) = 2)
    (hPB : rowDefect n lam (directionRow o e c (v.succAbove B)) = 2)
    (hPT : rowDefect n lam (directionRow o e c (v.succAbove T)) = 2) :
    False := by
  have hn2 : 2 ≤ n := by have := C.hn3; omega
  -- L-side witnesses are short-last: a short-first sender `S → H`
  -- lies in the bottom sliver of row `S`, forcing `θ_H < θ_S`,
  -- contradicting `θ_S < θ_H`.
  have hlsA : theta A + Real.pi - dirRep o e (c ∘ v.succAbove) A H < lam := by
    rcases hwa.2 with hf | hl
    · exfalso
      have hlt := saturated_row_bot_sliver_forces_low o e C.he hn2 C.hlam
        C.hn C.hleg v C.htheta A H hwa.1 le_rfl (by linarith)
      linarith
    · exact hl
  have hlsB : theta B + Real.pi - dirRep o e (c ∘ v.succAbove) B H < lam := by
    rcases hwb.2 with hf | hl
    · exfalso
      have hlt := saturated_row_bot_sliver_forces_low o e C.he hn2 C.hlam
        C.hn C.hleg v C.htheta B H hwb.1 le_rfl (by linarith)
      linarith
    · exact hl
  have hupAH := up_of_short_last C hHA.symm hlsA
  have hupBH := up_of_short_last C hHB.symm hlsB
  obtain ⟨hzu, -, -⟩ :=
    two_in_L_below C hHA hHB hHT hwa hwb haθ hbθ hord hzta hztb hH
  obtain ⟨hupHT, hupAT, hupBT, hupAB⟩ :=
    ll_reduces_to_Asource C hHA hHB hHT hAB hAT hBT hPA hPT hlsA hlsB hord hzu
      hupAH hupBH
  exact ll_leaf_Asource C hHA hHB hHT hAB hAT hBT hPB hPT hlsA hlsB haθ hbθ
    hord hzu hupAH hupBH hupHT hupAB hupAT hupBT

end SameSideTwoIn

end Jsp404
