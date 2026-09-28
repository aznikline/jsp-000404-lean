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

end SameSideTwoIn

end Jsp404
