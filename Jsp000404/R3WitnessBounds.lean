import Jsp000404.SameSideTwoIn

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section R3Dag

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}
  (C : SatChart o e n lam c v theta)
include C

/-- `theta` order determines `Up`: `theta a < theta b → Up a b`. -/
theorem up_of_theta_lt {a b : Fin 4} (hab : a ≠ b) (h : theta a < theta b) :
    Up o e c v a b := by
  rcases up_or_up C hab with h1 | h1
  · exact h1
  · exfalso; exact absurd (up_theta_lt C hab.symm h1) (by linarith)

/-- **Fan-gap overflow.**  In a defect-`2` row with sorted fan positions
`A < B < D`, three fan gaps `≥ lam` force `Σ⌊g/λ⌋ ≥ n+1`, contradicting
`fl_sum4` (`Σ⌊g/λ⌋ ≤ n` since the gaps sum to `π < (n+1)·lam`).  The
caller supplies the three floor witnesses `1 ≤ ⌊g/λ⌋₊`. -/
theorem r3_fan_overflow {a p q r : Fin 4} {A B D : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (h1 : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (h2 : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hg0 : 0 ≤ A - theta a) (hg1 : 0 ≤ B - A) (hg2 : 0 ≤ D - B)
    (hg3 : 0 ≤ theta a + Real.pi - D)
    (h3 : (1 ≤ ⌊(A - theta a) / lam⌋₊ ∧ 1 ≤ ⌊(B - A) / lam⌋₊ ∧
        1 ≤ ⌊(D - B) / lam⌋₊) ∨
      (1 ≤ ⌊(A - theta a) / lam⌋₊ ∧ 1 ≤ ⌊(B - A) / lam⌋₊ ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) ∨
      (1 ≤ ⌊(A - theta a) / lam⌋₊ ∧ 1 ≤ ⌊(D - B) / lam⌋₊ ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) ∨
      (1 ≤ ⌊(B - A) / lam⌋₊ ∧ 1 ≤ ⌊(D - B) / lam⌋₊ ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊)) : False := by
  have hrow := row4_defect C rfl hap haq har h1 h2
  rw [hda, hA, hB, hD] at hrow
  have hsum := fl_sum4 C.hlam C.hπ hg0 hg1 hg2 hg3 (by linarith)
  rcases h3 with ⟨e0, e1, e2⟩ | ⟨e0, e1, e3⟩ | ⟨e0, e2, e3⟩ | ⟨e1, e2, e3⟩ <;>
    omega

/-- **Fan-gap underflow.**  In a defect-`2` row with sorted fan
positions `A < B < D`, if the minimum chord lies *below* `theta a`
(`A < θ_a`, so its "gap" is negative and `⌊(A−θ_a)/λ⌋₊ = 0`) while the
remaining three gaps each contribute `⌊g/λ⌋₊ ≥ 1`, the defect equation
forces `f₁+f₂+f₃ = n+1`, hence `(n+1)·λ ≤ θ_a + π − A`, i.e.
`A ≤ θ_a + β − λ < λ` — contradicting `lam ≤ A` (`phi_ge_lam`). -/
theorem r3_fan_underflow {a p q r : Fin 4} {A B D : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (h1 : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (h2 : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hθA : A < theta a)
    (hg1 : 0 ≤ B - A) (hg2 : 0 ≤ D - B) (hg3 : 0 ≤ theta a + Real.pi - D)
    (h3 : 1 ≤ ⌊(B - A) / lam⌋₊ ∧ 1 ≤ ⌊(D - B) / lam⌋₊ ∧
      1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) : False := by
  have hrow := row4_defect C rfl hap haq har h1 h2
  rw [hda, hA, hB, hD] at hrow
  have hf0 : ⌊(A - theta a) / lam⌋₊ = 0 := by
    rw [Nat.floor_eq_zero]
    have h := div_neg_of_neg_of_pos (by linarith : A - theta a < 0) C.hlam
    linarith
  rw [hf0] at hrow
  obtain ⟨e1, e2, e3⟩ := h3
  have f1 := fl_mul_le C.hlam hg1
  have f2 := fl_mul_le C.hlam hg2
  have f3 := fl_mul_le C.hlam hg3
  have hAlam : lam ≤ A := by rw [← hA]; exact phi_ge_lam C hap
  have hθβ := (C.htheta a).1.2
  have hβ := C.hβ
  have hsum : (⌊(B - A) / lam⌋₊ : ℝ) + ⌊(D - B) / lam⌋₊ +
      ⌊(theta a + Real.pi - D) / lam⌋₊ = n + 1 := by
    have h : ⌊(B - A) / lam⌋₊ + ⌊(D - B) / lam⌋₊ +
        ⌊(theta a + Real.pi - D) / lam⌋₊ = n + 1 := by omega
    exact_mod_cast h
  nlinarith [hβ]

/-- **Low-row minimum.**  In the `theta`-order `u < a < x < w` the
chord from `a` to its lowest-`theta` target `u` is the minimum of row
`a` whenever `a` has defect `2`.  Every other position order puts three
big gaps into the fan: the first gap is big because the lowest chord
goes to a higher-`theta` target (corridor), and two inner gaps are big
by caps across `theta a`. -/
theorem r3_low_min {u a x w : Fin 4}
    (hua : u ≠ a) (huv : u ≠ x) (huw : u ≠ w)
    (hav : a ≠ x) (haw : a ≠ w) (hvw : x ≠ w)
    (hθ0 : theta u < theta a) (hθ1 : theta a < theta x)
    (hθ2 : theta x < theta w)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2) :
    dirRep o e (c ∘ v.succAbove) a u < dirRep o e (c ∘ v.succAbove) a x ∧
      dirRep o e (c ∘ v.succAbove) a u < dirRep o e (c ∘ v.succAbove) a w := by
  classical
  set fu := dirRep o e (c ∘ v.succAbove) a u with hfu
  set fv := dirRep o e (c ∘ v.succAbove) a x with hfv
  set fw := dirRep o e (c ∘ v.succAbove) a w with hfw
  have hlam := C.hlam
  have hβ := C.hβ
  have hn3 : 3 ≤ n := C.hn3
  obtain ⟨ta0, taβ⟩ := (C.htheta a).1
  -- `Up` facts from the `theta` order.
  have hupUA : Up o e c v u a := up_of_theta_lt C hua hθ0
  have hupAV : Up o e c v a x := up_of_theta_lt C hav hθ1
  have hupAW : Up o e c v a w := up_of_theta_lt C haw (lt_trans hθ1 hθ2)
  -- Corridors: `θ_u + λ ≤ fu ≤ π − λ + θ_a`; `θ_a + λ ≤ fv, fw`.
  obtain ⟨hcu1, hcu2⟩ := up_corridor C hua hupUA
  obtain ⟨hcv1, hcv2⟩ := up_corridor C hav hupAV
  obtain ⟨hcw1, hcw2⟩ := up_corridor C haw hupAW
  rw [phi_comm C hua] at hcu1 hcu2
  -- Caps across `theta a`: `λ ≤ |fv − fu|`, `λ ≤ |fw − fu|`.
  have hcapV := up_cap C hua hav huv hupUA hupAV
  have hcapW := up_cap C hua haw huw hupUA hupAW
  rw [phi_comm C hua] at hcapV hcapW
  simp only [← hfu, ← hfv, ← hfw] at hcu1 hcu2 hcv1 hcv2 hcw1 hcw2 hcapV hcapW
  -- `dirRep` distinctness for the three chords of row `a`.
  have hne_uv : fu ≠ fv := by
    have h := legal_dirRep_ne C C.hleg C.he
      (show v.succAbove a ≠ v.succAbove u from
        fun h => hua (Fin.succAbove_right_injective h).symm)
      (show v.succAbove a ≠ v.succAbove x from
        fun h => hav (Fin.succAbove_right_injective h))
      (show v.succAbove u ≠ v.succAbove x from
        fun h => huv (Fin.succAbove_right_injective h))
    rw [hfu, hfv]; exact h
  have hne_uw : fu ≠ fw := by
    have h := legal_dirRep_ne C C.hleg C.he
      (show v.succAbove a ≠ v.succAbove u from
        fun h => hua (Fin.succAbove_right_injective h).symm)
      (show v.succAbove a ≠ v.succAbove w from
        fun h => haw (Fin.succAbove_right_injective h))
      (show v.succAbove u ≠ v.succAbove w from
        fun h => huw (Fin.succAbove_right_injective h))
    rw [hfu, hfw]; exact h
  have hne_vw : fv ≠ fw := by
    have h := legal_dirRep_ne C C.hleg C.he
      (show v.succAbove a ≠ v.succAbove x from
        fun h => hav (Fin.succAbove_right_injective h))
      (show v.succAbove a ≠ v.succAbove w from
        fun h => haw (Fin.succAbove_right_injective h))
      (show v.succAbove x ≠ v.succAbove w from
        fun h => hvw (Fin.succAbove_right_injective h))
    rw [hfv, hfw]; exact h
  -- `lam ≤ fu` etc. and `fu < π`.
  have hfu_l := phi_ge_lam C hua
  have hfv_l := phi_ge_lam C hav
  have hfw_l := phi_ge_lam C haw
  have hfu_π := (phi_mem C a u).2
  have hfv_π := (phi_mem C a x).2
  have hfw_π := (phi_mem C a w).2
  simp only [← hfu, ← hfv, ← hfw] at hfu_l hfv_l hfw_l hfu_π hfv_π hfw_π
  -- Case split on the order of `fu, fv, fw`; the four orders where `fu`
  -- is not the minimum each put three big gaps into the fan.
  rcases lt_trichotomy fu fv with hufv | hufv | hufv
  · rcases lt_trichotomy fu fw with hufw | hufw | hufw
    · exact ⟨hufv, hufw⟩
    · exact absurd hufw hne_uw
    · -- `fw < fu < fv`: perm `(w,u,x)` — big gaps `g0, g1, g2`.
      exact (r3_fan_overflow C haw hua.symm hav hufw hufv hda hfw hfu hfv
        (by linarith) (by linarith) (by linarith) (by linarith)
        (Or.inl ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
            (by linarith : lam ≤ fw - theta a),
          one_le_floor_iff_ge lam _ hlam |>.mpr
            (by
              rw [abs_of_neg (sub_neg.mpr hufw)] at hcapW
              linarith : lam ≤ fu - fw),
          one_le_floor_iff_ge lam _ hlam |>.mpr
            (by
              rw [abs_of_pos (sub_pos.mpr hufv)] at hcapV
              linarith : lam ≤ fv - fu)⟩)).elim
  · exact absurd hufv hne_uv
  · rcases lt_trichotomy fu fw with hufw | hufw | hufw
    · -- `fv < fu < fw`: perm `(x,u,w)` — big gaps `g0, g1, g2`.
      exact (r3_fan_overflow C hav hua.symm haw hufv hufw hda hfv hfu hfw
        (by linarith) (by linarith) (by linarith) (by linarith)
        (Or.inl ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
            (by linarith : lam ≤ fv - theta a),
          one_le_floor_iff_ge lam _ hlam |>.mpr
            (by
              rw [abs_of_neg (sub_neg.mpr hufv)] at hcapV
              linarith : lam ≤ fu - fv),
          one_le_floor_iff_ge lam _ hlam |>.mpr
            (by
              rw [abs_of_pos (sub_pos.mpr hufw)] at hcapW
              linarith : lam ≤ fw - fu)⟩)).elim
    · exact absurd hufw hne_uw
    · rcases lt_trichotomy fv fw with hvw' | hvw' | hvw'
      · -- `fv < fw < fu`: perm `(x,w,u)` — big gaps `g0, g2, g3`.
        exact (r3_fan_overflow C hav haw hua.symm hvw' hufw hda hfv hfw hfu
          (by linarith) (by linarith) (by linarith) (by linarith)
          (Or.inr <| Or.inr <| Or.inl
            ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ fv - theta a),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_neg (sub_neg.mpr hufw)] at hcapW
                  linarith : lam ≤ fu - fw),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ theta a + Real.pi - fu)⟩)).elim
      · exact absurd hvw' hne_vw
      · -- `fw < fv < fu`: perm `(w,x,u)` — big gaps `g0, g2, g3`.
        exact (r3_fan_overflow C haw hav hua.symm hvw' hufv hda hfw hfv hfu
          (by linarith) (by linarith) (by linarith) (by linarith)
          (Or.inr <| Or.inr <| Or.inl
            ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ fw - theta a),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_neg (sub_neg.mpr hufv)] at hcapV
                  linarith : lam ≤ fu - fv),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ theta a + Real.pi - fu)⟩)).elim

/-- **Low-row maximum (mirror of `r3_low_min`).**  In the `theta`-order
`u < x < b < y` the chord from `b` to its highest-`theta` target `y`
is the maximum of row `b` whenever `b` has defect `2`.  Every other
position order puts three big gaps into the fan: the last gap is big
because the highest chord goes to a lower-`theta` target (corridor),
and the remaining big gaps come from corridors and caps across
`theta b`. -/
theorem r3_high_max {u x b y : Fin 4}
    (hub : u ≠ b) (hux : u ≠ x) (huy : u ≠ y)
    (hxb : x ≠ b) (hxy : x ≠ y) (hby : b ≠ y)
    (hθ0 : theta u < theta x) (hθ1 : theta x < theta b)
    (hθ2 : theta b < theta y)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2) :
    dirRep o e (c ∘ v.succAbove) b u < dirRep o e (c ∘ v.succAbove) b y ∧
      dirRep o e (c ∘ v.succAbove) b x < dirRep o e (c ∘ v.succAbove) b y := by
  classical
  set fu := dirRep o e (c ∘ v.succAbove) b u with hfu
  set fx := dirRep o e (c ∘ v.succAbove) b x with hfx
  set fy := dirRep o e (c ∘ v.succAbove) b y with hfy
  have hlam := C.hlam
  have hβ := C.hβ
  have hn3 : 3 ≤ n := C.hn3
  -- `Up` facts from the `theta` order.
  have hupUB : Up o e c v u b := up_of_theta_lt C hub (lt_trans hθ0 hθ1)
  have hupXB : Up o e c v x b := up_of_theta_lt C hxb hθ1
  have hupBY : Up o e c v b y := up_of_theta_lt C hby hθ2
  -- Corridors: `θ_u + λ ≤ fu ≤ π − λ + θ_b`; same for `fx`;
  -- `θ_b + λ ≤ fy`.
  obtain ⟨hcu1, hcu2⟩ := up_corridor C hub hupUB
  obtain ⟨hcx1, hcx2⟩ := up_corridor C hxb hupXB
  obtain ⟨hcy1, hcy2⟩ := up_corridor C hby hupBY
  rw [phi_comm C hub] at hcu1 hcu2
  rw [phi_comm C hxb] at hcx1 hcx2
  -- Caps across `theta b`: `λ ≤ |fy − fu|`, `λ ≤ |fy − fx|`.
  have hcapU := up_cap C hub hby huy hupUB hupBY
  have hcapX := up_cap C hxb hby hxy hupXB hupBY
  rw [phi_comm C hub] at hcapU
  rw [phi_comm C hxb] at hcapX
  simp only [← hfu, ← hfx, ← hfy] at hcu1 hcu2 hcx1 hcx2 hcy1 hcy2 hcapU hcapX
  -- `dirRep` distinctness for the three chords of row `b`.
  have hne_uy : fu ≠ fy := by
    have h := legal_dirRep_ne C C.hleg C.he
      (show v.succAbove b ≠ v.succAbove u from
        fun h => hub (Fin.succAbove_right_injective h).symm)
      (show v.succAbove b ≠ v.succAbove y from
        fun h => hby (Fin.succAbove_right_injective h))
      (show v.succAbove u ≠ v.succAbove y from
        fun h => huy (Fin.succAbove_right_injective h))
    rw [hfu, hfy]; exact h
  have hne_xy : fx ≠ fy := by
    have h := legal_dirRep_ne C C.hleg C.he
      (show v.succAbove b ≠ v.succAbove x from
        fun h => hxb (Fin.succAbove_right_injective h).symm)
      (show v.succAbove b ≠ v.succAbove y from
        fun h => hby (Fin.succAbove_right_injective h))
      (show v.succAbove x ≠ v.succAbove y from
        fun h => hxy (Fin.succAbove_right_injective h))
    rw [hfx, hfy]; exact h
  have hne_ux : fu ≠ fx := by
    have h := legal_dirRep_ne C C.hleg C.he
      (show v.succAbove b ≠ v.succAbove u from
        fun h => hub (Fin.succAbove_right_injective h).symm)
      (show v.succAbove b ≠ v.succAbove x from
        fun h => hxb (Fin.succAbove_right_injective h).symm)
      (show v.succAbove u ≠ v.succAbove x from
        fun h => hux (Fin.succAbove_right_injective h))
    rw [hfu, hfx]; exact h
  -- `fu < π` etc.
  have hfu_π := (phi_mem C b u).2
  have hfx_π := (phi_mem C b x).2
  have hfy_π := (phi_mem C b y).2
  simp only [← hfu, ← hfx, ← hfy] at hfu_π hfx_π hfy_π
  -- Case split on the order of `fu, fx, fy`; the four orders where `fy`
  -- is not the maximum each put three big gaps into the fan (or, when
  -- the minimum below-chord lies under `theta b`, an underflow).
  rcases lt_trichotomy fy fu with hyu | hyu | hyu
  · rcases lt_trichotomy fy fx with hyx | hyx | hyx
    · -- `fy` below both: split `fu` vs `fx`.
      rcases lt_trichotomy fu fx with hux' | hux' | hux'
      · -- `fy < fu < fx`: perm `(y,u,x)` — big gaps `g0, g1, g3`.
        exact (r3_fan_overflow C hby hub.symm hxb.symm hyu hux' hdb
          hfy hfu hfx (by linarith) (by linarith) (by linarith) (by linarith)
          (Or.inr <| Or.inl
            ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ fy - theta b),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_neg (sub_neg.mpr hyu)] at hcapU
                  linarith : lam ≤ fu - fy),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ theta b + Real.pi - fx)⟩)).elim
      · exact absurd hux' hne_ux
      · -- `fy < fx < fu`: perm `(y,x,u)` — big gaps `g0, g1, g3`.
        exact (r3_fan_overflow C hby hxb.symm hub.symm hyx hux' hdb
          hfy hfx hfu (by linarith) (by linarith) (by linarith) (by linarith)
          (Or.inr <| Or.inl
            ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ fy - theta b),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_neg (sub_neg.mpr hyx)] at hcapX
                  linarith : lam ≤ fx - fy),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ theta b + Real.pi - fu)⟩)).elim
    · exact absurd hyx.symm hne_xy
    · -- `fx < fy < fu`: perm `(x,y,u)` — big gaps `g1, g2, g3`, or
      -- underflow when `fx < theta b`.
      by_cases hfxθ : fx < theta b
      · exact (r3_fan_underflow C hxb.symm hby hub.symm hyx hyu hdb
          hfx hfy hfu hfxθ (by linarith) (by linarith) (by linarith)
          ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
              (by
                rw [abs_of_pos (sub_pos.mpr hyx)] at hcapX
                linarith : lam ≤ fy - fx),
            one_le_floor_iff_ge lam _ hlam |>.mpr
              (by
                rw [abs_of_neg (sub_neg.mpr hyu)] at hcapU
                linarith : lam ≤ fu - fy),
            one_le_floor_iff_ge lam _ hlam |>.mpr
              (by linarith : lam ≤ theta b + Real.pi - fu)⟩).elim
      · exact (r3_fan_overflow C hxb.symm hby hub.symm hyx hyu hdb
          hfx hfy hfu (by linarith) (by linarith) (by linarith) (by linarith)
          (Or.inr <| Or.inr <| Or.inr
            ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_pos (sub_pos.mpr hyx)] at hcapX
                  linarith : lam ≤ fy - fx),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_neg (sub_neg.mpr hyu)] at hcapU
                  linarith : lam ≤ fu - fy),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ theta b + Real.pi - fu)⟩)).elim
  · exact absurd hyu.symm hne_uy
  · -- `fu < fy`: decide by `fy` vs `fx`.
    rcases lt_trichotomy fy fx with hyx | hyx | hyx
    · -- `fu < fy < fx`: perm `(u,y,x)` — big gaps `g1, g2, g3`, or
      -- underflow when `fu < theta b`.
      by_cases hfuθ : fu < theta b
      · exact (r3_fan_underflow C hub.symm hby hxb.symm hyu hyx hdb
          hfu hfy hfx hfuθ (by linarith) (by linarith) (by linarith)
          ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
              (by
                rw [abs_of_pos (sub_pos.mpr hyu)] at hcapU
                linarith : lam ≤ fy - fu),
            one_le_floor_iff_ge lam _ hlam |>.mpr
              (by
                rw [abs_of_neg (sub_neg.mpr hyx)] at hcapX
                linarith : lam ≤ fx - fy),
            one_le_floor_iff_ge lam _ hlam |>.mpr
              (by linarith : lam ≤ theta b + Real.pi - fx)⟩).elim
      · exact (r3_fan_overflow C hub.symm hby hxb.symm hyu hyx hdb
          hfu hfy hfx (by linarith) (by linarith) (by linarith) (by linarith)
          (Or.inr <| Or.inr <| Or.inr
            ⟨one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_pos (sub_pos.mpr hyu)] at hcapU
                  linarith : lam ≤ fy - fu),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by
                  rw [abs_of_neg (sub_neg.mpr hyx)] at hcapX
                  linarith : lam ≤ fx - fy),
              one_le_floor_iff_ge lam _ hlam |>.mpr
                (by linarith : lam ≤ theta b + Real.pi - fx)⟩)).elim
    · exact absurd hyx.symm hne_xy
    · exact ⟨hyu, hyx⟩

end R3Dag

end Jsp404
