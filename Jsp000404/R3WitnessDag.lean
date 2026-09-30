import Jsp000404.SameSideTwoIn

/-!
# R=3 closure via θ-order pair-kill

Five-point `SatChart` (s = 4): anchor defect `1`, three low rows
defect `2`, high row defect `≥ 3`.  This file proves such a
configuration cannot exist.

## Discovery vs. proof

The original plan enumerated `ShortWitness` DAG classes.  Exploration
(`tools/r3_class_synth.py`) found a much sharper route: the new lemma
`up_theta_lt` turns `Up` into a strict `theta` order, after which the
pure defect profile `(2,2,2,≥3)` is already impossible — no witness
graph is needed.  The kills below are the kernel-checked certificates
of that finding, organized as *pair-kill* lemmas.

## Structure

Let the four non-anchor rows be ordered by `theta` as `t0 < t1 < t2 < t3`
and let `a < b` (in `theta`) be two defect-`2` rows.

* `pairkill_outer`:  `θ_x < θ_a < θ_b < θ_y` — the pair sits between
  two outsiders.  Row `a` must have `φ_{a,x}` as its row minimum and
  row `b` must have `φ_{b,y}` as its row maximum (`r3_low_min` /
  `r3_high_max`); the unique surviving position-order pair dies to the
  coupled defect equations (`r3_outer_coupled`).
* `pairkill_midtop`: `θ_a < θ_x < θ_b < θ_y`.
* `pairkill_midbot`: `θ_y < θ_a < θ_x < θ_b`.

`five_point_R3_impossible` then sorts the three defect-`2` rows and
dispatches on the rank of the high row `h` among them.
-/

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

/-- **Defect-2 fan trichotomy — forced first inner gap.**  For a sorted
row `A < B < D` with fan cut `theta a`, if the first inner gap is big
(`lam ≤ B − A`, supplied as `1 ≤ ⌊(B−A)/λ⌋₊`), the row's big-gap pattern
is one of `{0,1}`, `{1}`, `{1,3}`: every pattern containing `2`, the
triple `{0,1,3}`, or all four gaps overflows the defect equation
against the corridors (`A ≥ tl + lam`, `D ≤ π − lam + th`,
`tl < theta a < th ≤ β`). -/
theorem r3_fan_trich_lo {a p q r : Fin 4} {A B D tl th : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk1 : 1 ≤ ⌊(B - A) / lam⌋₊)
    (hAlo : tl + lam ≤ A) (hDhi : D ≤ Real.pi - lam + th)
    (htlt : tl < theta a) (htt : theta a < th)
    (htl0 : 0 ≤ tl) (htaβ : theta a ≤ Real.pi - n * lam)
    (hthβ : th ≤ Real.pi - n * lam) :
    (⌊(A - theta a) / lam⌋₊ + ⌊(B - A) / lam⌋₊ = n ∧ 1 ≤ ⌊(A - theta a) / lam⌋₊ ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(B - A) / lam⌋₊ = n - 1 ∧ ⌊(A - theta a) / lam⌋₊ = 0 ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(B - A) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  by_cases h2 : 1 ≤ f2
  · -- `f2` big: every pattern containing index `2` dies.
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,2,3}: Σf = n+2 → π ≥ (n+2)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {0,1,2}: D − ta ≥ (n+1)·lam but D < π < (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (D - B) := by
          have h : (f0:ℝ) + f1 + f2 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2]
        have hDlt : D < Real.pi := by linarith [hthβ, hβ]
        linarith [hFl, hDlt, hta0, hπ]
    · by_cases h3 : 1 ≤ f3
      · -- {1,2,3}: ta + π − A ≥ (n+1)·lam → A ≤ ta + β − λ < tl + λ
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f1:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2, e3]
        linarith [hFl, hAlo, htlt, htaβ, hβ]
      · -- {1,2}: D − A ≥ n·lam vs corridor bound (n−2)·lam + 2β
        exfalso
        have hFl : (n:ℝ) * lam ≤ (B - A) + (D - B) := by
          have h : (f1:ℝ) + f2 = n := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2]
        linarith [hFl, hAlo, hDhi, hthβ, htl0, hβ]
  · push_neg at h2
    have hf2z : f2 = 0 := Nat.lt_one_iff.mp h2
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,3}: π + B − D ≥ (n+1)·lam → B > D, contradicting sort
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e3]
        linarith [hFl, hord.2, hπ]
      · -- {0,1}: surviving family
        exact Or.inl ⟨by omega, h0, hf2z, by omega⟩
    · by_cases h3 : 1 ≤ f3
      · -- {1,3}: surviving family
        refine Or.inr (Or.inr ⟨by omega, by omega, hf2z, h3⟩)
      · -- {1}: f1 = n − 1
        exact Or.inr (Or.inl ⟨by omega, by omega, hf2z, by omega⟩)

/-- **Defect-2 fan trichotomy — forced last inner gap (mirror of
`r3_fan_trich_lo`).**  With `lam ≤ D − B` the big-gap pattern is one of
`{2}`, `{0,2}`, `{2,3}`. -/
theorem r3_fan_trich_hi {a p q r : Fin 4} {A B D tl th : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk2 : 1 ≤ ⌊(D - B) / lam⌋₊)
    (hAlo : tl + lam ≤ A) (hDhi : D ≤ Real.pi - lam + th)
    (htlt : tl < theta a) (htt : theta a < th)
    (htl0 : 0 ≤ tl) (htaβ : theta a ≤ Real.pi - n * lam)
    (hthβ : th ≤ Real.pi - n * lam) :
    (⌊(D - B) / lam⌋₊ = n - 1 ∧ ⌊(A - theta a) / lam⌋₊ = 0 ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(D - B) / lam⌋₊ = n ∧
        1 ≤ ⌊(A - theta a) / lam⌋₊ ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(D - B) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  by_cases h1 : 1 ≤ f1
  · -- `f1` big: every pattern containing index `1` dies.
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,2,3}: π ≥ (n+2)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {0,1,2}: D − ta ≥ (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (D - B) := by
          have h : (f0:ℝ) + f1 + f2 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2]
        have hDlt : D < Real.pi := by linarith [hthβ, hβ]
        linarith [hFl, hDlt, hta0, hπ]
    · by_cases h3 : 1 ≤ f3
      · -- {1,2,3}: ta + π − A ≥ (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f1:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2, e3]
        linarith [hFl, hAlo, htlt, htaβ, hβ]
      · -- {1,2}: D − A ≥ n·lam
        exfalso
        have hFl : (n:ℝ) * lam ≤ (B - A) + (D - B) := by
          have h : (f1:ℝ) + f2 = n := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2]
        linarith [hFl, hAlo, hDhi, hthβ, htl0, hβ]
  · push_neg at h1
    have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
    by_cases h0 : 1 ≤ f0
    · by_cases h3 : 1 ≤ f3
      · -- {0,2,3}: π + A − B ≥ (n+1)·lam → A > B
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e2, e3]
        linarith [hFl, hord.1, hπ]
      · -- {0,2}: surviving family
        exact Or.inr (Or.inl ⟨by omega, h0, hf1z, by omega⟩)
    · by_cases h3 : 1 ≤ f3
      · -- {2,3}: surviving family
        exact Or.inr (Or.inr ⟨by omega, by omega, hf1z, h3⟩)
      · -- {2}: f2 = n − 1
        exact Or.inl ⟨by omega, by omega, hf1z, by omega⟩

/-- **Defect-2 fan tetratomy — all-up row (forced first gap).**  When
every target lies above `theta a`, the first gap is always big
(`A ≥ theta a + lam`).  The big-gap pattern is one of `{0}`, `{0,1}`,
`{0,2}`, `{0,3}`; every pattern with three or more big gaps overflows.
Only ordering facts and `lam ≤ A`, `D < π`, `theta a ≤ β` are needed. -/
theorem r3_fan_trich_t3 {a p q r : Fin 4} {A B D : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk0 : 1 ≤ ⌊(A - theta a) / lam⌋₊)
    (hAl : lam ≤ A) (hDl : D < Real.pi)
    (htaβ : theta a ≤ Real.pi - n * lam) :
    (⌊(A - theta a) / lam⌋₊ = n - 1 ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(B - A) / lam⌋₊ = n ∧
        ⌊(D - B) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(B - A) / lam⌋₊) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(D - B) / lam⌋₊ = n ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(theta a + Real.pi - D) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(D - B) / lam⌋₊) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  -- every pattern with ≥3 big gaps dies; `f0` is always big.
  by_cases h1 : 1 ≤ f1
  · by_cases h2 : 1 ≤ f2
    · by_cases h3 : 1 ≤ f3
      · exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {0,1,2}: D − ta ≥ (n+1)·lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (D - B) := by
          have h : (f0:ℝ) + f1 + f2 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2]
        linarith [hFl, hDl, hta0, hπ]
    · by_cases h3 : 1 ≤ f3
      · -- {0,1,3}: B + π − D ≥ (n+1)·lam → B > D
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e3]
        linarith [hFl, hord.2, hπ]
      · -- {0,1}
        exact Or.inr (Or.inl ⟨by omega, by omega, by omega, h1⟩)
  · push_neg at h1
    have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
    by_cases h2 : 1 ≤ f2
    · by_cases h3 : 1 ≤ f3
      · -- {0,2,3}: A + π − B ≥ (n+1)·lam → A > B
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e2, e3]
        linarith [hFl, hord.1, hπ]
      · -- {0,2}
        exact Or.inr (Or.inr (Or.inl ⟨by omega, hf1z, by omega, h2⟩))
    · push_neg at h2
      have hf2z : f2 = 0 := Nat.lt_one_iff.mp h2
      by_cases h3 : 1 ≤ f3
      · -- {0,3}
        exact Or.inr (Or.inr (Or.inr ⟨by omega, hf1z, hf2z, h3⟩))
      · -- {0}: f0 = n − 1
        exact Or.inl ⟨by omega, hf1z, hf2z, by omega⟩

/-- **Defect-2 fan tetratomy — all-down row (forced last gap).**  Mirror
of `r3_fan_trich_t3`: the last gap is always big; the big-gap pattern is
one of `{3}`, `{0,3}`, `{1,3}`, `{2,3}`. -/
theorem r3_fan_trich_t4 {a p q r : Fin 4} {A B D : ℝ}
    (hap : a ≠ p) (haq : a ≠ q) (har : a ≠ r)
    (hAB : dirRep o e (c ∘ v.succAbove) a p < dirRep o e (c ∘ v.succAbove) a q)
    (hBD : dirRep o e (c ∘ v.succAbove) a q < dirRep o e (c ∘ v.succAbove) a r)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hA : dirRep o e (c ∘ v.succAbove) a p = A)
    (hB : dirRep o e (c ∘ v.succAbove) a q = B)
    (hD : dirRep o e (c ∘ v.succAbove) a r = D)
    (hk3 : 1 ≤ ⌊(theta a + Real.pi - D) / lam⌋₊)
    (hAl : lam ≤ A) (hDl : D < Real.pi)
    (htaβ : theta a ≤ Real.pi - n * lam) :
    (⌊(theta a + Real.pi - D) / lam⌋₊ = n - 1 ∧ ⌊(A - theta a) / lam⌋₊ = 0 ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0) ∨
      (⌊(A - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(B - A) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(A - theta a) / lam⌋₊) ∨
      (⌊(B - A) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(D - B) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(B - A) / lam⌋₊) ∨
      (⌊(D - B) / lam⌋₊ + ⌊(theta a + Real.pi - D) / lam⌋₊ = n ∧
        ⌊(A - theta a) / lam⌋₊ = 0 ∧ ⌊(B - A) / lam⌋₊ = 0 ∧
        1 ≤ ⌊(D - B) / lam⌋₊) := by
  have hrow := row4_defect C rfl hap haq har hAB hBD
  rw [hda, hA, hB, hD] at hrow
  set f0 := ⌊(A - theta a) / lam⌋₊ with hf0
  set f1 := ⌊(B - A) / lam⌋₊ with hf1
  set f2 := ⌊(D - B) / lam⌋₊ with hf2
  set f3 := ⌊(theta a + Real.pi - D) / lam⌋₊ with hf3
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have hg0 : 0 ≤ A - theta a := by linarith
  have hg1 : 0 ≤ B - A := by linarith
  have hg2 : 0 ≤ D - B := by linarith
  have hg3 : 0 ≤ theta a + Real.pi - D := by linarith
  have e0 := fl_mul_le C.hlam hg0
  have e1 := fl_mul_le C.hlam hg1
  have e2 := fl_mul_le C.hlam hg2
  have e3 := fl_mul_le C.hlam hg3
  have hord : A < B ∧ B < D := ⟨by rw [← hA, ← hB]; exact hAB,
    by rw [← hB, ← hD]; exact hBD⟩
  by_cases h2 : 1 ≤ f2
  · by_cases h1 : 1 ≤ f1
    · by_cases h0 : 1 ≤ f0
      · -- {0,1,2,3}
        exfalso
        have hFl : (n:ℝ) * lam + 2 * lam ≤ (A - theta a) + (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f2 + f3 = n + 2 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e2, e3]
        linarith [hFl, hπ]
      · -- {1,2,3}: ta + π − A ≥ (n+1)·lam → A < lam
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (B - A) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f1:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e1, e2, e3]
        linarith [hFl, hAl, htaβ, hβ]
    · push_neg at h1
      have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
      by_cases h0 : 1 ≤ f0
      · -- {0,2,3}: A + π − B ≥ (n+1)·lam → A > B
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (D - B) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f2 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e2, e3]
        linarith [hFl, hord.1, hπ]
      · -- {2,3}
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hf1z, h2⟩))
  · push_neg at h2
    have hf2z : f2 = 0 := Nat.lt_one_iff.mp h2
    by_cases h1 : 1 ≤ f1
    · by_cases h0 : 1 ≤ f0
      · -- {0,1,3}: B + π − D ≥ (n+1)·lam → B > D
        exfalso
        have hFl : (n:ℝ) * lam + 1 * lam ≤ (A - theta a) + (B - A) + (theta a + Real.pi - D) := by
          have h : (f0:ℝ) + f1 + f3 = n + 1 := by
            exact_mod_cast (by omega)
          linarith [congrArg (· * lam) h, e0, e1, e3]
        linarith [hFl, hord.2, hπ]
      · -- {1,3}
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, hf2z, h1⟩))
    · push_neg at h1
      have hf1z : f1 = 0 := Nat.lt_one_iff.mp h1
      by_cases h0 : 1 ≤ f0
      · -- {0,3}
        exact Or.inr (Or.inl ⟨by omega, hf1z, hf2z, h0⟩)
      · -- {3}: f3 = n − 1
        exact Or.inl ⟨by omega, by omega, hf1z, hf2z⟩

/-- **Pair-kill — outer.**  In the `theta`-order `x < a < b < y` two
defect-`2` rows `a,b` cannot coexist.  Transitivity pins the chord
order `φ_ax < φ_bx < φ_ab < φ_ay < φ_by`; caps force `1 ≤ f_{a1}` and
`1 ≤ f_{b2}`, and the nine signature pairs left by the two
trichotomies all die to short linear chains. -/
theorem pairkill_outer {x a b y : Fin 4}
    (hxa : x ≠ a) (hxb : x ≠ b) (hxy : x ≠ y)
    (hab : a ≠ b) (hay : a ≠ y) (hby : b ≠ y)
    (hθ0 : theta x < theta a) (hθ1 : theta a < theta b)
    (hθ2 : theta b < theta y)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2) : False := by
  classical
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hn3l : 3 * lam ≤ (n:ℝ) * lam :=
    mul_le_mul_of_nonneg_right C.hn3' (le_of_lt hlam)
  have hn3 : 3 ≤ n := C.hn3
  have hupXA : Up o e c v x a := up_of_theta_lt C hxa hθ0
  have hupXB : Up o e c v x b := up_of_theta_lt C hxb (lt_trans hθ0 hθ1)
  have hupAB : Up o e c v a b := up_of_theta_lt C hab hθ1
  have hupAY : Up o e c v a y := up_of_theta_lt C hay (lt_trans hθ1 hθ2)
  have hupBY : Up o e c v b y := up_of_theta_lt C hby hθ2
  obtain ⟨hmin1, hmin2⟩ := r3_low_min C hxa hxb hxy hab hay hby hθ0 hθ1 hθ2 hda
  obtain ⟨hmax1, hmax2⟩ := r3_high_max C hxb hxa hxy hab hay hby hθ0 hθ1 hθ2 hdb
  set fxa := dirRep o e (c ∘ v.succAbove) a x with hfxa
  set fba := dirRep o e (c ∘ v.succAbove) a b with hfba
  set fya := dirRep o e (c ∘ v.succAbove) a y with hfya
  set fxb := dirRep o e (c ∘ v.succAbove) b x with hfxb
  set fyb := dirRep o e (c ∘ v.succAbove) b y with hfyb
  obtain ⟨_, htr1⟩ := up_trans C hab hby hay hupAB hupBY
  obtain ⟨_, htr2⟩ := up_trans C hxa hab hxb hupXA hupAB
  obtain ⟨hcxa, hcxa'⟩ := up_corridor C hxa hupXA
  obtain ⟨hcxb, hcxb'⟩ := up_corridor C hxb hupXB
  obtain ⟨hcab, hcab'⟩ := up_corridor C hab hupAB
  obtain ⟨hcay, hcay'⟩ := up_corridor C hay hupAY
  obtain ⟨hcby, hcby'⟩ := up_corridor C hby hupBY
  have hcap1 := up_cap C hxa hab hxb hupXA hupAB
  have hcap2 := up_cap C hab hby hay hupAB hupBY
  rw [phi_comm C hxa] at htr2 hcap1 hcxa hcxa'
  rw [phi_comm C hxb] at htr2 hcxb hcxb'
  simp only [← hfxa, ← hfba, ← hfya, ← hfxb, ← hfyb] at hmin1 hmin2 hmax1 hmax2 htr1 htr2 hcxa hcxa' hcxb hcxb' hcab hcab' hcay hcay' hcby hcby' hcap1 hcap2
  -- full order: fxa < fxb < fba < fya < fyb
  have hfba_lt : fba < fyb := by
    have h := hmax2
    rw [← phi_comm C hab] at h
    exact h
  have hlt1 : fba < fya := by
    rcases htr1 with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso; linarith
  have hlt2 : fya < fyb := by
    rcases htr1 with ⟨-, h1⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso; linarith
  have hlt3 : fxb < fba := by
    rcases htr2 with ⟨-, h1⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso; linarith
  have hlt0' : fxa < fxb := by
    rcases htr2 with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso; linarith
  have hg1a : lam ≤ fba - fxa := by
    rw [abs_of_pos (by linarith : 0 < fba - fxa)] at hcap1; exact hcap1
  have hg2b : lam ≤ fyb - fba := by
    rw [abs_of_pos (by linarith : 0 < fyb - fba)] at hcap2; exact hcap2
  -- corridor data for the trichotomies
  have htx0 : 0 ≤ theta x := (C.htheta x).1.1
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have htb0 : 0 ≤ theta b := (C.htheta b).1.1
  have htaβ : theta a ≤ Real.pi - n * lam := (C.htheta a).1.2
  have htbβ : theta b ≤ Real.pi - n * lam := (C.htheta b).1.2
  have htyβ : theta y ≤ Real.pi - n * lam := (C.htheta y).1.2
  -- zero-floor conversion
  have hlt0 : ∀ {g : ℝ}, ⌊g / lam⌋₊ = 0 → g < lam := by
    intro g hg; rwa [Nat.floor_eq_zero, div_lt_one hlam] at hg
  -- floor lower bounds
  have e_a0 := fl_mul_le hlam (by linarith : 0 ≤ fxa - theta a)
  have e_a1 := fl_mul_le hlam (by linarith : 0 ≤ fba - fxa)
  have e_a2 := fl_mul_le hlam (by linarith : 0 ≤ fya - fba)
  have e_a3 := fl_mul_le hlam (by linarith : 0 ≤ theta a + Real.pi - fya)
  have e_b0 := fl_mul_le hlam (by linarith : 0 ≤ fxb - theta b)
  have e_b1 := fl_mul_le hlam (by linarith : 0 ≤ fba - fxb)
  have e_b2 := fl_mul_le hlam (by linarith : 0 ≤ fyb - fba)
  have e_b3 := fl_mul_le hlam (by linarith : 0 ≤ theta b + Real.pi - fyb)
  -- the two trichotomies
  have tria := r3_fan_trich_lo C hxa.symm hab hay hmin1 hlt1 hda rfl rfl rfl
    ((one_le_floor_iff_ge lam _ hlam).mpr hg1a) hcxa hcay' hθ0
    (lt_trans hθ1 hθ2) htx0 htaβ htyβ
  have trib := r3_fan_trich_hi C hxb.symm hab.symm hby
    (by rwa [← phi_comm C hab] : dirRep o e (c ∘ v.succAbove) b x <
      dirRep o e (c ∘ v.succAbove) b a) hmax2 hdb rfl
    (phi_comm C hab).symm rfl
    ((one_le_floor_iff_ge lam _ hlam).mpr hg2b) hcxb hcby'
    (lt_trans hθ0 hθ1) hθ2 htx0 htbβ htyβ
  simp only [← hfxa, ← hfba, ← hfya, ← hfxb, ← hfyb] at tria trib
  rcases tria with hA | hA | hA <;> rcases trib with hB | hB | hB
  · -- A{0,1} × B{2}: fba ≥ ta + nλ but fba < tb + 2λ
    obtain ⟨h01, -, -, -⟩ := hA; obtain ⟨-, h0z, h1z, -⟩ := hB
    have hge : (n:ℝ) * lam ≤ fba - theta a := by
      have h : (⌊(fxa - theta a) / lam⌋₊ : ℝ) + ⌊(fba - fxa) / lam⌋₊ = n := by
        exact_mod_cast h01
      linarith [congrArg (· * lam) h, e_a0, e_a1]
    linarith [hge, hlt0 h0z, hlt0 h1z, htbβ, hta0, hπ, hn3l]
  · -- A{0,1} × B{0,2}: fyb ≥ ta + (n+1)λ escapes the corridor
    obtain ⟨h01, -, -, -⟩ := hA
    have hge : (n:ℝ) * lam ≤ fba - theta a := by
      have h : (⌊(fxa - theta a) / lam⌋₊ : ℝ) + ⌊(fba - fxa) / lam⌋₊ = n := by
        exact_mod_cast h01
      linarith [congrArg (· * lam) h, e_a0, e_a1]
    linarith [hge, hg2b, hcby', htyβ, hta0, hβ]
  · -- A{0,1} × B{2,3}: fba ≥ ta + nλ but fba ≤ tb + β
    obtain ⟨h01, -, -, -⟩ := hA; obtain ⟨h23, -, -⟩ := hB
    have hge : (n:ℝ) * lam ≤ fba - theta a := by
      have h : (⌊(fxa - theta a) / lam⌋₊ : ℝ) + ⌊(fba - fxa) / lam⌋₊ = n := by
        exact_mod_cast h01
      linarith [congrArg (· * lam) h, e_a0, e_a1]
    have hle : fba ≤ theta b + Real.pi - n * lam := by
      have h : (⌊(fyb - fba) / lam⌋₊ : ℝ) + ⌊(theta b + Real.pi - fyb) / lam⌋₊
          = n := by exact_mod_cast h23
      linarith [congrArg (· * lam) h, e_b2, e_b3]
    linarith [hge, hle, htb0, hβ, hn3l]
  · -- A{1} × B{2}: fba ≥ tx + nλ but fba < tb + 2λ
    obtain ⟨h1n, -, -, -⟩ := hA; obtain ⟨-, h0z, h1z, -⟩ := hB
    have hge : (n:ℝ) * lam ≤ fba - theta x := by
      have h : (⌊(fba - fxa) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fba - fxa) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) h, e_a1, hcxa]
    linarith [hge, hlt0 h0z, hlt0 h1z, htbβ, htx0, hπ, hn3l]
  · -- A{1} × B{0,2}: fyb − fba < λ forces f_b0 = n, escaping corridor
    obtain ⟨h1n, -, -, -⟩ := hA; obtain ⟨h02, h0p, -, -⟩ := hB
    have hge : (n:ℝ) * lam ≤ fba - theta x := by
      have h : (⌊(fba - fxa) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fba - fxa) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) h, e_a1, hcxa]
    have hz : ⌊(fyb - fba) / lam⌋₊ = 0 := by
      have hlt : fyb - fba < lam := by linarith [hge, hcby', htyβ, htx0, hβ]
      rwa [Nat.floor_eq_zero, div_lt_one hlam]
    have hge2 : (n:ℝ) * lam ≤ fxb - theta b := by
      have h : (⌊(fxb - theta b) / lam⌋₊ : ℝ) = n := by
        exact_mod_cast (by omega : ⌊(fxb - theta b) / lam⌋₊ = n)
      linarith [congrArg (· * lam) h, e_b0]
    linarith [hge2, hlt3, hcab', htb0, hπ]
  · -- A{1} × B{2,3}: fba ≥ tx + nλ but fba ≤ tb + β
    obtain ⟨h1n, -, -, -⟩ := hA; obtain ⟨h23, -, -⟩ := hB
    have hge : (n:ℝ) * lam ≤ fba - theta x := by
      have h : (⌊(fba - fxa) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fba - fxa) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) h, e_a1, hcxa]
    have hle : fba ≤ theta b + Real.pi - n * lam := by
      have h : (⌊(fyb - fba) / lam⌋₊ : ℝ) + ⌊(theta b + Real.pi - fyb) / lam⌋₊
          = n := by exact_mod_cast h23
      linarith [congrArg (· * lam) h, e_b2, e_b3]
    linarith [hge, hle, htx0, htb0, hβ, hn3l]
  · -- A{1,3} × B{2}: fyb ≥ tx + (n+1)λ escapes corridor
    obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
    have hge : fyb ≥ theta x + (n:ℝ) * lam + lam := by
      have h : (⌊(fyb - fba) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fyb - fba) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) h, e_b2, hg1a, hcxa]
    linarith [hge, hcby', htyβ, htx0, hβ]
  · -- A{1,3} × B{0,2}: two-step parameter kill
    obtain ⟨h13, -, -, h3p⟩ := hA; obtain ⟨h02, h0p, -, -⟩ := hB
    -- step 1: (f_a3 + f_b0)·λ < π, so f_a3 + f_b0 ≤ n and f_a1 + f_b2 ≥ n
    have hltπ : ((⌊(theta a + Real.pi - fya) / lam⌋₊ : ℝ) +
        (⌊(fxb - theta b) / lam⌋₊ : ℝ)) * lam < Real.pi := by
      linarith [e_a3, e_b0, hlt3, hlt1, hθ1]
    have hsum' : ⌊(theta a + Real.pi - fya) / lam⌋₊ +
        ⌊(fxb - theta b) / lam⌋₊ ≤ n := by
      by_contra hcon
      push_neg at hcon
      have hge : ((n:ℝ) + 1) * lam ≤ ((⌊(theta a + Real.pi - fya) / lam⌋₊ : ℝ) +
          (⌊(fxb - theta b) / lam⌋₊ : ℝ)) * lam :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast (by omega : n + 1 ≤ ⌊(theta a + Real.pi - fya) / lam⌋₊ +
            ⌊(fxb - theta b) / lam⌋₊)) (le_of_lt hlam)
      linarith [hltπ, hπ]
    have hJ' : ⌊(fba - fxa) / lam⌋₊ + ⌊(fyb - fba) / lam⌋₊ ≥ n := by omega
    -- step 2: fyb ≥ tx + (n+1)λ escapes the corridor
    have hge : fyb ≥ theta x + (n:ℝ) * lam + lam := by
      have hJl : ((⌊(fba - fxa) / lam⌋₊ : ℝ) +
          (⌊(fyb - fba) / lam⌋₊ : ℝ)) * lam ≥ (n:ℝ) * lam :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hJ') (le_of_lt hlam)
      linarith [hJl, e_a1, e_b2, hcxa]
    linarith [hge, hcby', htyβ, htx0, hβ]
  · -- A{1,3} × B{2,3}: fba ≥ tx + 2λ but fba ≤ tb + β
    obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h23, -, -⟩ := hB
    have hge : theta x + 2 * lam ≤ fba := by linarith [hg1a, hcxa]
    have hle : fba ≤ theta b + Real.pi - n * lam := by
      have h : (⌊(fyb - fba) / lam⌋₊ : ℝ) + ⌊(theta b + Real.pi - fyb) / lam⌋₊
          = n := by exact_mod_cast h23
      linarith [congrArg (· * lam) h, e_b2, e_b3]
    linarith [hge, hle, htx0, htb0, hβ, hn3l]

set_option maxHeartbeats 1600000 in
/-- **Pair-kill — mid-top.**  In the `theta`-order `a < x < b < y` two
defect-`2` rows `a,b` cannot coexist.  Row `a` sees all three targets
above `theta a` (type T3); row `b` sees two below and one above (the
`hi` trichotomy with forced last inner gap).  The four transitivity
disjunctions split into 16 worlds: 8 die to pure order cycles, 5 to
three-big-gap overflow, and the three remaining worlds die to coupled
signature chains. -/
theorem pairkill_midtop {a x b y : Fin 4}
    (hax : a ≠ x) (hab : a ≠ b) (hay : a ≠ y)
    (hxb : x ≠ b) (hxy : x ≠ y) (hby : b ≠ y)
    (hθ0 : theta a < theta x) (hθ1 : theta x < theta b)
    (hθ2 : theta b < theta y)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2) : False := by
  classical
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hn3l : 3 * lam ≤ (n:ℝ) * lam :=
    mul_le_mul_of_nonneg_right C.hn3' (le_of_lt hlam)
  have hn3 : 3 ≤ n := C.hn3
  have hupAX : Up o e c v a x := up_of_theta_lt C hax hθ0
  have hupAB : Up o e c v a b := up_of_theta_lt C hab (lt_trans hθ0 hθ1)
  have hupAY : Up o e c v a y := up_of_theta_lt C hay (lt_trans (lt_trans hθ0 hθ1) hθ2)
  have hupXB : Up o e c v x b := up_of_theta_lt C hxb hθ1
  have hupXY : Up o e c v x y := up_of_theta_lt C hxy (lt_trans hθ1 hθ2)
  have hupBY : Up o e c v b y := up_of_theta_lt C hby hθ2
  obtain ⟨hcax, hcax'⟩ := up_corridor C hax hupAX
  obtain ⟨hcab, hcab'⟩ := up_corridor C hab hupAB
  obtain ⟨hcay, hcay'⟩ := up_corridor C hay hupAY
  obtain ⟨hcxb, hcxb'⟩ := up_corridor C hxb hupXB
  obtain ⟨hcxy, hcxy'⟩ := up_corridor C hxy hupXY
  obtain ⟨hcby, hcby'⟩ := up_corridor C hby hupBY
  have hcap0 := up_cap C hax hxb hab hupAX hupXB
  have hcap1 := up_cap C hax hxy hay hupAX hupXY
  have hcap2 := up_cap C hab hby hay hupAB hupBY
  have hcap3 := up_cap C hxb hby hxy hupXB hupBY
  obtain ⟨-, traxb⟩ := up_trans C hax hxb hab hupAX hupXB
  obtain ⟨-, traxy⟩ := up_trans C hax hxy hay hupAX hupXY
  obtain ⟨-, traby⟩ := up_trans C hab hby hay hupAB hupBY
  obtain ⟨-, trxby⟩ := up_trans C hxb hby hxy hupXB hupBY
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have htx0 : 0 ≤ theta x := (C.htheta x).1.1
  have htb0 : 0 ≤ theta b := (C.htheta b).1.1
  have hty0 : 0 ≤ theta y := (C.htheta y).1.1
  have htaβ : theta a ≤ Real.pi - n * lam := (C.htheta a).1.2
  have htxβ : theta x ≤ Real.pi - n * lam := (C.htheta x).1.2
  have htbβ : theta b ≤ Real.pi - n * lam := (C.htheta b).1.2
  have htyβ : theta y ≤ Real.pi - n * lam := (C.htheta y).1.2
  set fax := dirRep o e (c ∘ v.succAbove) a x with hfax
  set fab := dirRep o e (c ∘ v.succAbove) a b with hfab
  set fay := dirRep o e (c ∘ v.succAbove) a y with hfay
  set fxb := dirRep o e (c ∘ v.succAbove) x b with hfxb
  set fxy := dirRep o e (c ∘ v.succAbove) x y with hfxy
  set fby := dirRep o e (c ∘ v.succAbove) b y with hfby
  have hba : dirRep o e (c ∘ v.succAbove) b a = fab :=
    (phi_comm C hab).symm
  have hbx : dirRep o e (c ∘ v.succAbove) b x = fxb :=
    (phi_comm C hxb).symm
  have hlt0 : ∀ {g : ℝ}, ⌊g / lam⌋₊ = 0 → g < lam := by
    intro g hg; rwa [Nat.floor_eq_zero, div_lt_one hlam] at hg
  rcases traxb with ⟨t00, t01⟩ | ⟨t00, t01⟩ <;>
    rcases traxy with ⟨t10, t11⟩ | ⟨t10, t11⟩ <;>
    rcases traby with ⟨t20, t21⟩ | ⟨t20, t21⟩ <;>
    rcases trxby with ⟨t30, t31⟩ | ⟨t30, t31⟩
  -- W0 (0000): sorts a=(fax,fab,fay), b=(fab,fxb,fby)
  · rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fax)] at hcap0
    rw [abs_of_pos (by linarith : (0:ℝ) < fxy - fax)] at hcap1
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fab)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fxb)] at hcap3
    have hbig2 : 1 ≤ ⌊(fby - fxb) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have hbig0a : 1 ≤ ⌊(fax - theta a) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have tria := r3_fan_trich_t3 C hax hab hay t00 t20 hda rfl rfl rfl
      hbig0a (phi_ge_lam C hax) (by linarith) htaβ
    simp only [← hfax, ← hfab, ← hfay] at tria
    have trib := r3_fan_trich_hi C hab.symm hxb.symm hby
      (by rwa [hba, hbx] : dirRep o e (c ∘ v.succAbove) b a <
        dirRep o e (c ∘ v.succAbove) b x)
      (by rw [hbx]; exact lt_trans t30 t31 :
        dirRep o e (c ∘ v.succAbove) b x <
          dirRep o e (c ∘ v.succAbove) b y)
      hdb hba hbx rfl hbig2 hcab hcby' (lt_trans hθ0 hθ1) hθ2 hta0 htbβ htyβ
    simp only [← hfby] at trib
    have e_a0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fax - theta a)
    have e_a1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fax)
    have e_a2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fay - fab)
    have e_a3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta a + Real.pi - fay)
    have e_b0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - theta b)
    have e_b1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fxb - fab)
    have e_b2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fby - fxb)
    have e_b3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta b + Real.pi - fby)
    rcases tria with hA | hA | hA | hA <;> rcases trib with hB | hB | hB
    · -- {0} × {2}: fby ≥ fxb + (n−1)λ ≥ fax + nλ escapes corridor
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hs : (⌊(fby - fxb) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fxb) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) hs]
    · -- {0} × {0,2}: fby ≥ θa + (2n−f_b0)λ escapes corridor
      obtain ⟨h0n, -, -, -⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hsA : (⌊(fax - theta a) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fax - theta a) / lam⌋₊ + 1 = n)
      have hsB : (⌊(fab - theta b) / lam⌋₊ : ℝ) + ⌊(fby - fxb) / lam⌋₊ = n := by
        exact_mod_cast hbs
      have hb2p : (1:ℝ) ≤ ⌊(fby - fxb) / lam⌋₊ := by exact_mod_cast hbig2
      linarith [congrArg (· * lam) hsA, congrArg (· * lam) hsB]
    · -- {0} × {2,3}: fby squeezed between θa-chain and θb+f_b2λ+β
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h23, -, -, h3p⟩ := hB
      have ha0p : (1:ℝ) ≤ ⌊(fax - theta a) / lam⌋₊ := by exact_mod_cast hbig0a
      have hsB : (⌊(fby - fxb) / lam⌋₊ : ℝ) +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by
        exact_mod_cast h23
      linarith [congrArg (· * lam) hsB]
    · -- {0,1} × {2}
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hs : (⌊(fby - fxb) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fxb) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) hs]
    · -- {0,1} × {0,2}: fab ≥ θa + nλ; fby > fab + (n−f_b0)λ escapes corridor
      obtain ⟨h01, -, -, -⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hsA : (⌊(fax - theta a) / lam⌋₊ : ℝ) + ⌊(fab - fax) / lam⌋₊ = n := by
        exact_mod_cast h01
      have hsB : (⌊(fab - theta b) / lam⌋₊ : ℝ) + ⌊(fby - fxb) / lam⌋₊ = n := by
        exact_mod_cast hbs
      have hb2p : (1:ℝ) ≤ ⌊(fby - fxb) / lam⌋₊ := by exact_mod_cast hbig2
      linarith [congrArg (· * lam) hsA, congrArg (· * lam) hsB]
    · -- {0,1} × {2,3}
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h23, -, -, h3p⟩ := hB
      have ha0p : (1:ℝ) ≤ ⌊(fax - theta a) / lam⌋₊ := by exact_mod_cast hbig0a
      have hsB : (⌊(fby - fxb) / lam⌋₊ : ℝ) +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by
        exact_mod_cast h23
      linarith [congrArg (· * lam) hsB]
    · -- {0,2} × {2}
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hs : (⌊(fby - fxb) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fxb) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) hs]
    · -- {0,2} × {0,2}: zone split on f_a0 vs f_b0
      obtain ⟨h02, -, -, h2p⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hsA : (⌊(fax - theta a) / lam⌋₊ : ℝ) + ⌊(fay - fab) / lam⌋₊ = n := by
        exact_mod_cast h02
      have hsB : (⌊(fab - theta b) / lam⌋₊ : ℝ) + ⌊(fby - fxb) / lam⌋₊ = n := by
        exact_mod_cast hbs
      rcases lt_or_ge (⌊(fax - theta a) / lam⌋₊ : ℝ) (⌊(fab - theta b) / lam⌋₊ : ℝ) with hz | hz
      · -- zone f_a0 < f_b0: integer gap ≥ 1; fby > θb + (n+1)λ escapes corridor
        have hzn : ⌊(fax - theta a) / lam⌋₊ + 1 ≤ ⌊(fab - theta b) / lam⌋₊ := by
          have h : ⌊(fax - theta a) / lam⌋₊ < ⌊(fab - theta b) / lam⌋₊ := by
            exact_mod_cast hz
          omega
        have hzr : (⌊(fax - theta a) / lam⌋₊ : ℝ) + 1 ≤ ⌊(fab - theta b) / lam⌋₊ := by
          exact_mod_cast hzn
        have hzr' := mul_le_mul_of_nonneg_right hzr hlam.le
        linarith only [hzr', e_b0, e_a2, congrArg (· * lam) hsA, t21, hcby',
          htyβ, htb0, hπ]
      · -- zone f_b0 ≤ f_a0: fby ≥ θa + (f_a0+1+n−f_b0)λ escapes corridor
        have hz' := mul_le_mul_of_nonneg_right hz hlam.le
        linarith only [hz', e_a0, hcap0, e_b2, congrArg (· * lam) hsB, hcby',
          htyβ, hta0, hβ]
    · -- {0,2} × {2,3}
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h23, -, -, h3p⟩ := hB
      have ha0p : (1:ℝ) ≤ ⌊(fax - theta a) / lam⌋₊ := by exact_mod_cast hbig0a
      have hsB : (⌊(fby - fxb) / lam⌋₊ : ℝ) +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by
        exact_mod_cast h23
      linarith [congrArg (· * lam) hsB]
    · -- {0,3} × {2}
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hs : (⌊(fby - fxb) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fxb) / lam⌋₊ + 1 = n)
      linarith [congrArg (· * lam) hs]
    · -- {0,3} × {0,2}: zone split on f_a0 vs f_b0
      obtain ⟨h03, -, -, h3p⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hsA : (⌊(fax - theta a) / lam⌋₊ : ℝ) +
          ⌊(theta a + Real.pi - fay) / lam⌋₊ = n := by
        exact_mod_cast h03
      have hsB : (⌊(fab - theta b) / lam⌋₊ : ℝ) + ⌊(fby - fxb) / lam⌋₊ = n := by
        exact_mod_cast hbs
      rcases lt_or_ge (⌊(fax - theta a) / lam⌋₊ : ℝ) (⌊(fab - theta b) / lam⌋₊ : ℝ) with hz | hz
      · -- zone f_a0 < f_b0: integer gap ≥ 1; fab < fay squeezed
        have hzn : ⌊(fax - theta a) / lam⌋₊ + 1 ≤ ⌊(fab - theta b) / lam⌋₊ := by
          have h : ⌊(fax - theta a) / lam⌋₊ < ⌊(fab - theta b) / lam⌋₊ := by
            exact_mod_cast hz
          omega
        have hzr : (⌊(fax - theta a) / lam⌋₊ : ℝ) + 1 ≤ ⌊(fab - theta b) / lam⌋₊ := by
          exact_mod_cast hzn
        have hzr' := mul_le_mul_of_nonneg_right hzr hlam.le
        linarith only [hzr', e_b0, e_a3, congrArg (· * lam) hsA, t20,
          lt_trans hθ0 hθ1, hβ]
      · -- zone f_b0 ≤ f_a0: fby ≥ θa + (f_a0+1+n−f_b0)λ escapes corridor
        have hz' := mul_le_mul_of_nonneg_right hz hlam.le
        linarith only [hz', e_a0, hcap0, e_b2, congrArg (· * lam) hsB, hcby',
          htyβ, hta0, hβ]
    · -- {0,3} × {2,3}
      obtain ⟨-, -, -, -⟩ := hA; obtain ⟨h23, -, -, h3p⟩ := hB
      have ha0p : (1:ℝ) ≤ ⌊(fax - theta a) / lam⌋₊ := by exact_mod_cast hbig0a
      have hsB : (⌊(fby - fxb) / lam⌋₊ : ℝ) +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by
        exact_mod_cast h23
      linarith [congrArg (· * lam) hsB]
  -- W8 (1000): row-b sort (fab,fby,fxb): three big gaps {1,2,3}
  · exfalso
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fab)] at hcap2
    rw [abs_of_neg (by linarith : fby - fxb < 0)] at hcap3
    refine r3_fan_overflow C hab.symm hby hxb.symm ?_ ?_ hdb rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [hba]; exact lt_trans t20 t21
    · rw [hbx]; exact lt_trans t30 t31
    · right; right; right
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by rwa [hba]),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)⟩
  -- W4 (0100): dead — fby<fay<fxy<fby cycle
  · exfalso; linarith
  -- W12 (1100): row-b sort (fby,fab,fxb): three big gaps {0,1,3}
  · exfalso
    rw [abs_of_neg (by linarith : fby - fab < 0)] at hcap2
    rw [abs_of_neg (by linarith : fby - fxb < 0)] at hcap3
    refine r3_fan_overflow C hby hab.symm hxb.symm ?_ ?_ hdb rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [hba]; exact lt_trans t20 t21
    · rw [hba, hbx]; exact t01
    · right; left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)⟩
  -- W2 (0010): dead — fay<fax<fab<fay cycle
  · exfalso; linarith
  -- W10 (1010): dead — fby<fxy<fay<fby cycle
  · exfalso; linarith
  -- W6 (0110): dead — fab<fxb vs fxb<...<fab
  · exfalso; linarith
  -- W14 (1110): row-b sort (fby,fab,fxb): three big gaps {0,1,3}
  · exfalso
    rw [abs_of_neg (by linarith : fby - fab < 0)] at hcap2
    rw [abs_of_neg (by linarith : fby - fxb < 0)] at hcap3
    refine r3_fan_overflow C hby hab.symm hxb.symm ?_ ?_ hdb rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [hba]; exact lt_trans t20 t21
    · rw [hba, hbx]; exact t01
    · right; left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)⟩
  -- W1 (0001): sorts a=(fab,fax,fay), b=(fxb,fab,fby)
  · rw [abs_of_neg (by linarith : fxb - fax < 0)] at hcap0
    rw [abs_of_pos (by linarith : (0:ℝ) < fxy - fax)] at hcap1
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fab)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fxb)] at hcap3
    have hbig2 : 1 ≤ ⌊(fby - fab) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have hbig0a : 1 ≤ ⌊(fab - theta a) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have tria := r3_fan_trich_t3 C hab hax hay t01 t10 hda rfl rfl rfl
      hbig0a (phi_ge_lam C hab) (by linarith) htaβ
    have trib := r3_fan_trich_hi C hxb.symm hab.symm hby
      (by rwa [hbx, hba] : dirRep o e (c ∘ v.succAbove) b x <
        dirRep o e (c ∘ v.succAbove) b a)
      (by rw [hba]; exact lt_trans t20 t21 :
        dirRep o e (c ∘ v.succAbove) b a <
          dirRep o e (c ∘ v.succAbove) b y)
      hdb hbx hba rfl hbig2 hcxb hcby' hθ1 hθ2 htx0 htbβ htyβ
    simp only [← hfby] at trib
    simp only [← hfab, ← hfax, ← hfay] at tria
    have e_a0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - theta a)
    have e_a1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fax - fab)
    have e_a2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fay - fax)
    have e_a3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta a + Real.pi - fay)
    have e_b0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fxb - theta b)
    have e_b1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fxb)
    have e_b2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fby - fab)
    have e_b3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta b + Real.pi - fby)
    rcases tria with hA | hA | hA | hA <;> rcases trib with hB | hB | hB
    · -- {0} × {2}
      obtain ⟨h0n, h1z, h2z, h3z⟩ := hA; obtain ⟨h2n, hb0z, hb1z, hb3z⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fab - theta a) / lam⌋₊ + 1 = n)
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fab) / lam⌋₊ + 1 = n)
      have za3 : (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast h3z
      have ub0 := hlt0 hb0z
      have ub1 := hlt0 hb1z
      have zb3 : (⌊(theta b + Real.pi - fby) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast hb3z
      linarith [congrArg (· * lam) hsA, congrArg (· * lam) hsB]
    · -- {0} × {0,2}
      obtain ⟨h0n, h1z, h2z, h3z⟩ := hA; obtain ⟨hbs, hb0p, hb1z, hb3z⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fab - theta a) / lam⌋₊ + 1 = n)
      have hsB : (⌊(fxb - theta b) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊ = n := by
        exact_mod_cast hbs
      have hsAL := congrArg (· * lam) hsA
      have khi : (⌊(fby - fab) / lam⌋₊ : ℝ) < 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hsAL, hlam, hcL]
      have klo : (⌊(fxb - theta b) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(fxb - theta b) / lam⌋₊ : ℝ) := by linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_b0, hcap0, hcap1, t31, hcby', htyβ, htb0, hπ, hlam, hcL]
      have h2l : ⌊(fby - fab) / lam⌋₊ < 2 := by exact_mod_cast khi
      have h1l : ⌊(fxb - theta b) / lam⌋₊ + 1 < n := by exact_mod_cast klo
      omega
    · -- {0} × {2,3}
      obtain ⟨h0n, h1z, h2z, h3z⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fab - theta a) / lam⌋₊ + 1 = n)
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by
        exact_mod_cast h23
      have za3 : (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast h3z
      have ub0 := hlt0 hb0z
      have ub1 := hlt0 hb1z
      have pb3 : (1:ℝ) ≤ ⌊(theta b + Real.pi - fby) / lam⌋₊ := by exact_mod_cast hb3p
      have pb3L : lam ≤ ⌊(theta b + Real.pi - fby) / lam⌋₊ * lam := by
        have := mul_le_mul_of_nonneg_right pb3 (le_of_lt hlam)
        simpa using this
      linarith [congrArg (· * lam) hsA, congrArg (· * lam) hsB]
    · -- {0,1} × {2}
      obtain ⟨h01, h2z, h3z, h1p⟩ := hA; obtain ⟨h2n, hb0z, hb1z, hb3z⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fax - fab) / lam⌋₊ = n := by
        exact_mod_cast h01
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fab) / lam⌋₊ + 1 = n)
      have za2 : (⌊(fay - fax) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast h2z
      have za3 : (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast h3z
      have ub0 := hlt0 hb0z
      have ub1 := hlt0 hb1z
      have zb3 : (⌊(theta b + Real.pi - fby) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast hb3z
      linarith [congrArg (· * lam) hsA, congrArg (· * lam) hsB]
    · -- {0,1} × {0,2}
      obtain ⟨h01, h2z, h3z, h1p⟩ := hA; obtain ⟨hbs, hb0p, hb1z, hb3z⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fax - fab) / lam⌋₊ = n := by
        exact_mod_cast h01
      have hsB : (⌊(fxb - theta b) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊ = n := by
        exact_mod_cast hbs
      have ua2 := hlt0 h2z
      have za3 : (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast h3z
      have ub1 := hlt0 hb1z
      have zb3 : (⌊(theta b + Real.pi - fby) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast hb3z
      linarith [congrArg (· * lam) hsA, congrArg (· * lam) hsB]
    · -- {0,1} × {2,3}
      obtain ⟨h01, h2z, h3z, h1p⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fax - fab) / lam⌋₊ = n := by
        exact_mod_cast h01
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by
        exact_mod_cast h23
      have za3 : (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) = 0 := by exact_mod_cast h3z
      have ub0 := hlt0 hb0z
      have ub1 := hlt0 hb1z
      have pb3 : (1:ℝ) ≤ ⌊(theta b + Real.pi - fby) / lam⌋₊ := by exact_mod_cast hb3p
      have pb3L : lam ≤ ⌊(theta b + Real.pi - fby) / lam⌋₊ * lam := by
        have := mul_le_mul_of_nonneg_right pb3 (le_of_lt hlam)
        simpa using this
      linarith [congrArg (· * lam) hsA, congrArg (· * lam) hsB]
    · -- {0,2} × {2}
      obtain ⟨h02, h1z, h3z, h2p⟩ := hA; obtain ⟨h2n, hb0z, hb1z, hb3z⟩ := hB
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fab) / lam⌋₊ + 1 = n)
      have hsBL := congrArg (· * lam) hsB
      have khi : (⌊(fab - theta a) / lam⌋₊ : ℝ) < 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hsBL, hlam, hcL]
      have h0l : ⌊(fab - theta a) / lam⌋₊ < 2 := by exact_mod_cast khi
      have h2g : n ≤ ⌊(fay - fax) / lam⌋₊ + 1 := by omega
      have h2gr : (n : ℝ) ≤ (⌊(fay - fax) / lam⌋₊ : ℝ) + 1 := by exact_mod_cast h2g
      have h2gL := mul_le_mul_of_nonneg_right h2gr (le_of_lt hlam)
      linarith only [e_a2, h2gL, hcap0, hcxb, hθ0, hcay', htyβ, hta0, hπ, hlam]
    · -- {0,2} × {0,2}
      obtain ⟨h02, h1z, h3z, h2p⟩ := hA; obtain ⟨hbs, hb0p, hb1z, hb3z⟩ := hB
      have hi1 : (⌊(fay - fax) / lam⌋₊ : ℝ) + ⌊(fxb - theta b) / lam⌋₊ < n := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a2, e_b0, hcap0, t21, hcby', htyβ, htb0, hπ, hlam, hcL]
      have hi2 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊ < n + 1 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hlam, hcL]
      have hn1 : ⌊(fay - fax) / lam⌋₊ + ⌊(fxb - theta b) / lam⌋₊ < n := by
        exact_mod_cast hi1
      have hn2 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ < n + 1 := by
        exact_mod_cast hi2
      omega
    · -- {0,2} × {2,3}
      obtain ⟨h02, h1z, h3z, h2p⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fay - fax) / lam⌋₊ = n := by
        exact_mod_cast h02
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by exact_mod_cast h23
      have hi1 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hlam, hcL]
      have hi2 : (⌊(fay - fax) / lam⌋₊ : ℝ) + ⌊(theta b + Real.pi - fby) / lam⌋₊
          < n := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a2, e_b3, t21, hcap0, hcxb, htbβ, htx0, hπ, hlam, hcL]
      have hn1 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by exact_mod_cast hi1
      have hn2 : ⌊(fay - fax) / lam⌋₊ + ⌊(theta b + Real.pi - fby) / lam⌋₊
          < n := by exact_mod_cast hi2
      omega
    · -- {0,3} × {2}
      obtain ⟨h03, h1z, h2z, h3p⟩ := hA; obtain ⟨h2n, hb0z, hb1z, hb3z⟩ := hB
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fab) / lam⌋₊ + 1 = n)
      have hsBL := congrArg (· * lam) hsB
      have khi : (⌊(fab - theta a) / lam⌋₊ : ℝ) < 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hsBL, hlam, hcL]
      have h0l : ⌊(fab - theta a) / lam⌋₊ < 2 := by exact_mod_cast khi
      have h3g : n ≤ ⌊(theta a + Real.pi - fay) / lam⌋₊ + 1 := by omega
      have h3gr : (n : ℝ) ≤ (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) + 1 := by
        exact_mod_cast h3g
      have h3gL := mul_le_mul_of_nonneg_right h3gr (le_of_lt hlam)
      linarith only [e_a3, h3gL, t10, hcap0, hcxb, hθ0, hθ1, hπ, hlam]
    · -- {0,3} × {0,2}
      obtain ⟨h03, h1z, h2z, h3p⟩ := hA; obtain ⟨hbs, hb0p, hb1z, hb3z⟩ := hB
      have hi1 : (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) +
          ⌊(fxb - theta b) / lam⌋₊ < n := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a3, e_b0, hcap0, t10, hθ0, hθ1, hπ, hlam, hcL]
      have hi2 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hlam, hcL]
      have hn1 : ⌊(theta a + Real.pi - fay) / lam⌋₊ + ⌊(fxb - theta b) / lam⌋₊
          < n := by exact_mod_cast hi1
      have hn2 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by exact_mod_cast hi2
      omega
    · -- {0,3} × {2,3}
      obtain ⟨h03, h1z, h2z, h3p⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hi1 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, e_b3, htbβ, hta0, hπ, hlam, hcL]
      have hn1 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by exact_mod_cast hi1
      have h3g : n ≤ ⌊(theta a + Real.pi - fay) / lam⌋₊ + 1 := by omega
      have h3gr : (n : ℝ) ≤ (⌊(theta a + Real.pi - fay) / lam⌋₊ : ℝ) + 1 := by
        exact_mod_cast h3g
      have h3gL := mul_le_mul_of_nonneg_right h3gr (le_of_lt hlam)
      linarith only [e_a3, h3gL, t10, hcap0, hcxb, hθ0, hθ1, hπ, hlam]
  -- W9 (1001): dead — fab<fxb vs fxb<fab
  · exfalso; linarith
  -- W5 (0101): dead — fay<fab<fax<fay cycle
  · exfalso; linarith
  -- W13 (1101): dead — fay<fby<fay cycle
  · exfalso; linarith
  -- W3 (0011): sorts a=(fab,fay,fax), b=(fxb,fab,fby)
  · rw [abs_of_neg (by linarith : fxb - fax < 0)] at hcap0
    rw [abs_of_neg (by linarith : fxy - fax < 0)] at hcap1
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fab)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fxb)] at hcap3
    have hbig2 : 1 ≤ ⌊(fby - fab) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have hbig0a : 1 ≤ ⌊(fab - theta a) / lam⌋₊ :=
      (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)
    have tria := r3_fan_trich_t3 C hab hay hax t20 t11 hda rfl rfl rfl
      hbig0a (phi_ge_lam C hab) (by linarith) htaβ
    have trib := r3_fan_trich_hi C hxb.symm hab.symm hby
      (by rwa [hbx, hba] : dirRep o e (c ∘ v.succAbove) b x <
        dirRep o e (c ∘ v.succAbove) b a)
      (by rw [hba]; exact lt_trans t20 t21 :
        dirRep o e (c ∘ v.succAbove) b a <
          dirRep o e (c ∘ v.succAbove) b y)
      hdb hbx hba rfl hbig2 hcxb hcby' hθ1 hθ2 htx0 htbβ htyβ
    simp only [← hfby] at trib
    simp only [← hfab, ← hfay, ← hfax] at tria
    have e_a0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - theta a)
    have e_a1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fay - fab)
    have e_a2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fax - fay)
    have e_a3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta a + Real.pi - fax)
    have e_b0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fxb - theta b)
    have e_b1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fxb)
    have e_b2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fby - fab)
    have e_b3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta b + Real.pi - fby)
    rcases tria with hA | hA | hA | hA <;> rcases trib with hB | hB | hB
    · -- {0} × {2}
      obtain ⟨h0n, -, -, -⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fab - theta a) / lam⌋₊ + 1 = n)
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fab) / lam⌋₊ + 1 = n)
      linarith only [e_a0, e_b2, congrArg (· * lam) hsA, congrArg (· * lam) hsB,
        hcby', htyβ, hta0, hπ, hn3l, hlam]
    · -- {0} × {0,2}
      obtain ⟨h0n, -, -, -⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fab - theta a) / lam⌋₊ + 1 = n)
      have hsAL := congrArg (· * lam) hsA
      have khi : (⌊(fby - fab) / lam⌋₊ : ℝ) < 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hsAL, hlam, hcL]
      have klo : (⌊(fxb - theta b) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(fxb - theta b) / lam⌋₊ : ℝ) := by linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_b0, hcap0, hcax', hθ1, hπ, hlam, hcL]
      have h2l : ⌊(fby - fab) / lam⌋₊ < 2 := by exact_mod_cast khi
      have h1l : ⌊(fxb - theta b) / lam⌋₊ + 1 < n := by exact_mod_cast klo
      omega
    · -- {0} × {2,3}
      obtain ⟨h0n, -, -, -⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hsA : (⌊(fab - theta a) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fab - theta a) / lam⌋₊ + 1 = n)
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ = n := by
        exact_mod_cast h23
      linarith only [e_a0, e_b2, e_b3, congrArg (· * lam) hsA,
        congrArg (· * lam) hsB, htbβ, hta0, hπ, hn3l, hlam]
    · -- {0,1} × {2}
      obtain ⟨h01, -, -, -⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hi1 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hlam, hcL]
      have hi2 : (⌊(fay - fab) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(fay - fab) / lam⌋₊ : ℝ) := by linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_a1, t11, hcax', t00, hcxb, hπ, hlam, hcL]
      have hn1 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ < n + 1 := by
        exact_mod_cast hi1
      have hn2 : ⌊(fay - fab) / lam⌋₊ + 1 < n := by exact_mod_cast hi2
      omega
    · -- {0,1} × {0,2}
      obtain ⟨h01, -, -, -⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hi1 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hlam, hcL]
      have hi2 : (⌊(fay - fab) / lam⌋₊ : ℝ) + ⌊(fxb - theta b) / lam⌋₊
          < n := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a1, e_b0, t00, t11, hcax', hθ1, hπ, hlam, hcL]
      have hn1 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ < n + 1 := by
        exact_mod_cast hi1
      have hn2 : ⌊(fay - fab) / lam⌋₊ + ⌊(fxb - theta b) / lam⌋₊ < n := by
        exact_mod_cast hi2
      omega
    · -- {0,1} × {2,3}
      obtain ⟨h01, -, -, -⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hi1 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, e_b3, htbβ, hta0, hπ, hlam, hcL]
      have hi2 : (⌊(fay - fab) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(fay - fab) / lam⌋₊ : ℝ) := by linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_a1, t11, hcax', t00, hcxb, hπ, hlam, hcL]
      have hn1 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by exact_mod_cast hi1
      have hn2 : ⌊(fay - fab) / lam⌋₊ + 1 < n := by exact_mod_cast hi2
      omega
    · -- {0,2} × {2}
      obtain ⟨h02, -, -, h2p⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fab) / lam⌋₊ + 1 = n)
      have hsBL := congrArg (· * lam) hsB
      have khi : (⌊(fab - theta a) / lam⌋₊ : ℝ) < 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hsBL, hlam, hcL]
      have klo : (⌊(fax - fay) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(fax - fay) / lam⌋₊ : ℝ) := by linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_a2, t10, hcxy, hcax', hπ, hlam, hcL]
      have h0l : ⌊(fab - theta a) / lam⌋₊ < 2 := by exact_mod_cast khi
      have h2l : ⌊(fax - fay) / lam⌋₊ + 1 < n := by exact_mod_cast klo
      omega
    · -- {0,2} × {0,2}
      obtain ⟨h02, -, -, h2p⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hi1 : (⌊(fax - fay) / lam⌋₊ : ℝ) + ⌊(fxb - theta b) / lam⌋₊
          < n := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a2, e_b0, t30, t10, hcax', hθ1, hπ, hlam, hcL]
      have hi2 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hlam, hcL]
      have hn1 : ⌊(fax - fay) / lam⌋₊ + ⌊(fxb - theta b) / lam⌋₊ < n := by
        exact_mod_cast hi1
      have hn2 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ < n + 1 := by
        exact_mod_cast hi2
      omega
    · -- {0,2} × {2,3}
      obtain ⟨h02, -, -, h2p⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hi1 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, e_b3, htbβ, hta0, hπ, hlam, hcL]
      have klo : (⌊(fax - fay) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(fax - fay) / lam⌋₊ : ℝ) := by linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_a2, t10, hcxy, hcax', hπ, hlam, hcL]
      have hn1 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by exact_mod_cast hi1
      have h2l : ⌊(fax - fay) / lam⌋₊ + 1 < n := by exact_mod_cast klo
      omega
    · -- {0,3} × {2}
      obtain ⟨h03, -, -, h3p⟩ := hA; obtain ⟨h2n, -, -, -⟩ := hB
      have hsB : (⌊(fby - fab) / lam⌋₊ : ℝ) + 1 = n := by
        exact_mod_cast (by omega : ⌊(fby - fab) / lam⌋₊ + 1 = n)
      have hsBL := congrArg (· * lam) hsB
      have khi : (⌊(fab - theta a) / lam⌋₊ : ℝ) < 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hsBL, hlam, hcL]
      have klo : (⌊(theta a + Real.pi - fax) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(theta a + Real.pi - fax) / lam⌋₊ : ℝ) := by
          linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_a3, hcap0, hcxb, hθ0, hθ1, hπ, hlam, hcL]
      have h0l : ⌊(fab - theta a) / lam⌋₊ < 2 := by exact_mod_cast khi
      have h3l : ⌊(theta a + Real.pi - fax) / lam⌋₊ + 1 < n := by
        exact_mod_cast klo
      omega
    · -- {0,3} × {0,2}
      obtain ⟨h03, -, -, h3p⟩ := hA; obtain ⟨hbs, hb0p, -, -⟩ := hB
      have hi1 : (⌊(theta a + Real.pi - fax) / lam⌋₊ : ℝ) +
          ⌊(fxb - theta b) / lam⌋₊ < n := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a3, e_b0, hcap0, hθ0, hθ1, hπ, hlam, hcL]
      have hi2 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, hcby', htyβ, hta0, hπ, hlam, hcL]
      have hn1 : ⌊(theta a + Real.pi - fax) / lam⌋₊ +
          ⌊(fxb - theta b) / lam⌋₊ < n := by exact_mod_cast hi1
      have hn2 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊
          < n + 1 := by exact_mod_cast hi2
      omega
    · -- {0,3} × {2,3}
      obtain ⟨h03, -, -, h3p⟩ := hA; obtain ⟨h23, hb0z, hb1z, hb3p⟩ := hB
      have hi1 : (⌊(fab - theta a) / lam⌋₊ : ℝ) + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by
        by_contra hc; push_neg at hc
        have hcL := mul_le_mul_of_nonneg_right hc (le_of_lt hlam)
        linarith only [e_a0, e_b2, e_b3, htbβ, hta0, hπ, hlam, hcL]
      have klo : (⌊(theta a + Real.pi - fax) / lam⌋₊ : ℝ) + 1 < n := by
        by_contra hc; push_neg at hc
        have hc1 : (n : ℝ) - 1 ≤ (⌊(theta a + Real.pi - fax) / lam⌋₊ : ℝ) := by
          linarith
        have hcL := mul_le_mul_of_nonneg_right hc1 (le_of_lt hlam)
        linarith only [e_a3, hcap0, hcxb, hθ0, hθ1, hπ, hlam, hcL]
      have hn1 : ⌊(fab - theta a) / lam⌋₊ + ⌊(fby - fab) / lam⌋₊ +
          ⌊(theta b + Real.pi - fby) / lam⌋₊ < n + 2 := by exact_mod_cast hi1
      have h3l : ⌊(theta a + Real.pi - fax) / lam⌋₊ + 1 < n := by
        exact_mod_cast klo
      omega
  -- W11 (1011): dead — fby<fxy<fxb<fab<fay<fby cycle
  · exfalso; linarith
  -- W7 (0111): row-b sort (fxb,fby,fab): three big gaps {1,2,3}
  · exfalso
    rw [abs_of_neg (by linarith : fby - fab < 0)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fby - fxb)] at hcap3
    refine r3_fan_overflow C hxb.symm hby hab.symm ?_ ?_ hdb rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [hbx]; exact lt_trans t30 t31
    · rw [hba]; exact lt_trans t20 t21
    · right; right; right
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by rwa [hbx]),
        (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hba]; linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)⟩
  -- W15 (1111): row-b sort (fby,fxb,fab): three big gaps {0,1,3}
  · exfalso
    rw [abs_of_neg (by linarith : fby - fxb < 0)] at hcap3
    refine r3_fan_overflow C hby hxb.symm hab.symm ?_ ?_ hdb rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [hbx]; exact lt_trans t30 t31
    · rwa [hbx, hba]
    · right; left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith),
        (one_le_floor_iff_ge lam _ hlam).mpr (by linarith)⟩
set_option maxHeartbeats 1600000 in
/-- **Pair-kill — midbot configuration `θ_y < θ_a < θ_x < θ_b`.**  Two
defect-`2` rows `a,b` with `y` below `a` and `x,b` above `a`: row `a`
is `lo`-type (its minimum chord `φ_{a,y}` forces the first inner gap
through `cap`), row `b` is `t4` (all fan targets sit below `θ_b`, forcing
the last gap).  The four transitivity disjunctions split into `16`
worlds: `8` die to pure order cycles, `5` die to three-big-gap overflow
on row `a`, and the three signature worlds die to coupled floor
certificates. -/
theorem pairkill_midbot {y a x b : Fin 4}
    (hya : y ≠ a) (hyx : y ≠ x) (hyb : y ≠ b)
    (hax : a ≠ x) (hab : a ≠ b) (hxb : x ≠ b)
    (hθ0 : theta y < theta a) (hθ1 : theta a < theta x)
    (hθ2 : theta x < theta b)
    (hda : rowDefect n lam (directionRow o e c (v.succAbove a)) = 2)
    (hdb : rowDefect n lam (directionRow o e c (v.succAbove b)) = 2) : False := by
  classical
  have hlam := C.hlam; have hβ := C.hβ; have hπ := C.hπ
  have hn3l : 3 * lam ≤ (n:ℝ) * lam :=
    mul_le_mul_of_nonneg_right C.hn3' (le_of_lt hlam)
  have hn3 : 3 ≤ n := C.hn3
  have hupYA : Up o e c v y a := up_of_theta_lt C hya hθ0
  have hupYX : Up o e c v y x := up_of_theta_lt C hyx (lt_trans hθ0 hθ1)
  have hupYB : Up o e c v y b := up_of_theta_lt C hyb (lt_trans (lt_trans hθ0 hθ1) hθ2)
  have hupAX : Up o e c v a x := up_of_theta_lt C hax hθ1
  have hupAB : Up o e c v a b := up_of_theta_lt C hab (lt_trans hθ1 hθ2)
  have hupXB : Up o e c v x b := up_of_theta_lt C hxb hθ2
  obtain ⟨hcya, hcya'⟩ := up_corridor C hya hupYA
  obtain ⟨hcyx, hcyx'⟩ := up_corridor C hyx hupYX
  obtain ⟨hcyb, hcyb'⟩ := up_corridor C hyb hupYB
  obtain ⟨hcax, hcax'⟩ := up_corridor C hax hupAX
  obtain ⟨hcab, hcab'⟩ := up_corridor C hab hupAB
  obtain ⟨hcxb, hcxb'⟩ := up_corridor C hxb hupXB
  have hcap0 := up_cap C hya hax hyx hupYA hupAX
  have hcap1 := up_cap C hya hab hyb hupYA hupAB
  have hcap2 := up_cap C hyx hxb hyb hupYX hupXB
  have hcap3 := up_cap C hax hxb hab hupAX hupXB
  obtain ⟨-, tryax⟩ := up_trans C hya hax hyx hupYA hupAX
  obtain ⟨-, trayb⟩ := up_trans C hya hab hyb hupYA hupAB
  obtain ⟨-, tryxb⟩ := up_trans C hyx hxb hyb hupYX hupXB
  obtain ⟨-, traxb⟩ := up_trans C hax hxb hab hupAX hupXB
  have hty0 : 0 ≤ theta y := (C.htheta y).1.1
  have hta0 : 0 ≤ theta a := (C.htheta a).1.1
  have htx0 : 0 ≤ theta x := (C.htheta x).1.1
  have htb0 : 0 ≤ theta b := (C.htheta b).1.1
  have htyβ : theta y ≤ Real.pi - n * lam := (C.htheta y).1.2
  have htaβ : theta a ≤ Real.pi - n * lam := (C.htheta a).1.2
  have htxβ : theta x ≤ Real.pi - n * lam := (C.htheta x).1.2
  have htbβ : theta b ≤ Real.pi - n * lam := (C.htheta b).1.2
  set fya := dirRep o e (c ∘ v.succAbove) y a with hfya
  set fyx := dirRep o e (c ∘ v.succAbove) y x with hfyx
  set fyb := dirRep o e (c ∘ v.succAbove) y b with hfyb
  set fax := dirRep o e (c ∘ v.succAbove) a x with hfax
  set fab := dirRep o e (c ∘ v.succAbove) a b with hfab
  set fxb := dirRep o e (c ∘ v.succAbove) x b with hfxb
  have hday : dirRep o e (c ∘ v.succAbove) a y = fya := (phi_comm C hya).symm
  have hbyd : dirRep o e (c ∘ v.succAbove) b y = fyb := (phi_comm C hyb).symm
  have hbxd : dirRep o e (c ∘ v.succAbove) b x = fxb := (phi_comm C hxb).symm
  have hbad : dirRep o e (c ∘ v.succAbove) b a = fab := (phi_comm C hab).symm
  have hlt0 : ∀ {g : ℝ}, ⌊g / lam⌋₊ = 0 → g < lam := by
    intro g hg; rwa [Nat.floor_eq_zero, div_lt_one hlam] at hg
  rcases tryax with ⟨t00, t01⟩ | ⟨t00, t01⟩ <;>
    rcases trayb with ⟨t10, t11⟩ | ⟨t10, t11⟩ <;>
    rcases tryxb with ⟨t20, t21⟩ | ⟨t20, t21⟩ <;>
    rcases traxb with ⟨t30, t31⟩ | ⟨t30, t31⟩
  -- Wf (bullet 0): row-a sort (fya,fax,fab) lo; row-b sort (fyb,fab,fxb) t4
  · rw [abs_of_pos (by linarith : (0:ℝ) < fax - fya)] at hcap0
    rw [abs_of_pos (by linarith : (0:ℝ) < fab - fya)] at hcap1
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fyx)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fax)] at hcap3
    have tria := r3_fan_trich_lo C hya.symm hax hab
      (by rw [hday]; exact lt_trans t00 t01) t30 hda hday rfl rfl
      ((one_le_floor_iff_ge lam _ hlam).mpr hcap0)
      hcya hcab' hθ0 (lt_trans hθ1 hθ2) hty0 htaβ htbβ
    simp only [← hfax, ← hfab] at tria
    have trib := r3_fan_trich_t4 C hyb.symm hab.symm hxb.symm
      (by rw [hbyd, hbad]; exact t11) (by rw [hbad, hbxd]; exact t31)
      hdb hbyd hbad hbxd
      ((one_le_floor_iff_ge lam _ hlam).mpr (by linarith : lam ≤ theta b + Real.pi - fxb))
      (by rw [← hbyd]; exact phi_ge_lam C hyb.symm) (by linarith) htbβ
    have e_a0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fya - theta a)
    have e_a1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fax - fya)
    have e_a2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fax)
    have e_a3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta a + Real.pi - fab)
    have e_b0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fyb - theta b)
    have e_b1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fyb)
    have e_b2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fxb - fab)
    have e_b3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta b + Real.pi - fxb)
    have hlyb : lam ≤ fyb := phi_ge_lam C hyb
    rcases tria with hA | hA | hA <;> rcases trib with hB | hB | hB | hB
    · -- (0, 1) × (3,)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF0 : ⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fya - theta a) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fya - theta a) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b2, e_b3, e_a0, hcap1, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b2, e_b3, e_a1, t30, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (0, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF : ⌊(fya - theta a) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, hcap3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - theta b) / lam⌋₊ < n := by
        have hlt : ((⌊(fyb - theta b) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b0, hcyb', hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (1, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF : ⌊(fya - theta a) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, hcap3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fab - fyb) / lam⌋₊ < n := by
        have hlt : ((⌊(fab - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b1, hcab', htbβ, hπ, hlyb]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (2, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF : ⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fab - fax) / lam⌋₊ < n := by
        have hlt : ((⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fab - fax) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b2, e_b3, e_a2, hcap0, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (3,)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF : ⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fax - fya) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b2, e_b3, e_a1, t30, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (0, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF : ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcap3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - theta b) / lam⌋₊ < n := by
        have hlt : ((⌊(fyb - theta b) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b0, hcyb', hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (1, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF : ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcap3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fab - fyb) / lam⌋₊ < n := by
        have hlt : ((⌊(fab - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b1, hcab', htbβ, hπ, hlyb]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (2, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF : ⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fab - fax) / lam⌋₊ < n := by
        have hlt : ((⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fab - fax) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b2, e_b3, e_a2, hcap0, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (3,)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF : ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcap3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(theta a + Real.pi - fab) / lam⌋₊ < n := by
        have hlt : ((⌊(theta a + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a3, hcab, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (0, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF0 : ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcap3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - theta b) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(theta a + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(theta a + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b0, e_b1, e_a3, hθ1, hθ2, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (1, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF0 : ⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcap3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fab) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fab) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a3, e_b1, t00, t20, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (2, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF : ⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fab - fax) / lam⌋₊ < n := by
        have hlt : ((⌊(fxb - fab) / lam⌋₊ + ⌊(theta b + Real.pi - fxb) / lam⌋₊ + ⌊(fab - fax) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b2, e_b3, e_a2, hcap0, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
  -- W7 (bullet 1): row-a sort (fya,fab,fax) lo; row-b sort (fyb,fxb,fab) t4
  · rw [abs_of_pos (by linarith : (0:ℝ) < fax - fya)] at hcap0
    rw [abs_of_pos (by linarith : (0:ℝ) < fab - fya)] at hcap1
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fyx)] at hcap2
    rw [abs_of_neg (by linarith : fxb - fax < 0)] at hcap3
    have tria := r3_fan_trich_lo C hya.symm hab hax
      (by rw [hday]; exact lt_trans t10 t11) t31 hda hday rfl rfl
      ((one_le_floor_iff_ge lam _ hlam).mpr hcap1)
      hcya hcax' hθ0 hθ1 hty0 htaβ htxβ
    simp only [← hfab, ← hfax] at tria
    have trib := r3_fan_trich_t4 C hyb.symm hxb.symm hab.symm
      (by rw [hbyd, hbxd]; exact t21) (by rw [hbxd, hbad]; exact t30)
      hdb hbyd hbxd hbad
      ((one_le_floor_iff_ge lam _ hlam).mpr (by linarith : lam ≤ theta b + Real.pi - fab))
      (by rw [← hbyd]; exact phi_ge_lam C hyb.symm) (by linarith) htbβ
    have e_a0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fya - theta a)
    have e_a1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fya)
    have e_a2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fax - fab)
    have e_a3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta a + Real.pi - fax)
    have e_b0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fyb - theta b)
    have e_b1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fxb - fyb)
    have e_b2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fxb)
    have e_b3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta b + Real.pi - fab)
    rcases tria with hA | hA | hA <;> rcases trib with hB | hB | hB | hB
    · -- (0, 1) × (3,)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF : ⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 2 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 2 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (0, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF0 : ⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b0, e_b1, hcap3, hcax', hθ2, hπ]
        have h' : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      have hF1 : ⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 2 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 2 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (1, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF0 : ⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 2 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 2 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ < n := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a3, e_b1, t10, hcap3, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (2, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF : ⌊(fab - fxb) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ + ⌊(fya - theta a) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fxb) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ + ⌊(fya - theta a) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b2, e_b3, e_a0, t00, hcap2, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (3,)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (0, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF0 : ⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b0, e_b1, hcap3, hcax', hθ2, hπ]
        have h' : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      have hF1 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (1, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF0 : ⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b0, e_b1, hcap3, hcax', hθ2, hπ]
        have h' : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      have hF1 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (2, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fax - fab) / lam⌋₊ + ⌊(fab - fxb) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fax - fab) / lam⌋₊ + ⌊(fab - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_a2, e_b2, hcxb, hcax', hπ]
        have h' : ((⌊(fax - fab) / lam⌋₊ + ⌊(fab - fxb) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      omega
    · -- (1, 3) × (3,)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF0 : ⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_a0, e_a3, hcap2, hcap3, t00, hπ]
        have h' : ((⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      have hF1 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (0, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ < n := by
        have hlt : ((⌊(fyb - theta b) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_b0, e_b1, e_a3, hcap3, hθ1, hθ2, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (1, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ < n := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fxb - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a3, e_b1, t10, hcap3, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (2, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fax - fab) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fab - fxb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fab) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fab - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a2, e_a3, e_b2, hcxb, hθ1, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
  -- dead world bullet 2: transitivity cycle
  · exfalso; linarith
  -- W3 (bullet 3): row-a sort (fya,fab,fax) lo; row-b sort (fxb,fyb,fab) t4
  · rw [abs_of_pos (by linarith : (0:ℝ) < fax - fya)] at hcap0
    rw [abs_of_pos (by linarith : (0:ℝ) < fab - fya)] at hcap1
    rw [abs_of_neg (by linarith : fxb - fyx < 0)] at hcap2
    rw [abs_of_neg (by linarith : fxb - fax < 0)] at hcap3
    have tria := r3_fan_trich_lo C hya.symm hab hax
      (by rw [hday]; exact lt_trans t10 t11) t31 hda hday rfl rfl
      ((one_le_floor_iff_ge lam _ hlam).mpr hcap1)
      hcya hcax' hθ0 hθ1 hty0 htaβ htxβ
    simp only [← hfab, ← hfax] at tria
    have trib := r3_fan_trich_t4 C hxb.symm hyb.symm hab.symm
      (by rw [hbxd, hbyd]; exact t20) (by rw [hbyd, hbad]; exact t11)
      hdb hbxd hbyd hbad
      ((one_le_floor_iff_ge lam _ hlam).mpr (by linarith : lam ≤ theta b + Real.pi - fab))
      (by rw [← hbxd]; exact phi_ge_lam C hxb.symm) (by linarith) htbβ
    have e_a0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fya - theta a)
    have e_a1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fya)
    have e_a2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fax - fab)
    have e_a3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta a + Real.pi - fax)
    have e_b0 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fxb - theta b)
    have e_b1 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fyb - fxb)
    have e_b2 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ fab - fyb)
    have e_b3 := fl_mul_le hlam (by linarith : (0:ℝ) ≤ theta b + Real.pi - fab)
    rcases tria with hA | hA | hA <;> rcases trib with hB | hB | hB | hB
    · -- (0, 1) × (3,)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF : ⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 2 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 2 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (0, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF0 : ⌊(fxb - theta b) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fxb - theta b) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b0, hcap2, t01, hcax', hθ2, hπ]
        have h' : ((⌊(fxb - theta b) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      have hF1 : ⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 2 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 2 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (0, 1) × (1, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF0 : ⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 2 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 2 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b1, e_b2, e_a2, hcxb, hcax', hπ]
        have h' : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      omega
    · -- (0, 1) × (2, 3)
      obtain ⟨hAs, ha0p, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF0 : ⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 2 := by
        have hlt : ((⌊(fya - theta a) / lam⌋₊ + ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 2 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a0, e_a1, e_b3, htbβ, hπ, hta0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b1, e_b2, e_a2, hcxb, hcax', hπ]
        have h' : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      omega
    · -- (1,) × (3,)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (0, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF0 : ⌊(fxb - theta b) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fxb - theta b) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b0, hcap2, t01, hcax', hθ2, hπ]
        have h' : ((⌊(fxb - theta b) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      have hF1 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1,) × (1, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b1, e_b2, e_a2, hcxb, hcax', hπ]
        have h' : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      omega
    · -- (1,) × (2, 3)
      obtain ⟨hAs, hzA0, hzA2, hzA3⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_b1, e_b2, e_a2, hcxb, hcax', hπ]
        have h' : ((⌊(fyb - fxb) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ + ⌊(fax - fab) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      omega
    · -- (1, 3) × (3,)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hzB2⟩ := hB
      have hF0 : ⌊(theta a + Real.pi - fax) / lam⌋₊ + 1 < n := by
        have hlt : ((⌊(theta a + Real.pi - fax) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℝ) - 1) * lam := by
          push_cast; linarith [e_a3, hcap2, hcxb, t01, hθ1, hπ]
        have h' : ((⌊(theta a + Real.pi - fax) / lam⌋₊ : ℕ) : ℝ) + 1 < (n:ℝ) := by
          have h2 := lt_of_mul_lt_mul_right hlt hlam.le; linarith
        exact_mod_cast h'
      have hF1 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (0, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB1, hzB2, hb0p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fxb - theta b) / lam⌋₊ < n := by
        have hlt : ((⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fxb - theta b) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a3, e_b0, hcap2, t01, hθ1, hθ2, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (1, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB2, hb1p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fax - fab) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fyb - fxb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fab) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fyb - fxb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a2, e_a3, e_b1, t11, hcxb, hθ1, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
    · -- (1, 3) × (2, 3)
      obtain ⟨hAs, hzA0, hzA2, ha3p⟩ := hA; obtain ⟨hBs, hzB0, hzB1, hb2p⟩ := hB
      have hF0 : ⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ < n + 1 := by
        have hlt : ((⌊(fab - fya) / lam⌋₊ + ⌊(theta b + Real.pi - fab) / lam⌋₊ : ℕ) : ℝ) * lam < ((n + 1 : ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a1, e_b3, hcya, htbβ, hπ, hty0]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      have hF1 : ⌊(fax - fab) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ < n := by
        have hlt : ((⌊(fax - fab) / lam⌋₊ + ⌊(theta a + Real.pi - fax) / lam⌋₊ + ⌊(fab - fyb) / lam⌋₊ : ℕ) : ℝ) * lam < ((n:ℕ) : ℝ) * lam := by
          push_cast; linarith [e_a2, e_a3, e_b2, t20, hcxb, hθ1, hπ]
        have h' := lt_of_mul_lt_mul_right hlt hlam.le
        exact_mod_cast h'
      omega
  -- dead world bullet 4: transitivity cycle
  · exfalso; linarith
  -- dead world bullet 5: transitivity cycle
  · exfalso; linarith
  -- dead world bullet 6: transitivity cycle
  · exfalso; linarith
  -- M=0x1 (bullet 7): row-a sort (fab,fya,fax); forced big gaps {0,1,2}
  · rw [abs_of_pos (by linarith : (0:ℝ) < fax - fya)] at hcap0
    rw [abs_of_neg (by linarith : fab - fya < 0)] at hcap1
    rw [abs_of_neg (by linarith : fxb - fyx < 0)] at hcap2
    rw [abs_of_neg (by linarith : fxb - fax < 0)] at hcap3
    exfalso
    refine r3_fan_overflow C hab hya.symm hax ?_ ?_ hda rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [hday, ← hfab]
      exact lt_trans t10 t11
    · rw [hday, ← hfax]
      exact lt_trans t00 t01
    · left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by rw [← hfab]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith)⟩
  -- M=0xe (bullet 8): row-a sort (fax,fya,fab); forced big gaps {0,1,2}
  · rw [abs_of_neg (by linarith : fax - fya < 0)] at hcap0
    rw [abs_of_pos (by linarith : (0:ℝ) < fab - fya)] at hcap1
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fyx)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fax)] at hcap3
    exfalso
    refine r3_fan_overflow C hax hya.symm hab ?_ ?_ hda rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [hday, ← hfax]
      exact lt_trans t00 t01
    · rw [hday, ← hfab]
      exact lt_trans t10 t11
    · left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by rw [← hfax]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith)⟩
  -- dead world bullet 9: transitivity cycle
  · exfalso; linarith
  -- dead world bullet 10: transitivity cycle
  · exfalso; linarith
  -- dead world bullet 11: transitivity cycle
  · exfalso; linarith
  -- M=0xc (bullet 12): row-a sort (fax,fab,fya); forced big gaps {0,2,3}
  · rw [abs_of_neg (by linarith : fax - fya < 0)] at hcap0
    rw [abs_of_neg (by linarith : fab - fya < 0)] at hcap1
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fyx)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fax)] at hcap3
    exfalso
    refine r3_fan_overflow C hax hab hya.symm ?_ ?_ hda rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [← hfax, ← hfab]
      exact t30
    · rw [← hfab, hday]
      exact lt_trans t10 t11
    · right; right; left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by rw [← hfax]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith)⟩
  -- dead world bullet 13: transitivity cycle
  · exfalso; linarith
  -- M=0x8 (bullet 14): row-a sort (fax,fab,fya); forced big gaps {0,2,3}
  · rw [abs_of_neg (by linarith : fax - fya < 0)] at hcap0
    rw [abs_of_neg (by linarith : fab - fya < 0)] at hcap1
    rw [abs_of_neg (by linarith : fxb - fyx < 0)] at hcap2
    rw [abs_of_pos (by linarith : (0:ℝ) < fxb - fax)] at hcap3
    exfalso
    refine r3_fan_overflow C hax hab hya.symm ?_ ?_ hda rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [← hfax, ← hfab]
      exact t30
    · rw [← hfab, hday]
      exact lt_trans t10 t11
    · right; right; left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by rw [← hfax]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith)⟩
  -- M=0x0 (bullet 15): row-a sort (fab,fax,fya); forced big gaps {0,2,3}
  · rw [abs_of_neg (by linarith : fax - fya < 0)] at hcap0
    rw [abs_of_neg (by linarith : fab - fya < 0)] at hcap1
    rw [abs_of_neg (by linarith : fxb - fyx < 0)] at hcap2
    rw [abs_of_neg (by linarith : fxb - fax < 0)] at hcap3
    exfalso
    refine r3_fan_overflow C hab hax hya.symm ?_ ?_ hda rfl rfl rfl
      (by linarith) (by linarith) (by linarith) (by linarith) ?_
    · rw [← hfab, ← hfax]
      exact t31
    · rw [← hfax, hday]
      exact lt_trans t00 t01
    · right; right; left
      refine ⟨(one_le_floor_iff_ge lam _ hlam).mpr (by rw [← hfab]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith),
          (one_le_floor_iff_ge lam _ hlam).mpr (by rw [hday]; linarith)⟩

/-- **Five-point `R = 3` closure.**  A `SatChart` on `s = 4` cannot have
one row of defect `≥ 3` with the other three rows of defect `2`: sorting
the four non-anchor rows by `theta`, whichever pair of defect-`2` rows
straddles the high row is killed by `pairkill_{outer,midtop,midbot}`. -/
theorem five_point_R3_impossible (h : Fin 4)
    (hdh : 3 ≤ rowDefect n lam (directionRow o e c (v.succAbove h)))
    (hd : ∀ i : Fin 4, i ≠ h →
      rowDefect n lam (directionRow o e c (v.succAbove i)) = 2) : False := by
  classical
  have hθne : ∀ {i j : Fin 4}, i ≠ j → theta i ≠ theta j := by
    intro i j hij
    rcases up_or_up C hij with h1 | h1
    · exact ne_of_lt (up_theta_lt C hij h1)
    · exact (ne_of_lt (up_theta_lt C hij.symm h1)).symm
  fin_cases h
  · -- h = 0
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 2 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 2 (by decide)) (hd 1 (by decide))

  · -- h = 1
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 3 (by decide)) (hd 2 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 2 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 2 (by decide)) (hd 0 (by decide))

  · -- h = 2
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 3 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 3 (by decide)) (hd 0 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 0 (by decide)) (hd 3 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 3 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 1 (by decide)) (hd 3 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 3 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 3 (by decide)) (hd 1 (by decide))

  · -- h = 3
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
    rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
    rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
    rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c12 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c13 c23 (hd 1 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c13 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c12 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c23 c13 (hd 2 (by decide)) (hd 1 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c23 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c01 c12 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c03 c02 c12 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c01 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c02 c03 c13 (hd 0 (by decide)) (hd 1 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c03 c01 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c02 c01 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c02 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c01 c03 c23 (hd 0 (by decide)) (hd 2 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c03 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c01 c02 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c02 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c01 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · linarith
    · linarith
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c23 c03 (hd 2 (by decide)) (hd 0 (by decide))
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c23 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · linarith
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c13 c12 c02 (hd 1 (by decide)) (hd 2 (by decide))
    · exact pairkill_midbot C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c12 c13 c03 (hd 1 (by decide)) (hd 0 (by decide))
    · linarith
    · exact pairkill_midtop C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c13 c01 (hd 2 (by decide)) (hd 1 (by decide))
    · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        c23 c12 c01 (hd 2 (by decide)) (hd 1 (by decide))

/-- **Five-point `R = 4` closure.**  A `SatChart` on `s = 4` cannot have
all four non-anchor rows of defect `2`: after sorting by `theta`, the
middle two defect-`2` rows have the extreme rows on opposite sides, and
`pairkill_outer` kills the configuration. -/
theorem five_point_R4_impossible
    (hd : ∀ i : Fin 4,
      rowDefect n lam (directionRow o e c (v.succAbove i)) = 2) : False := by
  classical
  have hθne : ∀ {i j : Fin 4}, i ≠ j → theta i ≠ theta j := by
    intro i j hij
    rcases up_or_up C hij with h1 | h1
    · exact ne_of_lt (up_theta_lt C hij h1)
    · exact (ne_of_lt (up_theta_lt C hij.symm h1)).symm
  rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 1 by decide)) with c01 | c01 <;>
  rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 2 by decide)) with c02 | c02 <;>
  rcases lt_or_gt_of_ne (hθne (show (0 : Fin 4) ≠ 3 by decide)) with c03 | c03 <;>
  rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 2 by decide)) with c12 | c12 <;>
  rcases lt_or_gt_of_ne (hθne (show (1 : Fin 4) ≠ 3 by decide)) with c13 | c13 <;>
  rcases lt_or_gt_of_ne (hθne (show (2 : Fin 4) ≠ 3 by decide)) with c23 | c23
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c12 c23 (hd 1) (hd 2)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c13 c23 (hd 1) (hd 3)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c13 c12 (hd 3) (hd 1)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c12 c13 (hd 2) (hd 1)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c23 c13 (hd 2) (hd 3)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c23 c12 (hd 3) (hd 2)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c01 c12 (hd 0) (hd 1)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c03 c02 c12 (hd 0) (hd 2)
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c01 c13 (hd 0) (hd 1)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c02 c03 c13 (hd 0) (hd 3)
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c03 c01 (hd 3) (hd 0)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c02 c01 (hd 2) (hd 0)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c02 c23 (hd 0) (hd 2)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c01 c03 c23 (hd 0) (hd 3)
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c03 c02 (hd 3) (hd 0)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c01 c02 (hd 1) (hd 0)
  · linarith
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c02 c03 (hd 2) (hd 0)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c01 c03 (hd 1) (hd 0)
  · linarith
  · linarith
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c23 c03 (hd 2) (hd 3)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c23 c02 (hd 3) (hd 2)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c13 c12 c02 (hd 1) (hd 2)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c12 c13 c03 (hd 1) (hd 3)
  · linarith
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c13 c01 (hd 3) (hd 1)
  · exact pairkill_outer C (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      c23 c12 c01 (hd 2) (hd 1)

end R3Dag

end Jsp404
