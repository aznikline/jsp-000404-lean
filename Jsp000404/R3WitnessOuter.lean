import Jsp000404.R3WitnessBounds
import Jsp000404.R3WitnessTrichotomy

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section R3Dag

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}
  (C : SatChart o e n lam c v theta)
include C

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

end R3Dag

end Jsp404
