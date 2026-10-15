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

end R3Dag

end Jsp404
