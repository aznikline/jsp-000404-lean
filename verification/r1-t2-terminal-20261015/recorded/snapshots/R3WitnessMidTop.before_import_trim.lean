import Jsp000404.R3WitnessOuter

open scoped EuclideanGeometry EuclideanSpace

namespace Jsp404

section R3Dag

variable {n : ℕ} {o : Orientation ℝ Plane₂ (Fin 2)} {e : Plane₂}
  {lam : ℝ} {c : Fin (4 + 1) → Plane₂} {v : Fin (4 + 1)}
  {theta : Fin 4 → ℝ}
  (C : SatChart o e n lam c v theta)
include C

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
end R3Dag

end Jsp404
