import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S4
import Jsp000404.R1LeavesN7_32S5
import Jsp000404.R1LeavesN7_32S6
import Jsp000404.R1LeavesN7_32S7
import Jsp000404.R1LeavesN7_32S8
import Jsp000404.R1LeavesN7_32S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3145 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3689 | h3689
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x0 m hb0 hb4 h0 h2352 h2875 h2994 h3145 h3689
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1_x1 m hb0 hb4 h0 h2352 h2875 h2994 h3145 h3689

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h3145 | h3145
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x0 m hb0 hb4 h0 h2352 h2875 h2994 h3145
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x1_x1 m hb0 hb4 h0 h2352 h2875 h2994 h3145

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2875 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2994 | h2994
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x0 m hb0 hb4 h0 h2352 h2875 h2994
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1_x1 m hb0 hb4 h0 h2352 h2875 h2994

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2352 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2875 | h2875
  · exact r1l7_20_14_H_I_L_R_x1_x1_x0 m hb0 hb4 h0 h2352 h2875
  · exact r1l7_20_14_H_I_L_R_x1_x1_x1 m hb0 hb4 h0 h2352 h2875

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h2352 | h2352
  · exact r1l7_20_14_H_I_L_R_x1_x0 m hb0 hb4 h0 h2352
  · exact r1l7_20_14_H_I_L_R_x1_x1 m hb0 hb4 h0 h2352

set_option maxHeartbeats 9046000 in
theorem r1l7_20_14_H_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_14_H_I_L_R_x0 m hb0 hb4 h0
  · exact r1l7_20_14_H_I_L_R_x1 m hb0 hb4 h0

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h2013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h2014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  have h879 := hg879
  have h1407 := hg1407
  rcases m.htr 1 2 3 (by decide) (by decide) with h2015 | h2015
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2016 | h2016
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2017 | h2017
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2018 | h2018
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2019 | h2019
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2020 | h2020
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2021 | h2021
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2022 | h2022
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2023 | h2023
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2024 | h2024
                    · rcases h2bigk with h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c | h2025c
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h0, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2021, h2024, hc02, hc45, hlam, hphi, ht0b, ht5b, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        rcases p2025_3 (m.d 0 2) (by simp) with h2029 | h2029
                        · rcases p2025_3 (m.d 1 2) (by simp) with h2030 | h2030
                          · rcases p2025_3 (m.d 2 3) (by simp) with h2031 | h2031
                            · linarith only [h2009, h2031, hlam]
                            · linarith only [h2021, h2031, hlam]
                          · linarith only [h2016, h2030, hlam]
                        · linarith only [h2029, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        rcases p2025_3 (m.d 0 2) (by simp) with h2036 | h2036
                        · rcases p2025_3 (m.d 1 2) (by simp) with h2037 | h2037
                          · rcases p2025_3 (m.d 2 3) (by simp) with h2038 | h2038
                            · linarith only [h2009, h2038, hlam]
                            · linarith only [h2022, h2038, hlam]
                          · linarith only [h2017, h2037, hlam]
                        · linarith only [h2036, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2009, h2021, h2024, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2021, h2024, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        rcases p2025_3 (m.d 0 2) (by simp) with h2046 | h2046
                        · linarith only [h0, h2046, hlam]
                        · linarith only [h2010, h2046, hlam]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        rcases p2025_3 (m.d 0 2) (by simp) with h2049 | h2049
                        · linarith only [h0, h2049, hlam]
                        · linarith only [h2011, h2049, hlam]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2009, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2015, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2009, h2023, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2025_1, u2ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h0, h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2025_1, u2ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2010, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2016, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2021, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hc24, hlam, hphi, p2025_1, u2ehi4]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2011, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2017, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2022, hlam, p2025_0]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [h2023, hlam, p2025_1]
                      · have p2025_0 := h2025c.1
                        have p2025_1 := h2025c.2.1
                        have p2025_2 := h2025c.2.2.1
                        have p2025_3 := h2025c.2.2.2
                        linarith only [hlam, p2025_0]
                    · rcases h2bigk with h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c | h2067c
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h0, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h0, h2021, h2023, h2024, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h0, h2023, h2024, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        rcases p2067_3 (m.d 0 2) (by simp) with h2072 | h2072
                        · rcases p2067_3 (m.d 1 2) (by simp) with h2073 | h2073
                          · rcases p2067_3 (m.d 2 3) (by simp) with h2074 | h2074
                            · linarith only [h2009, h2074, hlam]
                            · linarith only [h2022, h2074, hlam]
                          · linarith only [h2017, h2073, hlam]
                        · linarith only [h2072, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2009, h2021, h2023, h2024, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2021, h2023, h2024, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2023, h2024, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2067_1]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        rcases p2067_3 (m.d 0 2) (by simp) with h2083 | h2083
                        · linarith only [h0, h2083, hlam]
                        · linarith only [h2011, h2083, hlam]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2009, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2015, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2009, h2023, h2024, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2067_1]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h0, h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2067_1, u2ehi4]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2010, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2016, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2021, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [hc24, hlam, hphi, p2067_1, u2ehi4]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2011, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2017, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2022, hlam, p2067_0]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [h2023, hlam, p2067_1]
                      · have p2067_0 := h2067c.1
                        have p2067_1 := h2067c.2.1
                        have p2067_2 := h2067c.2.2.1
                        have p2067_3 := h2067c.2.2.2
                        linarith only [hlam, p2067_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2101 | h2101
                    · linarith only [h2021, h2023, h2101, hlam]
                    · rcases h2bigk with h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c | h2103c
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h0, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 2) (by simp) with h2106 | h2106
                        · rcases p2103_3 (m.d 1 2) (by simp) with h2107 | h2107
                          · rcases p2103_3 (m.d 2 3) (by simp) with h2108 | h2108
                            · linarith only [h2108, hlam, p2103_0]
                            · rcases p2103_3 (m.d 2 4) (by simp) with h2110 | h2110
                              · linarith only [h2010, h2110, hlam]
                              · rcases p2103_3 (m.d 2 5) (by simp) with h2112 | h2112
                                · linarith only [h2011, h2112, hlam]
                                · rcases h3bigk with h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c | h2114c
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h879, hlam, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 3) (by simp) with h2117 | h2117
                                    · rcases p2114_3 (m.d 1 3) (by simp) with h2118 | h2118
                                      · rcases p2114_3 (m.d 2 3) (by simp) with h2119 | h2119
                                        · linarith only [h2009, h2119, hlam]
                                        · rcases p2114_3 (m.d 3 4) (by simp) with h2121 | h2121
                                          · linarith only [h2012, h2121, hlam]
                                          · rcases p2114_3 (m.d 3 5) (by simp) with h2123 | h2123
                                            · linarith only [h2013, h2123, hlam]
                                            · rcases h3emax with h2125 | h2125 | h2125 | h2125 | h2125
                                              · linarith only [h2125, hc23, hlam, p2114_1]
                                              · linarith only [h1407, h2018, h2020, h2125, hc01, hlam, ht12, ht23]
                                              · linarith only [h2125, hlam, ht23, u2ehi2]
                                              · rcases h5bigk with h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c | h2129c
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [hlam, p2129_0]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h1407, hlam, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  rcases p2129_3 (m.d 0 5) (by simp) with h2132 | h2132
                                                  · rcases p2129_3 (m.d 1 5) (by simp) with h2133 | h2133
                                                    · rcases p2129_3 (m.d 2 5) (by simp) with h2134 | h2134
                                                      · linarith only [h2011, h2134, hlam]
                                                      · rcases p2129_3 (m.d 3 5) (by simp) with h2136 | h2136
                                                        · linarith only [h2013, h2136, hlam]
                                                        · rcases p2129_3 (m.d 4 5) (by simp) with h2138 | h2138
                                                          · linarith only [h2014, h2138, hlam]
                                                          · linarith only [h2023, h2138, hlam]
                                                    · linarith only [h2017, h2133, hlam]
                                                  · linarith only [h2011, h2132, hlam]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  rcases p2129_3 (m.d 0 5) (by simp) with h2143 | h2143
                                                  · rcases p2129_3 (m.d 1 5) (by simp) with h2144 | h2144
                                                    · rcases p2129_3 (m.d 2 5) (by simp) with h2145 | h2145
                                                      · linarith only [h2011, h2145, hlam]
                                                      · linarith only [h2022, h2145, hlam]
                                                    · linarith only [h2019, h2144, hlam]
                                                  · linarith only [h2013, h2143, hlam]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2012, h2014, h2015, h2023, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2129_1, u2ehi3]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2014, h2020, h2023, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2129_1, u2ehi3]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [hlam, p2129_0]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  rcases p2129_3 (m.d 0 5) (by simp) with h2153 | h2153
                                                  · linarith only [h1407, h2153, hlam]
                                                  · linarith only [h2011, h2153, hlam]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  rcases p2129_3 (m.d 0 5) (by simp) with h2156 | h2156
                                                  · linarith only [h1407, h2156, hlam]
                                                  · linarith only [h2013, h2156, hlam]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2015, h2018, h2020, h2023, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2129_1, u2ehi3]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2011, hlam, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2017, hlam, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [hlam, p2129_0]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2015, h2022, h879, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2114_1, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2023, hlam, p2129_0]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2013, hlam, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2019, hlam, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2022, hlam, p2129_0]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [hlam, p2129_0]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2101, hlam, p2129_0]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2014, hlam, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [h2020, hlam, p2129_1]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [hc45, hlam, hphi, ht23, ht34, p2129_1, u2ehi4]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  rcases p2129_3 (m.d 0 5) (by simp) with h2173 | h2173
                                                  · rcases p2129_3 (m.d 1 5) (by simp) with h2174 | h2174
                                                    · rcases p2129_3 (m.d 2 5) (by simp) with h2175 | h2175
                                                      · linarith only [h2023, h2175, hlam]
                                                      · linarith only [h2022, h2175, hlam]
                                                    · linarith only [h2019, h2174, hlam]
                                                  · linarith only [h2013, h2173, hlam]
                                                · have p2129_0 := h2129c.1
                                                  have p2129_1 := h2129c.2.1
                                                  have p2129_2 := h2129c.2.2.1
                                                  have p2129_3 := h2129c.2.2.2
                                                  linarith only [hlam, p2129_0]
                                              · rcases h5bigk with h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c | h2181c
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [hlam, p2181_0]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h1407, hlam, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  rcases p2181_3 (m.d 0 5) (by simp) with h2184 | h2184
                                                  · rcases p2181_3 (m.d 1 5) (by simp) with h2185 | h2185
                                                    · rcases p2181_3 (m.d 2 5) (by simp) with h2186 | h2186
                                                      · linarith only [h2011, h2186, hlam]
                                                      · rcases p2181_3 (m.d 3 5) (by simp) with h2188 | h2188
                                                        · linarith only [h2013, h2188, hlam]
                                                        · rcases p2181_3 (m.d 4 5) (by simp) with h2190 | h2190
                                                          · linarith only [h2014, h2190, hlam]
                                                          · linarith only [h2023, h2190, hlam]
                                                    · linarith only [h2017, h2185, hlam]
                                                  · linarith only [h2011, h2184, hlam]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  rcases p2181_3 (m.d 0 5) (by simp) with h2195 | h2195
                                                  · rcases p2181_3 (m.d 1 5) (by simp) with h2196 | h2196
                                                    · rcases p2181_3 (m.d 2 5) (by simp) with h2197 | h2197
                                                      · linarith only [h2011, h2197, hlam]
                                                      · linarith only [h2022, h2197, hlam]
                                                    · linarith only [h2019, h2196, hlam]
                                                  · linarith only [h2013, h2195, hlam]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2023, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2181_1, u2ehi3]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2014, h2015, h2018, h2020, h2023, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2181_1, u2ehi3]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [hlam, p2181_0]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  rcases p2181_3 (m.d 0 5) (by simp) with h2205 | h2205
                                                  · linarith only [h1407, h2205, hlam]
                                                  · linarith only [h2011, h2205, hlam]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  rcases p2181_3 (m.d 0 5) (by simp) with h2208 | h2208
                                                  · linarith only [h1407, h2208, hlam]
                                                  · linarith only [h2013, h2208, hlam]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2023, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2181_1, u2ehi3]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2011, hlam, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2017, hlam, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [hlam, p2181_0]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2015, h2022, h2101, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2114_1, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2023, hlam, p2181_0]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2013, hlam, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2019, hlam, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2022, hlam, p2181_0]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [hlam, p2181_0]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2101, hlam, p2181_0]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2014, hlam, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [h2020, hlam, p2181_1]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [hc45, hlam, hphi, ht23, ht34, p2181_1, u2ehi4]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  rcases p2181_3 (m.d 0 5) (by simp) with h2225 | h2225
                                                  · rcases p2181_3 (m.d 1 5) (by simp) with h2226 | h2226
                                                    · rcases p2181_3 (m.d 2 5) (by simp) with h2227 | h2227
                                                      · linarith only [h2023, h2227, hlam]
                                                      · linarith only [h2022, h2227, hlam]
                                                    · linarith only [h2019, h2226, hlam]
                                                  · linarith only [h2013, h2225, hlam]
                                                · have p2181_0 := h2181c.1
                                                  have p2181_1 := h2181c.2.1
                                                  have p2181_2 := h2181c.2.2.1
                                                  have p2181_3 := h2181c.2.2.2
                                                  linarith only [hlam, p2181_0]
                                      · linarith only [h2015, h2118, hlam]
                                    · linarith only [h2009, h2117, hlam]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 3) (by simp) with h2235 | h2235
                                    · rcases p2114_3 (m.d 1 3) (by simp) with h2236 | h2236
                                      · rcases p2114_3 (m.d 2 3) (by simp) with h2237 | h2237
                                        · linarith only [h2009, h2237, hlam]
                                        · linarith only [h2021, h2237, hlam]
                                      · linarith only [h2018, h2236, hlam]
                                    · linarith only [h2235, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 3) (by simp) with h2242 | h2242
                                    · rcases p2114_3 (m.d 1 3) (by simp) with h2243 | h2243
                                      · rcases p2114_3 (m.d 2 3) (by simp) with h2244 | h2244
                                        · linarith only [h2009, h2244, hlam]
                                        · linarith only [h2022, h2244, hlam]
                                      · linarith only [h2019, h2243, hlam]
                                    · linarith only [h2242, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2012, h2014, h2015, h2023, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2114_1, u2ehi3]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 3) (by simp) with h2251 | h2251
                                    · linarith only [h2251, h879, hlam]
                                    · linarith only [h2009, h2251, hlam]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 3) (by simp) with h2254 | h2254
                                    · linarith only [h2254, h879, hlam]
                                    · linarith only [h2012, h2254, hlam]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    rcases p2114_3 (m.d 0 3) (by simp) with h2257 | h2257
                                    · linarith only [h2257, h879, hlam]
                                    · linarith only [h2013, h2257, hlam]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2009, hlam, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2015, hlam, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2103_1, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p2103_1, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2012, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2018, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2021, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2101, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2013, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2019, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h2022, hlam, p2114_0]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [h0, h2022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2103_1, p2114_1]
                                  · have p2114_0 := h2114c.1
                                    have p2114_1 := h2114c.2.1
                                    have p2114_2 := h2114c.2.2.1
                                    have p2114_3 := h2114c.2.2.2
                                    linarith only [hlam, p2114_0]
                          · linarith only [h2015, h2107, hlam]
                        · linarith only [h2106, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 2) (by simp) with h2277 | h2277
                        · rcases p2103_3 (m.d 1 2) (by simp) with h2278 | h2278
                          · rcases p2103_3 (m.d 2 3) (by simp) with h2279 | h2279
                            · linarith only [h2009, h2279, hlam]
                            · linarith only [h2021, h2279, hlam]
                          · linarith only [h2016, h2278, hlam]
                        · linarith only [h2277, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 2) (by simp) with h2284 | h2284
                        · rcases p2103_3 (m.d 1 2) (by simp) with h2285 | h2285
                          · rcases p2103_3 (m.d 2 3) (by simp) with h2286 | h2286
                            · linarith only [h2009, h2286, hlam]
                            · linarith only [h2022, h2286, hlam]
                          · linarith only [h2017, h2285, hlam]
                        · linarith only [h2284, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2103_1, u2ehi2]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 2) (by simp) with h2293 | h2293
                        · linarith only [h0, h2293, hlam]
                        · linarith only [h2009, h2293, hlam]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 2) (by simp) with h2296 | h2296
                        · linarith only [h0, h2296, hlam]
                        · linarith only [h2010, h2296, hlam]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        rcases p2103_3 (m.d 0 2) (by simp) with h2299 | h2299
                        · linarith only [h0, h2299, hlam]
                        · linarith only [h2011, h2299, hlam]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2009, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2015, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hc23, hlam, hphi, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h0, h2009, h2023, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2010, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2016, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2021, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2023, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2011, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2017, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [h2022, hlam, p2103_0]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hc25, hlam, hphi, p2103_1, u2ehi3]
                      · have p2103_0 := h2103c.1
                        have p2103_1 := h2103c.2.1
                        have p2103_2 := h2103c.2.2.1
                        have p2103_3 := h2103c.2.2.2
                        linarith only [hlam, p2103_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2317 | h2317
                  · linarith only [h2021, h2022, h2317, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2319 | h2319
                    · linarith only [h2317, h2319, hc34, hlam, hphi, ht23, u2ehi3]
                    · rcases h2bigk with h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c | h2321c
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h0, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        rcases p2321_3 (m.d 0 2) (by simp) with h2324 | h2324
                        · rcases p2321_3 (m.d 1 2) (by simp) with h2325 | h2325
                          · rcases p2321_3 (m.d 2 3) (by simp) with h2326 | h2326
                            · linarith only [h2326, hlam, p2321_0]
                            · rcases p2321_3 (m.d 2 4) (by simp) with h2328 | h2328
                              · linarith only [h2010, h2328, hlam]
                              · rcases p2321_3 (m.d 2 5) (by simp) with h2330 | h2330
                                · linarith only [h2011, h2330, hlam]
                                · linarith only [h2022, h2330, hlam]
                          · linarith only [h2015, h2325, hlam]
                        · linarith only [h2324, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        rcases p2321_3 (m.d 0 2) (by simp) with h2335 | h2335
                        · rcases p2321_3 (m.d 1 2) (by simp) with h2336 | h2336
                          · rcases p2321_3 (m.d 2 3) (by simp) with h2337 | h2337
                            · linarith only [h2009, h2337, hlam]
                            · linarith only [h2021, h2337, hlam]
                          · linarith only [h2016, h2336, hlam]
                        · linarith only [h2335, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        rcases p2321_3 (m.d 0 2) (by simp) with h2342 | h2342
                        · rcases p2321_3 (m.d 1 2) (by simp) with h2343 | h2343
                          · rcases p2321_3 (m.d 2 3) (by simp) with h2344 | h2344
                            · linarith only [h2009, h2344, hlam]
                            · rcases p2321_3 (m.d 2 4) (by simp) with h2346 | h2346
                              · linarith only [h2010, h2346, hlam]
                              · rcases p2321_3 (m.d 2 5) (by simp) with h2348 | h2348
                                · linarith only [h2348, hlam, p2321_0]
                                · rcases h3bigk with h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c | h2350c
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h879, hlam, p2350_1]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    rcases p2350_3 (m.d 0 3) (by simp) with h2353 | h2353
                                    · rcases p2350_3 (m.d 1 3) (by simp) with h2354 | h2354
                                      · rcases p2350_3 (m.d 2 3) (by simp) with h2355 | h2355
                                        · linarith only [h2009, h2355, hlam]
                                        · rcases p2350_3 (m.d 3 4) (by simp) with h2357 | h2357
                                          · linarith only [h2012, h2357, hlam]
                                          · rcases p2350_3 (m.d 3 5) (by simp) with h2359 | h2359
                                            · linarith only [h2013, h2359, hlam]
                                            · linarith only [h2022, h2359, hlam]
                                      · linarith only [h2015, h2354, hlam]
                                    · linarith only [h2009, h2353, hlam]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2012, h2014, h2021, h2022, h2319, hlam, p2350_2]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h0, h2009, h2021, h2022, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2350_1, u2ehi3]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2013, h2021, h2022, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2350_1, u2ehi3]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    rcases p2350_3 (m.d 0 3) (by simp) with h2368 | h2368
                                    · linarith only [h2368, h879, hlam]
                                    · linarith only [h2009, h2368, hlam]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2012, h2014, h2021, h2022, h2319, h879, hlam, p2350_2]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2021, h2022, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2350_1, u2ehi3]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2009, hlam, p2350_1]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2015, hlam, p2350_1]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2012, h2014, h2022, h2319, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p2350_1]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2022, hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2012, hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2018, hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2021, hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2319, hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2013, hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2019, hlam, p2350_0]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [h2012, h2014, h2319, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2350_1, u2ehi2]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    rcases p2350_3 (m.d 0 3) (by simp) with h2386 | h2386
                                    · rcases p2350_3 (m.d 1 3) (by simp) with h2387 | h2387
                                      · rcases p2350_3 (m.d 2 3) (by simp) with h2388 | h2388
                                        · linarith only [h2022, h2388, hlam]
                                        · linarith only [h2021, h2388, hlam]
                                      · linarith only [h2018, h2387, hlam]
                                    · linarith only [h2012, h2386, hlam]
                                  · have p2350_0 := h2350c.1
                                    have p2350_1 := h2350c.2.1
                                    have p2350_2 := h2350c.2.2.1
                                    have p2350_3 := h2350c.2.2.2
                                    linarith only [hlam, p2350_0]
                          · linarith only [h2017, h2343, hlam]
                        · linarith only [h2342, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2009, h2021, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2321_1, u2ehi3]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        rcases p2321_3 (m.d 0 2) (by simp) with h2398 | h2398
                        · linarith only [h0, h2398, hlam]
                        · linarith only [h2009, h2398, hlam]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        rcases p2321_3 (m.d 0 2) (by simp) with h2401 | h2401
                        · linarith only [h0, h2401, hlam]
                        · linarith only [h2010, h2401, hlam]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        rcases p2321_3 (m.d 0 2) (by simp) with h2404 | h2404
                        · linarith only [h0, h2404, hlam]
                        · linarith only [h2011, h2404, hlam]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2009, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2015, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2009, h2012, h2014, h2022, h2319, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2321_1, u2ehi3]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2022, hlam, p2321_1]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2010, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2016, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2021, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2317, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2011, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h2017, hlam, p2321_0]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [hc25, hlam, hphi, p2321_1, u2ehi2]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [h0, h2009, h2012, h2014, h2022, h2319, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2321_1, u2ehi3]
                      · have p2321_0 := h2321c.1
                        have p2321_1 := h2321c.2.1
                        have p2321_2 := h2321c.2.2.1
                        have p2321_3 := h2321c.2.2.2
                        linarith only [hlam, p2321_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2422 | h2422
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2423 | h2423
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2424 | h2424
                    · rcases h2bigk with h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c | h2425c
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h0, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        rcases p2425_3 (m.d 0 2) (by simp) with h2428 | h2428
                        · rcases p2425_3 (m.d 1 2) (by simp) with h2429 | h2429
                          · rcases p2425_3 (m.d 2 3) (by simp) with h2430 | h2430
                            · linarith only [h2430, hlam, p2425_0]
                            · rcases p2425_3 (m.d 2 4) (by simp) with h2432 | h2432
                              · linarith only [h2010, h2432, hlam]
                              · linarith only [h2021, h2432, hlam]
                          · linarith only [h2015, h2429, hlam]
                        · linarith only [h2428, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        rcases p2425_3 (m.d 0 2) (by simp) with h2437 | h2437
                        · rcases p2425_3 (m.d 1 2) (by simp) with h2438 | h2438
                          · rcases p2425_3 (m.d 2 3) (by simp) with h2439 | h2439
                            · linarith only [h2009, h2439, hlam]
                            · rcases p2425_3 (m.d 2 4) (by simp) with h2441 | h2441
                              · linarith only [h2441, hlam, p2425_0]
                              · rcases p2425_3 (m.d 2 5) (by simp) with h2443 | h2443
                                · linarith only [h2011, h2443, hlam]
                                · rcases h3bigk with h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c | h2445c
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h879, hlam, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    rcases p2445_3 (m.d 0 3) (by simp) with h2448 | h2448
                                    · rcases p2445_3 (m.d 1 3) (by simp) with h2449 | h2449
                                      · rcases p2445_3 (m.d 2 3) (by simp) with h2450 | h2450
                                        · linarith only [h2009, h2450, hlam]
                                        · rcases p2445_3 (m.d 3 4) (by simp) with h2452 | h2452
                                          · linarith only [h2012, h2452, hlam]
                                          · linarith only [h2021, h2452, hlam]
                                      · linarith only [h2015, h2449, hlam]
                                    · linarith only [h2009, h2448, hlam]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h0, h2009, h2021, h2422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2445_1, u2ehi4]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2012, h2021, h2422, hlam, p2445_2]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2012, h2015, h2021, h2422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2445_1, u2ehi4]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    rcases p2445_3 (m.d 0 3) (by simp) with h2461 | h2461
                                    · linarith only [h2461, h879, hlam]
                                    · linarith only [h2009, h2461, hlam]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2015, h2021, h2422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2445_1, u2ehi4]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2012, h2021, h2422, h879, hlam, p2445_2]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2009, hlam, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2015, hlam, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2021, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2012, h2021, hc03, hc35, hlam, hphi, ht0b, ht5b, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2012, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2018, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2012, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2445_1, u2ehi2]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    rcases p2445_3 (m.d 0 3) (by simp) with h2475 | h2475
                                    · rcases p2445_3 (m.d 1 3) (by simp) with h2476 | h2476
                                      · rcases p2445_3 (m.d 2 3) (by simp) with h2477 | h2477
                                        · linarith only [h2021, h2477, hlam]
                                        · linarith only [h2422, h2477, hlam]
                                      · linarith only [h2019, h2476, hlam]
                                    · linarith only [h2013, h2475, hlam]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2013, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2019, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2422, hlam, p2445_0]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [h2424, hlam, p2445_1]
                                  · have p2445_0 := h2445c.1
                                    have p2445_1 := h2445c.2.1
                                    have p2445_2 := h2445c.2.2.1
                                    have p2445_3 := h2445c.2.2.2
                                    linarith only [hlam, p2445_0]
                          · linarith only [h2016, h2438, hlam]
                        · linarith only [h2437, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        rcases p2425_3 (m.d 0 2) (by simp) with h2489 | h2489
                        · rcases p2425_3 (m.d 1 2) (by simp) with h2490 | h2490
                          · rcases p2425_3 (m.d 2 3) (by simp) with h2491 | h2491
                            · linarith only [h2009, h2491, hlam]
                            · linarith only [h2422, h2491, hlam]
                          · linarith only [h2017, h2490, hlam]
                        · linarith only [h2489, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2009, h2422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2425_1, u2ehi4]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        rcases p2425_3 (m.d 0 2) (by simp) with h2498 | h2498
                        · linarith only [h0, h2498, hlam]
                        · linarith only [h2009, h2498, hlam]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        rcases p2425_3 (m.d 0 2) (by simp) with h2501 | h2501
                        · linarith only [h0, h2501, hlam]
                        · linarith only [h2010, h2501, hlam]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        rcases p2425_3 (m.d 0 2) (by simp) with h2504 | h2504
                        · linarith only [h0, h2504, hlam]
                        · linarith only [h2011, h2504, hlam]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2009, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2015, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2021, hlam, p2425_1]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2009, h2012, h2021, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2425_1, u2ehi4]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2010, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2016, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [hc24, hlam, hphi, p2425_1, u2ehi2]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h0, h2009, h2012, h2021, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2425_1, u2ehi4]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2011, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2017, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2422, hlam, p2425_0]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [h2423, hlam, p2425_1]
                      · have p2425_0 := h2425c.1
                        have p2425_1 := h2425c.2.1
                        have p2425_2 := h2425c.2.2.1
                        have p2425_3 := h2425c.2.2.2
                        linarith only [hlam, p2425_0]
                    · linarith only [h0, h2009, h2012, h2014, h2021, h2422, h2424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · linarith only [h2021, h2422, h2423, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2524 | h2524
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2525 | h2525
                    · rcases h2bigk with h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c | h2526c
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h0, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        rcases p2526_3 (m.d 0 2) (by simp) with h2529 | h2529
                        · rcases p2526_3 (m.d 1 2) (by simp) with h2530 | h2530
                          · rcases p2526_3 (m.d 2 3) (by simp) with h2531 | h2531
                            · linarith only [h2531, hlam, p2526_0]
                            · rcases p2526_3 (m.d 2 4) (by simp) with h2533 | h2533
                              · linarith only [h2010, h2533, hlam]
                              · linarith only [h2021, h2533, hlam]
                          · linarith only [h2015, h2530, hlam]
                        · linarith only [h2529, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        rcases p2526_3 (m.d 0 2) (by simp) with h2538 | h2538
                        · rcases p2526_3 (m.d 1 2) (by simp) with h2539 | h2539
                          · rcases p2526_3 (m.d 2 3) (by simp) with h2540 | h2540
                            · linarith only [h2009, h2540, hlam]
                            · rcases p2526_3 (m.d 2 4) (by simp) with h2542 | h2542
                              · linarith only [h2542, hlam, p2526_0]
                              · rcases p2526_3 (m.d 2 5) (by simp) with h2544 | h2544
                                · linarith only [h2011, h2544, hlam]
                                · rcases h3bigk with h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c | h2546c
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h879, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    rcases p2546_3 (m.d 0 3) (by simp) with h2549 | h2549
                                    · rcases p2546_3 (m.d 1 3) (by simp) with h2550 | h2550
                                      · rcases p2546_3 (m.d 2 3) (by simp) with h2551 | h2551
                                        · linarith only [h2009, h2551, hlam]
                                        · rcases p2546_3 (m.d 3 4) (by simp) with h2553 | h2553
                                          · linarith only [h2012, h2553, hlam]
                                          · linarith only [h2021, h2553, hlam]
                                      · linarith only [h2015, h2550, hlam]
                                    · linarith only [h2009, h2549, hlam]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h0, h2009, h2021, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h0, h2009, h2422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2013, h2015, h2422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    rcases p2546_3 (m.d 0 3) (by simp) with h2562 | h2562
                                    · linarith only [h2562, h879, hlam]
                                    · linarith only [h2009, h2562, hlam]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2015, h2422, h2525, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2015, h2422, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2009, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2015, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2021, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2422, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2012, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2018, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2012, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2012, h2015, h2422, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2013, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2019, hlam, p2546_0]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hc35, hlam, hphi, ht23, p2546_1, u2ehi2]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [h2525, hlam, p2546_1]
                                  · have p2546_0 := h2546c.1
                                    have p2546_1 := h2546c.2.1
                                    have p2546_2 := h2546c.2.2.1
                                    have p2546_3 := h2546c.2.2.2
                                    linarith only [hlam, p2546_0]
                          · linarith only [h2016, h2539, hlam]
                        · linarith only [h2538, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        rcases p2526_3 (m.d 0 2) (by simp) with h2584 | h2584
                        · rcases p2526_3 (m.d 1 2) (by simp) with h2585 | h2585
                          · rcases p2526_3 (m.d 2 3) (by simp) with h2586 | h2586
                            · linarith only [h2009, h2586, hlam]
                            · rcases p2526_3 (m.d 2 4) (by simp) with h2588 | h2588
                              · linarith only [h2010, h2588, hlam]
                              · linarith only [h2524, h2588, hlam]
                          · linarith only [h2017, h2585, hlam]
                        · linarith only [h2584, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2009, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2526_1, u2ehi2]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        rcases p2526_3 (m.d 0 2) (by simp) with h2595 | h2595
                        · linarith only [h0, h2595, hlam]
                        · linarith only [h2009, h2595, hlam]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        rcases p2526_3 (m.d 0 2) (by simp) with h2598 | h2598
                        · linarith only [h0, h2598, hlam]
                        · linarith only [h2010, h2598, hlam]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        rcases p2526_3 (m.d 0 2) (by simp) with h2601 | h2601
                        · linarith only [h0, h2601, hlam]
                        · linarith only [h2011, h2601, hlam]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2009, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2015, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2021, hlam, p2526_1]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2422, hlam, p2526_1]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2010, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2016, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [hc24, hlam, hphi, p2526_1, u2ehi2]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2012, h2015, h2021, h2422, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2526_1, u2ehi2]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2011, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2017, hlam, p2526_0]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [hc25, hlam, hphi, p2526_1, u2ehi2]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [h2524, hlam, p2526_1]
                      · have p2526_0 := h2526c.1
                        have p2526_1 := h2526c.2.1
                        have p2526_2 := h2526c.2.2.1
                        have p2526_3 := h2526c.2.2.2
                        linarith only [hlam, p2526_0]
                    · linarith only [h2012, h2014, h2015, h2021, h2525, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2620 | h2620
                    · linarith only [h2524, h2620, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h2012, h2014, h2015, h2021, h2620, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h1407, h2014, h2020, hlam]
          · linarith only [h2013, h2019, h879, hlam]
        · linarith only [h2012, h2018, h879, hlam]
      · linarith only [h0, h2009, h2017, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h2009, h2016, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h2009, h2015, hlam]

end R2N4
