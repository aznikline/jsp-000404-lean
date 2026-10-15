import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2011 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  linarith only [h2009, h2011, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h2011 | h2011
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010 h2011

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2010 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  linarith only [h2009, h2010, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h2010 | h2010
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009 h2010

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2009 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h4200 | h4200
  · linarith only [h2009, h4200, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4202 | h4202
    · linarith only [h2009, h4202, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4204 | h4204
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4205 | h4205
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4206 | h4206
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4207 | h4207
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4208 | h4208
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4209 | h4209
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4210 | h4210
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4211 | h4211
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4212 | h4212
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4213 | h4213
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4214 | h4214
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4215 | h4215
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4216 | h4216
                              · rcases h2bigk with h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h0, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h2009, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4200, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4202, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  rcases p4217_3 (m.d 0 2) (by simp) with h4223 | h4223
                                  · linarith only [h0, h4223, hlam]
                                  · rcases p4217_3 (m.d 1 2) (by simp) with h4225 | h4225
                                    · rcases p4217_3 (m.d 2 3) (by simp) with h4226 | h4226
                                      · linarith only [h4207, h4226, hlam]
                                      · linarith only [h2009, h4226, hlam]
                                    · linarith only [h0, h4225, hlam]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4202, h4213, h4215, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4202, h4215, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4202, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4207, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4202, h4207, h4215, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4202, h4207, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hc24, hlam, hphi, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4208, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4213, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4202, h4207, h4213, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hc25, hlam, hphi, p4217_1, u2ehi0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4209, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4214, hlam, p4217_0]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [h4215, hlam, p4217_1]
                                · have p4217_0 := h4217c.1
                                  have p4217_1 := h4217c.2.1
                                  have p4217_2 := h4217c.2.2.1
                                  have p4217_3 := h4217c.2.2.2
                                  linarith only [hlam, p4217_0]
                              · rcases h2bigk with h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c | h4249c
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h0, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h2009, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4200, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4202, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  rcases p4249_3 (m.d 0 2) (by simp) with h4255 | h4255
                                  · linarith only [h0, h4255, hlam]
                                  · rcases p4249_3 (m.d 1 2) (by simp) with h4257 | h4257
                                    · rcases p4249_3 (m.d 2 3) (by simp) with h4258 | h4258
                                      · linarith only [h4207, h4258, hlam]
                                      · linarith only [h2009, h4258, hlam]
                                    · linarith only [h0, h4257, hlam]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4200, h4206, h4213, h4216, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4249_1]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4200, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4202, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4207, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4200, h4207, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4202, h4207, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hc24, hlam, hphi, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4208, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4213, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4202, h4207, h4213, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hc25, hlam, hphi, p4249_1, u2ehi0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4209, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4214, hlam, p4249_0]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [h4215, hlam, p4249_1]
                                · have p4249_0 := h4249c.1
                                  have p4249_1 := h4249c.2.1
                                  have p4249_2 := h4249c.2.2.1
                                  have p4249_3 := h4249c.2.2.2
                                  linarith only [hlam, p4249_0]
                            · linarith only [h2009, h4204, h4206, h4207, h4215, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h2009, h4214, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h2009, h4213, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h4200, h4204, h4206, h4208, h4212, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h2009, h4205, h4207, h4211, h879, hc01, hc12, hlam, hphi]
                  · linarith only [h2009, h4204, h4207, h4210, hlam]
                · linarith only [h4207, h4209, hc25, hlam, hphi, u2ehi2]
              · linarith only [h2009, h4207, h4208, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4289 | h4289
              · linarith only [h4207, h4289, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4291 | h4291
                · linarith only [h4207, h4291, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4293 | h4293
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4294 | h4294
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4295 | h4295
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4296 | h4296
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4297 | h4297
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4298 | h4298
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4299 | h4299
                              · rcases h2bigk with h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h0, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h2009, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4200, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4202, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4291, h4296, h4298, hc23, hlam, hphi, p4300_1, u2ehi0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4207, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4289, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4291, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4300_1, u2ehi0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4300_1, u2ehi1]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4300_1, u2ehi3]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h0, h4291, hc01, hc23, hlam, hphi, ht12, p4300_1]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hc24, hlam, hphi, p4300_1, u2ehi0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4300_1]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4296, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h0, h4291, h4296, hc01, hc23, hlam, hphi, ht12, p4300_1]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hc25, hlam, hphi, p4300_1, u2ehi0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4300_1]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4297, hlam, p4300_0]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [h4298, hlam, p4300_1]
                                · have p4300_0 := h4300c.1
                                  have p4300_1 := h4300c.2.1
                                  have p4300_2 := h4300c.2.2.1
                                  have p4300_3 := h4300c.2.2.2
                                  linarith only [hlam, p4300_0]
                              · rcases h2bigk with h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c | h4326c
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h0, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h2009, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4200, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4202, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4207, hc23, hlam, hphi, p4326_1, u2ehi0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4207, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4289, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4291, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4326_1, u2ehi0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4326_1, u2ehi1]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hc23, hlam, hphi, p4326_1, u2ehi3]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h0, h4291, hc01, hc23, hlam, hphi, ht12, p4326_1]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hc24, hlam, hphi, p4326_1, u2ehi0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4326_1]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4296, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h0, h4291, h4296, hc01, hc23, hlam, hphi, ht12, p4326_1]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hc25, hlam, hphi, p4326_1, u2ehi0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4326_1]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4297, hlam, p4326_0]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [h4298, hlam, p4326_1]
                                · have p4326_0 := h4326c.1
                                  have p4326_1 := h4326c.2.1
                                  have p4326_2 := h4326c.2.2.1
                                  have p4326_3 := h4326c.2.2.2
                                  linarith only [hlam, p4326_0]
                            · linarith only [h4204, h4206, h4207, h4298, h879, hc23, hlam, hphi, u2ehi3]
                          · linarith only [h1407, h4205, h4207, h4293, h4295, h4297, hlam]
                        · linarith only [h0, h4207, h4296, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4204, h4206, h4289, h4295, h879, hc01, hc13, hlam, hphi]
                    · linarith only [h4205, h4294, h879, hlam]
                  · linarith only [h4204, h4293, h879, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4358 | h4358
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4359 | h4359
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4360 | h4360
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4361 | h4361
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4362 | h4362
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4363 | h4363
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4364 | h4364
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4365 | h4365
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4366 | h4366
                            · linarith only [h4200, h4206, h4366, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h4200, h4358, h4361, h4363, h4366, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h2009, h4205, h4365, hlam]
                        · linarith only [h2009, h4204, h4205, h4206, h4358, h4361, h4363, h4364, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h4200, h4359, h4363, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h4205, h4362, h879, hlam]
                  · linarith only [h4204, h4361, h879, hlam]
                · linarith only [h4358, h4360, hc25, hlam, hphi, u2ehi2]
              · linarith only [h4358, h4359, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4376 | h4376
              · linarith only [h4358, h4376, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4378 | h4378
                · linarith only [h4358, h4378, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4380 | h4380
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4381 | h4381
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4382 | h4382
                      · linarith only [h4200, h4206, h4358, h4380, h4382, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4384 | h4384
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4385 | h4385
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4386 | h4386
                            · linarith only [h0, h4376, h4382, h4386, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h4200, h4386, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h2009, h4205, h4385, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h4204, h4206, h4384, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h4205, h4381, h879, hlam]
                  · linarith only [h4204, h4206, h4380, h879, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4393 | h4393
          · linarith only [h4204, h4205, h4393, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4395 | h4395
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4396 | h4396
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4397 | h4397
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4398 | h4398
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4399 | h4399
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4400 | h4400
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4401 | h4401
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4402 | h4402
                          · linarith only [h4200, h4204, h4205, h4395, h4402, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h2009, h4399, h4402, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h2009, h4204, h4401, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h4200, h4396, h4400, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h2009, h4395, h4399, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h2009, h4395, h4398, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2009, h4395, h4397, hc25, hlam, hphi, u2ehi0]
              · linarith only [h2009, h4395, h4396, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4411 | h4411
              · linarith only [h4395, h4411, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4413 | h4413
                · linarith only [h4395, h4413, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4415 | h4415
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4416 | h4416
                    · linarith only [h4200, h4204, h4205, h4395, h4416, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4418 | h4418
                      · linarith only [h4200, h4393, h4415, h4416, h4418, hc35, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4420 | h4420
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4421 | h4421
                          · linarith only [h0, h4411, h4415, h4416, h4421, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h2009, h4421, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h4204, h4395, h4420, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h4204, h4205, h4415, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4426 | h4426
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4427 | h4427
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4428 | h4428
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4429 | h4429
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4430 | h4430
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4431 | h4431
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4432 | h4432
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4433 | h4433
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4434 | h4434
                        · linarith only [h4204, h4426, h4428, h4434, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h2009, h4431, h4434, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h4202, h4204, h4426, h4427, h4431, h4433, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h4204, h4426, h4432, hc13, hc34, hlam, hphi]
                  · linarith only [h2009, h4428, h4431, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h4429, h4430, hc25, hlam, hphi, u2ehi3]
              · linarith only [h2009, h4428, h4429, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4442 | h4442
              · linarith only [h4428, h4442, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4444 | h4444
                · linarith only [h4428, h4444, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4446 | h4446
                  · linarith only [h2009, h4204, h4428, h4446, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4448 | h4448
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4449 | h4449
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4450 | h4450
                        · linarith only [h4202, h4426, h4446, h4450, h879, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2009, h4450, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h4202, h4204, h4426, h4427, h4446, h4449, h879, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h4426, h4448, h879, hlam]
          · linarith only [h4204, h4426, h4427, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4456 | h4456
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4457 | h4457
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4458 | h4458
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4459 | h4459
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4460 | h4460
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4461 | h4461
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4462 | h4462
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4463 | h4463
                        · linarith only [h2009, h4204, h4463, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2009, h4457, h4460, h4463, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h4200, h4456, h4458, h4462, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h2009, h4204, h4460, h4461, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h2009, h4457, h4460, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2009, h4457, h4459, hc25, hlam, hphi, u2ehi0]
              · linarith only [h2009, h4457, h4458, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4471 | h4471
              · linarith only [h4457, h4471, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4473 | h4473
                · linarith only [h4457, h4473, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4475 | h4475
                  · linarith only [h2009, h4204, h4457, h4475, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4477 | h4477
                    · linarith only [h2009, h4426, h4475, h4477, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4479 | h4479
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4480 | h4480
                        · linarith only [h0, h4457, h4475, h4480, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h2009, h4480, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h4204, h4456, h4471, h4479, hc34, hlam, hphi, ht23, u2ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4484 | h4484
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4485 | h4485
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4486 | h4486
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4487 | h4487
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4488 | h4488
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4489 | h4489
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4490 | h4490
                        · linarith only [h2009, h4204, h4490, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2009, h4490, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h4200, h4485, h4489, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h2009, h4484, h4488, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h2009, h4484, h4487, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h2009, h4484, h4486, hc25, hlam, hphi, u2ehi0]
              · linarith only [h2009, h4484, h4485, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4498 | h4498
              · linarith only [h4484, h4498, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4500 | h4500
                · linarith only [h4484, h4500, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4502 | h4502
                  · linarith only [h2009, h4204, h4484, h4502, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4504 | h4504
                    · linarith only [h2009, h4426, h4502, h4504, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4506 | h4506
                      · linarith only [h2009, h4204, h4456, h4498, h4506, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4508 | h4508
                        · linarith only [h2009, h4204, h4508, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h2009, h4508, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5004000 in
set_option maxHeartbeats 5004000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s2 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg879 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg1407 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2009 | h2009
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x0 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s2_x1 m hb2 hb3 hb5 hg0 hg879 hg1407 h2009

end R2N4
